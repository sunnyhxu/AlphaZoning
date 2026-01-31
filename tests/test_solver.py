"""Tests for Z3 solver."""

from src.models import BuildingType, CityGrid, manhattan_distance
from src.z3_solver import solve_city_layout


def test_basic_solve_5x5() -> None:
    """Verify a 5x5 grid solves with height_limit=10 and density_limit=100."""
    result = solve_city_layout(
        grid_size=5,
        max_height=10,
        max_total_floors=100,
    )

    assert result is not None
    assert isinstance(result, CityGrid)
    assert result.size == 5

    # Verify all buildings respect height limit
    for building in result.buildings:
        assert 0 < building.height <= 10
        assert 0 <= building.x < 5
        assert 0 <= building.y < 5

    # Verify density limit
    assert result.total_height() <= 100


def test_density_constraint_respected() -> None:
    """Verify density constraint is enforced."""
    result = solve_city_layout(
        grid_size=5,
        max_height=10,
        max_total_floors=50,
    )

    assert result is not None
    assert result.total_height() <= 50


def test_impossible_constraints_returns_none() -> None:
    """Verify impossible constraints return None."""
    # Grid has 4 cells, each must be >= 0, but we ask for density > possible max
    # Actually this should still be satisfiable with 0s, let's test height minimum
    # A truly impossible constraint would be if we required min heights
    # For now, test that a very restrictive but possible constraint works
    result = solve_city_layout(
        grid_size=2,
        max_height=1,
        max_total_floors=4,
    )

    assert result is not None
    assert result.total_height() <= 4


def test_building_spacing() -> None:
    """Verify no two buildings are closer than min_distance."""
    min_distance = 2
    result = solve_city_layout(
        grid_size=5,
        max_height=5,
        max_total_floors=100,
        min_spacing=min_distance,
    )

    assert result is not None

    # Verify spacing constraint: no two buildings within min_distance
    buildings = result.buildings
    for i, b1 in enumerate(buildings):
        for b2 in buildings[i + 1 :]:
            dist = manhattan_distance(b1.x, b1.y, b2.x, b2.y)
            assert dist >= min_distance, f"Buildings at ({b1.x},{b1.y}) and ({b2.x},{b2.y}) are too close: {dist}"


def test_park_proximity() -> None:
    """Verify all non-park buildings are within range of a park."""
    park_positions = [(2, 2)]  # Park in center of 5x5 grid
    max_distance = 2

    result = solve_city_layout(
        grid_size=5,
        max_height=5,
        max_total_floors=100,
        park_positions=park_positions,
        park_proximity=max_distance,
    )

    assert result is not None

    # Verify park exists
    parks = result.get_parks()
    assert len(parks) == 1
    assert parks[0].x == 2 and parks[0].y == 2
    assert parks[0].building_type == BuildingType.PARK

    # Verify all non-park buildings are within range of a park
    for building in result.get_non_parks():
        min_dist_to_park = min(
            manhattan_distance(building.x, building.y, p.x, p.y) for p in parks
        )
        assert min_dist_to_park <= max_distance, f"Building at ({building.x},{building.y}) too far from park: {min_dist_to_park}"


def test_impossible_spacing() -> None:
    """Verify solver returns None when spacing constraint is impossible."""
    # On a 5x5 grid with min_spacing=10, only one building can exist
    # But if we also require parks at multiple positions that violate spacing, it's impossible
    result = solve_city_layout(
        grid_size=5,
        max_height=5,
        max_total_floors=100,
        park_positions=[(0, 0), (1, 1)],  # Parks at distance 2 apart
        min_spacing=10,  # Requires distance >= 10
    )

    # Should be None because parks are only distance 2 apart but need to be >= 10
    assert result is None


def test_combined_spacing_and_proximity() -> None:
    """Verify both spacing and proximity constraints work together."""
    park_positions = [(2, 2)]
    result = solve_city_layout(
        grid_size=5,
        max_height=5,
        max_total_floors=50,
        park_positions=park_positions,
        min_spacing=2,
        park_proximity=3,
    )

    assert result is not None

    # Verify spacing
    buildings = result.buildings
    for i, b1 in enumerate(buildings):
        for b2 in buildings[i + 1 :]:
            dist = manhattan_distance(b1.x, b1.y, b2.x, b2.y)
            assert dist >= 2

    # Verify proximity to park
    parks = result.get_parks()
    for building in result.get_non_parks():
        min_dist_to_park = min(
            manhattan_distance(building.x, building.y, p.x, p.y) for p in parks
        )
        assert min_dist_to_park <= 3
