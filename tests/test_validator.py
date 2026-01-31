"""Tests for independent solution validator."""

from src.models import Building, BuildingType, CityGrid, Constraint
from src.validator import validate_solution


def test_valid_solution() -> None:
    """All constraints satisfied returns is_valid=True."""
    grid = CityGrid(
        size=5,
        buildings=[
            Building(x=0, y=0, height=3),
            Building(x=2, y=2, height=4, building_type=BuildingType.PARK),
            Building(x=4, y=4, height=5),
        ],
    )

    constraints = [
        Constraint(type="height_limit", params={"max_floors": 10}),
        Constraint(type="density_limit", params={"max_total_floors": 50}),
        Constraint(type="building_spacing", params={"min_distance": 2}),
        Constraint(type="park_proximity", params={"max_distance": 4}),
    ]

    is_valid, report = validate_solution(grid, constraints)

    assert is_valid is True
    assert len(report["satisfied"]) == 4
    assert len(report["violations"]) == 0
    assert report["satisfaction_rate"] == 1.0


def test_height_violation() -> None:
    """Building exceeding height_limit is caught."""
    grid = CityGrid(
        size=5,
        buildings=[
            Building(x=0, y=0, height=5),
            Building(x=2, y=2, height=15),  # Exceeds limit
        ],
    )

    constraints = [
        Constraint(type="height_limit", params={"max_floors": 10}),
    ]

    is_valid, report = validate_solution(grid, constraints)

    assert is_valid is False
    assert "height_limit" in report["violations"]
    assert len(report["violations"]["height_limit"]) == 1
    assert "15" in report["violations"]["height_limit"][0]
    assert "exceeds" in report["violations"]["height_limit"][0].lower()


def test_density_violation() -> None:
    """Total density exceeding limit is caught."""
    grid = CityGrid(
        size=5,
        buildings=[
            Building(x=0, y=0, height=30),
            Building(x=1, y=1, height=30),
        ],
    )

    constraints = [
        Constraint(type="density_limit", params={"max_total_floors": 50}),
    ]

    is_valid, report = validate_solution(grid, constraints)

    assert is_valid is False
    assert "density_limit" in report["violations"]
    assert "60" in report["violations"]["density_limit"][0]  # 30+30=60


def test_spacing_violation() -> None:
    """Buildings too close together are caught."""
    grid = CityGrid(
        size=5,
        buildings=[
            Building(x=0, y=0, height=5),
            Building(x=1, y=0, height=5),  # Distance 1, needs 3
        ],
    )

    constraints = [
        Constraint(type="building_spacing", params={"min_distance": 3}),
    ]

    is_valid, report = validate_solution(grid, constraints)

    assert is_valid is False
    assert "building_spacing" in report["violations"]
    assert "1 apart" in report["violations"]["building_spacing"][0]


def test_park_proximity_violation() -> None:
    """Building too far from park is caught."""
    grid = CityGrid(
        size=10,
        buildings=[
            Building(x=0, y=0, height=1, building_type=BuildingType.PARK),
            Building(x=9, y=9, height=5),  # Distance 18 from park
        ],
    )

    constraints = [
        Constraint(type="park_proximity", params={"max_distance": 3}),
    ]

    is_valid, report = validate_solution(grid, constraints)

    assert is_valid is False
    assert "park_proximity" in report["violations"]
    assert "18" in report["violations"]["park_proximity"][0]


def test_partial_satisfaction() -> None:
    """Some constraints pass, some fail - correct satisfaction rate."""
    grid = CityGrid(
        size=5,
        buildings=[
            Building(x=0, y=0, height=5),
            Building(x=1, y=1, height=15),  # Height violation
        ],
    )

    constraints = [
        Constraint(type="height_limit", params={"max_floors": 10}),  # Fail
        Constraint(type="density_limit", params={"max_total_floors": 100}),  # Pass
        Constraint(type="building_spacing", params={"min_distance": 1}),  # Pass
    ]

    is_valid, report = validate_solution(grid, constraints)

    assert is_valid is False
    assert len(report["satisfied"]) == 2
    assert "density_limit" in report["satisfied"]
    assert "building_spacing" in report["satisfied"]
    assert len(report["violations"]) == 1
    assert "height_limit" in report["violations"]
    assert report["satisfaction_rate"] == 2 / 3


def test_empty_constraints() -> None:
    """Empty constraint list returns valid with 100% satisfaction."""
    grid = CityGrid(size=5, buildings=[Building(x=0, y=0, height=10)])

    is_valid, report = validate_solution(grid, [])

    assert is_valid is True
    assert report["satisfaction_rate"] == 1.0


def test_no_parks_with_proximity_constraint() -> None:
    """Park proximity constraint with no parks reports violation."""
    grid = CityGrid(
        size=5,
        buildings=[
            Building(x=0, y=0, height=5),
            Building(x=2, y=2, height=5),
        ],
    )

    constraints = [
        Constraint(type="park_proximity", params={"max_distance": 2}),
    ]

    is_valid, report = validate_solution(grid, constraints)

    assert is_valid is False
    assert "park_proximity" in report["violations"]
    assert "No parks" in report["violations"]["park_proximity"][0]


def test_unknown_constraint_type() -> None:
    """Unknown constraint type is reported as violation."""
    grid = CityGrid(size=5, buildings=[])

    constraints = [
        Constraint(type="unknown_constraint", params={}),
    ]

    is_valid, report = validate_solution(grid, constraints)

    assert is_valid is False
    assert "unknown_constraint" in report["violations"]
    assert "Unknown" in report["violations"]["unknown_constraint"][0]
