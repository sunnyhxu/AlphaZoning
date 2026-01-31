"""Z3 SMT solver for city layout generation."""

import z3

from src.models import Building, BuildingType, CityGrid


def solve_city_layout(
    grid_size: int,
    max_height: int = 10,
    max_total_floors: int = 100,
    timeout_ms: int = 30000,
    optimize: bool = False,
    park_positions: list[tuple[int, int]] | None = None,
    min_spacing: int | None = None,
    park_proximity: int | None = None,
    min_residential: int = 0,
    min_commercial: int = 0,
) -> CityGrid | None:
    """
    Generate a valid city layout using Z3.

    Args:
        grid_size: Size of the square grid (grid_size x grid_size).
        max_height: Maximum height for any single building.
        max_total_floors: Maximum sum of all building heights (density limit).
        timeout_ms: Solver timeout in milliseconds.
        optimize: If True, maximize building density (slower). If False, find any valid solution.
        park_positions: List of (x, y) coordinates where parks are placed.
        min_spacing: Minimum Manhattan distance between any two buildings.
        park_proximity: Maximum Manhattan distance from any building to nearest park.
        min_residential: Minimum number of residential buildings to place.
        min_commercial: Minimum number of commercial buildings to place.

    Returns:
        CityGrid with buildings where height > 0, or None if unsatisfiable.
    """
    if optimize:
        solver = z3.Optimize()
    else:
        solver = z3.Solver()
    solver.set("timeout", timeout_ms)

    park_positions = park_positions or []
    park_set = set(park_positions)

    # Declare height variables for each cell
    heights: list[list[z3.ArithRef]] = [
        [z3.Int(f"h_{x}_{y}") for y in range(grid_size)] for x in range(grid_size)
    ]

    # Constraint: heights must be non-negative and within max_height
    # Parks have fixed height of 1
    for x in range(grid_size):
        for y in range(grid_size):
            if (x, y) in park_set:
                solver.add(heights[x][y] == 1)
            else:
                solver.add(heights[x][y] >= 0)
                solver.add(heights[x][y] <= max_height)

    # Constraint: total density (sum of all heights) must not exceed limit
    all_heights = [heights[x][y] for x in range(grid_size) for y in range(grid_size)]
    solver.add(z3.Sum(all_heights) <= max_total_floors)

    # Constraint: building spacing (Manhattan distance)
    if min_spacing is not None:
        for x1 in range(grid_size):
            for y1 in range(grid_size):
                for x2 in range(grid_size):
                    for y2 in range(grid_size):
                        if (x1, y1) < (x2, y2):  # Avoid duplicate pairs
                            dist = abs(x1 - x2) + abs(y1 - y2)
                            if dist < min_spacing:
                                # At most one of these cells can have a building
                                solver.add(
                                    z3.Or(heights[x1][y1] == 0, heights[x2][y2] == 0)
                                )

    # Constraint: park proximity (every non-park building must be within range of a park)
    if park_proximity is not None and park_positions:
        for x in range(grid_size):
            for y in range(grid_size):
                if (x, y) not in park_set:
                    # Check if any park is within range
                    within_range = any(
                        abs(x - px) + abs(y - py) <= park_proximity
                        for px, py in park_positions
                    )
                    if not within_range:
                        # This cell cannot have a building
                        solver.add(heights[x][y] == 0)

    # Building type variables: is_commercial[x][y] = True means commercial, False means residential
    # Only applies to non-park cells with height > 0
    is_commercial: list[list[z3.BoolRef]] = [
        [z3.Bool(f"commercial_{x}_{y}") for y in range(grid_size)] for x in range(grid_size)
    ]

    # Constraint: minimum number of residential buildings
    if min_residential > 0:
        residential_indicators = []
        for x in range(grid_size):
            for y in range(grid_size):
                if (x, y) not in park_set:
                    # Cell is residential if height > 0 and not commercial
                    is_res = z3.And(heights[x][y] > 0, z3.Not(is_commercial[x][y]))
                    residential_indicators.append(z3.If(is_res, 1, 0))
        solver.add(z3.Sum(residential_indicators) >= min_residential)

    # Constraint: minimum number of commercial buildings
    if min_commercial > 0:
        commercial_indicators = []
        for x in range(grid_size):
            for y in range(grid_size):
                if (x, y) not in park_set:
                    # Cell is commercial if height > 0 and is_commercial
                    is_com = z3.And(heights[x][y] > 0, is_commercial[x][y])
                    commercial_indicators.append(z3.If(is_com, 1, 0))
        solver.add(z3.Sum(commercial_indicators) >= min_commercial)

    # Soft constraint: maximize total building coverage (only if optimizing)
    if optimize and isinstance(solver, z3.Optimize):
        solver.maximize(z3.Sum(all_heights))

    result = solver.check()
    if result != z3.sat:
        return None

    model = solver.model()

    # Extract buildings where height > 0
    buildings: list[Building] = []
    for x in range(grid_size):
        for y in range(grid_size):
            h = model.evaluate(heights[x][y]).as_long()
            if h > 0:
                if (x, y) in park_set:
                    buildings.append(Building(x=x, y=y, height=h, building_type=BuildingType.PARK))
                else:
                    # Check if commercial
                    is_com = model.evaluate(is_commercial[x][y])
                    if z3.is_true(is_com):
                        buildings.append(Building(x=x, y=y, height=h, building_type=BuildingType.COMMERCIAL))
                    else:
                        buildings.append(Building(x=x, y=y, height=h, building_type=BuildingType.RESIDENTIAL))

    return CityGrid(size=grid_size, buildings=buildings)
