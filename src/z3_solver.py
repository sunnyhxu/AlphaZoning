"""Z3 SMT solver for city layout generation."""

import random
import z3

from src.models import Building, BuildingType, CityGrid


# Size options for different building types
PARK_SIZES = [(1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3)]
COMMERCIAL_SIZES = [(1, 1), (1, 2), (2, 1), (2, 2)]
RESIDENTIAL_SIZES = [(1, 1)]


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
    max_residential: int | None = None,
    max_commercial: int | None = None,
    max_buildings: int | None = None,
    residential_height_range: tuple[int, int] = (1, 5),
    commercial_height_range: tuple[int, int] = (3, 10),
    allow_large_buildings: bool = True,
) -> CityGrid | None:
    """
    Generate a valid city layout using Z3.

    Args:
        grid_size: Size of the square grid (grid_size x grid_size).
        max_height: Maximum height for any single building (fallback if type ranges not used).
        max_total_floors: Maximum sum of all building heights (density limit).
        timeout_ms: Solver timeout in milliseconds.
        optimize: If True, maximize building density (slower). If False, find any valid solution.
        park_positions: List of (x, y) coordinates where parks are placed.
        min_spacing: Minimum Manhattan distance between any two buildings.
        park_proximity: Maximum Manhattan distance from any building to nearest park.
        min_residential: Minimum number of residential buildings to place.
        min_commercial: Minimum number of commercial buildings to place.
        max_residential: Maximum number of residential buildings (None = unlimited).
        max_commercial: Maximum number of commercial buildings (None = unlimited).
        max_buildings: Maximum total buildings (excluding parks). None = unlimited.
        residential_height_range: (min, max) height for residential buildings.
        commercial_height_range: (min, max) height for commercial buildings.
        allow_large_buildings: Allow parks and commercial to span multiple cells.

    Returns:
        CityGrid with buildings where height > 0, or None if unsatisfiable.
    """
    if optimize:
        solver = z3.Optimize()
    else:
        solver = z3.Solver()
    solver.set("timeout", timeout_ms)

    park_positions = park_positions or []
    
    # Pre-place parks with sizes
    placed_parks: list[Building] = []
    occupied_cells: set[tuple[int, int]] = set()
    
    for px, py in park_positions:
        # Choose park size
        if allow_large_buildings:
            # Try larger sizes first, fall back to smaller if they don't fit
            possible_sizes = [s for s in PARK_SIZES if 
                             px + s[0] <= grid_size and py + s[1] <= grid_size]
            if possible_sizes:
                # Prefer larger parks with some randomness
                size = random.choice(possible_sizes[-3:] if len(possible_sizes) > 3 else possible_sizes)
            else:
                size = (1, 1)
        else:
            size = (1, 1)
        
        # Check for conflicts with already placed parks
        new_cells = [(px + dx, py + dy) for dx in range(size[0]) for dy in range(size[1])]
        if any(cell in occupied_cells for cell in new_cells):
            # Conflict - use 1x1 at the original position
            size = (1, 1)
            new_cells = [(px, py)]
        
        park = Building(x=px, y=py, height=1, width=size[0], depth=size[1], building_type=BuildingType.PARK)
        placed_parks.append(park)
        occupied_cells.update(new_cells)

    # Declare height variables for each cell
    heights: list[list[z3.ArithRef]] = [
        [z3.Int(f"h_{x}_{y}") for y in range(grid_size)] for x in range(grid_size)
    ]

    # Building type variables: is_commercial[x][y] = True means commercial, False means residential
    is_commercial: list[list[z3.BoolRef]] = [
        [z3.Bool(f"commercial_{x}_{y}") for y in range(grid_size)] for x in range(grid_size)
    ]

    # Constraint: heights based on building type
    res_min, res_max = residential_height_range
    com_min, com_max = commercial_height_range

    for x in range(grid_size):
        for y in range(grid_size):
            if (x, y) in occupied_cells:
                # Park cell - fixed height
                solver.add(heights[x][y] == 1)
            else:
                # Height is either 0 (empty) or within valid range for building type
                is_empty = heights[x][y] == 0
                is_valid_residential = z3.And(
                    z3.Not(is_commercial[x][y]),
                    heights[x][y] >= res_min,
                    heights[x][y] <= res_max
                )
                is_valid_commercial = z3.And(
                    is_commercial[x][y],
                    heights[x][y] >= com_min,
                    heights[x][y] <= com_max
                )
                solver.add(z3.Or(is_empty, is_valid_residential, is_valid_commercial))
                solver.add(heights[x][y] >= 0)
                solver.add(heights[x][y] <= max(res_max, com_max, max_height))

    # Constraint: total density (sum of all heights) must not exceed limit
    all_heights = [heights[x][y] for x in range(grid_size) for y in range(grid_size)]
    solver.add(z3.Sum(all_heights) <= max_total_floors)

    # Constraint: building spacing (Manhattan distance)
    # Applies to ALL building types including parks
    if min_spacing is not None and min_spacing > 1:
        for x1 in range(grid_size):
            for y1 in range(grid_size):
                for x2 in range(grid_size):
                    for y2 in range(grid_size):
                        if (x1, y1) < (x2, y2):  # Avoid duplicate pairs
                            dist = abs(x1 - x2) + abs(y1 - y2)
                            if dist < min_spacing:
                                both_are_buildings = z3.And(
                                    heights[x1][y1] > 0,
                                    heights[x2][y2] > 0
                                )
                                solver.add(z3.Not(both_are_buildings))

    # Constraint: park proximity (every non-park cell with building must be within range of a park)
    if park_proximity is not None and placed_parks:
        for x in range(grid_size):
            for y in range(grid_size):
                if (x, y) not in occupied_cells:
                    # Check if any park cell is within range
                    within_range = any(
                        abs(x - px) + abs(y - py) <= park_proximity
                        for park in placed_parks
                        for px, py in park.footprint()
                    )
                    if not within_range:
                        solver.add(heights[x][y] == 0)

    # Collect building indicators for non-park cells
    building_indicators = []
    residential_indicators = []
    commercial_indicators = []

    for x in range(grid_size):
        for y in range(grid_size):
            if (x, y) not in occupied_cells:
                is_building = heights[x][y] > 0
                building_indicators.append(z3.If(is_building, 1, 0))

                is_res = z3.And(heights[x][y] > 0, z3.Not(is_commercial[x][y]))
                residential_indicators.append(z3.If(is_res, 1, 0))

                is_com = z3.And(heights[x][y] > 0, is_commercial[x][y])
                commercial_indicators.append(z3.If(is_com, 1, 0))

    # Constraint: maximum total buildings (excluding parks)
    if max_buildings is not None:
        solver.add(z3.Sum(building_indicators) <= max_buildings)

    # Constraint: minimum number of residential buildings
    if min_residential > 0:
        solver.add(z3.Sum(residential_indicators) >= min_residential)

    # Constraint: maximum number of residential buildings
    if max_residential is not None:
        solver.add(z3.Sum(residential_indicators) <= max_residential)

    # Constraint: minimum number of commercial buildings
    if min_commercial > 0:
        solver.add(z3.Sum(commercial_indicators) >= min_commercial)

    # Constraint: maximum number of commercial buildings
    if max_commercial is not None:
        solver.add(z3.Sum(commercial_indicators) <= max_commercial)

    # Soft constraint: maximize total building coverage (only if optimizing)
    if optimize and isinstance(solver, z3.Optimize):
        solver.maximize(z3.Sum(all_heights))

    result = solver.check()
    if result != z3.sat:
        return None

    model = solver.model()

    # Extract buildings where height > 0
    buildings: list[Building] = list(placed_parks)  # Start with pre-placed parks
    
    # Track which cells we've already processed (for multi-cell commercial)
    processed_cells: set[tuple[int, int]] = set(occupied_cells)
    
    for x in range(grid_size):
        for y in range(grid_size):
            if (x, y) in processed_cells:
                continue
                
            h = model.evaluate(heights[x][y]).as_long()
            if h > 0:
                is_com = model.evaluate(is_commercial[x][y])
                if z3.is_true(is_com):
                    # Try to create multi-cell commercial building
                    if allow_large_buildings:
                        size = _find_best_commercial_size(
                            x, y, grid_size, model, heights, is_commercial, processed_cells
                        )
                    else:
                        size = (1, 1)
                    
                    buildings.append(Building(
                        x=x, y=y, height=h, 
                        width=size[0], depth=size[1],
                        building_type=BuildingType.COMMERCIAL
                    ))
                    # Mark all cells as processed
                    for dx in range(size[0]):
                        for dy in range(size[1]):
                            processed_cells.add((x + dx, y + dy))
                else:
                    buildings.append(Building(
                        x=x, y=y, height=h,
                        width=1, depth=1,
                        building_type=BuildingType.RESIDENTIAL
                    ))
                    processed_cells.add((x, y))

    return CityGrid(size=grid_size, buildings=buildings)


def _find_best_commercial_size(
    x: int, y: int, grid_size: int,
    model: z3.ModelRef,
    heights: list[list[z3.ArithRef]],
    is_commercial: list[list[z3.BoolRef]],
    processed_cells: set[tuple[int, int]]
) -> tuple[int, int]:
    """Find the best size for a commercial building starting at (x, y)."""
    base_height = model.evaluate(heights[x][y]).as_long()
    
    # Try sizes from largest to smallest
    for width, depth in reversed(COMMERCIAL_SIZES):
        if x + width > grid_size or y + depth > grid_size:
            continue
            
        valid = True
        for dx in range(width):
            for dy in range(depth):
                nx, ny = x + dx, y + dy
                if (nx, ny) in processed_cells:
                    valid = False
                    break
                    
                h = model.evaluate(heights[nx][ny]).as_long()
                is_com = model.evaluate(is_commercial[nx][ny])
                
                # All cells must be commercial with same height
                if h != base_height or not z3.is_true(is_com):
                    valid = False
                    break
            if not valid:
                break
                
        if valid:
            return (width, depth)
    
    return (1, 1)
