"""Independent validation of city layouts against constraints."""

from src.models import BuildingType, CityGrid, Constraint


def validate_solution(
    grid: CityGrid, constraints: list[Constraint]
) -> tuple[bool, dict]:
    """
    Validate a city layout against a list of constraints.

    Args:
        grid: The city grid to validate.
        constraints: List of constraints to check.

    Returns:
        Tuple of (is_valid, report) where report contains:
        - satisfied: list of constraint types that passed
        - violations: dict of {constraint_type: [violation details]}
        - satisfaction_rate: float (0.0-1.0)
    """
    satisfied: list[str] = []
    violations: dict[str, list[str]] = {}

    for constraint in constraints:
        constraint_violations = _validate_constraint(grid, constraint)
        if constraint_violations:
            violations[constraint.type] = constraint_violations
        else:
            satisfied.append(constraint.type)

    total = len(constraints)
    satisfaction_rate = len(satisfied) / total if total > 0 else 1.0
    is_valid = len(violations) == 0

    return is_valid, {
        "satisfied": satisfied,
        "violations": violations,
        "satisfaction_rate": satisfaction_rate,
    }


def count_satisfied_buildings(grid: CityGrid, constraints: list[Constraint]) -> tuple[int, int]:
    """
    Count buildings that satisfy all constraints.
    
    Returns:
        Tuple of (satisfied_building_count, total_building_count)
    """
    if not grid.buildings:
        return 0, 0
    
    # For each building, check if it violates any constraint
    buildings_with_violations: set[tuple[int, int]] = set()
    
    for constraint in constraints:
        if constraint.type == "height_limit":
            max_floors = constraint.params.get("max_floors", float("inf"))
            for b in grid.buildings:
                if b.height > max_floors:
                    buildings_with_violations.add((b.x, b.y))
        
        elif constraint.type == "park_proximity":
            max_distance = constraint.params.get("max_distance", float("inf"))
            parks = grid.get_parks()
            if parks:
                for b in grid.get_non_parks():
                    min_dist = min(
                        abs(b.x - p.x) + abs(b.y - p.y) 
                        for p in parks
                        for px, py in [(p.x + dx, p.y + dy) for dx in range(p.width) for dy in range(p.depth)]
                    ) if parks else float("inf")
                    # Simpler: use anchor-to-anchor for speed
                    min_dist = min(abs(b.x - p.x) + abs(b.y - p.y) for p in parks)
                    if min_dist > max_distance:
                        buildings_with_violations.add((b.x, b.y))
        
        elif constraint.type == "building_spacing":
            min_distance = constraint.params.get("min_distance", 0)
            buildings = grid.buildings
            for i, b1 in enumerate(buildings):
                for b2 in buildings[i + 1:]:
                    dist = abs(b1.x - b2.x) + abs(b1.y - b2.y)
                    if dist < min_distance:
                        buildings_with_violations.add((b1.x, b1.y))
                        buildings_with_violations.add((b2.x, b2.y))
    
    total = len(grid.buildings)
    satisfied = total - len(buildings_with_violations)
    return satisfied, total


def _validate_constraint(grid: CityGrid, constraint: Constraint) -> list[str]:
    """Validate a single constraint, returning list of violation messages."""
    validators = {
        "height_limit": _validate_height_limit,
        "density_limit": _validate_density_limit,
        "building_spacing": _validate_building_spacing,
        "park_proximity": _validate_park_proximity,
    }

    validator = validators.get(constraint.type)
    if validator is None:
        return [f"Unknown constraint type: {constraint.type}"]

    return validator(grid, constraint.params)


def _validate_height_limit(grid: CityGrid, params: dict) -> list[str]:
    """Validate that no building exceeds max height."""
    max_floors = params.get("max_floors", float("inf"))
    violations = []

    for building in grid.buildings:
        if building.height > max_floors:
            violations.append(
                f"Building at ({building.x}, {building.y}) has height {building.height}, "
                f"exceeds limit of {max_floors}"
            )

    return violations


def _validate_density_limit(grid: CityGrid, params: dict) -> list[str]:
    """Validate that total building height doesn't exceed density limit."""
    max_total_floors = params.get("max_total_floors", float("inf"))
    total = grid.total_height()

    if total > max_total_floors:
        return [f"Total density {total} exceeds limit of {max_total_floors}"]

    return []


def _validate_building_spacing(grid: CityGrid, params: dict) -> list[str]:
    """Validate that buildings maintain minimum spacing."""
    min_distance = params.get("min_distance", 0)
    violations = []
    buildings = grid.buildings

    for i, b1 in enumerate(buildings):
        for b2 in buildings[i + 1 :]:
            dist = abs(b1.x - b2.x) + abs(b1.y - b2.y)
            if dist < min_distance:
                violations.append(
                    f"Buildings at ({b1.x}, {b1.y}) and ({b2.x}, {b2.y}) "
                    f"are {dist} apart, minimum is {min_distance}"
                )

    return violations


def _validate_park_proximity(grid: CityGrid, params: dict) -> list[str]:
    """Validate that all non-park buildings are within range of a park."""
    max_distance = params.get("max_distance", float("inf"))
    violations = []

    parks = grid.get_parks()
    if not parks:
        non_parks = grid.get_non_parks()
        if non_parks:
            return ["No parks exist but park_proximity constraint is set"]
        return []

    for building in grid.get_non_parks():
        min_dist = min(
            abs(building.x - p.x) + abs(building.y - p.y) for p in parks
        )
        if min_dist > max_distance:
            violations.append(
                f"Building at ({building.x}, {building.y}) is {min_dist} from nearest park, "
                f"maximum is {max_distance}"
            )

    return violations
