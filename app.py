"""AlphaZoning - Streamlit Web Interface."""

import json
import random

from dotenv import load_dotenv
import streamlit as st

# Load environment variables from .env file
load_dotenv()

from src import (
    Building,
    BuildingType,
    CityGrid,
    Constraint,
    load_example_constraints,
    parse_constraints,
    solve_layout,
    validate_solution,
    count_satisfied_buildings,
    visualize_city,
)

# Page config
st.set_page_config(
    page_title="AlphaZoning",
    page_icon="🏙️",
    layout="wide",
)


def init_session_state() -> None:
    """Initialize session state variables."""
    if "grid" not in st.session_state:
        st.session_state.grid = None
    if "constraints" not in st.session_state:
        st.session_state.constraints = []
    if "validation_report" not in st.session_state:
        st.session_state.validation_report = None
    if "error_message" not in st.session_state:
        st.session_state.error_message = None
    if "user_input" not in st.session_state:
        st.session_state.user_input = ""


def constraints_to_solver_params(constraints: list[Constraint]) -> dict:
    """Convert constraint list to solver parameters."""
    params: dict = {}
    for c in constraints:
        if c.type == "height_limit":
            params["max_height"] = c.params.get("max_floors", 10)
        elif c.type == "density_limit":
            params["max_total_floors"] = c.params.get("max_total_floors", 100)
        elif c.type == "building_spacing":
            params["min_spacing"] = c.params.get("min_distance")
        elif c.type == "park_proximity":
            params["park_proximity"] = c.params.get("max_distance")
    return params


def generate_greedy_layout(
    grid_size: int,
    num_buildings: int,
    num_parks: int,
    max_height: int = 10,
    residential_ratio: float = 0.6,
    allow_large_buildings: bool = True,
    park_proximity: int | None = None,
    min_spacing: int | None = None,
) -> CityGrid:
    """
    Generate a city layout using greedy constraint-aware placement.
    
    Strategy:
    1. Place parks to maximize grid coverage (spread evenly)
    2. Place buildings greedily, prioritizing positions that:
       - Are within park_proximity of a park
       - Respect min_spacing from other buildings
    """
    buildings: list[Building] = []
    occupied: set[tuple[int, int]] = set()
    
    # Park size options
    park_sizes = [(2, 2), (2, 3), (3, 2), (3, 3), (1, 2), (2, 1)] if allow_large_buildings else [(1, 1)]
    commercial_sizes = [(1, 1), (1, 2), (2, 1), (2, 2)] if allow_large_buildings else [(1, 1)]
    
    # --- STEP 1: Place parks strategically to maximize coverage ---
    # Use a grid-based placement to spread parks evenly
    if num_parks > 0:
        # Calculate optimal park positions for coverage
        parks_per_side = max(1, int(num_parks ** 0.5))
        step = grid_size // (parks_per_side + 1)
        
        park_positions = []
        for i in range(parks_per_side):
            for j in range(parks_per_side):
                if len(park_positions) < num_parks:
                    px = step * (i + 1)
                    py = step * (j + 1)
                    park_positions.append((px, py))
        
        # Add remaining parks at strategic positions
        while len(park_positions) < num_parks:
            # Find position furthest from existing parks
            best_pos = None
            best_min_dist = -1
            for x in range(grid_size):
                for y in range(grid_size):
                    if park_positions:
                        min_dist = min(abs(x - px) + abs(y - py) for px, py in park_positions)
                    else:
                        min_dist = grid_size * 2
                    if min_dist > best_min_dist:
                        best_min_dist = min_dist
                        best_pos = (x, y)
            if best_pos:
                park_positions.append(best_pos)
        
        # Place parks at calculated positions
        for px, py in park_positions:
            # Try different sizes, prefer larger
            placed = False
            for w, d in park_sizes:
                if px + w <= grid_size and py + d <= grid_size:
                    cells = [(px + dx, py + dy) for dx in range(w) for dy in range(d)]
                    if all(c not in occupied for c in cells):
                        buildings.append(Building(x=px, y=py, height=1, width=w, depth=d, building_type=BuildingType.PARK))
                        occupied.update(cells)
                        placed = True
                        break
            # Fallback to 1x1
            if not placed and (px, py) not in occupied:
                buildings.append(Building(x=px, y=py, height=1, width=1, depth=1, building_type=BuildingType.PARK))
                occupied.add((px, py))
    
    # Get park footprints for proximity calculation
    park_cells = set()
    for b in buildings:
        if b.building_type == BuildingType.PARK:
            for dx in range(b.width):
                for dy in range(b.depth):
                    park_cells.add((b.x + dx, b.y + dy))
    
    # --- STEP 2: Greedy building placement ---
    def get_min_park_distance(x: int, y: int) -> int:
        """Get Manhattan distance to nearest park cell."""
        if not park_cells:
            return 0
        return min(abs(x - px) + abs(y - py) for px, py in park_cells)
    
    def get_min_building_distance(x: int, y: int, w: int, d: int) -> int:
        """Get minimum distance to any existing non-park building."""
        min_dist = float('inf')
        cells = [(x + dx, y + dy) for dx in range(w) for dy in range(d)]
        for b in buildings:
            if b.building_type == BuildingType.PARK:
                continue
            for bx, by in b.footprint():
                for cx, cy in cells:
                    dist = abs(cx - bx) + abs(cy - by)
                    min_dist = min(min_dist, dist)
        return min_dist if min_dist != float('inf') else grid_size * 2
    
    def score_position(x: int, y: int, w: int, d: int) -> float:
        """Score a position based on constraint satisfaction."""
        score = 0.0
        
        # Prefer positions close to parks (if park_proximity constraint)
        park_dist = get_min_park_distance(x, y)
        if park_proximity is not None:
            if park_dist <= park_proximity:
                score += 100  # Big bonus for satisfying proximity
            else:
                score -= (park_dist - park_proximity) * 10  # Penalty for violation
        else:
            score += 50 - park_dist  # Mild preference for park proximity
        
        # Respect spacing constraint
        building_dist = get_min_building_distance(x, y, w, d)
        if min_spacing is not None:
            if building_dist >= min_spacing:
                score += 50  # Bonus for satisfying spacing
            else:
                score -= (min_spacing - building_dist) * 20  # Penalty for violation
        
        # Add small random factor to break ties
        score += random.random() * 5
        
        return score
    
    # Place buildings
    residential_count = int(num_buildings * residential_ratio)
    
    for i in range(num_buildings):
        if i < residential_count:
            b_type = BuildingType.RESIDENTIAL
            sizes = [(1, 1)]
            height = random.randint(1, min(5, max_height))
        else:
            b_type = BuildingType.COMMERCIAL
            sizes = commercial_sizes
            height = random.randint(3, max_height)
        
        # Find best position using greedy scoring
        best_pos = None
        best_score = float('-inf')
        best_size = (1, 1)
        
        # Sample candidate positions (full search too slow)
        candidates = []
        for _ in range(50):
            for w, d in sizes:
                if grid_size - w >= 0 and grid_size - d >= 0:
                    x = random.randint(0, grid_size - w)
                    y = random.randint(0, grid_size - d)
                    candidates.append((x, y, w, d))
        
        for x, y, w, d in candidates:
            cells = [(x + dx, y + dy) for dx in range(w) for dy in range(d)]
            if all(c not in occupied for c in cells):
                score = score_position(x, y, w, d)
                if score > best_score:
                    best_score = score
                    best_pos = (x, y)
                    best_size = (w, d)
        
        if best_pos:
            x, y = best_pos
            w, d = best_size
            cells = [(x + dx, y + dy) for dx in range(w) for dy in range(d)]
            buildings.append(Building(x=x, y=y, height=height, width=w, depth=d, building_type=b_type))
            occupied.update(cells)
    
    return CityGrid(size=grid_size, buildings=buildings)


def generate_layout(
    user_input: str,
    grid_size: int,
    min_residential: int = 0,
    min_commercial: int = 0,
    max_residential: int | None = None,
    max_commercial: int | None = None,
    max_buildings: int | None = None,
    num_parks: int = 0,
    allow_large_buildings: bool = True,
) -> None:
    """Generate city layout from user input."""
    st.session_state.error_message = None
    st.session_state.grid = None
    st.session_state.validation_report = None

    # Parse constraints (no caching - always re-parse to allow regeneration)
    if user_input.strip():
        parsed = parse_constraints(user_input)
        st.session_state.constraints = parsed
    else:
        st.session_state.constraints = []

    # Convert to solver params
    solver_params = constraints_to_solver_params(st.session_state.constraints)

    # Place parks in a distributed pattern
    park_positions = None
    if num_parks > 0 or "park_proximity" in solver_params:
        park_positions = []
        actual_parks = max(num_parks, 1 if "park_proximity" in solver_params else 0)
        # Distribute parks across the grid
        if actual_parks == 1:
            center = grid_size // 2
            park_positions = [(center, center)]
        else:
            # Spread parks evenly
            step = grid_size // (actual_parks + 1)
            for i in range(actual_parks):
                px = step * (i + 1)
                py = step * ((i % 2) + 1) if actual_parks > 2 else grid_size // 2
                if px < grid_size and py < grid_size:
                    park_positions.append((px, py))

    # Solve with Z3
    grid = solve_layout(
        grid_size=grid_size,
        park_positions=park_positions,
        min_residential=min_residential,
        min_commercial=min_commercial,
        max_residential=max_residential,
        max_commercial=max_commercial,
        max_buildings=max_buildings,
        allow_large_buildings=allow_large_buildings,
        **solver_params,
    )

    if grid is None:
        st.session_state.error_message = (
            "Could not generate a valid layout with these constraints. "
            "Try relaxing the constraints (larger grid, lower density, smaller spacing)."
        )
        return

    # Check satisfaction rate (per-building)
    constraints = st.session_state.constraints
    if constraints:
        satisfied, total = count_satisfied_buildings(grid, constraints)
        satisfaction_rate = satisfied / total if total > 0 else 1.0
        
        # Fallback: if satisfaction < 90%, try random sampling
        if satisfaction_rate < 0.9:
            best_grid = grid
            best_satisfaction = satisfaction_rate
            
            max_height = solver_params.get("max_height", 10)
            num_buildings_target = max_buildings if max_buildings else int(grid_size * grid_size * 0.5)
            
            for _ in range(100):  # Fewer iterations since greedy is smarter
                greedy_grid = generate_greedy_layout(
                    grid_size=grid_size,
                    num_buildings=num_buildings_target,
                    num_parks=num_parks,
                    max_height=max_height,
                    park_proximity=solver_params.get("park_proximity"),
                    min_spacing=solver_params.get("min_spacing"),
                )
                sat, tot = count_satisfied_buildings(greedy_grid, constraints)
                rate = sat / tot if tot > 0 else 0
                if rate > best_satisfaction:
                    best_grid = greedy_grid
                    best_satisfaction = rate
                    if rate >= 0.95:  # Early exit if good enough
                        break
            
            grid = best_grid

    st.session_state.grid = grid

    # Validate and compute per-building satisfaction
    if st.session_state.constraints:
        is_valid, report = validate_solution(grid, st.session_state.constraints)
        # Override satisfaction_rate with per-building calculation
        satisfied, total = count_satisfied_buildings(grid, st.session_state.constraints)
        report["satisfaction_rate"] = satisfied / total if total > 0 else 1.0
        report["satisfied_buildings"] = satisfied
        report["total_buildings"] = total
        st.session_state.validation_report = report


def load_preset(preset_name: str) -> list[Constraint]:
    """Load preset constraints from examples."""
    return load_example_constraints(preset_name)


def main() -> None:
    """Main application entry point."""
    init_session_state()

    # Header
    st.title("🏙️ AlphaZoning")
    st.caption("Neuro-Symbolic Urban Design with Formal Verification")

    # Sidebar
    with st.sidebar:
        st.header("City Configuration")

        # Natural language input
        user_input = st.text_area(
            "Describe your city",
            value=st.session_state.user_input,
            placeholder="e.g., eco-friendly city with parks everywhere, max 5 floors",
            height=100,
            key="user_input_widget",
        )
        # Sync widget value back to session state
        st.session_state.user_input = user_input

        # Grid size
        grid_size = st.slider("Grid Size", min_value=5, max_value=15, value=10)

        # Building counts
        st.subheader("Building Counts")
        
        # Total buildings limit
        max_cells = grid_size * grid_size
        default_max_buildings = int(max_cells * 0.6)  # 60% coverage default
        max_buildings = st.slider(
            "Max Buildings",
            min_value=1,
            max_value=max_cells,
            value=default_max_buildings,
            help="Maximum total buildings (excluding parks). Controls grid coverage.",
        )
        
        st.caption("Residential")
        col_res_min, col_res_max = st.columns(2)
        with col_res_min:
            min_residential = st.number_input(
                "Min",
                min_value=0,
                max_value=max_buildings,
                value=5,
                help="Minimum residential buildings",
                key="min_res",
            )
        with col_res_max:
            max_residential = st.number_input(
                "Max",
                min_value=0,
                max_value=max_buildings,
                value=max_buildings,
                help="Maximum residential buildings",
                key="max_res",
            )
        
        st.caption("Commercial")
        col_com_min, col_com_max = st.columns(2)
        with col_com_min:
            min_commercial = st.number_input(
                "Min",
                min_value=0,
                max_value=max_buildings,
                value=3,
                help="Minimum commercial buildings",
                key="min_com",
            )
        with col_com_max:
            max_commercial = st.number_input(
                "Max",
                min_value=0,
                max_value=max_buildings,
                value=int(max_buildings * 0.4),  # Default 40% max commercial
                help="Maximum commercial buildings",
                key="max_com",
            )
        
        num_parks = st.number_input(
            "Parks",
            min_value=0,
            max_value=grid_size * grid_size // 4,
            value=2,
            help="Number of parks to place",
        )
        
        # Multi-cell buildings toggle
        allow_large_buildings = st.checkbox(
            "Allow large buildings",
            value=True,
            help="Allow parks and commercial buildings to span multiple cells",
        )

        # Presets
        st.subheader("Presets")
        col1, col2, col3 = st.columns(3)

        with col1:
            if st.button("🌳 Green", use_container_width=True):
                st.session_state.user_input = "eco-friendly with parks"
                st.rerun()

        with col2:
            if st.button("🏢 Dense", use_container_width=True):
                st.session_state.user_input = "dense urban downtown"
                st.rerun()

        with col3:
            if st.button("👨‍👩‍👧 Family", use_container_width=True):
                st.session_state.user_input = "family-friendly neighborhood"
                st.rerun()

        st.divider()

        # Generate button
        if st.button("🚀 Generate Layout", type="primary", use_container_width=True):
            with st.spinner("Generating city layout..."):
                generate_layout(
                    user_input,
                    grid_size,
                    min_residential=min_residential,
                    min_commercial=min_commercial,
                    max_residential=max_residential if max_residential < max_buildings else None,
                    max_commercial=max_commercial if max_commercial < max_buildings else None,
                    max_buildings=max_buildings,
                    num_parks=num_parks,
                    allow_large_buildings=allow_large_buildings,
                )

    # Main content
    if st.session_state.error_message:
        st.error(st.session_state.error_message)

    if st.session_state.grid is not None:
        # 3D Visualization
        fig = visualize_city(st.session_state.grid)
        st.plotly_chart(fig, use_container_width=True)

        # Stats row
        grid = st.session_state.grid
        col1, col2, col3, col4, col5 = st.columns(5)

        parks = [b for b in grid.buildings if b.building_type == BuildingType.PARK]
        residential = [b for b in grid.buildings if b.building_type == BuildingType.RESIDENTIAL]
        commercial = [b for b in grid.buildings if b.building_type == BuildingType.COMMERCIAL]

        with col1:
            st.metric("Residential", len(residential))
        with col2:
            st.metric("Commercial", len(commercial))
        with col3:
            st.metric("Parks", len(parks))
        with col4:
            st.metric("Total Floors", grid.total_height())
        with col5:
            if st.session_state.validation_report:
                rate = st.session_state.validation_report["satisfaction_rate"]
                st.metric("Satisfaction", f"{rate:.0%}")

        # Expandable sections
        with st.expander("📋 Constraint Satisfaction Report"):
            if st.session_state.validation_report:
                report = st.session_state.validation_report

                if report["satisfied"]:
                    st.success(f"✅ Satisfied: {', '.join(report['satisfied'])}")

                if report["violations"]:
                    for constraint_type, violations in report["violations"].items():
                        st.error(f"❌ {constraint_type}")
                        for v in violations:
                            st.write(f"  - {v}")
            else:
                st.info("No constraints to validate")

        with st.expander("🔧 Parsed Constraints (Debug)"):
            if st.session_state.constraints:
                constraints_json = [
                    {"type": c.type, "params": c.params}
                    for c in st.session_state.constraints
                ]
                st.json(constraints_json)
            else:
                st.info("No constraints parsed")

    else:
        # Empty state
        st.info(
            "👈 Enter a city description and click **Generate Layout** to get started!"
        )


if __name__ == "__main__":
    main()
