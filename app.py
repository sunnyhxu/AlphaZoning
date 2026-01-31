"""AlphaZoning - Streamlit Web Interface."""

import json

from dotenv import load_dotenv
import streamlit as st

# Load environment variables from .env file
load_dotenv()

from src import (
    BuildingType,
    Constraint,
    load_example_constraints,
    parse_constraints,
    solve_layout,
    validate_solution,
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

    # Solve
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

    st.session_state.grid = grid

    # Validate
    if st.session_state.constraints:
        is_valid, report = validate_solution(grid, st.session_state.constraints)
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
