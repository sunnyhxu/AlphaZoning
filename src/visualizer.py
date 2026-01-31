"""3D visualization of city layouts using Plotly."""

import plotly.graph_objects as go

from src.models import BuildingType, CityGrid

# Color mapping for building types
BUILDING_COLORS = {
    BuildingType.PARK: "green",
    BuildingType.RESIDENTIAL: "blue",
    BuildingType.COMMERCIAL: "orange",
}


def visualize_city(grid: CityGrid) -> go.Figure:
    """
    Create a 3D visualization of the city grid.

    Args:
        grid: The city grid to visualize.

    Returns:
        Plotly Figure with 3D bar chart representation.
    """
    fig = go.Figure()

    if not grid.buildings:
        # Empty grid - show just the base plane
        fig.add_trace(
            go.Mesh3d(
                x=[0, grid.size, grid.size, 0],
                y=[0, 0, grid.size, grid.size],
                z=[0, 0, 0, 0],
                color="lightgray",
                opacity=0.3,
                name="Grid",
            )
        )
    else:
        # Group buildings by type for legend
        buildings_by_type: dict[BuildingType, list] = {
            BuildingType.PARK: [],
            BuildingType.RESIDENTIAL: [],
            BuildingType.COMMERCIAL: [],
        }

        for building in grid.buildings:
            buildings_by_type[building.building_type].append(building)

        # Add buildings as 3D boxes
        for building_type, buildings in buildings_by_type.items():
            if not buildings:
                continue

            color = BUILDING_COLORS[building_type]

            for building in buildings:
                _add_building_box(
                    fig,
                    building.x,
                    building.y,
                    building.height,
                    color,
                    building_type.value,
                    show_legend=(building == buildings[0]),
                )

    # Configure layout
    max_height = max((b.height for b in grid.buildings), default=1)

    fig.update_layout(
        title="City Layout - 3D View",
        scene=dict(
            xaxis=dict(
                title="X",
                range=[-0.5, grid.size + 0.5],
                dtick=1,
                gridcolor="lightgray",
            ),
            yaxis=dict(
                title="Y",
                range=[-0.5, grid.size + 0.5],
                dtick=1,
                gridcolor="lightgray",
            ),
            zaxis=dict(
                title="Height (floors)",
                range=[0, max_height + 1],
                dtick=1,
                gridcolor="lightgray",
            ),
            aspectmode="manual",
            aspectratio=dict(x=1, y=1, z=0.5),
        ),
        showlegend=True,
        legend=dict(
            yanchor="top",
            y=0.99,
            xanchor="left",
            x=0.01,
        ),
        margin=dict(l=0, r=0, t=40, b=0),
    )

    return fig


def _add_building_box(
    fig: go.Figure,
    x: int,
    y: int,
    height: int,
    color: str,
    name: str,
    show_legend: bool = True,
) -> None:
    """Add a 3D box representing a building."""
    # Define the 8 vertices of a box
    # Box is centered at (x+0.5, y+0.5) with size 0.8 to show grid gaps
    offset = 0.1
    x0, x1 = x + offset, x + 1 - offset
    y0, y1 = y + offset, y + 1 - offset
    z0, z1 = 0, height

    # Vertices
    vertices_x = [x0, x1, x1, x0, x0, x1, x1, x0]
    vertices_y = [y0, y0, y1, y1, y0, y0, y1, y1]
    vertices_z = [z0, z0, z0, z0, z1, z1, z1, z1]

    # Faces (triangles) - each face defined by 3 vertex indices
    i = [0, 0, 4, 4, 0, 0, 1, 1, 0, 0, 3, 3]
    j = [1, 2, 5, 6, 1, 4, 2, 5, 3, 4, 2, 6]
    k = [2, 3, 6, 7, 4, 5, 5, 6, 4, 7, 6, 7]

    fig.add_trace(
        go.Mesh3d(
            x=vertices_x,
            y=vertices_y,
            z=vertices_z,
            i=i,
            j=j,
            k=k,
            color=color,
            opacity=0.8,
            name=name,
            showlegend=show_legend,
            legendgroup=name,
            hovertemplate=(
                f"Type: {name}<br>"
                f"Position: ({x}, {y})<br>"
                f"Height: {height}<extra></extra>"
            ),
        )
    )
