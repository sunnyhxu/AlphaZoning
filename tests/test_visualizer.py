"""Tests for 3D city visualization."""

import plotly.graph_objects as go

from src.models import Building, BuildingType, CityGrid
from src.visualizer import visualize_city


def test_visualization_returns_figure() -> None:
    """Verify visualize_city returns a Plotly Figure."""
    grid = CityGrid(
        size=5,
        buildings=[
            Building(x=0, y=0, height=3, building_type=BuildingType.RESIDENTIAL),
            Building(x=2, y=2, height=1, building_type=BuildingType.PARK),
            Building(x=4, y=4, height=5, building_type=BuildingType.COMMERCIAL),
        ],
    )

    fig = visualize_city(grid)

    assert isinstance(fig, go.Figure)
    assert fig.layout.title.text == "City Layout - 3D View"


def test_empty_grid() -> None:
    """Handles grid with no buildings."""
    grid = CityGrid(size=5, buildings=[])

    fig = visualize_city(grid)

    assert isinstance(fig, go.Figure)
    # Should have at least the base plane trace
    assert len(fig.data) >= 1


def test_building_colors() -> None:
    """Verify buildings are colored by type."""
    grid = CityGrid(
        size=5,
        buildings=[
            Building(x=0, y=0, height=3, building_type=BuildingType.RESIDENTIAL),
            Building(x=2, y=2, height=1, building_type=BuildingType.PARK),
            Building(x=4, y=4, height=5, building_type=BuildingType.COMMERCIAL),
        ],
    )

    fig = visualize_city(grid)

    # Check that we have traces for each building type
    trace_colors = [trace.color for trace in fig.data if hasattr(trace, "color")]
    assert "blue" in trace_colors  # RESIDENTIAL
    assert "green" in trace_colors  # PARK
    assert "orange" in trace_colors  # COMMERCIAL


def test_axis_labels() -> None:
    """Verify axis labels are set."""
    grid = CityGrid(
        size=5,
        buildings=[Building(x=0, y=0, height=3)],
    )

    fig = visualize_city(grid)

    assert fig.layout.scene.xaxis.title.text == "X"
    assert fig.layout.scene.yaxis.title.text == "Y"
    assert fig.layout.scene.zaxis.title.text == "Height (floors)"


def test_grid_size_respected() -> None:
    """Verify axis ranges match grid size."""
    grid = CityGrid(
        size=10,
        buildings=[Building(x=5, y=5, height=3)],
    )

    fig = visualize_city(grid)

    # X and Y axes should range from -0.5 to size+0.5
    assert fig.layout.scene.xaxis.range[1] == 10.5
    assert fig.layout.scene.yaxis.range[1] == 10.5


def test_multiple_buildings_same_type() -> None:
    """Multiple buildings of same type share legend group."""
    grid = CityGrid(
        size=5,
        buildings=[
            Building(x=0, y=0, height=3, building_type=BuildingType.RESIDENTIAL),
            Building(x=2, y=0, height=4, building_type=BuildingType.RESIDENTIAL),
            Building(x=4, y=0, height=5, building_type=BuildingType.RESIDENTIAL),
        ],
    )

    fig = visualize_city(grid)

    # Should have 3 traces but only 1 shows in legend
    residential_traces = [
        t for t in fig.data if hasattr(t, "legendgroup") and t.legendgroup == "residential"
    ]
    assert len(residential_traces) == 3
    legend_shown = [t.showlegend for t in residential_traces]
    assert legend_shown.count(True) == 1
    assert legend_shown.count(False) == 2
