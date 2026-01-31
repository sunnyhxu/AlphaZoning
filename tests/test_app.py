"""Smoke tests for Streamlit app."""

import sys
from unittest.mock import MagicMock, patch


def test_app_imports() -> None:
    """Verify app.py imports without error."""
    # Mock streamlit to avoid needing actual Streamlit runtime
    mock_st = MagicMock()
    mock_st.cache_data = lambda f: f  # Pass-through decorator

    with patch.dict(sys.modules, {"streamlit": mock_st}):
        # Re-import with mocked streamlit
        import importlib
        import app

        importlib.reload(app)

        # Verify key functions exist
        assert hasattr(app, "main")
        assert hasattr(app, "init_session_state")
        assert hasattr(app, "generate_layout")
        assert hasattr(app, "load_preset")
        assert callable(app.main)


def test_session_state_keys() -> None:
    """Verify expected session state keys exist after initialization."""
    mock_st = MagicMock()
    mock_st.cache_data = lambda f: f
    # Use MagicMock for session_state to support attribute access
    mock_st.session_state = MagicMock()
    mock_st.session_state.__contains__ = lambda self, key: False  # Always "not in"

    with patch.dict(sys.modules, {"streamlit": mock_st}):
        import importlib
        import app

        importlib.reload(app)

        # Call init
        app.init_session_state()

        # Verify attributes were set
        assert hasattr(mock_st.session_state, "grid")
        assert hasattr(mock_st.session_state, "constraints")
        assert hasattr(mock_st.session_state, "validation_report")
        assert hasattr(mock_st.session_state, "error_message")


def test_constraints_to_solver_params() -> None:
    """Verify constraint conversion to solver parameters."""
    mock_st = MagicMock()
    mock_st.cache_data = lambda f: f

    with patch.dict(sys.modules, {"streamlit": mock_st}):
        import importlib
        import app
        from src.models import Constraint

        importlib.reload(app)

        constraints = [
            Constraint(type="height_limit", params={"max_floors": 5}),
            Constraint(type="density_limit", params={"max_total_floors": 50}),
            Constraint(type="building_spacing", params={"min_distance": 2}),
            Constraint(type="park_proximity", params={"max_distance": 3}),
        ]

        params = app.constraints_to_solver_params(constraints)

        assert params["max_height"] == 5
        assert params["max_total_floors"] == 50
        assert params["min_spacing"] == 2
        assert params["park_proximity"] == 3


def test_load_preset_family_city() -> None:
    """Verify family_city preset loads correctly."""
    mock_st = MagicMock()
    mock_st.cache_data = lambda f: f

    with patch.dict(sys.modules, {"streamlit": mock_st}):
        import importlib
        import app

        importlib.reload(app)

        constraints = app.load_preset("family_city")

        assert len(constraints) == 4
        types = {c.type for c in constraints}
        assert "height_limit" in types
        assert "park_proximity" in types
        assert "building_spacing" in types
        assert "density_limit" in types
