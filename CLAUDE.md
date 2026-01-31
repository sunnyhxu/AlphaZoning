# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

**AlphaZoning** generates city layouts from natural language with Z3-verified constraint satisfaction.

**Pipeline**: NL → Constraints (Gemini) → Layout (Z3 SMT) → Validation → 3D Viz (Plotly)

**Target**: Hack@Brown 2026

## Commands

```bash
pip install -r requirements.txt    # Install dependencies
streamlit run app.py               # Launch web UI
pytest tests/ -v                   # Run tests (39 total)
python -c "from src import *"      # Verify imports
```

## Project Structure

```
src/
├── __init__.py           # Public API exports
├── models.py             # Building, BuildingType, Constraint, CityGrid
├── z3_solver.py          # solve_layout() - Z3 constraint encoding
├── constraint_parser.py  # parse_constraints() - Gemini NL→JSON
├── validator.py          # validate_solution() - Independent verification
└── visualizer.py         # visualize_city() - Plotly 3D rendering

app.py                    # Streamlit web interface
tests/                    # pytest suite (39 tests)
examples/                 # Preset constraint files (green_city, dense_city, family_city)
```

## Public API

```python
from src import (
    solve_layout,           # Generate layout with Z3
    parse_constraints,      # NL → Constraint list via Gemini
    load_example_constraints,  # Load from examples/
    validate_solution,      # Verify constraints independently
    visualize_city,         # Create Plotly 3D figure
    Building, BuildingType, Constraint, CityGrid,
)
```

## Solver Parameters

| Param | Type | Description |
|-------|------|-------------|
| `grid_size` | int | Size of square grid |
| `max_height` | int | Fallback max height (default 10) |
| `max_total_floors` | int | Density limit (default 100) |
| `park_positions` | list | List of (x, y) park coordinates |
| `min_spacing` | int | Min Manhattan distance between buildings |
| `park_proximity` | int | Max distance to nearest park |
| `min_residential` | int | Minimum residential buildings |
| `max_residential` | int | Maximum residential buildings |
| `min_commercial` | int | Minimum commercial buildings |
| `max_commercial` | int | Maximum commercial buildings |
| `max_buildings` | int | Maximum total buildings (excluding parks) |
| `residential_height_range` | tuple | (min, max) height for residential (default 1-5) |
| `commercial_height_range` | tuple | (min, max) height for commercial (default 3-10) |
| `allow_large_buildings` | bool | Allow multi-cell parks/commercial (default True) |

## Constraint Types (NL Parser)

| Type | Param | Description |
|------|-------|-------------|
| `height_limit` | `max_floors` | Max height per building |
| `density_limit` | `max_total_floors` | Max sum of all heights |
| `building_spacing` | `min_distance` | Min Manhattan distance between buildings |
| `park_proximity` | `max_distance` | Max distance to nearest park |

## Z3 Patterns

```python
# Building type-specific height ranges
is_valid_residential = z3.And(
    z3.Not(is_commercial[x][y]),
    heights[x][y] >= res_min,
    heights[x][y] <= res_max
)

# Building count constraint
solver.add(z3.Sum(residential_indicators) >= min_residential)

# Spacing: both cells can't have buildings within min_distance
both_are_buildings = z3.And(heights[x1][y1] > 0, heights[x2][y2] > 0)
solver.add(z3.Not(both_are_buildings))
```

Use `z3.Solver()` for speed (default). Manhattan distance only.

## Environment

```bash
# .env (not committed)
GEMINI_API_KEY=your_key       # Primary (Free at https://ai.google.dev/)
OPENROUTER_API_KEY=your_key   # Fallback (https://openrouter.ai/)
```

## Status

**Complete**:
- Phase 1: Core solver with height ranges and build counts
- Phase 2: Multi-cell buildings (parks up to 3x3, commercial up to 2x2)
- Constraints: spacing, density, proximity, building counts
- LLM Pipeline: Gemini → OpenRouter fallback → JSON parser
- Validation: Independent checks + Z3 verification
- Visualization: 3D Plotly with building sizes
- UI: Streamlit with detailed controls and feedback
- Testing: 39 passing tests verified
