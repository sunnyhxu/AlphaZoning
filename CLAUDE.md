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
pytest tests/ -v                   # Run tests
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
tests/                    # pytest suite
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

## Constraint Types

| Type | Param | Description |
|------|-------|-------------|
| `height_limit` | `max_floors` | Max height per building |
| `density_limit` | `max_total_floors` | Max sum of all heights |
| `building_spacing` | `min_distance` | Min Manhattan distance between buildings |
| `park_proximity` | `max_distance` | Max distance to nearest park |

## Solver Parameters

| Param | Description |
|-------|-------------|
| `min_residential` | Minimum residential buildings to place |
| `min_commercial` | Minimum commercial buildings to place |
| `park_positions` | List of (x, y) park coordinates |

## Z3 Patterns

Use `z3.Solver()` for speed (default). Use `z3.Optimize()` only when maximizing density.

```python
# Building count constraint
solver.add(z3.Sum([z3.If(heights[x][y] > 0, 1, 0) for ...]) >= min_buildings)

# Spacing constraint: at most one building per pair within min_distance
if dist < min_spacing:
    solver.add(Or(heights[x1][y1] == 0, heights[x2][y2] == 0))
```

Manhattan distance only—Euclidean causes timeouts.

## Environment

```bash
# .env (not committed)
GEMINI_API_KEY=your_key   # Free at https://ai.google.dev/
```

## Status

**Complete**:
- Core solver with 4 constraint types + building count minimums
- Gemini parser (gemini-2.0-flash) with pydantic validation
- Independent validator with detailed reports
- 3D Plotly visualization with building type colors
- Streamlit web UI with building count inputs
