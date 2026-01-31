# CLAUDE.md

## Overview

**AlphaZoning** - Neuro-symbolic urban design with formal verification for Hack@Brown 2026.

**Pipeline**: Natural Language → LLM Parser → Z3 SMT Solver → Greedy Optimizer → 3D Visualization

## Commands

```bash
pip install -r requirements.txt    # Install dependencies
streamlit run app.py               # Launch web UI
pytest tests/ -v                   # Run tests (39 total)
```

## Project Structure

```
src/
├── models.py             # Building (with width/depth), Constraint, CityGrid
├── z3_solver.py          # Z3 constraint encoding + multi-cell buildings
├── constraint_parser.py  # Gemini + OpenRouter fallback
├── validator.py          # Independent verification + count_satisfied_buildings
└── visualizer.py         # Plotly 3D with building footprints

app.py                    # Streamlit UI with greedy fallback
tests/                    # 39 tests
examples/                 # Preset configurations
```

## Key Features

- **Multi-cell buildings**: Parks up to 3x3, commercial up to 2x2
- **Dual LLM support**: Gemini primary, OpenRouter fallback
- **Hybrid solving**: Z3 for correctness, greedy for optimization
- **Per-building satisfaction**: Tracks which buildings satisfy constraints

## Solver Parameters

| Param | Description |
|-------|-------------|
| `min_residential` / `max_residential` | Residential building count bounds |
| `min_commercial` / `max_commercial` | Commercial building count bounds |
| `max_buildings` | Total building limit (excluding parks) |
| `residential_height_range` | (min, max) floors for residential |
| `commercial_height_range` | (min, max) floors for commercial |
| `allow_large_buildings` | Enable multi-cell parks and commercial |

## Constraint Types

| Type | Param | Effect |
|------|-------|--------|
| `height_limit` | `max_floors` | Cap per-building height |
| `density_limit` | `max_total_floors` | Cap total floor area |
| `building_spacing` | `min_distance` | Min Manhattan distance |
| `park_proximity` | `max_distance` | Max distance to park |

## Environment

```bash
# .env (not committed)
GEMINI_API_KEY=...       # Primary LLM
OPENROUTER_API_KEY=...   # Fallback LLM
```

## Status: Ready for Submission

- 39 passing tests
- Dual LLM fallback working
- Z3 + greedy hybrid solver
- Multi-cell buildings
- Per-building constraint tracking
