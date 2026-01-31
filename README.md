# AlphaZoning

**Neuro-Symbolic Urban Design with Formal Verification**

*Hack@Brown 2026*

Generate city layouts from natural language descriptions with mathematical proof of constraint satisfaction.

## Quick Start

```bash
# Install dependencies
pip install -r requirements.txt

# Set up environment
cp .env.example .env
# Edit .env:
# GEMINI_API_KEY=...    (Primary)
# OPENROUTER_API_KEY=... (Fallback)

# Launch web UI
streamlit run app.py
```

## Web Interface

The Streamlit app provides:
- Natural language input for city descriptions
- **Multi-cell buildings** (parks up to 3x3, commercial up to 2x2)
- Building count controls (residential, commercial, parks)
- Grid size configuration
- Preset city templates (Green, Dense, Family)
- Interactive 3D visualization with building footprints
- Constraint satisfaction reports and Z3 verification

## Architecture

**Pipeline**: Natural Language → Structured Constraints → Valid Layout → Verification → 3D Visualization

```
┌─────────────────┐     ┌────────────────────────────┐     ┌─────────────────┐
│  User Input     │────▶│  Gemini / OpenRouter LLM   │────▶│  Constraints    │
│  "eco-friendly  │     │  (Parser + Fallback)       │     │  [JSON]         │
│   city..."      │     └────────────────────────────┘     └────────┬────────┘
                                                                    │
                                                                    ▼
┌─────────────────┐     ┌────────────────────────────┐     ┌─────────────────┐
│  3D Viz         │◀────│  Validator                 │◀────│  Z3 SMT Solver  │
│  (Plotly)       │     │  (Independent)             │     │  (Layout Gen)   │
└─────────────────┘     └────────────────────────────┘     └─────────────────┘
```

### Components

| Module | Purpose |
|--------|---------|
| `app.py` | Streamlit web interface |
| `constraint_parser.py` | NL → JSON via Gemini API |
| `z3_solver.py` | SMT-based layout generation |
| `validator.py` | Independent constraint verification |
| `visualizer.py` | 3D Plotly rendering |

### Constraint Types

- **height_limit**: Maximum floors per building
- **density_limit**: Maximum total floors in grid
- **building_spacing**: Minimum Manhattan distance between buildings
- **park_proximity**: Maximum distance from any building to nearest park

### Building Types

- **Residential** (blue): Housing units
- **Commercial** (orange): Business buildings
- **Parks** (green): Green spaces

## Examples

Pre-configured constraint sets in `examples/`:

- `green_city.json` - Eco-friendly: low-rise, parks everywhere
- `dense_city.json` - Urban downtown: tall buildings, high density
- `family_city.json` - Family-friendly: balanced with parks

## Usage (Python API)

```python
from src import solve_layout, validate_solution, visualize_city

# Generate layout with building minimums
grid = solve_layout(
    grid_size=10,
    max_height=10,
    park_positions=[(5, 5)],
    min_residential=5,
    min_commercial=3,
)

# Validate
is_valid, report = validate_solution(grid, constraints)

# Visualize
fig = visualize_city(grid)
fig.show()
```

## Tech Stack

Python 3.12+ · z3-solver · google-generativeai · streamlit · plotly · pydantic

## License

MIT
