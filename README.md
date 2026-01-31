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
# Edit .env and add your GEMINI_API_KEY (free at https://ai.google.dev/)

# Run tests
pytest tests/ -v
```

## Architecture

**Pipeline**: Natural Language → Structured Constraints → Valid Layout → Verification → 3D Visualization

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  User Input     │────▶│  Gemini LLM     │────▶│  Constraints    │
│  "eco-friendly  │     │  (Parser)       │     │  [JSON]         │
│   city..."      │     └─────────────────┘     └────────┬────────┘
└─────────────────┘                                      │
                                                         ▼
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  3D Viz         │◀────│  Validator      │◀────│  Z3 SMT Solver  │
│  (Plotly)       │     │  (Independent)  │     │  (Layout Gen)   │
└─────────────────┘     └─────────────────┘     └─────────────────┘
```

### Components

| Module | Purpose |
|--------|---------|
| `constraint_parser.py` | NL → JSON via Gemini API |
| `z3_solver.py` | SMT-based layout generation |
| `validator.py` | Independent constraint verification |
| `visualizer.py` | 3D Plotly rendering |

### Constraint Types

- **height_limit**: Maximum floors per building
- **density_limit**: Maximum total floors in grid
- **building_spacing**: Minimum Manhattan distance between buildings
- **park_proximity**: Maximum distance from any building to nearest park

## Examples

Pre-configured constraint sets in `examples/`:

```bash
# Load example constraints
python -c "from src import load_example_constraints; print(load_example_constraints('green_city'))"
```

- `green_city.json` - Eco-friendly: low-rise, parks everywhere
- `dense_city.json` - Urban downtown: tall buildings, high density

## Usage

```python
from src import solve_layout, validate_solution, visualize_city

# Generate layout
grid = solve_layout(
    grid_size=5,
    max_height=10,
    park_positions=[(2, 2)],
    min_spacing=2,
    park_proximity=3,
)

# Validate
is_valid, report = validate_solution(grid, constraints)

# Visualize
fig = visualize_city(grid)
fig.show()
```

## Tech Stack

Python 3.12+ · z3-solver · google-generativeai · plotly · pydantic

## License

MIT
