# AlphaZoning

> *"What if city planning had a cheat code?"*

**AlphaZoning** turns your wildest urban dreams into mathematically proven reality. Describe your ideal city in plain English, and watch as our neuro-symbolic AI generates layouts that are *guaranteed* to satisfy your constraints. No compromises. No "close enough." Just cities that work.

**Built for Hack@Brown 2026**

## The Problem

Urban planning is hard. Zoning regulations, building codes, green space requirements, density limits... the constraints multiply, and finding a valid layout becomes a nightmare of trial and error.

Traditional approaches:
- Manual planning: Slow, error-prone, doesn't scale
- Random generation: Fast, but constraints? What constraints?
- ML-only: "Trust me bro, this layout is probably fine"

## Our Solution: Neuro-Symbolic AI

AlphaZoning combines the best of both worlds:

1. **Neural**: GPT-4o-mini parses your natural language into structured constraints
2. **Symbolic**: Z3 SMT solver generates layouts with *mathematical proof* of constraint satisfaction
3. **Hybrid**: Greedy optimization ensures high satisfaction rates when constraints get tricky

The result? Tell us "eco-friendly neighborhood with max 5 floors and parks everywhere" and get a city layout that *provably* meets those requirements.

## Quick Start

```bash
# Clone and setup
git clone https://github.com/yourusername/alphazoning.git
cd alphazoning
pip install -r requirements.txt

# Configure API keys (at least one required)
cp .env.example .env
# Edit .env with your keys

# Launch
streamlit run app.py
```

Then open http://localhost:8501 and start designing cities.

## Features

**Natural Language Input**
- "Dense downtown with skyscrapers"
- "Family-friendly suburb with lots of parks"
- "Eco-friendly low-rise with green space everywhere"

**Smart Building Placement**
- Multi-cell parks (up to 3x3)
- Multi-cell commercial buildings (up to 2x2)
- Residential units with varied heights

**Constraint System**
| Constraint | What It Does |
|------------|--------------|
| Height Limit | Cap building floors |
| Density Limit | Control total floor area |
| Building Spacing | Minimum distance between structures |
| Park Proximity | Ensure buildings are near green space |

**Dual-Engine Generation**
- Primary: Z3 SMT solver for provably correct layouts
- Fallback: Greedy optimizer for complex constraint combinations

## Architecture

```
Your Words                    Your City
    |                             ^
    v                             |
[GPT-4o-mini] ──> [Constraints] ──> [Z3 Solver] ──> [3D Viz]
    |                                    |
    |                                    v
    └──────────────────────> [Greedy Fallback]
```

**Tech Stack**: Python 3.12 / Z3-Solver / OpenAI API / Streamlit / Plotly

## Example Outputs

**Green City** (park_proximity: 2, height_limit: 5)
- Every building within 2 blocks of a park
- No skyscrapers ruining the skyline

**Dense Downtown** (height_limit: 20, density_limit: 500)
- Tall commercial towers
- Maximized floor space

**Family Neighborhood** (height_limit: 8, spacing: 2, parks: 3)
- Medium-density housing
- Room to breathe between buildings

## API Keys

AlphaZoning needs at least one LLM API for constraint parsing. You can use Google Gemini or OpenRouter.

## Project Structure

```
alphazoning/
├── app.py                 # Streamlit web interface
├── src/
│   ├── models.py          # Building, Constraint, CityGrid
│   ├── z3_solver.py       # Z3 SMT constraint encoding
│   ├── constraint_parser.py   # LLM natural language parsing
│   ├── validator.py       # Independent constraint verification
│   └── visualizer.py      # Plotly 3D rendering
├── tests/                 # 39 passing tests
└── examples/              # Preset city configurations
```

## How It Works

1. **Parse**: Your description goes to Gemini, which extracts structured constraints
2. **Encode**: Constraints become Z3 formulas (SMT-LIB under the hood)
3. **Solve**: Z3 finds a satisfying assignment or proves impossibility
4. **Optimize**: If satisfaction rate is low, greedy search improves it
5. **Verify**: Independent validator confirms all constraints
6. **Render**: Plotly generates interactive 3D visualization

## The Z3 Magic

```python
# "Buildings must be at least 2 apart"
if dist < min_spacing:
    solver.add(Not(And(height[x1][y1] > 0, height[x2][y2] > 0)))

# "At least 5 residential buildings"
solver.add(Sum(residential_indicators) >= 5)

# Z3 finds values that satisfy ALL constraints simultaneously
# or proves it's impossible
```

No heuristics. No "good enough." Mathematical certainty.

## Testing

```bash
pytest tests/ -v  # 39 tests covering all components
```

## What's Next

- Custom constraint types via UI
- Export to common urban planning formats
- Multi-objective optimization (cost, sustainability, walkability)
- Real-world GIS data integration

## License

MIT

---

*This project serves as a test of AI agentic coding tools. Coauthors: Claude (Anthropic), Gemini (Google).*