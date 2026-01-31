# CLAUDE.md

## Overview

**AlphaZoning** is a neuro-symbolic urban design system that generates city layouts with mathematical proof of constraint satisfaction.

**Pipeline**: Natural Language → Structured Constraints (Gemini) → Valid Layout (Z3 SMT) → Proof Certificate → 3D Visualization (Plotly/Streamlit)

**Target**: Hack@Brown 2026

## Project Structure

```
alphazoning/
├── src/
│   ├── models.py              # Building, Constraint, CityGrid
│   ├── constraint_parser.py   # NL→JSON via Gemini
│   ├── z3_solver.py           # Z3 constraint encoding
│   ├── validator.py           # Independent verification
│   └── visualizer.py          # Plotly 3D rendering
├── app.py                     # Streamlit UI
├── tests/                     # pytest suite
└── examples/                  # Pre-configured scenarios
```

## Commands

```bash
# Setup
python -m venv venv && source venv/bin/activate
pip install -r requirements.txt

# Run
streamlit run app.py

# Test & Lint
pytest tests/ -v
mypy src/
ruff check src/
```

## Tech Stack

Python 3.12+ · z3-solver · google-generativeai · streamlit · plotly · pydantic

## Code Style

- Type hints everywhere (mypy enforced)
- Google-style docstrings
- 100 char line limit
- Use dataclasses, not raw dicts

## Z3 Patterns

**Declare variables upfront, then add constraints:**

```python
solver = z3.Optimize()
heights = [[z3.Int(f'h_{x}_{y}') for y in range(SIZE)] for x in range(SIZE)]

for x, y in product(range(SIZE), repeat=2):
    solver.add(And(heights[x][y] >= 0, heights[x][y] <= 20))
```

**Distance**: Use Manhattan (`|x1-x2| + |y1-y2|`) — Euclidean causes timeouts.

**Optimization**: Use `z3.Optimize()` with soft constraints for nice-to-haves.

### Constraint Encoding Reference

| Type | Pattern |
|------|---------|
| Park proximity | `Or([dist(b, p) <= D for p in parks])` |
| Building spacing | `dist(b1, b2) >= D` for all pairs |
| Sunlight | `If(heights[x][y-1] > 10, heights[x][y] == 0, True)` |
| Density | `Sum(heights) <= threshold` |
| Height limit | `heights[x][y] <= max_height` |

## Error Handling

```python
result = solver.check()
if result == z3.sat:
    model = solver.model()
elif result == z3.unsat:
    raise ImpossibleConstraintsError("Try: relax density or increase grid")
elif result == z3.unknown:
    raise SolverTimeoutError("Try: simpler constraints or smaller grid")
```

**LLM failures**: Validate with Pydantic, fallback to `examples/` if API fails.

## Performance

- Grid size ≤10×10 for demos (100 variables)
- Timeout: `solver.set('timeout', 30000)`
- Cache LLM responses: `@st.cache_data`
- Reuse solver: `@st.cache_resource`

## Common Pitfalls

| Issue | Solution |
|-------|----------|
| Z3 variables losing scope | Declare all in list/matrix upfront |
| Non-linear constraints timeout | Use Manhattan distance or dist² |
| LLM returns markdown-wrapped JSON | Strip ` ```json ` fences before parsing |
| Streamlit reruns everything | Use `st.session_state` and caching |

## Environment

```bash
# .env (not committed)
GEMINI_API_KEY=your_key
Z3_TIMEOUT_MS=30000
GRID_SIZE=10
```

**Gemini API**: Free key at https://ai.google.dev/ (60 req/min)

## Debugging

**Z3 stuck?**
1. Print assertions: `print(solver.assertions())`
2. Try 5×5 grid
3. Add constraints incrementally to find conflict

**Gemini errors?**
1. Verify `$GEMINI_API_KEY`
2. Use `response_mime_type: "application/json"`
3. Add exponential backoff

## Development Priority

1. **Foundation**: `models.py` + `z3_solver.py` with 2-3 constraints
2. **Integration**: LLM parsing + validation, end-to-end tests
3. **Polish**: Streamlit UI + Plotly visualization
4. **Demo Prep**: Error handling, fallbacks, practice

## Success Criteria

| Level | Requirements |
|-------|--------------|
| **MVP** | 3 constraint types, valid layout, visualization, satisfaction report |
| **Competitive** | 5-7 constraints, 3D Plotly, Gemini integration, polished UI |
| **Prize-winning** | Formal proof certificate, comparative layouts, graceful impossible-constraint handling |