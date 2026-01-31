"""Parse natural language into structured constraints using Gemini."""

import json
import logging
import os
import re

from pydantic import BaseModel, ValidationError

from src.models import Constraint

logger = logging.getLogger(__name__)

SUPPORTED_CONSTRAINT_TYPES = {
    "height_limit",
    "density_limit",
    "building_spacing",
    "park_proximity",
}

SYSTEM_PROMPT = """You are a city planning assistant. Convert natural language descriptions into structured constraints for city layout generation.

Output a JSON array of constraint objects. Each constraint has:
- "type": one of ["height_limit", "density_limit", "building_spacing", "park_proximity"]
- "params": object with constraint-specific parameters

Parameter schemas:
- height_limit: {"max_floors": int} - Maximum building height in floors
- density_limit: {"max_total_floors": int} - Maximum sum of all building heights
- building_spacing: {"min_distance": int} - Minimum Manhattan distance between buildings
- park_proximity: {"max_distance": int} - Maximum distance from any building to nearest park

Examples:
Input: "low-rise neighborhood with lots of green space"
Output: [{"type": "height_limit", "params": {"max_floors": 3}}, {"type": "park_proximity", "params": {"max_distance": 2}}]

Input: "dense downtown with skyscrapers"
Output: [{"type": "height_limit", "params": {"max_floors": 20}}, {"type": "density_limit", "params": {"max_total_floors": 500}}]

Only output the JSON array, no explanation."""


class ConstraintModel(BaseModel):
    """Pydantic model for constraint validation."""

    type: str
    params: dict


class ConstraintListModel(BaseModel):
    """Pydantic model for list of constraints."""

    constraints: list[ConstraintModel]


def strip_markdown_fences(text: str) -> str:
    """Remove markdown code fences from text."""
    text = text.strip()
    # Remove ```json ... ``` or ``` ... ```
    pattern = r"^```(?:json)?\s*\n?(.*?)\n?```$"
    match = re.match(pattern, text, re.DOTALL)
    if match:
        return match.group(1).strip()
    return text


def parse_constraints(user_input: str) -> list[Constraint]:
    """
    Parse natural language into structured constraints using Gemini.

    Args:
        user_input: Natural language description of desired city layout.

    Returns:
        List of Constraint objects. Returns empty list on API failure.
    """
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key:
        logger.warning("GEMINI_API_KEY not set, returning empty constraints")
        return []

    try:
        import google.generativeai as genai

        genai.configure(api_key=api_key)
        model = genai.GenerativeModel("gemini-1.5-flash")

        response = model.generate_content(
            f"{SYSTEM_PROMPT}\n\nInput: {user_input}",
            generation_config=genai.GenerationConfig(
                response_mime_type="application/json",
                temperature=0.1,
            ),
        )

        raw_text = response.text
        clean_text = strip_markdown_fences(raw_text)

        # Parse JSON
        parsed = json.loads(clean_text)

        # Handle both array and object with "constraints" key
        if isinstance(parsed, dict) and "constraints" in parsed:
            constraint_list = parsed["constraints"]
        elif isinstance(parsed, list):
            constraint_list = parsed
        else:
            logger.warning(f"Unexpected response format: {type(parsed)}")
            return []

        # Validate with pydantic
        validated = ConstraintListModel(constraints=constraint_list)

        # Convert to Constraint objects, filtering unsupported types
        constraints = []
        for c in validated.constraints:
            if c.type in SUPPORTED_CONSTRAINT_TYPES:
                constraints.append(Constraint(type=c.type, params=c.params))
            else:
                logger.warning(f"Skipping unsupported constraint type: {c.type}")

        return constraints

    except ImportError:
        logger.warning("google-generativeai not installed")
        return []
    except json.JSONDecodeError as e:
        logger.warning(f"Failed to parse Gemini response as JSON: {e}")
        return []
    except ValidationError as e:
        logger.warning(f"Constraint validation failed: {e}")
        return []
    except Exception as e:
        logger.warning(f"Gemini API error: {e}")
        return []


def load_example_constraints(example_name: str) -> list[Constraint]:
    """
    Load pre-configured constraints from examples directory.

    Args:
        example_name: Name of example file (without .json extension).

    Returns:
        List of Constraint objects, or empty list if not found.
    """
    examples_dir = os.path.join(os.path.dirname(__file__), "..", "examples")
    filepath = os.path.join(examples_dir, f"{example_name}.json")

    try:
        with open(filepath) as f:
            data = json.load(f)

        constraints = []
        for c in data.get("constraints", []):
            if c.get("type") in SUPPORTED_CONSTRAINT_TYPES:
                constraints.append(Constraint(type=c["type"], params=c.get("params", {})))

        return constraints
    except (FileNotFoundError, json.JSONDecodeError) as e:
        logger.warning(f"Failed to load example {example_name}: {e}")
        return []
