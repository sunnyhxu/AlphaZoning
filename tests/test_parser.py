"""Tests for constraint parser."""

import json
from unittest.mock import MagicMock, patch

import pytest

from src.constraint_parser import (
    load_example_constraints,
    parse_constraints,
    strip_markdown_fences,
)
from src.models import Constraint


class TestStripMarkdownFences:
    """Tests for markdown fence stripping."""

    def test_strip_json_fence(self) -> None:
        text = '```json\n[{"type": "height_limit"}]\n```'
        assert strip_markdown_fences(text) == '[{"type": "height_limit"}]'

    def test_strip_plain_fence(self) -> None:
        text = '```\n[{"type": "height_limit"}]\n```'
        assert strip_markdown_fences(text) == '[{"type": "height_limit"}]'

    def test_no_fence(self) -> None:
        text = '[{"type": "height_limit"}]'
        assert strip_markdown_fences(text) == '[{"type": "height_limit"}]'


class TestParseConstraints:
    """Tests for constraint parsing with mocked Gemini API."""

    @patch("src.constraint_parser.os.getenv")
    def test_no_api_key_returns_empty(self, mock_getenv: MagicMock) -> None:
        """Verify missing API key returns empty list."""
        mock_getenv.return_value = None
        result = parse_constraints("any input")
        assert result == []

    @patch("src.constraint_parser.genai", create=True)
    @patch("src.constraint_parser.os.getenv")
    def test_parse_green_city(
        self, mock_getenv: MagicMock, mock_genai: MagicMock
    ) -> None:
        """Parse eco-friendly city description."""
        mock_getenv.return_value = "fake_api_key"

        # Mock Gemini response
        mock_response = MagicMock()
        mock_response.text = json.dumps([
            {"type": "park_proximity", "params": {"max_distance": 2}},
            {"type": "height_limit", "params": {"max_floors": 5}},
        ])

        mock_model = MagicMock()
        mock_model.generate_content.return_value = mock_response
        mock_genai.GenerativeModel.return_value = mock_model
        mock_genai.GenerationConfig = MagicMock()

        with patch.dict("sys.modules", {"google.generativeai": mock_genai}):
            result = parse_constraints(
                "eco-friendly city with parks everywhere, max 5 floors"
            )

        assert len(result) == 2
        types = {c.type for c in result}
        assert "park_proximity" in types
        assert "height_limit" in types

        height_constraint = next(c for c in result if c.type == "height_limit")
        assert height_constraint.params["max_floors"] == 5

    @patch("src.constraint_parser.genai", create=True)
    @patch("src.constraint_parser.os.getenv")
    def test_parse_dense_city(
        self, mock_getenv: MagicMock, mock_genai: MagicMock
    ) -> None:
        """Parse dense urban description."""
        mock_getenv.return_value = "fake_api_key"

        mock_response = MagicMock()
        mock_response.text = json.dumps([
            {"type": "height_limit", "params": {"max_floors": 20}},
            {"type": "density_limit", "params": {"max_total_floors": 300}},
            {"type": "building_spacing", "params": {"min_distance": 1}},
        ])

        mock_model = MagicMock()
        mock_model.generate_content.return_value = mock_response
        mock_genai.GenerativeModel.return_value = mock_model
        mock_genai.GenerationConfig = MagicMock()

        with patch.dict("sys.modules", {"google.generativeai": mock_genai}):
            result = parse_constraints(
                "dense urban downtown, tall buildings close together"
            )

        assert len(result) == 3
        types = {c.type for c in result}
        assert "height_limit" in types
        assert "density_limit" in types
        assert "building_spacing" in types

        density = next(c for c in result if c.type == "density_limit")
        assert density.params["max_total_floors"] == 300

    @patch("src.constraint_parser.genai", create=True)
    @patch("src.constraint_parser.os.getenv")
    def test_invalid_input_returns_empty(
        self, mock_getenv: MagicMock, mock_genai: MagicMock
    ) -> None:
        """Gibberish input or API error returns empty list."""
        mock_getenv.return_value = "fake_api_key"

        mock_model = MagicMock()
        mock_model.generate_content.side_effect = Exception("API Error")
        mock_genai.GenerativeModel.return_value = mock_model
        mock_genai.GenerationConfig = MagicMock()

        with patch.dict("sys.modules", {"google.generativeai": mock_genai}):
            result = parse_constraints("asdfghjkl gibberish 12345")

        assert result == []

    @patch("src.constraint_parser.genai", create=True)
    @patch("src.constraint_parser.os.getenv")
    def test_invalid_json_returns_empty(
        self, mock_getenv: MagicMock, mock_genai: MagicMock
    ) -> None:
        """Invalid JSON response returns empty list."""
        mock_getenv.return_value = "fake_api_key"

        mock_response = MagicMock()
        mock_response.text = "not valid json {"

        mock_model = MagicMock()
        mock_model.generate_content.return_value = mock_response
        mock_genai.GenerativeModel.return_value = mock_model
        mock_genai.GenerationConfig = MagicMock()

        with patch.dict("sys.modules", {"google.generativeai": mock_genai}):
            result = parse_constraints("some input")

        assert result == []

    @patch("src.constraint_parser.genai", create=True)
    @patch("src.constraint_parser.os.getenv")
    def test_unsupported_constraint_type_filtered(
        self, mock_getenv: MagicMock, mock_genai: MagicMock
    ) -> None:
        """Unsupported constraint types are filtered out."""
        mock_getenv.return_value = "fake_api_key"

        mock_response = MagicMock()
        mock_response.text = json.dumps([
            {"type": "height_limit", "params": {"max_floors": 10}},
            {"type": "unknown_type", "params": {}},
        ])

        mock_model = MagicMock()
        mock_model.generate_content.return_value = mock_response
        mock_genai.GenerativeModel.return_value = mock_model
        mock_genai.GenerationConfig = MagicMock()

        with patch.dict("sys.modules", {"google.generativeai": mock_genai}):
            result = parse_constraints("some city")

        assert len(result) == 1
        assert result[0].type == "height_limit"

    @patch("src.constraint_parser.genai", create=True)
    @patch("src.constraint_parser.os.getenv")
    def test_handles_markdown_wrapped_json(
        self, mock_getenv: MagicMock, mock_genai: MagicMock
    ) -> None:
        """Handle JSON wrapped in markdown fences."""
        mock_getenv.return_value = "fake_api_key"

        mock_response = MagicMock()
        mock_response.text = '```json\n[{"type": "height_limit", "params": {"max_floors": 8}}]\n```'

        mock_model = MagicMock()
        mock_model.generate_content.return_value = mock_response
        mock_genai.GenerativeModel.return_value = mock_model
        mock_genai.GenerationConfig = MagicMock()

        with patch.dict("sys.modules", {"google.generativeai": mock_genai}):
            result = parse_constraints("medium height city")

        assert len(result) == 1
        assert result[0].params["max_floors"] == 8


class TestLoadExampleConstraints:
    """Tests for loading example constraint files."""

    def test_load_green_city(self) -> None:
        """Load green_city.json example."""
        result = load_example_constraints("green_city")

        assert len(result) == 4
        types = {c.type for c in result}
        assert "height_limit" in types
        assert "park_proximity" in types

    def test_load_dense_city(self) -> None:
        """Load dense_city.json example."""
        result = load_example_constraints("dense_city")

        assert len(result) == 3
        types = {c.type for c in result}
        assert "height_limit" in types
        assert "density_limit" in types

    def test_load_nonexistent_returns_empty(self) -> None:
        """Loading nonexistent example returns empty list."""
        result = load_example_constraints("nonexistent_example")
        assert result == []
