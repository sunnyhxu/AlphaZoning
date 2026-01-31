"""Core data models for AlphaZoning."""

from dataclasses import dataclass, field
from enum import Enum
from typing import Any


class BuildingType(Enum):
    """Type of building on the grid."""

    RESIDENTIAL = "residential"
    COMMERCIAL = "commercial"
    PARK = "park"


@dataclass
class Building:
    """A building placed on the city grid."""

    x: int
    y: int
    height: int
    building_type: BuildingType = BuildingType.RESIDENTIAL


@dataclass
class Constraint:
    """A constraint to be satisfied by the city layout."""

    type: str
    params: dict[str, Any] = field(default_factory=dict)


@dataclass
class CityGrid:
    """A city grid containing buildings."""

    size: int
    buildings: list[Building] = field(default_factory=list)

    def get_building_at(self, x: int, y: int) -> Building | None:
        """Get building at coordinates, or None if empty."""
        for b in self.buildings:
            if b.x == x and b.y == y:
                return b
        return None

    def total_height(self) -> int:
        """Sum of all building heights."""
        return sum(b.height for b in self.buildings)

    def get_parks(self) -> list["Building"]:
        """Get all park buildings."""
        return [b for b in self.buildings if b.building_type == BuildingType.PARK]

    def get_non_parks(self) -> list["Building"]:
        """Get all non-park buildings."""
        return [b for b in self.buildings if b.building_type != BuildingType.PARK]


def manhattan_distance(x1: int, y1: int, x2: int, y2: int) -> int:
    """Calculate Manhattan distance between two points."""
    return abs(x1 - x2) + abs(y1 - y2)
