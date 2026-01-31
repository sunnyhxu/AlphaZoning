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
    """A building placed on the city grid.
    
    Buildings occupy a rectangular region from (x, y) to (x + width - 1, y + depth - 1).
    """

    x: int
    y: int
    height: int
    width: int = 1
    depth: int = 1
    building_type: BuildingType = BuildingType.RESIDENTIAL

    def occupies(self, check_x: int, check_y: int) -> bool:
        """Check if this building occupies the given cell."""
        return (
            self.x <= check_x < self.x + self.width and
            self.y <= check_y < self.y + self.depth
        )

    def footprint(self) -> list[tuple[int, int]]:
        """Return all cells occupied by this building."""
        cells = []
        for dx in range(self.width):
            for dy in range(self.depth):
                cells.append((self.x + dx, self.y + dy))
        return cells

    def cell_count(self) -> int:
        """Number of cells this building occupies."""
        return self.width * self.depth


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
            if b.occupies(x, y):
                return b
        return None

    def total_height(self) -> int:
        """Sum of all building heights (weighted by footprint size)."""
        return sum(b.height * b.cell_count() for b in self.buildings)

    def get_parks(self) -> list["Building"]:
        """Get all park buildings."""
        return [b for b in self.buildings if b.building_type == BuildingType.PARK]

    def get_non_parks(self) -> list["Building"]:
        """Get all non-park buildings."""
        return [b for b in self.buildings if b.building_type != BuildingType.PARK]

    def all_occupied_cells(self) -> set[tuple[int, int]]:
        """Get all cells occupied by any building."""
        cells = set()
        for b in self.buildings:
            cells.update(b.footprint())
        return cells


def manhattan_distance(x1: int, y1: int, x2: int, y2: int) -> int:
    """Calculate Manhattan distance between two points."""
    return abs(x1 - x2) + abs(y1 - y2)


def building_distance(b1: Building, b2: Building) -> int:
    """Calculate minimum Manhattan distance between two building footprints."""
    min_dist = float('inf')
    for x1, y1 in b1.footprint():
        for x2, y2 in b2.footprint():
            dist = manhattan_distance(x1, y1, x2, y2)
            if dist < min_dist:
                min_dist = dist
    return int(min_dist)
