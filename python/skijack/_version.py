"""The single source of the version.

Kept in its own module with no imports so that the build backend can
read it statically, without importing the package (which would drag in
``aviary-kernel`` at build time).  ``skijack/__init__.py`` re-exports it
and ``pyproject.toml`` reads it from here.
"""

__version__ = "0.2.3"
