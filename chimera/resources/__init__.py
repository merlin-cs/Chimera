"""
Chimera resources package.

Contains:
- RewriteRule.csv: CSV-encoded rewrite rules for Aries mimetic mutation
- rewrite_config/: Operator type mappings and conversion tables
"""

from pathlib import Path

# Resource directory paths
RESOURCES_DIR = Path(__file__).parent
REWRITE_RULES_CSV = RESOURCES_DIR / "RewriteRule.csv"
REWRITE_CONFIG_DIR = RESOURCES_DIR / "rewrite_config"

__all__ = [
    "RESOURCES_DIR",
    "REWRITE_RULES_CSV",
    "REWRITE_CONFIG_DIR",
]
