"""
Test suite for Chimera SMT Solver Fuzzer.

This package contains unit and integration tests for the Chimera fuzzer components.
"""

import sys
from pathlib import Path

# Add project root to path for imports
PROJECT_ROOT = Path(__file__).parent.parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))
