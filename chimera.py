"""
Chimera – grammar-based SMT solver fuzzer.

DEPRECATED: This entry point is deprecated. Use the new CLI instead:

    python -m chimera.chimera_cli --mode histfuzz ...

Or install the package and use:

    chimera --mode histfuzz ...

This file will be removed in a future version.
"""

import warnings

warnings.warn(
    "The 'chimera.py' entry point is deprecated. "
    "Use 'python -m chimera.chimera_cli' or 'chimera' command instead.",
    DeprecationWarning,
    stacklevel=2,
)

# Redirect to new CLI
if __name__ == "__main__":
    import sys
    from chimera.chimera_cli import main as cli_main
    sys.exit(cli_main())

