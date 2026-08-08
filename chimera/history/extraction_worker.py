"""Single-input worker used by the streaming corpus exporter.

The worker boundary protects the long-running exporter from malformed or
pathologically deep historical formulas that can crash the parser process.
The protocol is deliberately plain JSON over stdin/stdout.
"""

from __future__ import annotations

import json
import logging
import sys

from chimera.history.extractor import LogicAwareExtractor


def _process(request: dict) -> dict:
    extractor = LogicAwareExtractor()
    extraction = extractor._extract_from_file(request["path"], request["logic"])
    return {
        "parse_errors": extraction.parse_errors,
        "blocks": [item.to_dict() for item in extraction.blocks],
        "skeletons": [item.to_dict() for item in extraction.skeletons],
    }


def main() -> int:
    logging.disable(logging.CRITICAL)
    if "--serve" in sys.argv:
        for line in sys.stdin:
            if not line.strip():
                continue
            try:
                response = _process(json.loads(line))
                response["ok"] = True
            except Exception as exc:
                response = {"ok": False, "error": str(exc)}
            json.dump(response, sys.stdout, sort_keys=True, separators=(",", ":"))
            sys.stdout.write("\n")
            sys.stdout.flush()
        return 0

    response = _process(json.load(sys.stdin))
    response["ok"] = True
    json.dump(response, sys.stdout, sort_keys=True, separators=(",", ":"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
