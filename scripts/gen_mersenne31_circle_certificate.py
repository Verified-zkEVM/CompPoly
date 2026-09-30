#!/usr/bin/env python3
"""Emit the untrusted doubling certificate checked by Circle.lean's kernel proof."""

import argparse
from pathlib import Path


SOURCE = Path(__file__).resolve().parents[1] / "CompPoly/Fields/Mersenne31/Circle.lean"


def certificate() -> str:
    modulus = 2**31 - 1
    x, y = 2, 1268011823
    points = []
    for _ in range(30):
        x, y = (x * x - y * y) % modulus, (2 * x * y) % modulus
        points.append(f"({x}, {y})")
    rows = [", ".join(points[i : i + 3]) for i in range(0, len(points), 3)]
    return (
        "private def generatorDoublings : List (Field \u00d7 Field) :=\n"
        "  [" + ",\n   ".join(rows) + "]\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", nargs="?", type=Path, const=SOURCE, metavar="LEAN_FILE",
        help="check that the file contains the generated declaration (default: Circle.lean)",
    )
    args = parser.parse_args()
    expected = certificate()
    if args.check is None:
        print(expected, end="")
    elif expected not in args.check.read_text(encoding="utf-8"):
        raise SystemExit(f"Certificate differs from generated data: {args.check}")
    else:
        print(f"Certificate is current: {args.check}")


if __name__ == "__main__":
    main()
