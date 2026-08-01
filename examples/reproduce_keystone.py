#!/usr/bin/env python3
"""Reproduce the keystone identity by two independent calculation paths."""

from __future__ import annotations

import argparse

from zpa_lm_reference.geometry import bhattacharyya_divisor_overlap, divisor_kernel


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=128)
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")

    maximum_error = 0.0
    worst_pair = (1, 1)
    for n in range(1, args.limit + 1):
        for m in range(1, args.limit + 1):
            error = abs(divisor_kernel(n, m) - bhattacharyya_divisor_overlap(n, m))
            if error > maximum_error:
                maximum_error = error
                worst_pair = (n, m)

    print(f"pairs checked: {args.limit * args.limit}")
    print(f"maximum absolute error: {maximum_error:.17g}")
    print(f"worst pair: {worst_pair}")


if __name__ == "__main__":
    main()
