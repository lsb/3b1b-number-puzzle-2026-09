#!/usr/bin/env python3
"""Find multipliers k so that n * k is written only with 0s and 1s (or only 1s).

    python3 find_multiplier.py 7 12 2026 99999

Every method below works on remainders mod n, so it takes at most about n steps and
never needs big-number arithmetic until the final answer is built.
"""
import sys
from collections import deque



def smallest_zero_one_multiple(n):
    """Smallest positive multiple of n whose digits are all 0 or 1.

    Breadth-first search over remainders mod n. Numbers are tried in increasing
    order (1, 10, 11, 100, ...) and a remainder is expanded only the first time it
    is seen, so there are at most n states.
    """
    if n == 1:
        return 1
    parent = {1 % n: None}  # remainder -> (previous remainder, digit appended)
    queue = deque([1 % n])
    while queue:
        r = queue.popleft()
        if r == 0:
            break
        for d in (0, 1):
            s = (10 * r + d) % n
            if s not in parent:
                parent[s] = (r, d)
                queue.append(s)
    digits, r = [], 0
    while parent[r] is not None:
        r, d = parent[r]
        digits.append(str(d))
    return int("1" + "".join(reversed(digits)))


def pigeonhole_multiple(n):
    """The multiple the Lean proof builds, 11...100...0 = R(b) - R(a), as a string."""
    seen = {}  # R(j) mod n -> j
    r = 0
    for j in range(n + 1):
        if r in seen:
            a, b = seen[r], j
            return "1" * (b - a) + "0" * a
        seen[r] = j
        r = (10 * r + 1) % n


def smallest_repunit_multiple(n):
    """Smallest repunit 11...1 divisible by n, as a string.

    Only exists when n ends in 1/3/7/9.
    """
    if n % 2 == 0 or n % 5 == 0:
        return None
    r, length = 1 % n, 1
    while r != 0:
        r, length = (10 * r + 1) % n, length + 1
    return "1" * length


def show(x, width=60):
    s = str(x)
    return s if len(s) <= width else f"{s[:20]}...{s[-20:]} ({len(s)} digits)"


def main(args):
    for n in map(int, args or ["7", "12", "13", "2026", "9999"]):
        rows = [
            ("smallest 0/1", str(smallest_zero_one_multiple(n))),
            ("pigeonhole 0/1", pigeonhole_multiple(n)),
            ("smallest 1s", smallest_repunit_multiple(n)),
        ]
        print(f"n = {n}")
        for name, m in rows:
            if m is None:
                print(f"  {name:15} none (n is divisible by 2 or 5)")
                continue
            if len(m) > 5000:  # dividing huge numbers is the slow part; skip it
                print(f"  {name:15} n*k = {show(m)}")
                continue
            assert int(m) % n == 0 and set(m) <= {"0", "1"}
            print(f"  {name:15} k = {show(int(m) // n)}   n*k = {show(m)}")


if __name__ == "__main__":
    main(sys.argv[1:])
