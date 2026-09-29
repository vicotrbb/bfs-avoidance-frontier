#!/usr/bin/env python3
"""Check the parent-sequence DP against exhaustive parent-map enumeration.

All permutations of lengths 1 through 7 are tested at branching bounds
1 through 4, with bounded and full outdegrees. The independent oracle
constructs nondecreasing parent maps directly and tests their edges.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
from itertools import permutations
import json
from pathlib import Path
import platform
import time

from parent_words import realization


def parent_maps(n, k):
    """Enumerate parent maps directly, without the degree-sequence DP."""
    maps = []
    parents = []
    multiplicities = [0] * n

    def visit():
        child = len(parents) + 1
        if child == n:
            maps.append(tuple(parents))
            return
        first = parents[-1] if parents else 0
        for parent in range(first, child):
            if multiplicities[parent] < k:
                parents.append(parent)
                multiplicities[parent] += 1
                visit()
                multiplicities[parent] -= 1
                parents.pop()

    visit()
    return maps


def verify_witness(word, degrees, k, full):
    """Independently reconstruct and check a returned degree witness."""
    n = len(word)
    assert len(degrees) == n, (word, degrees)
    assert all(isinstance(d, int) and 0 <= d <= k for d in degrees)
    if full:
        assert all(d in (0, k) for d in degrees)
    assert sum(degrees) == n - 1
    children = [[] for _ in range(n)]
    next_child = 1
    for parent, degree in enumerate(degrees):
        for child in range(next_child, next_child + degree):
            assert parent < child < n, (word, degrees, parent, child)
            assert word[parent] < word[child], (word, degrees, parent, child)
            children[parent].append(child)
        next_child += degree
    assert next_child == n
    queue = [0]
    for vertex in queue:
        queue.extend(children[vertex])
    assert queue == list(range(n)), (word, degrees, queue)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write the JSON audit receipt')
    args = parser.parse_args()
    start = time.monotonic()
    cases = []
    total = 0
    witnesses = 0
    for n in range(1, 8):
        for k in range(1, 5):
            bounded = parent_maps(n, k)
            full_maps = [p for p in bounded if all(v == k for v in Counter(p).values())]
            families = ((False, bounded), (True, full_maps))
            comparisons = 0
            accepted = {False: 0, True: 0}
            for word in permutations(range(1, n + 1)):
                for full, maps in families:
                    expected = any(
                        all(word[parent] < word[child]
                            for child, parent in enumerate(parents, 1))
                        for parents in maps
                    )
                    degrees = realization(word, k, full)
                    assert (degrees is not None) == expected, (n, k, full, word)
                    if degrees is not None:
                        verify_witness(word, degrees, k, full)
                        accepted[full] += 1
                        witnesses += 1
                    comparisons += 1
            cases.append({
                'n': n, 'k': k, 'comparisons': comparisons,
                'bounded_parent_maps': len(bounded),
                'full_parent_maps': len(full_maps),
                'bounded_realizable_words': accepted[False],
                'full_realizable_words': accepted[True],
            })
            total += comparisons
    assert total == 47304, total
    report = {
        'status': 'pass',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'python': platform.python_version(),
        'platform': platform.platform(),
        'seconds': round(time.monotonic() - start, 3),
        'oracle': 'direct exhaustive nondecreasing parent-map enumeration',
        'lengths': list(range(1, 8)),
        'branching_bounds': list(range(1, 5)),
        'modes': ['bounded', 'full'],
        'comparisons': total,
        'witnesses_verified': witnesses,
        'cases': cases,
    }
    encoded = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
