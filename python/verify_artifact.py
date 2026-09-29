#!/usr/bin/env python3
"""Reproduce and check the sequence files, certificates, and general-k proofs.

--full recomputes every directly enumerated retained term (up to UB length
14 and full binary length 15). Without it the solver stops at length 11.
The long 312 b-files are always checked using the Catalan recurrence.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
from datetime import datetime, timezone
from itertools import permutations
import json
from math import comb
from pathlib import Path
import platform
import time

from parent_words import avoids, realization, parent_list, full_k_parents, reconstruct
from reference import bfs_words, avoids as reference_avoids
from solver import solve, PATS

ROOT = Path(__file__).resolve().parents[1]


def read_raw(mode, pattern):
    return dict(tuple(map(int, line.replace('n=', '').replace('count=', '').split()))
                for line in (ROOT / 'data/raw' / f'{mode}_{pattern}.txt').read_text().splitlines())


def compute_series(job):
    mode, pattern, full = job
    start = time.monotonic()
    expected = read_raw(mode, pattern)
    actual = {n: solve(n, mode, PATS[str(pattern)]) for n in expected if full or n <= 11}
    assert all(expected[n] == value for n, value in actual.items()), (mode, pattern, actual)
    return {'mode': mode, 'pattern': pattern, 'values': actual,
            'seconds': round(time.monotonic() - start, 3)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    checks = {}
    jobs = [(mode, pattern, args.full) for mode in ('ub', 'b') for pattern in (231, 312, 321)]
    with ProcessPoolExecutor(max_workers=4) as pool:
        checks['solver'] = []
        for result in pool.map(compute_series, jobs):
            checks['solver'].append(result)
            print('Solver verified:', result['mode'], result['pattern'], 'through', max(result['values']), flush=True)

    # Tree enumeration cross-checks every published term and the first extensions.
    reference_checks = 0
    ub321 = b321 = None
    for mode in ('ub', 'b'):
        for n in (range(1, 12) if mode == 'ub' else range(1, 12, 2)):
            words = bfs_words(n, mode)
            for pattern in (231, 312, 321):
                selected = {w for w in words if reference_avoids(w, PATS[str(pattern)])}
                assert len(selected) == read_raw(mode, pattern)[n], (mode, n, pattern)
                reference_checks += 1
                if n == 11 and pattern == 321:
                    if mode == 'ub': ub321 = selected
                    else: b321 = selected
    checks['reference_values'] = reference_checks
    certificate_path = ROOT / 'data/certificates/certificate_321_n11.txt'
    certificate = [tuple(map(int, line.split())) for line in certificate_path.read_text().splitlines()
                   if line and not line.startswith('#')]
    assert len(certificate) == len(set(certificate)) == 47
    assert set(certificate) == ub321 - b321
    for word in certificate:
        assert sorted(word) == list(range(1, 12)) and avoids(word, 321)
        assert realization(word) is not None and realization(word, full=True) is None
    for n in (1, 3, 5, 7, 9):
        ub = {w for w in bfs_words(n, 'ub') if avoids(w, 321)}
        fb = {w for w in bfs_words(n, 'b') if avoids(w, 321)}
        assert ub == fb, n
    checks['certificate_words'] = len(certificate)
    print('Reference values and exact 47-word certificate verified', flush=True)

    # All permutations, including words that do not begin with the minimum.
    general = []
    for k in (2, 3, 4):
        cases = conversions = 0
        for n in range(1, 8):
            for word in permutations(range(1, n + 1)):
                degrees = realization(word, k)
                if avoids(word, 312):
                    heap = all(word[(i - 1) // k] < word[i] for i in range(1, n))
                    assert (degrees is not None) == heap, (k, word)
                if (n - 1) % k == 0 and avoids(word, 231):
                    full = realization(word, k, full=True)
                    assert (degrees is not None) == (full is not None), (k, word)
                    if degrees is not None:
                        new = full_k_parents(parent_list(degrees), k)
                        adjacency = reconstruct(new)
                        assert all(len(c) in (0, k) for c in adjacency)
                        assert all(word[p] < word[i] for i, p in enumerate(new, 1))
                        conversions += 1
                cases += 1
        general.append({'k': k, 'permutations': cases, 'conversions': conversions})
    checks['general_k'] = general
    # Independent relative-order predicate cross-check.
    for word in permutations(range(1, 7)):
        for pattern in (231, 312, 321):
            assert avoids(word, pattern) == reference_avoids(word, PATS[str(pattern)])

    cats = [comb(2 * i, i) // (i + 1) for i in range(501)]
    recurrence = [1]
    for n in range(1, 1001):
        recurrence.append(sum(cats[i] * recurrence[n - i - 1] for i in range((n - 1) // 2 + 1)))
    bfiles = {}
    for seq, mode, pattern in [('245898', 'ub', 231), ('245899', 'ub', 312),
                               ('245900', 'ub', 321), ('245901', 'b', 231),
                               ('245902', 'b', 312), ('245903', 'b', 321)]:
        path = ROOT / 'oeis-submission/bfiles' / f'b{seq}.txt'
        rows = [tuple(map(int, line.split())) for line in path.read_text().splitlines()
                if line and not line.startswith('#')]
        assert [i for i, _ in rows] == list(range(1, len(rows) + 1)), seq
        raw = read_raw(mode, pattern)
        for i, value in rows:
            n = i if mode == 'ub' else 2 * i - 1
            if pattern == 312:
                expected = recurrence[n]
            elif mode == 'ub' and n == 15 and pattern == 231:
                expected = read_raw('b', 231)[15]
            else:
                expected = raw[n]
            assert value == expected, (seq, i, value, expected)
        bfiles[seq] = {'first_index': 1, 'last_index': len(rows)}
    checks['bfiles'] = bfiles
    checks['new_sequence_entries'] = 7 + 6 + 6 + 3 + 3 + 3
    checks['previously_displayed_entries'] = 3 * 8 + 3 * 5
    report = {'status': 'pass', 'full_recomputation': args.full,
              'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'python': platform.python_version(), 'platform': platform.platform(),
              'seconds': round(time.monotonic() - start, 3), 'checks': checks}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
