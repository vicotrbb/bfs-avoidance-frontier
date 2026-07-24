#!/usr/bin/env python3
"""Fast solver: counts pattern-avoiding BFS reading words of increasing trees.

Independent algorithm from reference.py.  Instead of enumerating trees, it
enumerates permutation prefixes (DFS) and prunes any prefix that
  (a) contains the forbidden classical pattern, or
  (b) is not extendable to a BFS reading word of an increasing tree of the
      given class (unary-binary: <=2 children per node; binary: 0 or 2).

Realizability is tracked incrementally with a set of configurations.  A
configuration is (prev_level_start, cur_level_start, nfa_states) where
nfa_states is the set of (parent_index, children_assigned_to_that_parent)
states of the left-to-right matching between the previous (complete) level
and the current (growing) level.  Levels are contiguous blocks of the word;
children of consecutive parents form consecutive groups.

Usage: solver.py {ub|b} PATTERN NMAX   e.g. solver.py ub 231 12
"""
import sys
sys.setrecursionlimit(100000)

PATS = {"231": (2, 3, 1), "312": (3, 1, 2), "321": (3, 2, 1)}


def solve(n, mode, pat):
    binary = (mode == "b")
    word = [1]

    def creates_pattern(c):
        m = len(word)
        for i in range(m):
            for j in range(i + 1, m):
                a, b = word[i], word[j]
                trip = sorted([a, b, c])
                if (trip.index(a) + 1, trip.index(b) + 1, trip.index(c) + 1) == pat:
                    return True
        return False

    def nfa_feed(states, parents, c):
        """Advance matching-NFA states by one child with label c."""
        out = set()
        for (i, used) in states:
            # option 1: give c to parent i
            if i < len(parents) and used < 2 and c > parents[i]:
                out.add((i, used + 1))
            # option 2..: close parent i (if allowed) and try later parents
            j, u = i, used
            while j < len(parents):
                if binary and u == 1:
                    break  # cannot close a parent with exactly 1 child
                j += 1
                u = 0
                if j < len(parents) and c > parents[j]:
                    out.add((j, 1))
        return out

    def nfa_closes(states, nparents):
        """Can the level be closed (remaining parents get 0 children)?"""
        for (i, used) in states:
            if binary and used == 1:
                continue
            return True  # all parents from i on take 0 children: always ok
        return False

    count = 0

    def dfs(configs, used_mask, depth):
        nonlocal count
        if depth == n:
            for (ps, cs, states) in configs:
                if nfa_closes(states, cs - ps):
                    count += 1
                    break
            return
        for c in range(2, n + 1):
            if used_mask >> c & 1:
                continue
            if creates_pattern(c):
                continue
            newconfigs = []
            seen = set()
            for (ps, cs, states) in configs:
                parents = word[ps:cs]
                # extend current level with c
                ns = nfa_feed(states, parents, c)
                if ns:
                    key = (ps, cs, frozenset(ns))
                    if key not in seen:
                        seen.add(key)
                        newconfigs.append((ps, cs, ns))
                # or close current level at depth, open new level with c
                if nfa_closes(states, cs - ps):
                    nparents = word[cs:depth]
                    ns2 = nfa_feed({(0, 0)}, nparents, c)
                    if ns2:
                        key = (cs, depth, frozenset(ns2))
                        if key not in seen:
                            seen.add(key)
                            newconfigs.append((cs, depth, ns2))
            if not newconfigs:
                continue
            word.append(c)
            dfs(newconfigs, used_mask | 1 << c, depth + 1)
            word.pop()
        return

    if n == 1:
        return 1
    # initial: root level [0,1); position 1 starts level 2 handled by dfs's
    # "close and open" path from a virtual config where level [0,1) is current.
    init = [(0, 1, {(0, 0)})]
    # here prev level is empty-before-root; represent root as current level
    # with a dummy previous level that is already closed.  Simpler: treat
    # root level as the *previous* level and start the second level empty.
    # We encode: ps=0, cs=1, states = fresh NFA for parents=[1] with no
    # children yet.
    dfs(init, 1 << 1, 1)
    return count


def main():
    mode, pat, nmax = sys.argv[1], PATS[sys.argv[2]], int(sys.argv[3])
    ns = range(1, nmax + 1) if mode == "ub" else range(1, nmax + 1, 2)
    for n in ns:
        print(f"n={n} count={solve(n, mode, pat)}", flush=True)


if __name__ == "__main__":
    main()
