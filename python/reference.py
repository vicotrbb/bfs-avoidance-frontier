#!/usr/bin/env python3
"""Reference (brute-force) enumerator for BFS reading words of increasing trees.

Enumerates, level by level, every way to build an increasing tree on labels
1..n where each node has at most 2 children ("unary-binary" mode) or exactly
0 or 2 children ("binary" mode, i.e. full binary trees).  The BFS reading
word is the concatenation of the levels read left to right.  Words are
deduplicated in a set; we then count how many avoid each classical pattern.

This is deliberately simple and slow: it is the ground truth used to
validate the fast solver.

Sequences covered:
  unary-binary: A245898 (avoid 231), A245899 (312), A245900 (321)
  binary      : A245901 (231), A245902 (312), A245903 (321)  [lengths 2k-1]
"""
import sys
from itertools import combinations, permutations


def avoids(word, pat):
    """True if word contains no (classical) occurrence of the length-3 pattern."""
    n = len(word)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                a, b, c = word[i], word[j], word[k]
                trip = sorted([a, b, c])
                rank = (trip.index(a) + 1, trip.index(b) + 1, trip.index(c) + 1)
                if rank == pat:
                    return False
    return True


def bfs_words(n, mode):
    """Set of all BFS reading words of increasing trees on n nodes.

    mode 'ub': each node has 0..2 children.
    mode 'b' : each node has 0 or 2 children (full binary trees).
    """
    words = set()
    child_counts = (0, 1, 2) if mode == "ub" else (0, 2)

    def extend(level, remaining, word):
        # level: tuple of labels of current level, left to right
        # remaining: frozenset of unused labels
        if not remaining:
            if True:
                words.add(word)
            return
        # choose children counts for each node in level, then assign labels
        def assign(i, counts_left, rem, next_level):
            # i indexes into level; pick children for level[i]
            if i == len(level):
                if next_level:
                    extend(tuple(next_level), frozenset(rem), word + tuple(next_level))
                return
            parent = level[i]
            for c in child_counts:
                if c == 0:
                    assign(i + 1, counts_left, rem, next_level)
                else:
                    # choose an ordered tuple of c distinct labels > parent
                    cands = [x for x in rem if x > parent]
                    if len(cands) < c:
                        continue
                    for combo in combinations(cands, c):
                        for perm in permutations(combo):
                            assign(i + 1, counts_left, rem - set(perm),
                                   next_level + list(perm))
        assign(0, None, remaining, [])

    extend((1,), frozenset(range(2, n + 1)), (1,))
    return words


PATS = {"231": (2, 3, 1), "312": (3, 1, 2), "321": (3, 2, 1)}


def main():
    mode = sys.argv[1]           # 'ub' or 'b'
    nmax = int(sys.argv[2])
    ns = range(1, nmax + 1) if mode == "ub" else range(1, nmax + 1, 2)
    for n in ns:
        words = bfs_words(n, mode)
        counts = {name: sum(1 for w in words if avoids(w, p))
                  for name, p in PATS.items()}
        print(f"n={n} total_words={len(words)} "
              + " ".join(f"{k}:{v}" for k, v in sorted(counts.items())),
              flush=True)


if __name__ == "__main__":
    main()
