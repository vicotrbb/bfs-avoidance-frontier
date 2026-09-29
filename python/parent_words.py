"""Parent-sequence realizability and the full-k construction.

Positions are zero-based. A degree sequence is accepted only if its queue
contains the next parent and every assigned child exceeds that parent.
This implementation is separate from the level-boundary NFA in solver.py.
"""
from functools import lru_cache


def avoids(word, pattern):
    """Direct inequalities, independent of reference.py's rank construction."""
    for i, a in enumerate(word):
        for j in range(i + 1, len(word)):
            b = word[j]
            for c in word[j + 1:]:
                if pattern == 231 and c < a < b:
                    return False
                if pattern == 312 and b < c < a:
                    return False
                if pattern == 321 and c < b < a:
                    return False
    return True


def realization(word, k=2, full=False):
    """Return a BFS degree sequence, or None when no realization exists."""
    n = len(word)
    if n == 0 or k < 1:
        return None

    @lru_cache(None)
    def search(parent, child):
        if child == n:
            return (0,) * (n - parent)
        if parent >= child:
            return None
        sizes = (0, k) if full else range(k + 1)
        for degree in sizes:
            end = child + degree
            if end > n or any(word[parent] >= x for x in word[child:end]):
                continue
            tail = search(parent + 1, end)
            if tail is not None:
                return (degree,) + tail
        return None

    return search(0, 1)


def parent_list(degrees):
    return tuple(parent for parent, degree in enumerate(degrees)
                 for _ in range(degree))


def full_k_parents(parents, k):
    """Block construction from Theorem B; input must satisfy its hypotheses."""
    if k < 1 or len(parents) % k:
        raise ValueError('The number of nonroot positions must be divisible by k')
    return tuple(parents[(offset // k) * k] for offset in range(len(parents)))


def reconstruct(parents):
    """Return adjacency lists and check the supplied numbering is BFS order."""
    n = len(parents) + 1
    children = [[] for _ in range(n)]
    for child, parent in enumerate(parents, 1):
        if not 0 <= parent < child:
            raise ValueError('Parent must precede child')
        children[parent].append(child)
    order = [0]
    for vertex in order:
        order.extend(children[vertex])
    if order != list(range(n)):
        raise ValueError('Parent sequence does not preserve BFS order')
    return children
