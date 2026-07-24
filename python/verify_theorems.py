#!/usr/bin/env python3
"""Exhaustive machine verification of every lemma/theorem in docs/THEOREMS.md.

Run: python3 python/verify_theorems.py  (from the repository root)   (~2-3 min)
Exits nonzero on any failure.
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from reference import bfs_words, avoids
from functools import lru_cache

def feasible(P, C, binary=False):
    M, K = len(P), len(C)
    if K == 0: return True
    if M == 0 or K > 2 * M: return False
    states = {(0, 0)}
    for c in C:
        ns = set()
        for (i, u) in states:
            if i < M and u < 2 and c > P[i]: ns.add((i, u + 1))
            j, uu = i, u
            while j < M:
                if binary and uu == 1: break
                j += 1; uu = 0
                if j < M and c > P[j]: ns.add((j, 1))
        states = ns
        if not states: return False
    return any(not (binary and u == 1) for (_, u) in states)

def heap_words(n):
    res = set()
    def rec(pos, used, word):
        if pos == n + 1: res.add(tuple(word)); return
        for v in range(1, n + 1):
            if used >> v & 1: continue
            if pos > 1 and v < word[pos // 2 - 1]: continue
            word.append(v); rec(pos + 1, used | 1 << v, word); word.pop()
    rec(1, 0, [])
    return res

failures = 0
def check(name, cond, detail=""):
    global failures
    if not cond:
        failures += 1
        print("FAIL:", name, detail)

# --- Theorem A: 312-avoiding UB words == heap words (set identity) ---
for n in range(1, 12):
    ub = {w for w in bfs_words(n, 'ub') if avoids(w, (3, 1, 2))}
    hp = {w for w in heap_words(n) if avoids(w, (3, 1, 2))}
    check("Theorem A set identity n=%d" % n, ub == hp)
print("Theorem A verified (n<=11)")

# --- Lemmas B3, B4, B5 ---
b3 = b4 = b5 = 0
for n in (8, 9):
    for w in bfs_words(n, 'ub'):
        is231 = avoids(w, (2, 3, 1))
        @lru_cache(None)
        def T(a, b):
            if b == n: return True
            return any(feasible(w[a:b], w[b:e]) and T(b, e) for e in range(b + 1, n + 1))
        for a in range(0, n):
            for b in range(a + 1, n):
                # B5: unconditional promotion cascade (all words)
                if T(a, b):
                    b5 += 1
                    check("Lemma B5 (T+)", T(a, b + 1), (w, a, b))
                if not is231: continue
                for e in range(b + 1, n):
                    P, C = w[a:b], w[b:e]
                    if not feasible(P, C): continue
                    K = e - b
                    if K % 2 == 1:   # B3: odd extension
                        b3 += 1
                        check("Lemma B3", feasible(P, w[b:e + 1]), (w, a, b, e))
                    else:            # B4: even fibers
                        b4 += 1
                        check("Lemma B4", feasible(P, C, binary=True), (w, a, b, e))
        T.cache_clear()
print("Lemma B3 instances: %d, B4: %d, B5: %d" % (b3, b4, b5))

# --- Theorem B consequence: odd-length 231 UB words are B-realizable ---
for n in (9, 11):
    ub = {w for w in bfs_words(n, 'ub') if avoids(w, (2, 3, 1))}
    b = {w for w in bfs_words(n, 'b') if avoids(w, (2, 3, 1))}
    check("Theorem B set identity n=%d" % n, ub == b)
print("Theorem B verified (n=9,11)")

# --- Sharpness: 321 collapse fails at n=11 ---
ub321 = {w for w in bfs_words(11, 'ub') if avoids(w, (3, 2, 1))}
b321 = {w for w in bfs_words(11, 'b') if avoids(w, (3, 2, 1))}
check("321 sharpness", len(ub321) == 8095 and len(b321) == 8048 and len(ub321 - b321) == 47)
print("Sharpness verified (8095/8048, 47 witnesses)")

# --- A246747 recurrence matches A245899 counts ---
from math import comb
def catalan(i): return comb(2 * i, i) // (i + 1)
a = [1]
for m in range(1, 15):
    a.append(sum(catalan(i) * a[m - i - 1] for i in range((m - 1) // 2 + 1)))
counts = [len({w for w in bfs_words(n, 'ub') if avoids(w, (3, 1, 2))}) for n in range(1, 11)]
check("A245899 == A246747 numerically", counts == a[1:11], (counts, a[1:11]))
print("Recurrence identity verified (n<=10)")

print("ALL CHECKS PASSED" if failures == 0 else "%d FAILURES" % failures)
sys.exit(1 if failures else 0)
