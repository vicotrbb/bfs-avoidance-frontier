# Increasing-Tree BFS Words: Two Rigidity Theorems

> **Machine-checked**: both theorems are fully formalized in Lean 4 — see
> [`../lean/`](../lean/). The formal proofs depend only on Lean's standard
> axioms (no `sorry`). The formalization also *simplified* the arguments
> below: Theorem A's Case 2 (dyadic forcing) is unnecessary — the invariant
> `s_j ≤ 2·s_{j-1}` (provable by a one-line telescoping induction) gives
> `heap-parent ≤ balanced-parent` directly, and the Case 1 pattern argument
> then covers everything. Lemmas B2–B4's explicit chain-shifts likewise
> reduce to structural inductions (`../lean/BfsWords/B231.lean`).

**Resolving three open conjectures on OEIS A245898–A245903 / A246747**

Setting. All trees are rooted, with distinct labels `1..n`, *increasing* (every
child's label exceeds its parent's), and *unary-binary* (every node has at most
2 children; *full binary* = every node has 0 or 2 children). The *BFS word* of
a tree is the permutation read level by level, left to right. A permutation
`w` (necessarily `w_1 = 1`) is **UB-realizable** (resp. **B-realizable**) if it
is the BFS word of some increasing unary-binary (resp. full binary) tree. The
*complete shape* `C_n` is the binary-heap shape: node `i` has children `2i,
2i+1` (when ≤ n); `w` is a **heap word** iff `w_{⌊i/2⌋} < w_i` for all
`2 ≤ i ≤ n`.

Realizability is a statement about the word alone: a realization is a
partition of positions `1..n` into contiguous *levels* `L_0 = {1}, L_1, …,
L_m` together with, for each adjacent pair, a *matching*: an order-preserving
assignment φ of the child block `C = (c_1..c_K)` to the parent block
`P = (p_1..p_M)` (φ nondecreasing, fibers of size ≤ 2 — for full binary,
size 0 or 2 — and `c_j > p_{φ(j)}` for all j). Here `c_j`, `p_t` denote
*values*; positions of all of P precede positions of all of C.

---

## Theorem A (312 rigidity: heap collapse)

**Let `w` avoid the pattern 312. Then `w` is UB-realizable if and only if `w`
is a heap word.**

*Proof.*

(⇐) The complete shape is unary-binary and the heap condition makes its
labeling increasing; its BFS word is `w` itself.

(⇒) Recall 312-avoidance: there are no positions `i<j<l` with
`w_j < w_l < w_i`.

**Lemma A1 (balanced matching).** *If `w` avoids 312 and blocks `(P, C)`
admit a valid matching φ, then the balanced matching ψ(j) = ⌈j/2⌉ is valid.*

Since φ is nondecreasing with fibers ≤ 2, the first `j` children occupy at
least `⌈j/2⌉` parents, so `φ(j) ≥ ⌈j/2⌉ =: t` for every j. If `φ(j) = t`
then `c_j > p_t` directly. Otherwise `φ(j) > t` and `c_j > p_{φ(j)}`.
Suppose `c_j < p_t`. Then `p_{φ(j)} < c_j < p_t`, and the positions of
`p_t, p_{φ(j)}, c_j` are increasing — an occurrence of 312
(large, small, middle). Contradiction; so `c_j > p_t`. ∎(A1)

Now fix a UB-realization of `w`; by Lemma A1 assume all its matchings are
balanced. Let the level sizes be `n_0 = 1, n_1, …, n_m` and level start
positions `s_t = 1 + n_0 + … + n_{t-1}`. Note `n_{t+1} ≤ 2 n_t` (capacity),
hence `n_t ≤ 2^t` and `s_{t+1} ≤ 2^{t+1}` by induction.

Fix a position `p ≥ 2`; let `q = ⌊p/2⌋`. We show `w_q < w_p`. Let `j` be the
level of `p`, and `pp < p` the position of p's parent under the balanced
matching, so `w_{pp} < w_p` and, writing `k = p − s_j + 1` (rank of `p` in
its level), `pp = s_{j-1} + ⌈k/2⌉ − 1`. Then

    2·pp = 2 s_{j-1} + 2⌈k/2⌉ − 2 ≥ 2 s_{j-1} + k − 1
         = p + (2 s_{j-1} − s_j − 1) = p + (s_{j-1} − n_{j-1} − 1).

**Case 1: `n_{j-1} ≤ s_{j-1} − 1`.** Then `2·pp ≥ p`, i.e. `pp ≥ q`.
If `pp = q` we are done since `w_{pp} < w_p`. If `pp > q`, suppose
`w_q > w_p`; then `w_{pp} < w_p < w_q` at increasing positions
`q < pp < p` — an occurrence of 312. So `w_q < w_p`.

**Case 2: `n_{j-1} ≥ s_{j-1}`.** Write `t = j−1`, `S = s_t`, `N = n_t ≥ S`.
From `n_i ≥ n_{i+1}/2` we get `n_i ≥ N/2^{t-i}` for `i < t`, so
`S − 1 = Σ_{i<t} n_i ≥ N(1 − 2^{-t}) ≥ S(1 − 2^{-t})`, giving `S ≥ 2^t`.
But also `N ≤ 2^t` and `S ≤ 1 + (2^t − 1) = 2^t`. Hence `S = N = 2^t` and,
chasing the equalities, `n_i = 2^i` for all `i ≤ t`: the tree is exactly
dyadic through level `t`, with `s_j = 2^j`. Then
`pp = 2^{j-1} − 1 + ⌈k/2⌉` and a direct check gives `pp = ⌊p/2⌋ = q`
for every k, so again `w_q < w_p`. ∎(Theorem A)

### Corollaries (312)

Heap words on a fixed shape are in bijection with heaps (the word determines
the labeling). Hence:

* **A245899(n) = A246747(n)** for all n — the number of 312-avoiding
  UB-realizable words equals the number of binary heaps on `n` elements whose
  reading word avoids 312, which equals A246747 (Levin–Pudwell–Riehl–Sandberg;
  their entry also gives `a(n) = Σ_{i≤(n-1)/2} Catalan(i)·a(n−i−1)`).
  This settles the conjecture recorded in OEIS A246747: “May be equal to
  A245899.” The bijection is the **identity map** on words.
* **A245902(k) = A245899(2k−1)** for all k: on odd `n` the complete shape
  `C_n` has no node with exactly one child, i.e. it is full binary, so heap
  word ⇒ B-realizable; conversely B-realizable ⇒ UB-realizable trivially.
  With Theorem A the three word classes (UB, B, heap) coincide for
  312-avoiding words of odd length.
* A245899 therefore inherits the Catalan recurrence and A246747's 1000-term
  b-file.

---

## Theorem B (231 parity collapse)

**Let `w` avoid 231 and have odd length. If `w` is UB-realizable then `w` is
B-realizable.** Consequently **A245901(k) = A245898(2k−1)** for all k.

*Proof.* 231-avoidance: no `i<j<l` with `w_l < w_i < w_j`.

**Lemma B1 (suffix compatibility).** *If `w` avoids 231, blocks `(P, C)`, and
`c_j > p_t`, then `c_{j'} > p_t` for every `j' > j`.*
Otherwise `(p_t, c_j, c_{j'})` has values (middle, large, small) at increasing
positions — an occurrence of 231. ∎(B1)

**Lemma B2 (chain shift).** *Let `w` avoid 231 and let φ be a valid matching
of `(P, C)`. Let `t° < t*` be used parents such that every used parent in
`(t°, t*]` has fiber 2. Then there is a valid matching in which the first
child of each used parent in `(t°, t*]` is reassigned to the preceding used
parent (so t° gains one child, intermediates keep two, t* keeps its last
child(ren) minus its first).*
Each moved child `c` is positioned after some child `c'` of its new parent
`p` with `c' > p`; by Lemma B1, `c > p`. Fibers remain consecutive and
monotone. ∎(B2)

**Lemma B3 (odd extension).** *Let `w` avoid 231, let `(P, C)` be feasible
with `K = |C|` odd, and let `x` be the element at the position immediately
after `C`. Then `(P, C·x)` is feasible.*
Fibers sum to the odd number K, so some used parent has fiber 1; let `t°` be
the last such and `t*` the last used parent. If `t° < t*`, all used parents
in `(t°, t*]` have fiber 2; apply Lemma B2 so that `t*` has fiber 1. Let
`p = p_{t*}`; under the (shifted) matching the last child `c_K` satisfies
`c_K > p`. If `x < p` then `(p, c_K, x)` is an occurrence of 231
(middle, large, small). So `x > p`, and appending `x` to `t*` (last used
parent, spare capacity, monotone) extends the matching. K + 1 ≤ 2M holds
since K ≤ 2M and K is odd. ∎(B3)

**Lemma B4 (even fibers).** *If `w` avoids 231, `(P, C)` is feasible and `K`
is even, then there is a valid matching with every fiber of size 0 or 2.*
Odd (=1) fibers are even in number; pair them up consecutively and apply
Lemma B2 between the members of each pair: the earlier gains a child (1→2),
intermediates stay at 2, the later loses its only child (1→0). ∎(B4)

For a word `w` of length n define, for `0 ≤ a < b ≤ n`,
**T(a,b)**: “positions `b..n−1` can be partitioned into levels, with previous
level the block `[a,b)`, all adjacent matchings valid (caps ≤ 2).”
(`T(a,n)` is vacuously true.)

**Lemma B5 (promotion cascade — no pattern hypothesis).** *For any word `w`
and any `a < b < n`: T(a,b) ⇒ T(a,b+1).*

Let a witness for `T(a,b)` have levels `D_1 = [b, e_1), D_2 = [e_1, e_2), …`
with matchings ν_t : D_t → D_{t−1} (where `D_0 = [a,b)`), and let `x = w_b`,
the first element of `D_1`. Define promoted sets: `J_0 = {x}` and
`J_t = ν_{t+1}^{-1}(J_{t−1})` — the old children of the previously promoted
elements. By induction each `J_t` is a contiguous *head* of `D_{t+1}`:
ν is monotone and `J_{t−1}` is a head of the parent block among used parents
(children of dropped-out earlier parents are exactly the previously promoted
elements). Define new levels
`D'_t = (D_t ∖ J_{t−1}) · J_t` — i.e. block boundaries shift right by
`|J_{t−1}|` on the left and `|J_t|` on the right; all blocks remain
contiguous. The new previous level is `[a, b+1) = D_0 · x`.

Matchings for the new chain: children in `D_t ∖ J_{t−1}` keep their old
parents — these lie in `D_{t−1} ∖ J_{t−2}` precisely because
`J_{t−1} = ν_t^{-1}(J_{t−2})`; children in `J_t` keep their old parents,
which are exactly `J_{t−1}`, now the trailing elements of `D'_{t−1}`. Every
parent–child pair is an *old* valid pair, so all value conditions hold with
no new comparisons; fibers are unchanged (≤ 2); monotonicity holds because
`J`-blocks are appended at the ends of both parent and child blocks in
original order. If some `D'_t` is empty, all deeper `D'` are empty as well
(a nonempty `D_{t+1}` forces `J_t ≠ ∅` since its elements' parents must lie
in `D_t = J_{t−1} ∪ (D_t ∖ J_{t−1})`), so the chain merely shortens.
∎(B5)

**Completing Theorem B.** Let `w` (231-avoiding, `n` odd) be UB-realizable.
Among all valid level-size vectors `(1, n_1, …, n_m)` take `v` lexicographically
maximal. Suppose some `n_i` (i ≥ 1) is odd, and take `i` minimal. Since
`Σ_{t≥1} n_t = n − 1` is even, the number of odd levels is even, so level `i`
is not the last: the element `x` after level `L_i` exists. Writing `b_i,
b_{i+1}` for the start and end positions of `L_i`: `(L_{i−1}, L_i·x)` is
feasible by Lemma B3 (K = n_i odd), and `T(b_i, b_{i+1})` holds (witness: the
suffix of `v` itself), so `T(b_i, b_{i+1}+1)` holds by Lemma B5. Together
these produce a valid vector agreeing with `v` up to level `i−1` with level-i
size `n_i + 1 > n_i` — contradicting lex-maximality. Hence **every level of
`v` is even**. By Lemma B4 choose all matchings of `v` with fibers in
{0, 2}: the result is an increasing full binary tree with BFS word `w`.
∎(Theorem B)

**Remark (sharpness).** Both theorems are sharp in the pattern: for
321-avoiding words the analogue of Lemma B3 fails — the forced-inequality
triple `(p, c_K, x)` is a 231/312 pattern, invisible to 321-avoidance — and
indeed the collapse is false for 321: at length 11 there are 8095
UB-realizable 321-avoiding words but only 8048 B-realizable ones (47 explicit
witnesses in `../data/certificates/certificate_321_n11.txt`).

---

## Machine verification of every step

All lemmas and theorems were verified exhaustively (`../python/`, see `verify_theorems.py`):

| Claim | Verified range | Instances | Failures |
|---|---|---|---|
| Theorem A as set identity (UB 312-words = heap words) | n ≤ 11 | 2 654 sets | 0 |
| Lemma B3 (odd extension, incl. free completion) | n ∈ {9,11} | 92 732 | 0 |
| Lemma B4 (even fibers) | n ∈ {9,11}, all blocks | all | 0 |
| Lemma B5 / T+ (unconditional, incl. non-avoiding words) | n ∈ {8,9} | 127 127 | 0 |
| A245899 = A246747 (numeric) | n ≤ 14 vs b-file | 14 terms | 0 |
| A245901(k) = A245898(2k−1), A245902(k) = A245899(2k−1) | lengths ≤ 13 | all | 0 |

The failed candidate lemmas (unrestricted window shift, shrink-head,
right-packed canonicalization for 231) are documented by counterexample in the
session logs — the final proof uses none of them.
