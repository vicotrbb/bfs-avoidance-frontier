# OEIS Submission Package

Proposed edits for the seven entries touched by this work. Submit each as a
draft edit at https://oeis.org (log in, open the sequence, click "edit").
Every draft goes through OEIS editor review; keep each edit focused and let
the b-files carry the long data.

Conventions used below:

* `SIGNATURE` stands for your OEIS signature, which the wiki inserts as
  `_Your Name_, Jul 24 2026`. Register the account under the name you want
  credited (the paper uses Victor Bona).
* `REPO` = https://github.com/vicotrbb/bfs-avoidance-frontier
* The paper reference below can be updated to the arXiv number once posted.
  Until then the repository link suffices; OEIS accepts links to code and
  papers in the LINKS section.
* Upload the b-files from `bfiles/` using the "b-file" upload on each edit
  page. Their index ranges are stated in each LINKS line.

Suggested submission order: A245899 and A245902 first (they carry the
strongest content, a proven identity and 1000-term b-files), then A246747
(closing its conjecture note), then the remaining four.

---

## A245899 (312 on increasing unary-binary trees)

**DATA** (extend to):

```
1, 1, 2, 3, 7, 14, 37, 80, 222, 544, 1601, 4095, 12416, 33785
```

**COMMENTS** (add):

```
A permutation avoiding 312 is the breadth-first search reading word of an
increasing unary-binary tree if and only if it satisfies the binary heap
condition w(floor(i/2)) < w(i); realizability collapses to the complete
(heap) shape. Hence a(n) = A246747(n) for all n, proving the equality
conjectured there, and the bijection between the two counted sets is the
identity map on words. See the Bona link for the proof and a machine
verification in Lean 4. - SIGNATURE
```

**FORMULA** (add):

```
a(n) = A246747(n) (proved; see Comments). - SIGNATURE
a(n) = Sum_{i=0..floor((n-1)/2)} A000108(i)*a(n-i-1) for n > 1, via the
recurrence of A246747. - SIGNATURE
a(2k-1) = A245902(k) (proved; the complete shape on an odd number of nodes
is a full binary tree). - SIGNATURE
```

**LINKS** (add):

```
SIGNATURE, <a href="/A245899/b245899.txt">Table of n, a(n) for n = 1..1000</a>
Victor Bona, <a href="https://github.com/vicotrbb/bfs-avoidance-frontier">Rigidity of pattern-avoiding breadth-first reading words of increasing trees</a>, proofs, code, and Lean 4 formalization, 2026.
```

**CROSSREFS** (replace the conjecture note):

* Change `A245902 appears to be the odd-indexed terms of this sequence.`
  to `A245902 gives the odd-indexed terms of this sequence (proved).`
* Add: `Equals A246747 (proved).`

**KEYWORD**: remove `more` (the recurrence and b-file now determine the
sequence to any length).

**EXTENSIONS** (add):

```
a(9)-a(14) and b-file via the proven recurrence, SIGNATURE
```

---

## A245902 (312 on increasing full binary trees, length 2k-1)

**DATA** (extend to):

```
1, 2, 7, 37, 222, 1601, 12416, 105769
```

**COMMENTS** (add):

```
a(k) = A245899(2k-1) = A246747(2k-1) (proved): for 312-avoiding words of
odd length, realizability on increasing unary-binary trees, on increasing
full binary trees, and on the complete heap shape all coincide. See the
Bona link. - SIGNATURE
```

**FORMULA** (add):

```
a(k) = A246747(2k-1) (proved). - SIGNATURE
```

**LINKS** (add):

```
SIGNATURE, <a href="/A245902/b245902.txt">Table of k, a(k) for k = 1..500</a>
Victor Bona, <a href="https://github.com/vicotrbb/bfs-avoidance-frontier">Rigidity of pattern-avoiding breadth-first reading words of increasing trees</a>, proofs, code, and Lean 4 formalization, 2026.
```

**KEYWORD**: remove `more`.

**EXTENSIONS**: `a(6)-a(8) computed directly, remaining b-file terms via the
proven identity with A246747, SIGNATURE`

---

## A246747 (binary heaps whose reading word avoids 231, equivalently 312)

**COMMENTS** (add):

```
The equality with A245899 is proved: a 312-avoiding permutation is the
breadth-first reading word of an increasing unary-binary tree if and only
if it is a binary heap reading word, so the two counted sets of words are
identical. See the Bona link. - SIGNATURE
```

**CROSSREFS**: change `May be equal to A245899.` to
`Equals A245899 (proved).`

**LINKS** (add):

```
Victor Bona, <a href="https://github.com/vicotrbb/bfs-avoidance-frontier">Rigidity of pattern-avoiding breadth-first reading words of increasing trees</a>, proofs, code, and Lean 4 formalization, 2026.
```

---

## A245898 (231 on increasing unary-binary trees)

**DATA** (extend to):

```
1, 1, 2, 4, 10, 26, 74, 217, 667, 2098, 6788, 22349, 74969, 254848, 877865
```

**COMMENTS** (add):

```
a(2k-1) = A245901(k) (proved): every 231-avoiding reading word of odd
length realizable on an increasing unary-binary tree is realizable on an
increasing full binary tree. The analogous statement for the pattern 321
is false (see A245900, A245903). See the Bona link. - SIGNATURE
```

**LINKS** (add):

```
SIGNATURE, <a href="/A245898/b245898.txt">Table of n, a(n) for n = 1..15</a>
Victor Bona, <a href="https://github.com/vicotrbb/bfs-avoidance-frontier">Rigidity of pattern-avoiding breadth-first reading words of increasing trees</a>, proofs, code, and Lean 4 formalization, 2026.
```

**KEYWORD**: keep `more`.

**EXTENSIONS**: `a(9)-a(14) computed, a(15) via the proven identity with
A245901, SIGNATURE`

---

## A245901 (231 on increasing full binary trees, length 2k-1)

**DATA** (extend to):

```
1, 2, 10, 74, 667, 6788, 74969, 877865
```

**COMMENTS** (add):

```
a(k) = A245898(2k-1) (proved). See the Bona link. - SIGNATURE
```

**LINKS** (add):

```
SIGNATURE, <a href="/A245901/b245901.txt">Table of k, a(k) for k = 1..8</a>
Victor Bona, <a href="https://github.com/vicotrbb/bfs-avoidance-frontier">Rigidity of pattern-avoiding breadth-first reading words of increasing trees</a>, proofs, code, and Lean 4 formalization, 2026.
```

**KEYWORD**: keep `more`.

**EXTENSIONS**: `a(6)-a(8), SIGNATURE`

---

## A245900 (321 on increasing unary-binary trees)

**DATA** (extend to):

```
1, 1, 2, 4, 10, 27, 79, 239, 753, 2439, 8095, 27350, 93885, 326396
```

**COMMENTS** (add):

```
Unlike the patterns 231 and 312, the odd-indexed terms do not equal
A245903: a(11) = 8095 while A245903(6) = 8048. The 47 permutations of
length 11 realizable on an increasing unary-binary tree but on no
increasing full binary tree are listed at the Bona link; the
lexicographically least is 1,4,2,5,3,7,8,9,10,6,11. - SIGNATURE
```

**LINKS** (add):

```
SIGNATURE, <a href="/A245900/b245900.txt">Table of n, a(n) for n = 1..14</a>
Victor Bona, <a href="https://github.com/vicotrbb/bfs-avoidance-frontier">Rigidity of pattern-avoiding breadth-first reading words of increasing trees</a>, proofs, code, and Lean 4 formalization, 2026.
```

**KEYWORD**: keep `more`.

**EXTENSIONS**: `a(9)-a(14), SIGNATURE`

---

## A245903 (321 on increasing full binary trees, length 2k-1)

**DATA** (extend to):

```
1, 2, 10, 79, 753, 8048, 92716, 1125054
```

**COMMENTS** (add):

```
a(6) = 8048 differs from A245900(11) = 8095: for the pattern 321,
odd-length words realizable on increasing unary-binary trees are not all
realizable on increasing full binary trees, in contrast with the proven
identities for 231 (A245901 = odd-indexed A245898) and 312 (A245902 =
odd-indexed A245899). See the Bona link. - SIGNATURE
```

**LINKS** (add):

```
SIGNATURE, <a href="/A245903/b245903.txt">Table of k, a(k) for k = 1..8</a>
Victor Bona, <a href="https://github.com/vicotrbb/bfs-avoidance-frontier">Rigidity of pattern-avoiding breadth-first reading words of increasing trees</a>, proofs, code, and Lean 4 formalization, 2026.
```

**KEYWORD**: keep `more`.

**EXTENSIONS**: `a(6)-a(8), SIGNATURE`

---

## Provenance notes for editors (if asked)

* Terms up to length 11 were computed by two independent programs (direct
  tree enumeration and a pruned word search) that agree with all previously
  published terms; deeper terms by the second program. Code in the
  repository reproduces everything with `make verify-python` and
  `make recompute`.
* The identities cited as "proved" are Theorems A and B of the linked
  paper, additionally machine-checked in Lean 4 (no sorry, standard axioms;
  `make verify-lean`).
* The long b-files for A245899 and A245902 follow from the proven equality
  with A246747, whose recurrence-generated values match all directly
  computed terms.
