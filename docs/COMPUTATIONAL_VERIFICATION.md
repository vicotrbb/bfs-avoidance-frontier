# Computational and formal verification

This file states what each check establishes. The current paper is the source of the unrestricted mathematical proofs.

## Counting objects

A word is a distinct permutation, not a labeled tree. Every parent has at most two children in unary-binary mode, and zero or two in full binary mode. Children are ordered and their labels exceed the parent's label. Full binary sequence index r corresponds to word length 2r-1.

## Implementations

- `python/reference.py` enumerates increasing trees level by level, deduplicates their words, and tests pattern avoidance by ranking triples.
- `python/solver.py` enumerates permutation prefixes. Its pruning uses incremental pattern containment and a nondeterministic matching state across candidate level boundaries.
- `python/parent_words.py` recognizes a supplied word by dynamic programming over BFS parent outdegrees. Queue nonemptiness, child capacity, and label inequalities are checked directly. Its pattern predicate uses inequalities rather than triple ranking. It also implements the arbitrary-k full-degree construction and validates the reconstructed BFS traversal.

The first two implementations check different realizability algorithms. Their agreement is corroboration, not a probability estimate for correctness. The third is used for certificates and bounded generalization tests rather than the largest enumeration totals.

## Coverage

| Check | Range |
|---|---|
| Tree enumeration versus prefix solver | All six classes through word length 11 |
| Historical baseline | 39 displayed entries: 3 times 8 unary-binary and 3 times 5 full binary |
| Direct extensions checked by both enumerators | 12 entries through length 11 |
| Full prefix-solver recomputation | Unary-binary lengths 1 through 14; full binary lengths 1,3,...,15 |
| Derived extension | A245898(15)=877865, from A245901(8) and Theorem B |
| Long recurrence b-files | A245899 indices 1 through 1000; A245902 indices 1 through 500 |
| Exact 321 difference certificate | All 47 words, compared against the reference set difference |
| Independent certificate recognition | Each retained word: unary-binary accepted, full binary rejected |
| First parity-failure check | Set equality at odd lengths 1 through 9; inequality at length 11 |
| Arbitrary-k theorems and construction | Every permutation of lengths 1 through 7, k=2,3,4 |
| Pattern-predicate cross-check | Every permutation of length 6, all three patterns |

The original `verify_theorems.py` checks the binary heap equality through length 11, the binary 231 equality at lengths 9 and 11, and the recurrence through length 10. It also reports 27,364 odd-extension, 18,677 even-regrouping, and 127,127 promotion instances. These auxiliary instances are drawn from unary-binary-realizable permutations at lengths 8 and 9. The promotion checks have no avoidance filter; they are not an enumeration of all words.

## Reproduce

```sh
make verify-python
make verify-lean
make recompute
make paper
make verify-publication
```

For a retained full-computation receipt:

```sh
python3 python/verify_artifact.py --full --output data/verification/20260929/artifact.json
```

`verify_artifact.py` exits nonzero on any mismatch and compares every b-file with its declared direct or recurrence source. It reads raw counts rather than silently replacing them. The full table run uses up to four worker processes. Execution dates, Python/platform versions, ranges, and elapsed times appear in the JSON receipt.

## Formal verification

The Lean build uses toolchain 4.24.0 without external dependencies. `Sanity.lean` prints axiom dependencies for the binary encoded and tree-level results, the semantic bridges, and the general parent-sequence results. No admitted proofs or additional axioms are used. General parent constraints and full child fibers are described in `GENERAL_K_FORMALIZATION.md`.

The formal theorems establish structural statements. They do not certify the Python programs, finite enumeration totals, historical annotations, or novelty. Those claims have separate evidence in the computation receipts and source notes.
