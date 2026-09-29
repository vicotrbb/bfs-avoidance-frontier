# Structural results

The canonical mathematical exposition is `paper/main.tex`. All words here are permutations of `[n]`, with `n >= 1`; tree children are ordered, and labels increase along edges.

## Parent-sequence representation

Number vertices in BFS order. For each nonroot position i, its parent position p(i) satisfies p(i)<i. Parent positions are nondecreasing. An outdegree bound k is exactly a bound of k on each parent's multiplicity. Conversely, these constraints reconstruct an ordered rooted tree with the specified BFS order. A compatible labeling satisfies w[p(i)]<w[i].

## Theorem A: heap collapse

For any k >= 2, a 312-avoiding permutation is realizable with maximum outdegree k if and only if

`w[ceil((i-1)/k)] < w[i]` for every nonroot position i (one-based).

Capacity gives `ceil((i-1)/k) <= p(i)`. If the corresponding heap inequality failed, the heap parent, actual parent, and child would form a 312 occurrence. The converse uses the complete heap shape.

## Theorem B: full-degree collapse

For any k >= 2 and n congruent to 1 modulo k, every 231-avoiding word realizable with maximum outdegree k is realizable on a full k-ary tree.

Group nonroot positions into blocks of k. Assign each block to the original parent of its first position. Selected parents strictly increase, since equality at positions k apart would give k+1 children to one old parent. Every new label inequality follows from 231 avoidance. The new parent sequence is full, compatible, and reconstructs the same word. Conversion from a given realization takes O(n) time.

## Binary identities

For n,r >= 1:

- A245899(n) = A246747(n).
- A245902(r) = A245899(2r-1).
- A245901(r) = A245898(2r-1).

The first identity transfers the established heap recurrence, with auxiliary a(0)=1:

`a(n) = sum(Catalan(i) * a(n-i-1), i=0..floor((n-1)/2))`.

## Sharpness and growth

The 321 heap analogue fails first at length 4, witnessed by 1423. The full binary analogue first fails at odd length 11, where the counts are 8095 and 8048. The complete 47-word difference is in `data/certificates/`.

Defant's Theorem 2.1 applies to each of 231, 312, and 321. Heap-word inclusion and the Catalan upper bound give nth-root growth 4 per vertex for bounded-degree words and for full words at admissible sizes. Consecutive-ratio convergence and subexponential asymptotics are separate questions.

## Formal scope

`theoremA_trees` and `theoremB_trees` establish the binary statements on inductive trees. `parent_theoremA_iff` and `parent_theoremB` establish the general statements over parent sequences. See `GENERAL_K_FORMALIZATION.md` for the definitions and exact-child theorems. The arbitrary-k tree reconstruction appears in the paper's Proposition 2.2; its binary counterpart is additionally formalized in `Trees.lean`.

The original binary promotion lemma remains formalized as `chain_plus`. Its general-degree mathematical proof appears in the paper's appendix. The main structural proofs now use parent sequences directly.
