# Prior work and attribution

Updated September 29, 2026. This is a source-based account of the relationship between the results, not a claim that all potentially relevant literature has been enumerated.

## Primary sources

1. [Levin, Pudwell, Riehl, Sandberg, Pattern avoidance in k-ary heaps (2016)](https://ajc.maths.uq.edu.au/pdf/64/ajc_v64_p120.pdf). Studies fixed complete heap shapes. Theorems 5 and 6 provide the relevant Catalan recurrence and the connection between 231- and 312-avoiding binary heaps. The present work identifies the union-over-shapes 312 word set with the complete-shape word set.
2. [Defant, Proofs of conjectures about pattern-avoiding linear extensions (2019)](https://dmtcs.episciences.org/articles/5796). Theorem 2.1 applies to every set of sum-indecomposable forbidden patterns, not only 321. Together with inclusions between heap words, arbitrary-shape words, and unrestricted avoiders, it implies exponential growth 4 for the three patterns treated here. Consecutive-ratio convergence is a different question.
3. [Bettinelli, Fusy, Mailler, Randazzo, A bijective study of basketball walks](https://arxiv.org/abs/1611.01478). Studies 213-avoiding increasing unary-binary trees and basketball-walk bijections. Its fixed-shape labeling criterion is related to realizability, but its counted objects and pattern differ from the present word-set equalities.
4. [OEIS A246747](https://oeis.org/A246747). Counts 231-avoiding heaps and also 312-avoiding heaps; records the tentative equality with A245899 and the established recurrence. Its offset includes n=0, whereas A245899 begins at n=1.
5. [OEIS A245899](https://oeis.org/A245899). Counts distinct 312-avoiding unary-binary words and records a tentative odd-index relationship with A245902.
6. [OEIS A245898](https://oeis.org/A245898). States the odd-index relationship with A245901 affirmatively. That entry does not supply a proof, but its wording should not be described as an explicit conjecture without historical evidence.
7. [OEIS A245900](https://oeis.org/A245900). Lists 1423 among the size-4 words. This is already a counterexample to 321 heap collapse. The length-11 computation concerns the different full binary collapse.

## Contribution

The paper gives direct proofs of two word-set equalities for arbitrary branching bounds using BFS parent sequences. The binary consequences establish the three stated sequence identities. The additional data extends the six word-count sequences relative to their retained baseline; many 312 values were already available in A246747 and become transferable through the proved identity.

Targeted searches for the sequence identifiers and the relevant reading-word terminology did not identify an earlier proof of these exact arbitrary-shape equalities. This supports a qualified novelty assessment. OEIS's `more` keyword requests terms and does not certify that a mathematical statement is open. Search result counts do not establish literature completeness.

Some OEIS pages were retrieved through cached search records. Source wording is reported as observed; no claim of a comprehensive historical audit is made. The paper cites the primary results that it uses and does not treat formal verification as evidence of novelty.
