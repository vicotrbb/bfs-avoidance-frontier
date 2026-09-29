# OEIS contribution preparation

This package supplies data and a factual map of the seven affected entries. It does not contain ready-to-paste editorial comments. The contributor should check the current entries and pending edits, then write comments and editorial replies in their own words, following the [OEIS AI policy](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions).

The release paper is the proof reference. Cite the exact published version and its DOI when available. Link the corresponding source release for Lean proofs and computations. All indices below are sequence indices; full binary index r corresponds to word length 2r-1.

| Entry | Mathematical contribution | Retained b-file |
|---|---|---|
| A245899 | Equality with A246747 for positive n; Catalan recurrence with auxiliary a(0)=1; full binary odd-index identity | b245899.txt, n=1..1000 |
| A245902 | A245902(r)=A245899(2r-1)=A246747(2r-1) | b245902.txt, r=1..500 |
| A246747 | Proof reference for its recorded tentative equality with A245899 | Existing heap entry; no new b-file in this package |
| A245898 | Proof reference for A245898(2r-1)=A245901(r); new direct values n=9..14 and derived n=15 | b245898.txt, n=1..15 |
| A245901 | Same 231 identity; additional values at r=6,7,8 | b245901.txt, r=1..8 |
| A245900 | Additional values n=9..14; odd-index equality with A245903 fails at n=11 | b245900.txt, n=1..14 |
| A245903 | Additional values r=6,7,8; a(6)=8048 whereas A245900(11)=8095 | b245903.txt, r=1..8 |

## Mathematical distinctions

- The 312 identities are equalities of word sets, with identity on words as the bijection.
- A245898 already states its odd-index relationship affirmatively. Add the proof reference without mischaracterizing its existing wording.
- The 321 full binary obstruction begins at word length 11. Heap collapse is a different property and already fails at length 4.
- The first 47 full binary counterexamples are in `../data/certificates/certificate_321_n11.txt`.
- The growth rate per vertex is 4. For full binary sequence index r, the r-th root rate is 16.

## Data provenance

The 39 retained baseline entries and 12 direct extensions through length 11 agree between tree enumeration and prefix search. Larger direct terms use prefix search. A245898(15) follows from the proved 231 identity. The long 312 files follow from the established heap recurrence transported by Theorem A. The verification driver checks all six b-files, including offsets, and recomputes the complete retained direct table with `make recompute`.

There are 28 additional entries relative to the retained baseline. This number includes the derived A245898(15); it does not describe 28 entirely new integers, since the 312 values occur in A246747.

## Submission procedure

Use the existing entry's edit workflow, review pending drafts before changing it, and upload a replacement b-file only after checking the current file. Follow editor guidance for coordinated changes and keyword updates. Account or draft observations do not establish that edits were submitted or accepted.
