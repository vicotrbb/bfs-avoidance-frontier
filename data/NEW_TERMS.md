# Additional entries for A245898 through A245903

Relative to the retained baseline (unary-binary n=1..8 and full binary lengths 1,3,...,9), this package contains 28 additional sequence entries. There are 27 direct enumerations plus A245898(15), obtained from the full binary count through the proved identity. This describes additional entries in these sequences; the 312 values are also obtainable from the previously known heap sequence A246747.

## Unary-binary words

| n | A245898 (231) | A245899 (312) | A245900 (321) |
|---|---:|---:|---:|
| 9 | 667 | 222 | 753 |
| 10 | 2098 | 544 | 2439 |
| 11 | 6788 | 1601 | 8095 |
| 12 | 22349 | 4095 | 27350 |
| 13 | 74969 | 12416 | 93885 |
| 14 | 254848 | 33785 | 326396 |
| 15 | 877865 (identity) | | |

## Full binary words

| Word length | Sequence index r | A245901 (231) | A245902 (312) | A245903 (321) |
|---|---:|---:|---:|---:|
| 11 | 6 | 6788 | 1601 | 8048 |
| 13 | 7 | 74969 | 12416 | 92716 |
| 15 | 8 | 877865 | 105769 | 1125054 |

All direct terms through word length 11 have been reproduced by both enumerators. The larger direct terms are recomputed by the prefix solver, and every 312 term is additionally checked against the Catalan recurrence. The b-files contain extended recurrence values for the two 312 sequences.

The proof identities, for positive indices, are:

- A245899(n)=A246747(n).
- A245902(r)=A245899(2r-1).
- A245901(r)=A245898(2r-1).

For 321, A245900(11)=8095 differs from A245903(6)=8048. The exact set of 47 missing full binary words is retained in `certificates/certificate_321_n11.txt` and checked by `python/verify_artifact.py`.
