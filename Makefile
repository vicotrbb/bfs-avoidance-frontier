# BFS-Avoidance Frontier — verification targets
.PHONY: all verify-python verify-lean audit clean

all: verify-python verify-lean

# Exhaustive Python verification of every lemma and theorem (~1 min)
verify-python:
	python3 python/verify_theorems.py

# Kernel-checked Lean proofs; the build succeeding IS the proof.
# Prints the axiom audit for all six named theorems.
verify-lean:
	cd lean && lake build

# Reproduce the frontier computations (new OEIS terms); see data/raw/
recompute:
	python3 python/reference.py ub 10
	python3 python/reference.py b 11
	for p in 231 312 321; do python3 python/solver.py ub $$p 12; done
	for p in 231 312 321; do python3 python/solver.py b $$p 13; done

clean:
	rm -rf python/__pycache__ lean/.lake/build
