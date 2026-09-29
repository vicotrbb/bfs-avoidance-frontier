# Reproduction and publication checks
.PHONY: all verify-python verify-lean recompute paper verify-publication release clean

all: verify-python verify-lean

verify-python:
	PYTHONDONTWRITEBYTECODE=1 python3 python/verify_theorems.py
	PYTHONDONTWRITEBYTECODE=1 python3 python/verify_artifact.py
	PYTHONDONTWRITEBYTECODE=1 python3 python/verify_parent_dp.py

verify-lean:
	cd lean && lake build

recompute:
	PYTHONDONTWRITEBYTECODE=1 python3 python/verify_artifact.py --full

paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=paper paper/main.tex

verify-publication:
	python3 release/verify.py

release:
	python3 release/package.py

clean:
	rm -rf python/__pycache__ lean/.lake/build
	latexmk -c -outdir=paper paper/main.tex
