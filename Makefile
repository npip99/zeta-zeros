.PHONY: install test verify verify-fast verify-main verify-legacy paper

install:
	python3 -m pip install --upgrade pip
	python3 -m pip install -e .

test:
	python3 -m unittest discover -s tests -v

verify: verify-fast verify-main

verify-fast:
	python3 -m zeta_ext.cli fast

verify-main:
	python3 -m zeta_ext.cli main --workers 8

verify-legacy:
	python3 -m zeta_simple_zeros seven

paper:
	tectonic --outdir paper paper/main.tex
