# The paper's own builds are latexmk and convert.sh (see README.md); these targets build the sketches.
PAPER := schwartz-space-n-fold-cover-sl2

.PHONY: all paper sketched figures html check-html audit-html clean
PYTHON ?= python3
all: paper
paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build $(PAPER).tex
	mkdir -p output/pdf
	cp build/$(PAPER).pdf output/pdf/$(PAPER).pdf
sketched:
	TEXINPUTS=".:$$HOME/work/sketches:$$TEXINPUTS:" BIBINPUTS=".:$$BIBINPUTS:" latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/sketched sketched.tex
	mkdir -p output/pdf
	cp build/sketched/sketched.pdf output/pdf/sketched.pdf
html:
	$(PYTHON) portable/build.py
check-html: html
	PYTHON=$(PYTHON) node portable/check/check.mjs
audit-html:
	$(PYTHON) portable/audit.py status
figures:
	$(PYTHON) portable/figures/make_figures.py
clean:
	latexmk -C -outdir=build $(PAPER).tex
	latexmk -C -outdir=build/sketched sketched.tex
