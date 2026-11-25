# Build the paper's PDF into build/ and output/pdf/.  The site build (PDF and
# HTML of the paper and the exercises, and the landing page) is preview-site.sh.
PAPER := schwartz-space-n-fold-cover-sl2

.PHONY: all paper clean
all: paper
paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build $(PAPER).tex
	mkdir -p output/pdf
	cp build/$(PAPER).pdf output/pdf/$(PAPER).pdf
clean:
	latexmk -C -outdir=build $(PAPER).tex
