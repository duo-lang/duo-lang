MODE = batchmode

LATEX = pdflatex -interaction=$(MODE) -synctex=1
BIB = bibtex

MAIN_DEPS = $(wildcard *.tex)

.PHONY: all view clean

all : spec.pdf

view:
	@xdg-open spec.pdf &

clean:
	@find . -name "*.aux" -type f -delete
	@find . -name "*.log" -type f -delete
	@find . -name "*.bbl" -type f -delete
	@find . -name "*.blg" -type f -delete
	@find . -name "*.bcf" -type f -delete
	@find . -name "*.run.xml" -type f -delete
	@find . -name "*.out" -type f -delete
	@find . -name "*.pdf" -type f -delete
	@find . -name "*.synctex.gz" -type f -delete
	@echo "Deleted .aux .log .out .synctex.gz .pdf files."

.PHONY : bib
bib : spec.tex bib.bib
	$(LATEX) spec ;true 
	$(BIB) spec
	$(LATEX) spec ;true
	$(LATEX) spec ;true

spec.pdf: $(MAIN_DEPS) spec.tex
	$(LATEX) spec.tex