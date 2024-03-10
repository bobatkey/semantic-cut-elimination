ROOT := $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
MAIN ?= paper
DEPS := $(MAIN).tex $(MAIN).bib $(wildcard sections/*.lagda)

AGDA ?= $(shell which agda)
ifeq (,$(AGDA))
$(error "Building the paper requires Agda ( https://agda.readthedocs.io/ ).")
endif

BIBTEX ?= $(shell which bibtex)
ifeq (,$(BIBTEX))
$(error "Building the paper requires bibtex. Please install a LaTeX distribution.")
endif

LATEXMK ?= $(shell which latexmk)
ifeq (,$(LATEXMK))
$(error "Building the paper requires latexmk. Please install a LaTeX distribution.")
endif

.PHONY: build
build: $(MAIN).pdf

.PHONY: clean
clean:
	$(LATEXMK) -C $(MAIN).tex

.PHONY: watch
watch: $(DEPS)
	$(LATEXMK) -pdf -pvc -interaction=nonstopmode -use-make $(MAIN)

$(MAIN).pdf: $(DEPS)
	$(LATEXMK) -pdf -interaction=nonstopmode -use-make $(MAIN)

sections_latex/%.tex: sections/%.lagda
	$(AGDA) --latex --latex-dir=sections_latex $<

agda.sty:
	cp $(shell $(AGDA) --print-agda-dir)/latex/agda.sty agda.sty

$(MAIN).bbl: $(DEPS)
	$(BIBTEX) $(MAIN)