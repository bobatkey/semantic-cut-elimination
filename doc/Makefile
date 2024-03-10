AGDA ?= $(shell which agda)
ifeq (,$(AGDA))
$(error "Building the paper requires Agda ( https://agda.readthedocs.io/ ).")
endif
AGDA_DIR := $(shell $(AGDA) --print-agda-dir)

BIBTEX ?= $(shell which bibtex)
ifeq (,$(BIBTEX))
$(error "Building the paper requires bibtex. Please install a LaTeX distribution.")
endif

LATEXMK ?= $(shell which latexmk)
ifeq (,$(LATEXMK))
$(error "Building the paper requires latexmk. Please install a LaTeX distribution.")
endif

###########
## Build ##
###########

MAIN ?= paper
SOURCES_LAGDA := $(wildcard sections/*.lagda)
SOURCES := agda.sty $(MAIN).tex $(MAIN).bib $(SOURCES_LAGDA)

.PHONY: build
build: $(MAIN).pdf

.PHONY: watch
watch: $(SOURCES)
	$(LATEXMK) -pdf -pvc -interaction=nonstopmode $(MAIN)

$(MAIN).pdf: $(SOURCES)
	$(LATEXMK) -pdf -interaction=nonstopmode $(MAIN).tex

# sections_latex/%.tex: sections/%.lagda
# 	$(AGDA) --latex --latex-dir=sections_latex $<

agda.sty: $(AGDA_DIR)/latex/agda.sty
	cp $(AGDA_DIR)/latex/agda.sty agda.sty

###########
## Clean ##
###########

GEN_LAGDA_TEX := $(wildcard $(patsubst %.lagda,%.tex,$(SOURCES_LAGDA)))
GEN_AGDA_STY := $(wildcard agda.sty sections/agda.sty)

.PHONY: clean
clean:
	$(LATEXMK) -C $(MAIN).tex
ifneq (,$(GEN_LAGDA_TEX))
	rm $(GEN_LAGDA_TEX)
endif
ifneq (,$(GEN_AGDA_STY))
	rm $(GEN_AGDA_STY)
endif