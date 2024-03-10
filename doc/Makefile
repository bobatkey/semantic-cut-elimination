###########
## Setup ##
###########

MAIN ?= paper

AGDA ?= $(shell which agda)
ifeq (,$(AGDA))
$(error "Building the paper requires Agda ( https://agda.readthedocs.io/ ).")
endif

LATEXMK ?= $(shell which latexmk)
ifeq (,$(LATEXMK))
$(error "Building the paper requires latexmk. Please install a LaTeX distribution.")
endif

###########
## Build ##
###########

AGDA_DIR := $(shell $(AGDA) --print-agda-dir)
SOURCES_LAGDA := $(wildcard sections/*.lagda)
SOURCES := .latexmkrc agda.sty $(MAIN).tex $(MAIN).bib $(SOURCES_LAGDA)

.PHONY: build
build: $(MAIN).pdf

.PHONY: watch
watch: $(SOURCES)
	$(LATEXMK) -pdf -pvc -interaction=nonstopmode $(MAIN)

$(MAIN).pdf: $(SOURCES)
	$(LATEXMK) -pdf -interaction=nonstopmode $(MAIN).tex

agda.sty: $(AGDA_DIR)/latex/agda.sty
	cp $(AGDA_DIR)/latex/agda.sty agda.sty

.latexmkrc: .latexmkrc.sample
	cp .latexmkrc.sample .latexmkrc

###########
## Clean ##
###########

GEN_LAGDA_TEX := $(wildcard $(patsubst %.lagda,%.tex,$(SOURCES_LAGDA)))
GEN_MAIN_PTB := $(wildcard $(MAIN).ptb)
GEN_AGDA_STY := $(wildcard agda.sty sections/agda.sty)
GEN_AGDA_BUILD := $(wildcard _build)

.PHONY: clean
clean:
	$(LATEXMK) -C $(MAIN).tex
ifneq (,$(GEN_LAGDA_TEX))
	rm $(addprefix ./,$(GEN_LAGDA_TEX))
endif
ifneq (,$(GEN_MAIN_PTB))
	rm $(addprefix ./,$(GEN_MAIN_PTB))
endif
ifneq (,$(GEN_AGDA_STY))
	rm $(addprefix ./,$(GEN_AGDA_STY))
endif
ifneq (,$(GEN_AGDA_BUILD))
	rm -r $(addprefix ./,$(GEN_AGDA_BUILD))
endif