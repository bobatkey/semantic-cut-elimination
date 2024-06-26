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
SOURCES_LAGDA := $(wildcard sections/*.lagda.tex)
SOURCES := .latexmkrc agda.sty $(MAIN).tex $(MAIN).bib $(wildcard sections/*.tex) $(wildcard appendix/*.tex)

.PHONY: build
build: $(MAIN).pdf

.PHONY: watch
watch: $(SOURCES)
	$(LATEXMK) -pdf -pvc -interaction=nonstopmode $(MAIN)

$(MAIN).pdf: $(SOURCES)
	$(LATEXMK) -pdf -interaction=nonstopmode -e '$$max_repeat=10' $(MAIN).tex

agda.sty: $(AGDA_DIR)/latex/agda.sty
	@cp $(AGDA_DIR)/latex/agda.sty agda.sty

.latexmkrc: .latexmkrc.sample
	@cp .latexmkrc.sample .latexmkrc
	@echo "Created .latexmkrc from .latexmkrc.sample."
	@echo "Please review the file and modify it as needed."

###########
## ArXiv ##
###########

SUPPORTFILES=entics.bst entics.cls enticsmacro.sty virginialake.sty

arxiv.tar.gz: $(MAIN).pdf $(SUPPORTFILES)
	tar czf $@ $(SOURCES) $(MAIN).bbl $(SUPPORTFILES)

###########
## Clean ##
###########

GEN_LAGDA_TEX := $(wildcard $(patsubst %.lagda.tex,%.tex,$(SOURCES_LAGDA)))
GEN_MAIN_PTB := $(wildcard $(MAIN).ptb)
GEN_AGDA_STY := $(wildcard agda.sty sections/agda.sty)
GEN_AGDA_BUILD := $(wildcard _build)

.PHONY: clean
clean:
	rm -f arxiv.tar.gz
	$(LATEXMK) -C $(MAIN).tex
ifneq (,$(GEN_LAGDA_TEX))
	rm -f $(addprefix ./,$(GEN_LAGDA_TEX))
endif
ifneq (,$(GEN_MAIN_PTB))
	rm -f $(addprefix ./,$(GEN_MAIN_PTB))
endif
ifneq (,$(GEN_AGDA_STY))
	rm -f $(addprefix ./,$(GEN_AGDA_STY))
endif
ifneq (,$(GEN_AGDA_BUILD))
	rm -rf $(addprefix ./,$(GEN_AGDA_BUILD))
endif

###########
## Shell ##
###########

ROOT := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

.PHONY: docker-nix-shell
docker-nix-shell: shell.nix
	docker run -v "$(ROOT):/doc" -w "/doc" --rm -ti nixos/nix nix-shell

.PHONY: docker-nix-build
docker-nix-build: shell.nix
	docker run -v "$(ROOT):/doc" -w "/doc" --rm -ti nixos/nix nix-shell --run "make build"

.PHONY: docker-nix-watch
docker-nix-watch: shell.nix
	docker run -v "$(ROOT):/doc" -w "/doc" --rm -ti nixos/nix nix-shell --run "make watch"
