MAIN ?= index

.PHONY: build
build: $(MAIN).pdf

.PHONY: clean
clean:
	latexmk -C $(MAIN).tex

.PHONY: watch
watch: $(MAIN).tex
	latexmk -pdf -pvc -interaction=nonstopmode $(MAIN).tex

$(MAIN).pdf: $(MAIN).tex
	latexmk -pdf -interaction=nonstopmode $(MAIN).tex
