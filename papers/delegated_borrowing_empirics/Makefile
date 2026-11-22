.PHONY: all main blinded clean

all: main blinded

main:
	pdflatex -interaction=nonstopmode main && bibtex main && pdflatex -interaction=nonstopmode main && pdflatex -interaction=nonstopmode main
	if grep -q "Rerun to get cross-references right" main.log; then pdflatex -interaction=nonstopmode main; fi

blinded:
	pdflatex -interaction=nonstopmode blinded && bibtex blinded && pdflatex -interaction=nonstopmode blinded && pdflatex -interaction=nonstopmode blinded
	if grep -q "Rerun to get cross-references right" blinded.log; then pdflatex -interaction=nonstopmode blinded; fi

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.fls *.fdb_latexmk *.synctex.gz *.toc
