all:
	./latex_compile.sh main.tex

old_all:
	latexmk -pdf -halt-on-error main.tex

display:
	atril main.pdf 2>/dev/null

clean:
	rm -f *.aux *.log *.out
	rm -f *.dvi *.ps *.pdf *.nav *.snm *.toc
	rm -f *.fdb_latexmk *.fls
