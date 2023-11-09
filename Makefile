main.pdf: main.tex
	pdflatex main.tex
	pdflatex main.tex

main.tex: main.ml
	ocaml main.ml > main.tex

clean:
	rm -rf *.aux *.dvi *.log *.nav *.out *.snm *.tex *.toc
