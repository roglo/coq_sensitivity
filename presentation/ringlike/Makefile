# $Id: Makefile,v 1.4 2012/01/16 14:42:50 deraugla Exp $

SRC=main
RM= rm -rf 
LATEXOPTS=-file-line-error -halt-on-error

all: pdf

pdf:	common.tex
	pdflatex $(LATEXOPTS) ${SRC}.tex 	 
	pdflatex $(LATEXOPTS) ${SRC}.tex 

ps:	common.tex
	latex  ${SRC}.tex 
	latex  ${SRC}.tex 
	dvips  ${SRC}.dvi 
	ps2pdf ${SRC}.ps


open:
	evince  ${SRC}.pdf

openpdf:
	pdfopen --file  ${SRC}.pdf

clean:
	$(RM) \
	*.aux *.haux *.log *.bbl *.blg *.toc \
	*.htoc *.nav *.out *.snm *~  \
	*.html *.png *.dvi *.odt  \
       _region_.tex 

cleanpdf: 
	$(RM) *.pdf *.ps *.dvi *.html

cleanall:
	make clean cleanpdf
