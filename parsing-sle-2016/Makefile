include commondefs

SHELL = /bin/sh

TARGET = main.pdf
TARGETS = $(TARGET)

E = extract.py

TEXS = paper.tex 
STY = balance.sty bcprules.sty code.sty defs.sty ifpdf.sty times-lite.sty txtt.sty utils.sty x10.sty sizes.sty

#
# Add any included TeX files to TEXS

VPATH = $(TEXDIR)

FIGS = 

# Override the .eps.pdf rule to do nothing
# %.pdf : %.eps

# This makes lousy PostScript
# .pdf.eps:
	# pdf2ps $< $@

#
# List of postscript figures to be included

default: $(TARGETS)

$(TARGET): paper.pdf
	-rm -f tmp.pdf
	-cp paper.pdf tmp.pdf
	-mv tmp.pdf $(TARGET)

BIBFILE = bib.bib
#
# Ignore this if you're not using bibtex. Change the $(DOC) part if your bib
# file has a different name from your document

paper.dvi: $(TEXS) $(STY) paper.stamp $(FIGS) paper.bbl $(BIBFILE) Makefile
paper.pdf: $(TEXS) $(STY) paper.stamp $(FIGS:.eps=.pdf) paper.bbl $(BIBFILE) Makefile

# To use makeindex, add this to dependency list:
# $(DOC).ind
#
# To use glossaries, add this to dependency list:
# $(DOC).glo
paper.bbl: paper.stamp $(BIBFILE)
paper.glo paper.ind: paper.stamp
paper.ps: paper.dvi $(FIGS)
#
# These are standard dependencies. Shouldn't need to modify these.

include commonrules

#SEP=\;  # windows miktex -- annoying
SEP=:
# unix including linux, cygwin

LATEX = TEXINPUTS=$(TEXDIR)${SEP} latex
PDFLATEX = TEXINPUTS=$(TEXDIR)${SEP} pdflatex

DIRT += $(TARGET) paper.pdf

#P = /opt/local/bin/python2.6
#P = arch -i386 /usr/bin/python
P = VERSIONER_PYTHON_PREFER_32_BIT=yes /usr/bin/python

N=16
split: $(TARGET)
	$(P) $(E) --input $(TARGET) --output summary.pdf --slice '[0]'
	$(P) $(E) --input $(TARGET) --output description.pdf --slice '[2:17]'
	$(P) $(E) --input $(TARGET) --output refs.pdf --slice '[17:25]'
	$(P) $(E) --input $(TARGET) --output bio.pdf --slice '[25:27]'
	$(P) $(E) --input $(TARGET) --output budget.pdf --slice '[27]'
	$(P) $(E) --input $(TARGET) --output equip.pdf --slice '[28]'
