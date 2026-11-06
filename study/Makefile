.PHONY: all clean

CHAPTERS := $(wildcard chapters/*.tex)

all: programme.pdf

programme.pdf: programme.tex $(CHAPTERS) .build/xelatex-ru.fmt
	mkdir -p .build
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build programme.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build programme.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build programme.tex
	cp .build/programme.pdf programme.pdf

.build/xelatex-ru.fmt: tex/language.dat
	mkdir -p .build
	TEXINPUTS=tex//: xelatex -ini -etex -interaction=batchmode -halt-on-error -jobname=xelatex-ru -output-directory=.build '\input xelatex.ini'

clean:
	latexmk -c -outdir=.build programme.tex
