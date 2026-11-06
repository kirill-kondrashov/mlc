.PHONY: all clean

CHAPTERS := $(wildcard chapters/*.tex)

all: programme.pdf first_days.pdf

programme.pdf: programme.tex $(CHAPTERS) .build/xelatex-ru.fmt
	mkdir -p .build
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build programme.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build programme.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build programme.tex
	cp .build/programme.pdf programme.pdf

.build/xelatex-ru.fmt: tex/language.dat
	mkdir -p .build
	TEXINPUTS=tex//: xelatex -ini -etex -interaction=batchmode -halt-on-error -jobname=xelatex-ru -output-directory=.build '\input xelatex.ini'

.build/B1_first_days.tex: research/B1_first_days.md tex/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=tex/short_tables.lua $< -o $@

first_days.pdf: first_days.tex .build/B1_first_days.tex .build/xelatex-ru.fmt
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build first_days.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build first_days.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build first_days.tex
	cp .build/first_days.pdf first_days.pdf

clean:
	latexmk -c -outdir=.build programme.tex
	latexmk -c -outdir=.build first_days.tex
