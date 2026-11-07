.PHONY: all clean

all: programme.pdf first_days.pdf novelty_audit.pdf b2_audit.pdf b3_candidate.pdf b3_audit.pdf b3_publication.pdf

programme.pdf: programme.tex publication_plan.tex .build/xelatex-ru.fmt
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

.build/B1_novelty_audit.tex: research/B1_novelty_audit.md tex/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=tex/short_tables.lua $< -o $@

novelty_audit.pdf: novelty_audit.tex .build/B1_novelty_audit.tex .build/xelatex-ru.fmt
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build novelty_audit.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build novelty_audit.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build novelty_audit.tex
	cp .build/novelty_audit.pdf novelty_audit.pdf

.build/B2_novelty_audit.tex: research/B2_novelty_audit.md tex/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=tex/short_tables.lua $< -o $@

b2_audit.pdf: b2_audit.tex .build/B2_novelty_audit.tex .build/xelatex-ru.fmt
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b2_audit.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b2_audit.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b2_audit.tex
	cp .build/b2_audit.pdf b2_audit.pdf

.build/B3_candidate.tex: research/B3_candidate.md tex/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=tex/short_tables.lua $< -o $@

b3_candidate.pdf: b3_candidate.tex .build/B3_candidate.tex .build/xelatex-ru.fmt
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b3_candidate.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b3_candidate.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b3_candidate.tex
	cp .build/b3_candidate.pdf b3_candidate.pdf

.build/B3_novelty_audit.tex: research/B3_novelty_audit.md tex/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=tex/short_tables.lua $< -o $@

b3_audit.pdf: b3_audit.tex .build/B3_novelty_audit.tex .build/xelatex-ru.fmt
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b3_audit.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b3_audit.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b3_audit.tex
	cp .build/b3_audit.pdf b3_audit.pdf

.build/B3_publication_screening.tex: research/B3_publication_screening.md tex/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=tex/short_tables.lua $< -o $@

b3_publication.pdf: b3_publication.tex .build/B3_publication_screening.tex .build/xelatex-ru.fmt
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b3_publication.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b3_publication.tex
	xelatex -fmt=.build/xelatex-ru.fmt -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build b3_publication.tex
	cp .build/b3_publication.pdf b3_publication.pdf

clean:
	latexmk -c -outdir=.build programme.tex
	latexmk -c -outdir=.build first_days.tex
	latexmk -c -outdir=.build novelty_audit.tex
	latexmk -c -outdir=.build b2_audit.tex
	latexmk -c -outdir=.build b3_candidate.tex
	latexmk -c -outdir=.build b3_audit.tex
	latexmk -c -outdir=.build b3_publication.tex
