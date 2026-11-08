TEX_SUPPORT := ../../tex/research

.PHONY: all check clean

all: b3_candidate.pdf b3_audit.pdf b3_publication.pdf

b3_candidate.pdf: .build/B3_candidate.tex

.build/B3_candidate.tex: research/B3_candidate.md $(TEX_SUPPORT)/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=$(TEX_SUPPORT)/short_tables.lua $< -o $@

b3_audit.pdf: .build/B3_novelty_audit.tex

.build/B3_novelty_audit.tex: research/B3_novelty_audit.md $(TEX_SUPPORT)/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=$(TEX_SUPPORT)/short_tables.lua $< -o $@

b3_publication.pdf: .build/B3_publication_screening.tex

.build/B3_publication_screening.tex: research/B3_publication_screening.md $(TEX_SUPPORT)/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=$(TEX_SUPPORT)/short_tables.lua $< -o $@

b3_candidate.pdf b3_audit.pdf b3_publication.pdf: %.pdf: %.tex
	mkdir -p .build
	xelatex -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build $*.tex
	xelatex -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build $*.tex
	xelatex -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build $*.tex
	cp .build/$*.pdf $@


check:
	python3 research/b3_compute.py --check
	python3 research/b3_audit_compute.py --check

clean:
	rm -rf .build
