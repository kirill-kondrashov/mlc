TEX_SUPPORT := ../tex/research

.PHONY: all check clean

all: programme.pdf mlc_bridge.pdf

programme.pdf: publication_plan.tex

mlc_bridge.pdf: .build/MLC_bridge.tex

.build/MLC_bridge.tex: research/MLC_bridge.md $(TEX_SUPPORT)/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=$(TEX_SUPPORT)/short_tables.lua $< -o $@

first_days.pdf: .build/B1_first_days.tex

.build/B1_first_days.tex: research/B1_first_days.md $(TEX_SUPPORT)/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=$(TEX_SUPPORT)/short_tables.lua $< -o $@

novelty_audit.pdf: .build/B1_novelty_audit.tex

.build/B1_novelty_audit.tex: research/B1_novelty_audit.md $(TEX_SUPPORT)/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=$(TEX_SUPPORT)/short_tables.lua $< -o $@

b2_audit.pdf: .build/B2_novelty_audit.tex

.build/B2_novelty_audit.tex: research/B2_novelty_audit.md $(TEX_SUPPORT)/short_tables.lua
	mkdir -p .build
	pandoc --from=markdown+tex_math_dollars --to=latex --no-highlight --lua-filter=$(TEX_SUPPORT)/short_tables.lua $< -o $@

programme.pdf mlc_bridge.pdf first_days.pdf novelty_audit.pdf b2_audit.pdf: %.pdf: %.tex
	mkdir -p .build
	xelatex -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build $*.tex
	xelatex -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build $*.tex
	xelatex -interaction=batchmode -halt-on-error -file-line-error -output-directory=.build $*.tex
	cp .build/$*.pdf $@


check:
	python3 research/mlc_bridge_calibration.py --check
	python3 research/b1_compute.py --check
	python3 research/b2_compute.py --check

clean:
	rm -rf .build
