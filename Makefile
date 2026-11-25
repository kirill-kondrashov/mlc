.PHONY: all build check check-progress install-hooks cache clean graphs serve report-pdf

all: check

cache:
	lake exe cache get

build:
	lake build

check: build
	lake env lean --run check_axioms.lean

check-progress:
	python3 scripts/check_progress.py

install-hooks:
	git config core.hooksPath .githooks

graphs: build
	python3 scripts/generate_dependency_graph_site.py --output site

serve: graphs
	python3 scripts/serve_graph_site.py --directory site --port 8000

report-pdf: graphs
	mkdir -p docs
	inkscape site/mlc_conjecture/progress.svg --export-filename=docs/mlc_progress_figure.pdf
	xelatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=docs docs/mlc_progress.tex
	xelatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=docs docs/mlc_progress.tex

.cache_marker: lake-manifest.json lean-toolchain
	lake exe cache get
	touch .cache_marker

clean:
	rm -f .cache_marker
	rm -f docs/mlc_progress.aux docs/mlc_progress.log docs/mlc_progress.out docs/mlc_progress.toc
	rm -f docs/mlc_progress.pdf docs/mlc_progress_figure.pdf
