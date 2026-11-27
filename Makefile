.PHONY: all build check check-progress test-scripts install-hooks cache clean graphs serve report-pdf seed

all: check

cache:
	lake exe cache get

build:
	lake build

check: build
	lake env lean --run check_axioms.lean

check-progress:
	python3 scripts/check_progress.py

test-scripts:
	python3 scripts/test_map_raster.py
	python3 scripts/test_progress_history.py

install-hooks:
	git config core.hooksPath .githooks

graphs: build
	python3 scripts/generate_dependency_graph_site.py --output site

serve: graphs
	python3 scripts/serve_graph_site.py --directory site --port 8000

report-pdf: graphs
	mkdir -p docs
	cp site/mlc_conjecture/progress_commits.tex docs/mlc_progress_commits.tex
	cp site/mlc_conjecture/progress_routes.tex docs/mlc_progress_routes.tex
	inkscape site/mlc_conjecture/progress_map.svg --export-filename=docs/mlc_progress_map.pdf
	xelatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=docs docs/mlc_progress.tex
	xelatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=docs docs/mlc_progress.tex

.cache_marker: lake-manifest.json lean-toolchain
	lake exe cache get
	touch .cache_marker

# Publish the local build outputs of the grid tiles as the seed of CI (docs/ci.md).
seed: build
	python3 scripts/ci_grid.py pack --with-defs --level 10 --out .ci/tiles-all.tar.zst
	python3 scripts/ci_grid.py seed-push --archive .ci/tiles-all.tar.zst

clean:
	rm -f .cache_marker
	rm -rf .ci
	rm -f docs/mlc_progress.aux docs/mlc_progress.log docs/mlc_progress.out docs/mlc_progress.toc
	rm -f docs/mlc_progress_map.pdf
	rm -f docs/mlc_progress_commits.tex docs/mlc_progress_routes.tex
