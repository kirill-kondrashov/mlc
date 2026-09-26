.PHONY: all build check cache clean graphs serve proof-pdf factorization-figure check-uniform

# Default target
all: check

# Get Mathlib cache. 
# This is useful when dependencies (lake-manifest.json) change.
cache:
	lake exe cache get

# Build the project
build:
	lake build

# Check axioms
# Depends on build implicitly via lake, but we can make it explicit if we want make to handle it.
# However, lake handles its own dependencies well.
check:
	lake env lean --run check_axioms.lean

check-uniform:
	lake build Mlc.UniformGeometricRoot Mlc.UniformGeometricVertexControl Mlc.TrappingRegionObstruction Mlc.FiniteTrappingRegions
	lake env lean --run check_uniform_program.lean

FACTOR_FIGURES := \
	docs/figures/factorization-global-levels.pdf \
	docs/figures/factorization-critical-orbit.pdf \
	docs/figures/factorization-source.pdf \
	docs/figures/factorization-target.pdf

proof-pdf: docs/uniform_geometric_mlc.pdf

docs/uniform_geometric_mlc.pdf: docs/uniform_geometric_mlc.tex $(FACTOR_FIGURES)
	xelatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=docs $<
	xelatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=docs $<
	xelatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=docs $<

$(FACTOR_FIGURES): factorization-figure

factorization-figure:
	cd scripts && poetry run python generate_factorization_figures.py --output-dir ../docs/figures

# Build static dependency-graph pages under site/
graphs: build
	cd scripts && poetry run python generate_dependency_graph_site.py --output site

# Serve the generated graph site locally over HTTP
serve: graphs
	cd scripts && poetry run python serve_graph_site.py --directory ../site --port 8000

# A target that ensures cache is fetched if lake-manifest.json is newer than a marker file
# This attempts to satisfy "getting cache on change of files"
.cache_marker: lake-manifest.json lean-toolchain
	lake exe cache get
	touch .cache_marker

# Use this target if you want automatic caching based on file changes
auto-build: .cache_marker
	lake build
	lake exe check_axioms

# Clean build artifacts
clean:
	rm -f docs/proof.aux docs/proof.log docs/proof.out docs/proof.toc .cache_marker
	rm -f docs/uniform_geometric_mlc.aux docs/uniform_geometric_mlc.log docs/uniform_geometric_mlc.out docs/uniform_geometric_mlc.toc docs/uniform_geometric_mlc.build.log
