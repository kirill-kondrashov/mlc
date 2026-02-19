.PHONY: all build check cache clean serve auto-build

PORT ?= 8000
GRAPH_JSON := site/mlc_conjecture/graph.json
LEAN_SOURCES := $(shell find Mlc -type f -name '*.lean')
GRAPH_SOURCES := $(LEAN_SOURCES) check_axioms.lean scripts/generate_dependency_graph_site.py scripts/pyproject.toml scripts/poetry.lock

# Default target
all: check

# Get Mathlib cache. 
# This is useful when dependencies (lake-manifest.json) change.
cache:
	lake exe cache get

# Build the project
build:
	lake build
	$(MAKE) --no-print-directory graphs

# Check axioms
# Depends on build implicitly via lake, but we can make it explicit if we want make to handle it.
# However, lake handles its own dependencies well.
check:
	lake env lean --run check_axioms.lean

# Build static dependency-graph pages under site/
graphs: $(GRAPH_JSON)

$(GRAPH_JSON): $(GRAPH_SOURCES)
	cd scripts && poetry run python generate_dependency_graph_site.py --output site

# Serve the generated graph site locally over HTTP
serve: graphs
	cd scripts && poetry run python serve_graph_site.py --directory ../site --port $(PORT)

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
