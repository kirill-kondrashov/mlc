.PHONY: all build check cache clean graphs notebook notebook-env serve

NOTEBOOK_HOST ?= 127.0.0.1
NOTEBOOK_PORT ?= 8888
NOTEBOOK_DIR ?= $(CURDIR)/notebooks
NOTEBOOK_PROJECT_DIR ?= $(CURDIR)/notebooks

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

# Build static dependency-graph pages under site/
graphs:
	cd scripts && poetry run python generate_dependency_graph_site.py --output site

# Serve the generated graph site locally over HTTP
serve: graphs
	cd scripts && poetry run python serve_graph_site.py --directory ../site --port 8000

# Sync the local uv environment used for notebooks
notebook-env:
	@command -v uv >/dev/null 2>&1 || { echo "uv not found; install uv locally and retry."; exit 1; }
	uv sync --project "$(NOTEBOOK_PROJECT_DIR)" --locked

# Run a local read-only JupyterLab server for viewing repository notebooks
notebook: notebook-env
	uv run --project "$(NOTEBOOK_PROJECT_DIR)" --no-sync python "$(NOTEBOOK_PROJECT_DIR)/readonly_jupyter.py" --ip $(NOTEBOOK_HOST) --port $(NOTEBOOK_PORT) --no-browser --ServerApp.root_dir="$(NOTEBOOK_DIR)"

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
