.PHONY: all build check cache clean graphs serve

all: check

cache:
	lake exe cache get

build:
	lake build

check: build
	lake env lean --run check_axioms.lean

graphs: build
	python3 scripts/generate_dependency_graph_site.py --output site

serve: graphs
	python3 scripts/serve_graph_site.py --directory site --port 8000

.cache_marker: lake-manifest.json lean-toolchain
	lake exe cache get
	touch .cache_marker

clean:
	rm -f .cache_marker
