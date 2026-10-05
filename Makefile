# All paths are relative so this works from the project directory (its name has spaces and
# CJK characters). `make test` builds everything, checks the proofs and runs the harness.
BIN := .lake/build/bin/crashproof
RUNS ?= 500
JOBS ?= 4

.PHONY: build proofs test harness wren diff-wren mutants demo results clean

build:
	lake build

# No sorry, no extra axioms: the main theorems use only propext / Classical.choice / Quot.sound.
proofs:
	./scripts/check-proofs.sh

# Build, check proofs, then model-test the executable against the spec.
test: build proofs harness

harness: build
	python3 harness/crashtest.py --runs $(RUNS) --jobs $(JOBS)

# Build wren-os's log (its kernel/log.c, unmodified) on the host. Needs the wren-os repo as a
# sibling, or WREN=/path. Skips cleanly if it is absent.
wren:
	bash wren/build.sh

# Differential test: drive wren-os's real log through the same crash harness.
diff-wren: build wren
	python3 harness/crashtest.py --backend wren --runs $(RUNS) --jobs $(JOBS)

# Every one-line protocol bug must break a proof or be caught by the harness.
mutants: build
	python3 harness/mutants.py --runs $(RUNS)

demo: build
	$(BIN) demo

# Regenerate docs/results.html from fresh harness runs.
results: build
	mkdir -p out
	./scripts/check-proofs.sh > out/axioms.txt 2>&1 || true
	python3 harness/crashtest.py --runs 2000 --quiet --json out/crashproof.json
	-python3 harness/crashtest.py --backend wren --runs 2000 --quiet --json out/wren.json
	python3 harness/mutants.py --runs 1000 --json out/mutants.json
	python3 scripts/make_results.py

clean:
	rm -rf .lake/build build out
