CHARON_HOME	?= $(dir $(abspath $(lastword $(MAKEFILE_LIST))))/../charon
AENEAS_HOME	?= $(dir $(abspath $(lastword $(MAKEFILE_LIST))))/../aeneas
EURYDICE_HOME	?= $(dir $(abspath $(lastword $(MAKEFILE_LIST))))/../eurydice

CHARON_EXE = $(CHARON_HOME)/bin/charon
AENEAS_EXE = $(AENEAS_HOME)/bin/aeneas
EURYDICE_EXE = $(EURYDICE_HOME)/eurydice

AENEAS_OPTIONS ?=

all: extract transpile build

# 1. Building in Rust via cargo
# -----------------------------

.PHONY: build
build:
	cargo build

# 2. Extraction to Lean via aeneas
# --------------------------------

.PHONY: extract
extract: symcrust.llbc proofs/Symcrust/Funs.lean proofs/Symcrust/FunsExternal_Template.lean proofs/Symcrust/Types.lean
	$(AENEAS_EXE) -backend lean symcrust.llbc $(AENEAS_OPTIONS) -dest proofs -split-files -no-gen-lib-entry -namespace Symcrust

# Alternatively, this could be marked as a phony target, since cargo (and hence
# charon) can skip recompilations if the sources have not changed.
symcrust.llbc: $(wildcard */*.rs)
	$(CHARON_EXE) --hide-marker-traits --exclude=core::fmt::Debug::fmt --opaque=core::fmt::Formatter --remove-associated-types="*"

# 3. Transpiling to C via eurydice
# --------------------------------

transpile: c/symcrust.c

c/symcrust.c: symcrust.llbc
	mkdir -p $(dir $@)
	$(EURYDICE_HOME)/eurydice $< --output $(dir $@) -fcomments

# Replaying the proofs
.PHONY: timed-lean
timed-lean:
	cd proofs && find Symcrust -type f -iname "*.lean" -exec printf "\n{}\n" \; -exec lake env time lean {} \; >& timing.out


# Misc
# ----

clean:
	rm -rf *.llbc
