CHARON_HOME	?= $(dir $(abspath $(lastword $(MAKEFILE_LIST))))/../charon
AENEAS_HOME	?= $(dir $(abspath $(lastword $(MAKEFILE_LIST))))/../aeneas
EURYDICE_HOME	?= $(dir $(abspath $(lastword $(MAKEFILE_LIST))))/../eurydice

CHARON_EXE = $(CHARON_HOME)/bin/charon --remove-associated-types '*'
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

extract: Symcrust/Symcrust.lean

Symcrust/Symcrust.lean: symcrust.llbc
	$(AENEAS_EXE) -backend lean symcrust.llbc $(AENEAS_OPTIONS) -dest Symcrust

# Alternatively, this could be marked as a phony target, since cargo (and hence
# charon) can skip recompilations if the sources have not changed.
symcrust.llbc: $(wildcard */*.rs)
	RUSTFLAGS="--cfg eurydice" $(CHARON_EXE) --hide-marker-traits --exclude=core::fmt::Debug::fmt --opaque=core::fmt::Formatter

# 3. Transpiling to C via eurydice
# --------------------------------

transpile: c/symcrust.c

c/symcrust.c: symcrust.llbc
	mkdir -p $(dir $@)
	$(EURYDICE_HOME)/eurydice $< --output $(dir $@) -fcomments

# Misc
# ----

clean:
	rm -rf *.llbc
