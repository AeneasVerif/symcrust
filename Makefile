CHARON_HOME ?= ../charon
AENEAS_HOME ?= ../aeneas

CHARON_EXE = $(CHARON_HOME)/bin/charon
AENEAS_EXE = $(AENEAS_HOME)/bin/aeneas

AENEAS_OPTIONS ?=

.PHONY: extract
extract: symcrust.llbc
	$(AENEAS_EXE) -backend lean symcrust.llbc $(AENEAS_OPTIONS) -dest Symcrust

symcrust.llbc: src/ntt.rs src/misc.rs src/lib.rs
	$(CHARON_EXE) --hide-marker-traits --exclude=core::fmt::Debug::fmt --opaque=core::fmt::Formatter

ntt.rs:

clean:
	rm *.llbc
