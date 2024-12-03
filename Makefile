CHARON_HOME ?= ../charon
AENEAS_HOME ?= ../aeneas

CHARON_EXE = $(CHARON_HOME)/bin/charon
AENEAS_EXE = $(AENEAS_HOME)/bin/aeneas

.PHONY: extract
extract: symcrust.llbc
	$(AENEAS_EXE) -backend lean symcrust.llbc

symcrust.llbc:
	$(CHARON_EXE) --hide-marker-traits

clean:
	rm *.llbc
