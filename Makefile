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
extract: symcrust-aeneas.llbc proofs/Symcrust/Code/Funs.lean proofs/Symcrust/Code/FunsExternal_Template.lean proofs/Symcrust/Code/Types.lean
	$(AENEAS_EXE) -backend lean symcrust-aeneas.llbc $(AENEAS_OPTIONS) -dest proofs -subdir /Symcrust/Code -split-files -namespace Symcrust

# Alternatively, this could be marked as a phony target, since cargo (and hence
# charon) can skip recompilations if the sources have not changed.
symcrust.llbc: $(wildcard */*.rs)
	RUSTFLAGS="--cfg eurydice" $(CHARON_EXE) --hide-marker-traits --exclude=core::fmt::Debug::fmt --opaque=core::fmt::Formatter

symcrust-aeneas.llbc: $(wildcard */*.rs)
	$(CHARON_EXE) --hide-marker-traits --exclude=core::fmt::Debug::fmt --opaque=core::fmt::Formatter --remove-associated-types='*' \
	  --dest-file='symcrust-aeneas.llbc' \
	  --exclude=symcrust::ffi::* --exclude=symcrust::hash::* --exclude=symcrust::mlkem::* \
	  --exclude=symcrust::ntt::InternalComputationTemporaries \
	  --include=symcrust::hash::HashState \
	  --include=symcrust::hash::KeccakState \
	  --include=crate::hash::shake128_extract --opaque=crate::hash::shake128_extract \
	  --exclude=symcrust::key::Key3 --exclude=symcrust::key::Key3::* \
	  --opaque=symcrust::common::random \
	  --opaque=symcrust::common::wipe_slice \
	  --exclude=core::intrinsics::discriminant_value --exclude=core::marker::DiscriminantKind \
	  --exclude=core::fmt::Arguments \
	  --exclude='symcrust::common::{core::fmt::Debug for symcrust::common::Error}::*' \
	  --exclude='symcrust::common::{core::fmt::Debug for symcrust::common::Error}' \
	  --exclude='core::fmt::Display' \
	  --exclude='core::fmt::Display::*' \
	  --exclude='symcrust::error::{core::fmt::Display for symcrust::common::Error}::*' \
	  --exclude='symcrust::error::{core::fmt::Display for symcrust::common::Error}' \
	  --exclude='core::error::Error' \
	  --exclude='core::error::Error::*' \
          --exclude='symcrust::error::{core::error::Error for symcrust::common::Error}' \
	  --exclude='symcrust::error::{core::error::Error for symcrust::common::Error}::*' \
	  --translate-all-methods \
          --include=core::clone::Clone::clone_from
# TODO: `DiscriminantKind` should be eliminated by Charon
# TODO: why does `core::fmt::Arguments` appear in the crate?
# TODO: having to include `Clone::clone_from` is annoying

# 3. Transpiling to C via eurydice
# --------------------------------

transpile: c/symcrust.c

c/symcrust.c: symcrust.llbc
	mkdir -p $(dir $@)
	$(EURYDICE_HOME)/eurydice $< --output $(dir $@) -fcomments

# Replaying the proofs
.PHONY: build-proofs
build-proofs:
	cd proofs && lake build

# Replaying the proofs and measuring the time.
# Note that we rebuild the proofs before measuring to make sure the dependencies
# are rebuilt (TODO: there is probably a better way).
.PHONY: timed-lean
timed-lean: build-proofs
	cd proofs && find Symcrust -type f -iname "*.lean" -exec printf "\n{}\n" \; -exec lake env time lean {} \;


# Misc
# ----

clean:
	rm -rf *.llbc
