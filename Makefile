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
	RUSTFLAGS="--cfg eurydice" $(CHARON_EXE) cargo --hide-marker-traits \
	  --exclude=core::fmt::Debug::fmt --opaque=core::fmt::Formatter --preset=eurydice \
	  --include=alloc::collections::*  --include=core::alloc::* --include=core::ptr::*

.PHONY: symcrust-aeneas.llbc
symcrust-aeneas.llbc: $(wildcard */*.rs)
	RUSTFLAGS="--cfg eurydice" \
	$(CHARON_EXE) cargo --preset=aeneas --exclude=core::fmt::Debug::fmt --opaque=core::fmt::Formatter --remove-associated-types='*' \
	  --dest-file='symcrust-aeneas.llbc' \
	  --exclude=symcrust::ffi::* --exclude=symcrust::hash::* \
	  --include=symcrust::hash::HashState \
	  --include=symcrust::hash::KeccakState \
	  --include=crate::hash::UNINITIALIZED_HASH_STATE \
	  --include=crate::hash::shake128_state_copy --opaque=crate::hash::shake128_state_copy \
	  --include=crate::hash::shake128_init --opaque=crate::hash::shake128_init \
	  --include=crate::hash::shake128_extract --opaque=crate::hash::shake128_extract \
	  --include=crate::hash::shake128_append --opaque=crate::hash::shake128_append \
	  --include=crate::hash::shake256_state_copy --opaque=crate::hash::shake256_state_copy \
	  --include=crate::hash::shake256_init --opaque=crate::hash::shake256_init \
	  --include=crate::hash::shake256_extract --opaque=crate::hash::shake256_extract \
	  --include=crate::hash::shake256_append --opaque=crate::hash::shake256_append \
	  --include=crate::hash::sha3_256_init --opaque=crate::hash::sha3_256_init \
	  --include=crate::hash::sha3_256_append --opaque=crate::hash::sha3_256_append \
	  --include=crate::hash::sha3_256_result --opaque=crate::hash::sha3_256_result \
	  --include=crate::hash::sha3_512 --opaque=crate::hash::sha3_512 \
	  --include=crate::hash::sha3_512_init --opaque=crate::hash::sha3_512_init \
	  --include=crate::hash::sha3_512_append --opaque=crate::hash::sha3_512_append \
	  --include=crate::hash::sha3_512_result --opaque=crate::hash::sha3_512_result \
	  --opaque=crate::mlkem::cbd_sample_buffer_try_into \
	  --opaque=crate::mlkem::pb_random_try_into \
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
	$(EURYDICE_HOME)/eurydice $< --output $(dir $@) -fcomments --config c.yaml

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
