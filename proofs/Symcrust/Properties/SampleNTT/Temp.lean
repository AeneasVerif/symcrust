import Symcrust.Spec
import Symcrust.Code.Funs
import Symcrust.Properties.Basic

#setup_aeneas_simps

namespace Symcrust.ntt

open Symcrust.Spec
open Aeneas Aeneas.Std Aeneas.SRRange Result
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

set_option maxHeartbeats 1000000

open CustomLoops in
def poly_element_sample_ntt_from_shake128_modified
  (p_state : hash.HashState) (pe_dst : Array U16 256#usize) :
  Result (hash.HashState × (Array U16 256#usize))
  :=
  do
  let shake_output_buf := Array.repeat 24#usize 0#u8
  let s ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
  let curr_buf_index := Slice.len s
  -- Before while loop, instantiate mutable variables corresponding to arguments that would
  -- have been created for the auxiliary recurisve function
  let mut p_state := p_state
  let mut pe_dst := pe_dst
  let mut i := 0#usize
  let mut shake_output_buf := shake_output_buf
  let mut curr_buf_index := curr_buf_index
  while i < key.MLWE_POLYNOMIAL_COEFFICIENTS do
    let s ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
    let i1 := Slice.len s
    massert (curr_buf_index <= i1)
    let s1 ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
    let i2 := Slice.len s1
    if curr_buf_index = i2
    then
      do
      let (s2, to_slice_mut_back) ←
        (↑(Array.to_slice_mut shake_output_buf) : Result ((Slice U8) ×
          (Slice U8 → Array U8 24#usize)))
      let (p_state1, s3) ← hash.shake128_extract p_state s2 false
      let shake_output_buf1 := to_slice_mut_back s3
      let s4 ← (↑(Array.to_slice shake_output_buf1) : Result (Slice U8))
      let a ← ntt.slice_to_sub_array2 s4 0#usize
      let i3 ← (↑(core.num.U16.from_le_bytes a) : Result U16)
      let sample0 ← (↑(i3 &&& 4095#u16) : Result U16)
      let s5 ← (↑(Array.to_slice shake_output_buf1) : Result (Slice U8))
      let i4 ← 0#usize + 1#usize
      let a1 ← ntt.slice_to_sub_array2 s5 i4
      let i5 ← (↑(core.num.U16.from_le_bytes a1) : Result U16)
      let sample1 ← i5 >>> 4#i32
      let curr_buf_index1 ← 0#usize + 3#usize
      let i6 ← (↑(UScalar.cast .U32 sample0) : Result U32)
      let i7 ←
        (↑(UScalar.cast_fromBool .Usize (i6 < ntt.Q)) : Result Usize)
      let i8 ← i + i7
      if i8 < key.MLWE_POLYNOMIAL_COEFFICIENTS
      then
        do
        let pe_dst1 ← Array.update pe_dst i sample0
        let pe_dst2 ← Array.update pe_dst1 i8 sample1
        let i9 ← (↑(UScalar.cast .U32 sample1) : Result U32)
        let i10 ←
          (↑(UScalar.cast_fromBool .Usize (i9 < ntt.Q)) : Result Usize)
        let i11 ← i8 + i10
        -- Wherever the auxiliary recursive function would have terminated, instead set the mutable variables
        -- with the values that would have been passed into the recursive call
        p_state := p_state1
        pe_dst := pe_dst2
        i := i11
        shake_output_buf := shake_output_buf1
        curr_buf_index := curr_buf_index1
      else
        do
        let pe_dst1 ← Array.update pe_dst i sample0
        -- Wherever the auxiliary recursive function would have terminated, instead set the mutable variables
        -- with the values that would have been passed into the recursive call
        p_state := p_state1
        pe_dst := pe_dst1
        i := i8
        shake_output_buf := shake_output_buf1
        curr_buf_index := curr_buf_index1
    else
      do
      let s2 ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
      let a ← ntt.slice_to_sub_array2 s2 curr_buf_index
      let i3 ← (↑(core.num.U16.from_le_bytes a) : Result U16)
      let sample0 ← (↑(i3 &&& 4095#u16) : Result U16)
      let s3 ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
      let i4 ← curr_buf_index + 1#usize
      let a1 ← ntt.slice_to_sub_array2 s3 i4
      let i5 ← (↑(core.num.U16.from_le_bytes a1) : Result U16)
      let sample1 ← i5 >>> 4#i32
      let curr_buf_index1 ← curr_buf_index + 3#usize
      let i6 ← (↑(UScalar.cast .U32 sample0) : Result U32)
      let i7 ←
        (↑(UScalar.cast_fromBool .Usize (i6 < ntt.Q)) : Result Usize)
      let i8 ← i + i7
      if i8 < key.MLWE_POLYNOMIAL_COEFFICIENTS
      then
        do
        let pe_dst1 ← Array.update pe_dst i sample0
        let pe_dst2 ← Array.update pe_dst1 i8 sample1
        let i9 ← (↑(UScalar.cast .U32 sample1) : Result U32)
        let i10 ←
          (↑(UScalar.cast_fromBool .Usize (i9 < ntt.Q)) : Result Usize)
        let i11 ← i8 + i10
        -- Wherever the auxiliary recursive function would have terminated, instead set the mutable variables
        -- with the values that would have been passed into the recursive call
        p_state := p_state
        pe_dst := pe_dst2
        i := i11
        shake_output_buf := shake_output_buf
        curr_buf_index := curr_buf_index1
      else
        do
        let pe_dst1 ← Array.update pe_dst i sample0
        -- Wherever the auxiliary recursive function would have terminated, instead set the mutable variables
        -- with the values that would have been passed into the recursive call
        p_state := p_state
        pe_dst := pe_dst1
        i := i8
        shake_output_buf := shake_output_buf
        curr_buf_index := curr_buf_index1
  ok (p_state, pe_dst)

open CustomLoops in
def poly_element_sample_ntt_from_shake128_modified2
  (p_state : hash.HashState) (pe_dst : Array U16 256#usize) :
  Result (hash.HashState × (Array U16 256#usize))
  :=
  do
  let shake_output_buf := Array.repeat 24#usize 0#u8
  let s ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
  let curr_buf_index := Slice.len s
  let (p_state, pe_dst, i, shake_output_buf, curr_buf_index) ←
    whileLoop (p_state, pe_dst, 0#usize, shake_output_buf, curr_buf_index) $
    fun (p_state, pe_dst, i, shake_output_buf, curr_buf_index) => do
      if i < key.MLWE_POLYNOMIAL_COEFFICIENTS
      then
        do
        let s ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
        let i1 := Slice.len s
        massert (curr_buf_index <= i1)
        let s1 ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
        let i2 := Slice.len s1
        if curr_buf_index = i2
        then
          do
          let (s2, to_slice_mut_back) ←
            (↑(Array.to_slice_mut shake_output_buf) : Result ((Slice U8) ×
              (Slice U8 → Array U8 24#usize)))
          let (p_state1, s3) ← hash.shake128_extract p_state s2 false
          let shake_output_buf1 := to_slice_mut_back s3
          let s4 ← (↑(Array.to_slice shake_output_buf1) : Result (Slice U8))
          let a ← ntt.slice_to_sub_array2 s4 0#usize
          let i3 ← (↑(core.num.U16.from_le_bytes a) : Result U16)
          let sample0 ← (↑(i3 &&& 4095#u16) : Result U16)
          let s5 ← (↑(Array.to_slice shake_output_buf1) : Result (Slice U8))
          let i4 ← 0#usize + 1#usize
          let a1 ← ntt.slice_to_sub_array2 s5 i4
          let i5 ← (↑(core.num.U16.from_le_bytes a1) : Result U16)
          let sample1 ← i5 >>> 4#i32
          let curr_buf_index1 ← 0#usize + 3#usize
          let i6 ← (↑(UScalar.cast .U32 sample0) : Result U32)
          let i7 ←
            (↑(UScalar.cast_fromBool .Usize (i6 < ntt.Q)) : Result Usize)
          let i8 ← i + i7
          if i8 < key.MLWE_POLYNOMIAL_COEFFICIENTS
          then
            do
            let pe_dst1 ← Array.update pe_dst i sample0
            let pe_dst2 ← Array.update pe_dst1 i8 sample1
            let i9 ← (↑(UScalar.cast .U32 sample1) : Result U32)
            let i10 ←
              (↑(UScalar.cast_fromBool .Usize (i9 < ntt.Q)) : Result Usize)
            let i11 ← i8 + i10
            ForInStep.yield (p_state1, pe_dst2, i11, shake_output_buf1, curr_buf_index1)
          else
            do
            let pe_dst1 ← Array.update pe_dst i sample0
            ForInStep.yield (p_state1, pe_dst1, i8, shake_output_buf1, curr_buf_index1)
        else
          do
          let s2 ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
          let a ← ntt.slice_to_sub_array2 s2 curr_buf_index
          let i3 ← (↑(core.num.U16.from_le_bytes a) : Result U16)
          let sample0 ← (↑(i3 &&& 4095#u16) : Result U16)
          let s3 ← (↑(Array.to_slice shake_output_buf) : Result (Slice U8))
          let i4 ← curr_buf_index + 1#usize
          let a1 ← ntt.slice_to_sub_array2 s3 i4
          let i5 ← (↑(core.num.U16.from_le_bytes a1) : Result U16)
          let sample1 ← i5 >>> 4#i32
          let curr_buf_index1 ← curr_buf_index + 3#usize
          let i6 ← (↑(UScalar.cast .U32 sample0) : Result U32)
          let i7 ←
            (↑(UScalar.cast_fromBool .Usize (i6 < ntt.Q)) : Result Usize)
          let i8 ← i + i7
          if i8 < key.MLWE_POLYNOMIAL_COEFFICIENTS
          then
            do
            let pe_dst1 ← Array.update pe_dst i sample0
            let pe_dst2 ← Array.update pe_dst1 i8 sample1
            let i9 ← (↑(UScalar.cast .U32 sample1) : Result U32)
            let i10 ←
              (↑(UScalar.cast_fromBool .Usize (i9 < ntt.Q)) : Result Usize)
            let i11 ← i8 + i10
            ForInStep.yield (p_state, pe_dst2, i11, shake_output_buf, curr_buf_index1)
          else
            do
            let pe_dst1 ← Array.update pe_dst i sample0
            ForInStep.yield (p_state, pe_dst1, i8, shake_output_buf, curr_buf_index1)
      else ForInStep.done (p_state, pe_dst, i, shake_output_buf, curr_buf_index)
  ok (p_state, pe_dst)

/- This is not the infinite stream axiomatization that we discussed, but it is a consequence that follows
   from it. Tentatively, I believe this is the only fact required for
   `poly_element_sample_ntt_from_shake128_modified`, but if I am incorrect, this axiom can be replaced with
   a theorem that derives this fact from the infinite stream axiomatization. -/
axiom XOF.squeeze.composable (ctx : SHAKE128.Context) (z1 z2 : Nat) :
  let (ctx'_part1, v1) := XOF.squeeze ctx z1
  let (ctx'_part2, v2) := XOF.squeeze ctx'_part1 z2
  let (ctx', v) := XOF.squeeze ctx (z1 + z2)
  ctx'_part2 = ctx' ∧ v1 ++ v2 = v

-- **TODO** It might instead be better to have the reverse mapping, not sure
axiom SHAKE128.Context.ofHashState (s : hash.HashState) : SHAKE128.Context

axiom shake128_extract.length_inv :
  ∀ s l r, hash.shake128_extract s l false = ok r → r.2.1.length = l.length

axiom SHAKE128.squeeze_eq_extract (s : hash.HashState) (n : ℕ) :
  -- Second arg to shake128_extract is irrelevant (it is location of Rust output)
  ∀ l, ∀ hl : l.length = n, ∃ r, ∃ h : hash.shake128_extract s l false = ok r,
  XOF.squeeze (SHAKE128.Context.ofHashState s) n =
  (SHAKE128.Context.ofHashState r.1,
    ⟨(r.2.1.map U8.bv).toArray, by simp [shake128_extract.length_inv _ _ _ h, hl]⟩)

set_option pp.analyze true in
set_option pp.coercions.types true in
set_option pp.analyze.typeAscriptions true in
@[progress]
def poly_element_sample_ntt_from_shake128_modified.spec (p_state : hash.HashState)
  (pe_dst : Array U16 256#usize) (B : {l : List Byte // l.length = 34 })
  (hB : XOF.absorb XOF.init B = SHAKE128.Context.ofHashState p_state)
  (hDiv : poly_element_sample_ntt_from_shake128_modified p_state pe_dst ≠ div) :
  ∃ r, poly_element_sample_ntt_from_shake128_modified p_state pe_dst = ok r ∧
  sampleNTT B = some (to_poly r.2) := by
  unfold poly_element_sample_ntt_from_shake128_modified
  simp only [CustomLoops.instForInResultLoopUnit_symcrust, UScalar.lt_equiv,
    key.MLWE_POLYNOMIAL_COEFFICIENTS_eq, UScalar.le_equiv, Usize.ofNat_val_eq, Q.eq,
    UScalar.ofNat_val_eq, forIn, Spec.Q, Prod.exists]
  let* ⟨s, hs⟩ ← Array.to_slice.progress_spec
  let loop_state_type := MProd Usize
    (MProd (UScalar UScalarTy.Usize)
    (MProd hash.HashState (MProd (Std.Array U16 256#usize) (Std.Array (UScalar UScalarTy.U8) 24#usize))))
  -- Automation note: It might be worthwhile to write a tactic that makes it simpler to extract the inner
  -- loop body without having to painstakingly copy the loop body into a `tlet`
  olet hloop_body : (loop_body : Unit → loop_state_type → Result (ForInStep loop_state_type)) :=
    fun x (r : loop_state_type) =>
      if (↑r.snd.fst : ℕ) < 256 then do
        let s ← (↑r.snd.snd.snd.snd.to_slice : Result (Slice (UScalar UScalarTy.U8)))
        massert ((↑r.fst : ℕ) ≤ (↑s : List (UScalar UScalarTy.U8)).length)
        let s1 ← (↑r.snd.snd.snd.snd.to_slice : Result (Slice (UScalar UScalarTy.U8)))
        if r.fst = s1.len then do
            let __discr ←
              (↑r.snd.snd.snd.snd.to_slice_mut :
                  Result
                    (Slice (UScalar UScalarTy.U8) ×
                      (Slice (UScalar UScalarTy.U8) → Std.Array (UScalar UScalarTy.U8) 24#usize)))
            let __discr_1 ← hash.shake128_extract r.snd.snd.fst __discr.1 false
            let s4 ← (↑(__discr.2 __discr_1.2).to_slice : Result (Slice (UScalar UScalarTy.U8)))
            let a ← slice_to_sub_array2 s4 0#usize
            let i3 ← (↑(core.num.U16.from_le_bytes a) : Result U16)
            let sample0 ← (↑(i3 &&& 4095#u16) : Result (UScalar UScalarTy.U16))
            let s5 ← (↑(__discr.2 __discr_1.2).to_slice : Result (Slice (UScalar UScalarTy.U8)))
            let i4 ← 0#usize + 1#usize
            let a1 ← slice_to_sub_array2 s5 i4
            let i5 ← (↑(core.num.U16.from_le_bytes a1) : Result U16)
            let sample1 ← i5 >>> 4#i32
            let curr_buf_index1 ← 0#usize + 3#usize
            let i6 ← (↑(UScalar.cast UScalarTy.U32 sample0) : Result (UScalar UScalarTy.U32))
            let i7 ←
              (↑(UScalar.cast_fromBool UScalarTy.Usize (decide ((↑i6 : ℕ) < 3329))) :
                  Result (UScalar UScalarTy.Usize))
            let i8 ← r.snd.fst + i7
            if (↑i8 : ℕ) < 256 then do
                let pe_dst1 ← r.snd.snd.snd.fst.update r.snd.fst sample0
                let pe_dst2 ← pe_dst1.update i8 sample1
                let i9 ← (↑(UScalar.cast UScalarTy.U32 sample1) : Result (UScalar UScalarTy.U32))
                let i10 ←
                  (↑(UScalar.cast_fromBool UScalarTy.Usize (decide ((↑i9 : ℕ) < 3329))) :
                      Result (UScalar UScalarTy.Usize))
                let i11 ← i8 + i10
                ok (ForInStep.yield ⟨curr_buf_index1, i11, __discr_1.1, pe_dst2, __discr.2 __discr_1.2⟩)
              else do
                let pe_dst1 ← r.snd.snd.snd.fst.update r.snd.fst sample0
                ok (ForInStep.yield ⟨curr_buf_index1, i8, __discr_1.1, pe_dst1, __discr.2 __discr_1.2⟩)
          else do
            let s2 ← (↑r.snd.snd.snd.snd.to_slice : Result (Slice (UScalar UScalarTy.U8)))
            let a ← slice_to_sub_array2 s2 r.fst
            let i3 ← (↑(core.num.U16.from_le_bytes a) : Result U16)
            let sample0 ← (↑(i3 &&& 4095#u16) : Result (UScalar UScalarTy.U16))
            let s3 ← (↑r.snd.snd.snd.snd.to_slice : Result (Slice (UScalar UScalarTy.U8)))
            let i4 ← r.fst + 1#usize
            let a1 ← slice_to_sub_array2 s3 i4
            let i5 ← (↑(core.num.U16.from_le_bytes a1) : Result U16)
            let sample1 ← i5 >>> 4#i32
            let curr_buf_index1 ← r.fst + 3#usize
            let i6 ← (↑(UScalar.cast UScalarTy.U32 sample0) : Result (UScalar UScalarTy.U32))
            let i7 ←
              (↑(UScalar.cast_fromBool UScalarTy.Usize (decide ((↑i6 : ℕ) < 3329))) :
                  Result (UScalar UScalarTy.Usize))
            let i8 ← r.snd.fst + i7
            if (↑i8 : ℕ) < 256 then do
                let pe_dst1 ← r.snd.snd.snd.fst.update r.snd.fst sample0
                let pe_dst2 ← pe_dst1.update i8 sample1
                let i9 ← (↑(UScalar.cast UScalarTy.U32 sample1) : Result (UScalar UScalarTy.U32))
                let i10 ←
                  (↑(UScalar.cast_fromBool UScalarTy.Usize (decide ((↑i9 : ℕ) < 3329))) :
                      Result (UScalar UScalarTy.Usize))
                let i11 ← i8 + i10
                ok (ForInStep.yield ⟨curr_buf_index1, i11, r.snd.snd.fst, pe_dst2, r.snd.snd.snd.snd⟩)
              else do
                let pe_dst1 ← r.snd.snd.snd.fst.update r.snd.fst sample0
                ok (ForInStep.yield ⟨curr_buf_index1, i8, r.snd.snd.fst, pe_dst1, r.snd.snd.snd.snd⟩)
      else ok (ForInStep.done ⟨r.fst, r.snd.fst, r.snd.snd.fst, r.snd.snd.snd.fst, r.snd.snd.snd.snd⟩)
  let* ⟨r, hr⟩ ← CustomLoops.Result.Loop.forIn.progress_spec
  . intro h
    contrapose hDiv -- **TODO** Is there a better way to do this?
    unfold poly_element_sample_ntt_from_shake128_modified
    simp only [CustomLoops.instForInResultLoopUnit_symcrust, UScalar.lt_equiv,
      key.MLWE_POLYNOMIAL_COEFFICIENTS_eq, UScalar.le_equiv, Usize.ofNat_val_eq, Q.eq,
      UScalar.ofNat_val_eq, forIn, ne_eq, not_not]
    let* ⟨s', hs'⟩ ← Array.to_slice.progress_spec
    rw [hs] at h
    rw [hs', ← hloop_body, h]
    simp
  . intro e
    -- **PLAN** Use `cases poly_element_sample_ntt_from_shake128_modified p_state pe_dst`
    -- to get the values for the second and third goals generated by
    -- CustomLoops.Result.Loop.forIn.loop.partial_correctness2
    let motive : loop_state_type → loop_state_type → Error → Prop := fun b _ _ =>
      CustomLoops.Result.Loop.forIn Lean.Loop.mk b loop_body ≠ fail e
    -- have test1 := CustomLoops.Result.Loop.forIn.loop.partial_correctness loop_body motive
    -- have test2 := CustomLoops.Result.Loop.forIn.loop.partial_correctness2 loop_body motive
    apply CustomLoops.Result.Loop.forIn.loop.partial_correctness2 loop_body motive
      _ ⟨s.len, 0#usize, p_state, pe_dst, Array.repeat 24#usize 0#u8⟩
    . sorry
    . sorry
    . sorry
    . sorry
  . sorry

set_option pp.analyze true in
set_option pp.coercions.types true in
set_option pp.analyze.typeAscriptions true in
@[progress]
def poly_element_sample_ntt_from_shake128_modified2.spec (p_state : hash.HashState)
  (pe_dst : Array U16 256#usize) (B : {l : List Byte // l.length = 34 })
  (hB : XOF.absorb XOF.init B = SHAKE128.Context.ofHashState p_state)
  (hDiv : poly_element_sample_ntt_from_shake128_modified p_state pe_dst ≠ div) :
  ∃ r, poly_element_sample_ntt_from_shake128_modified2 p_state pe_dst = ok r ∧
  sampleNTT B = some (to_poly r.2) := by
  unfold poly_element_sample_ntt_from_shake128_modified2
  simp only [CustomLoops.instForInResultLoopUnit_symcrust, UScalar.lt_equiv,
    key.MLWE_POLYNOMIAL_COEFFICIENTS_eq, UScalar.le_equiv, Usize.ofNat_val_eq, Q.eq,
    UScalar.ofNat_val_eq, forIn, Spec.Q, Prod.exists]
  -- **NOTE** As soon as `simp` is called, the state used by `whileLoop` reverts to projections
  -- rather than named matching
  sorry

structure myTest where
  a : Nat
  b : Nat

def hi : myTest := {a := 2, b := 3}

def getB (x : myTest) :=
  match x with
  | ⟨_, b⟩ => b

def get2 (x : myTest) := x.2

theorem test : getB hi = get2 hi := by
  simp [getB]
  sorry
