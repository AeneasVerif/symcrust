import Symcrust.Properties.Polynomials
import Symcrust.Code.Funs

#setup_aeneas_simps

namespace Symcrust

open Aeneas Aeneas.Std Result

namespace ntt

def to_poly (a : Array U16 256#usize) : Spec.Polynomial := Vector.ofFn (fun i => a[i]!)

@[simp]
theorem getElem!_to_poly (a : Array U16 256#usize) (i : ℕ) :
  (to_poly a)[i]! = ((a.val[i]!) : Spec.Zq) := by
  simp [to_poly]
  dcases hi : i < a.val.length <;> simp_all [default, Vector.getElem!_ofFn]

@[simp]
theorem to_poly_set (a : Array U16 256#usize) (i : Usize) (x : U16) :
  to_poly (Std.Array.set a i x) = (to_poly a).set! i.val (x.val : Spec.Zq) := by
  simp only [to_poly, Spec.Q, id_eq, Array.set_val_eq, List.map_set]
  rw [Vector.eq_iff_forall_eq_getElem!]
  intro j hj
  simp_lists
  by_cases hj': j = i <;> simp_lists

@[simp]
theorem to_poly_getElem!_eq (a : Std.Array U16 256#usize) (i : Nat) :
  (to_poly a)[i]! = a.val[i]! := by
  fsimp [to_poly]
  dcases h: i < 256 <;> simp_all [Vector.getElem!_ofFn, default]

def wfArray {n} (a : Array U16 n) : Prop :=
  ∀ i, i < n.val → a.val[i]!.val < 3329

theorem wfArray_update {n : Usize} (v : Std.Array U16 n) (i : Usize) (x : U16)
  (hbound : i.val < v.length)
  (hx : x.val < 3329)
  (hWf : wfArray v) :
  ∃ nv, v.update i x = ok nv ∧ nv = v.set i x ∧
  wfArray nv := by
  progress as ⟨ nv, hnv ⟩
  fsimp [wfArray] at *
  fsimp [hnv, toResult]
  intro j hj
  dcases hLt : j = i.val <;> fsimp [*]

theorem wfArray_index {n : Usize} (v : Std.Array U16 n) (i : Usize)
  (hbound : i.val < v.length)
  (hWf : wfArray v) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! ∧ x.val < 3329 := by
  progress as ⟨ x ⟩
  fsimp [wfArray] at hWf
  fsimp [*]
  replace hWf := hWf i.val (by scalar_tac)
  scalar_tac

theorem wfArray_iff_forAll {n : Usize} (a : Std.Array U16 n) : wfArray a ↔ a.val.all (fun x => x.val < 3329) := by
  simp +contextual only [wfArray, List.getElem!_eq_getElem?_getD, List.Vector.length_val,
    List.getElem?_eq_getElem, Option.getD_some, List.all_eq_true, decide_eq_true_eq, ←
    List.forall_getElem]

@[simp, scalar_tac_simps, bvify_simps] theorem Q.eq : Q = 3329#u32 := by simp [global_simps]
@[simp, scalar_tac_simps, bvify_simps] theorem NEG_Q_INV_MOD_R.eq : NEG_Q_INV_MOD_R = 3327#u32 := by simp [global_simps]
@[simp, scalar_tac_simps, bvify_simps] theorem RMASK.eq : RMASK = 65535#u32 := by simp [global_simps]
@[simp, scalar_tac_simps, bvify_simps] theorem RLOG2.eq : RLOG2 = 16#u32 := by simp [global_simps]
@[simp, scalar_tac_simps, bvify_simps] theorem RSQR.eq : RSQR = 1353#u32 := by simp [global_simps]
@[simp, scalar_tac_simps, bvify_simps] theorem RSQR_TIMES_NEG_Q_INV_MOD_R.eq : RSQR_TIMES_NEG_Q_INV_MOD_R = 44983#u32 := by simp [global_simps]

@[simp, scalar_tac_simps, bvify_simps]
theorem key.MLWE_POLYNOMIAL_COEFFICIENTS_eq : key.MLWE_POLYNOMIAL_COEFFICIENTS.val = 256 := by simp [global_simps]

@[simp] theorem INTT_FIXUP_TIMES_RSQR.eq : INTT_FIXUP_TIMES_RSQR.val = 1441 := by simp [global_simps]
@[simp] theorem INTT_FIXUP_TIMES_RSQR.bv_eq : INTT_FIXUP_TIMES_RSQR.bv = 1441#32 := by simp [global_simps]

@[simp] theorem INTT_FIXUP_TIMES_RSQR_TIMES_NEQ_Q_INV_MOD_R.bv_eq : INTT_FIXUP_TIMES_RSQR_TIMES_NEQ_Q_INV_MOD_R.bv = 10079#32 := by simp [global_simps]

attribute [simp, scalar_tac_simps, bvify_simps] Spec.Q

-- TODO: macro for this
@[simp, scalar_tac_simps, bvify_simps]
theorem COMPRESS_MULCONSTANT.spec : COMPRESS_MULCONSTANT.val = 10321339 := by prove_eval_global

@[simp, scalar_tac_simps, bvify_simps]
theorem COMPRESS_SHIFTCONSTANT.spec : COMPRESS_SHIFTCONSTANT.val = 35 := by prove_eval_global

def to_bytes (b : Slice U8) : List Byte :=
  b.val.map fun x => x.bv

@[simp, simp_lists_simps]
theorem getElem!_to_bytes (b : Slice U8) (i : ℕ) :
  (to_bytes b)[i]! = b.val[i]! := by
  simp only [to_bytes, BitVec.natCast_eq_ofNat, Bvify.UScalar.BitVec_ofNat_setWidth,
    UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv, BitVec.setWidth_eq]
  by_cases hi: i < b.length
  . simp_lists
  . simp_lists_scalar

@[simp, simp_lists_simps]
theorem to_bytes_update {b : Slice U8} (i : Usize) (x : U8) :
  to_bytes (b.set i x) = (to_bytes b).set i x.bv := by
  simp only [to_bytes, Slice.set_val_eq, List.map_set]

@[simp, simp_lists_simps, simp_scalar_simps, scalar_tac_simps, scalar_tac to_bytes b]
theorem to_bytes_length (b : Slice U8) : (to_bytes b).length = b.length := by
  simp only [to_bytes, List.length_map, Slice.length]

@[simp, simp_lists_simps]
theorem to_bytes_setSlice! {b : Slice U8} (i : Usize) (s : List U8) :
  to_bytes (b.setSlice! i s) = (to_bytes b).setSlice! i (s.map U8.bv) := by
  simp only [to_bytes, Slice.setSlice!_val, List.map_setSlice!]

end ntt

end Symcrust
