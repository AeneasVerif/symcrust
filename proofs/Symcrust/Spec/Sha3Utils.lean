import Aeneas.BitVec
import Init.Data.Nat.Div.Lemmas

def Vector.setWidth[Inhabited α](v: Vector α n)(m: Nat): Vector α m := (v.take m ++ replicate (m-n) (default: α)).cast (by simp [←Nat.sub_sub_eq_min])

def Array.chunks_exact(k: Nat)(arr: Array α): Array (Vector α k) :=
  /- assert! arr.size % k == 0 -/
  if h: arr.size < k ∨ k = 0 then
    #[]
  else
    #[⟨arr.extract (start:= 0) (stop := k), by simp_all⟩] ++ (arr.extract (start := k) (stop:= arr.size)).chunks_exact k
termination_by arr.size

def Array.extract_size_of_chunks_exact(P: Array α)(r: Nat)
: let n := P.size / r
  ∀ (i: Fin n), (P.extract (r*i) (r*(i+1))).size = r
:= by
  intro n i
  obtain ⟨i, iLt⟩ := i
  simp
  if h: n = 0 then
    rw [h] at iLt
    cases iLt
  else
    have: r*(i+1) <= P.size := by
      calc r*(i+1)
        _ <= r*(n-1+1) := by
          apply Nat.mul_le_mul (Nat.le_of_eq rfl)
          simp
          apply Nat.le_sub_one_of_lt
          assumption
        _ =  r*n := by
          have: 1 <= n := Nat.pos_of_ne_zero h
          have: (n + 1 - 1) = (n-1 + 1) := Nat.sub_add_comm this
          simp [←this]
        _ <= P.size := by simp [n]; rw [Nat.mul_comm]; exact Nat.div_mul_le_self P.size r
    simp [Nat.min_eq_left this]
    simp [←Nat.mul_sub_left_distrib _ _ _]

def Array.chunks (k: Nat)(arr: Array α): Array (Array α) :=
  if arr.size = 0 ∨ k = 0 then #[] else #[arr.take k] ++ (arr.extract k arr.size |>.chunks k)
termination_by arr.size

/- def String.zfill(s: String)(len: Nat) := List.asString <| -/
/-   (List.replicate (len - s.length) '0') ++ (s.take len).toList -/

def UInt8.toBitString(u: UInt8): Vector Bool 8 :=
  let bv := u.toBitVec
  #v[ (bv >>> 0) % 2 == 1,
      (bv >>> 1) % 2 == 1,
      (bv >>> 2) % 2 == 1,
      (bv >>> 3) % 2 == 1,
      (bv >>> 4) % 2 == 1,
      (bv >>> 5) % 2 == 1,
      (bv >>> 6) % 2 == 1,
      (bv >>> 7) % 2 == 1 ]

def Vector.ofArray(arr: Array α): Vector α arr.size := ⟨arr, rfl⟩

def Vector.joinBitVec(v: Vector (BitVec n) m): BitVec (n*m) :=
  if h: n = 0 then
    by simpa [h] using 0#0
  else
    match m with
    | 0 => by simpa using 0#0
    | n+1 => let val := v[0]'(Nat.zero_lt_succ n) ++ joinBitVec (v.drop 1)
      by
        rw [Nat.mul_add, Nat.add_comm]
        simpa [Nat.add_sub_cancel] using val

def ByteArray.toBitVecLE(arr: ByteArray): BitVec (8*arr.size) :=
  (Vector.ofArray arr.data).map (·.toBitVec) |>.reverse |>.joinBitVec
def ByteArray.toBitVecBE(arr: ByteArray): BitVec (8*arr.size) :=
  (Vector.ofArray arr.data).map (·.toBitVec) |>.joinBitVec

def String.toBitVecLE(s: String) := ByteArray.toBitVecLE <| toUTF8 s
def String.toBitVecBE(s: String) := ByteArray.toBitVecBE <| toUTF8 s

def BitVec.toList(bv: BitVec n): List Bool := List.finRange n |>.map (bv[·])

def Vector.toBitVecLE(vec: Vector Bool n): BitVec n := BitVec.ofBoolListLE vec.toArray.toList |>.cast (by simp)

open Std.Format in
def Utils.dump' (S: BitVec n)(spacing? : Bool := false): Std.Format :=
  let final := S.toByteArray.data
    |>.map (·.toBitVec.toHex)
    |>.toList
    |> "".intercalate
  let singleSpace? := if spacing? then text " " else nil
  let lineBreak? := if spacing? then align false else nil
  let formatted := Array.mk final.toList
    |>.chunks 16
    |>.map (·.chunks 2
      |>.map (fun v => text  <| String.ofList v.toList)
      |>.toList
      |> singleSpace?.joinSep
      |> group)
    |>.chunks 2
    |>.map (·.toList |> singleSpace?.joinSep)
    |>.toList
    |> lineBreak?.joinSep
    if spacing? then
      nest 8 <| lineBreak? ++ formatted
    else
      formatted

def Utils.dump (S: Vector Bool n)(spacing? : Bool := false): Std.Format := Utils.dump' S.toBitVecLE (spacing? := spacing?)

theorem Nat.lt_packing_right {x y: Nat}(x_lt: x < n)(y_lt: y < m)
: n*y + x < n*m
:= by
  have n_pos: n > 0 := by omega
  have m_pos: m > 0 := by omega
  calc n*y + x
    _ ≤ n * (m-1) + x := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.le_pred_iff_lt m_pos |>.mpr
      assumption
    _ ≤ n * (m-1) + (n-1) := by
      apply Nat.add_le_add_left
      apply Nat.le_pred_iff_lt n_pos |>.mpr
      assumption
    _ < n * m := by
      simp [Nat.mul_sub, ←Nat.add_sub_assoc n_pos]
      have: n*m > 0 := Nat.mul_pos n_pos m_pos
      have: n*m >= n := by
        conv => rhs; rw [←Nat.mul_one n]
        apply Nat.mul_le_mul_left n m_pos
      omega
