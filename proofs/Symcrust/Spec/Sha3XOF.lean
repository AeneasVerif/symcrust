import Symcrust.Spec.Sha3

set_option grind.warning false

namespace Spec

/-
Incremental sponge functions that can be used to initialize a state, absorb the input data
and then incrementally squeeze the required output data.-/

section Sponge -- generic sponge construction

namespace Incremental

variable
  -- algorithm
  (n   : Nat)
  (f   : Bitstring n → Bitstring n)
  (pad : (r : Nat) → Nat → Array Bit := «pad10*1»)  -- padding function
  (r   : Nat)  -- rate: number of bits added/squeezed at a time
  (hr  : 0 < r ∧ r < n := by decide)

structure sponge.state where
  -- current state (including additional proof-oriented details)
  S   : Bitstring n       -- permutation internal state
  Z   : Array Bit         -- bits already squeezed, excluding S.setWidth r
  x   : Nat               -- number of bits already returned
  hx  : x ≤ Z.size + r

def sponge.init : sponge.state n r := {
  S := .replicate n false,
  Z := #[],
  x := 0,
  hx := by omega }

-- pads then absorbs bits; this part is not incremental
def sponge.absorb1 (s : state n r) (N: Array Bit) :=
  let P := N ++ pad r N.size
  let Ps := P.chunks_exact r
  let S := Ps.foldl (λ S Pᵢ => f (S ^^^ Pᵢ.setWidth n)) s.S
  { s with S }
  /- code closer to absorb:
  Id.run do
  let mut S := s.S
  for Pᵢ in Ps do
    S := S ^^^ (Pᵢ.setWidth n)
    S := f S
  return { s with S }
  -/

-- squeezes r extra bits; can be applied at any time
def sponge.squeeze_r (s : state n r) :=
  let Z := s.Z ++ (s.S.setWidth r).toArray
  let S := f s.S
  have hx : s.x ≤ Z.size + r := le_trans s.hx (by grind)
  { s with Z, S, hx }

-- squeezes extra bits only on demand
def sponge.squeeze1 (s : state n r) d : state n r × Bitstring d :=
  if hd : s.Z.size + r < s.x + d then
    squeeze1 (squeeze_r n f r hr s) d
  else
    -- returns available bits without internal squeezing
    let A := s.Z ++ (s.S.setWidth r).toArray
    let D : Bitstring d := (A.extract s.x (s.x + d)).toVector.cast (by grind)
    have hx : s.x + d ≤ s.Z.size + r := by grind
    ({ s with x := s.x + d, hx}, D)
  termination_by s.x + d - (s.Z.size + r)
  decreasing_by
    simp [squeeze_r]
    grind

-- towards lemmas for squeezing at different strides
lemma sponge.squeeze3 (s: state n r) d :
  let t := squeeze_r n f r hr s
  let u := squeeze1 n f r hr s d
  let v := squeeze1 n f r hr t d
  if s.Z.size + r < s.x + d then
    v = u -- u squeezes at least once, catching up on v
  else
    v = (squeeze_r n f r hr u.1, u.2) -- v is still ahead by one round
  := by
    intro t u v
    have ht : t = squeeze_r n f r hr s := rfl
    have hu : u = squeeze1 n f r hr s d := rfl
    have hv : v = squeeze1 n f r hr t d := rfl
    unfold squeeze1 at hu
    split_ifs at hu with h0
    . rw [ht] at hv
      grind

    . unfold squeeze1 at hv
      split_ifs at hv with h1
      . exfalso
        rw [ht] at h1
        unfold squeeze_r at h1
        simp at h0 h1
        omega

      . split_ifs
        simp at hv
        simp [hv, ht, hu, squeeze_r]
        have eqz : s.x + d - (s.Z.size + r) = 0 := by
          apply Nat.sub_eq_zero_of_le
          apply Nat.ge_of_not_lt h0
        simp [eqz]

private lemma size_extract (A : Array α) {i size} (hsize : i + size ≤ A.size) :
  (A.extract i (i+size)).size = size := by
  let B := A.extract i (i+size)
  have hB: B.size = min (i + size) A.size - min i A.size := by
    grind [Array.extract]
  grind

-- simplified squeeze when we have enough bits in Z: no need to use S or f
def sponge.lookup (s : state n r) m (hm : s.x + m ≤ s.Z.size := by grind) : state n r × Bitstring m :=
  let s' := { s with x := s.x + m, hx := by grind }
  let B := s.Z.extract s.x (s.x + m)
  (s', B.toVector.cast (size_extract s.Z hm))

lemma sponge.squeeze_unrolled (s: state n r) d :
  let t := squeeze_r n f r hr (squeeze_r n f r hr s)
  (squeeze1 n f r hr t d).2 = (squeeze1 n f r hr s d).2 := by
    have h1 := squeeze3 n f r hr s d
    simp at h1
    have h2 := squeeze3 n f r hr (squeeze_r n f r hr s) d
    simp at h2
    split_ifs at h1 h2 with h0 h3 <;> grind

lemma sponge.squeeze_lookup s m hm :
  squeeze1 n f r hr s m = lookup n r hr s m hm := by
  unfold lookup squeeze1
  split_ifs
  . grind -- excluded branch of squeeze1
  . simp_all

end Incremental

end Sponge

-- Incremental API for SHAKE128 and SHAKE256

private def n := b 6
private def k6 := Keccak.P 6 (nᵣ := 24)

def SHAKE128.init := Incremental.sponge.init n (r := b 6 - 256)
def SHAKE256.init := Incremental.sponge.init n (r := b 6 - 512)

def SHAKE128.absorb s B := Incremental.sponge.absorb1 n k6 (r := b 6 - 256) (s := s) (N := B ++ SHAKE_suffix)
def SHAKE256.absorb s B := Incremental.sponge.absorb1 n k6 (r := b 6 - 512) (s := s) (N := B ++ SHAKE_suffix)

def SHAKE128.squeeze := Incremental.sponge.squeeze1 n k6 (r := b 6 - 256)
def SHAKE256.squeeze := Incremental.sponge.squeeze1 n k6 (r := b 6 - 512)

end Spec
