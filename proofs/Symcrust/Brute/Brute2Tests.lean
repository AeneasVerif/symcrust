import Symcrust.Brute.Brute2

open Aeneas Std

theorem testLt : ∀ x : U8, x < UScalar.ofNat 5 → x = x := by brute
theorem testLe1 : ∀ x : U8, x ≤ UScalar.ofNat 5 → x = x := by brute
theorem testLe2 : ∀ x : U8, x ≤ UScalar.ofNat (2^8 - 1) → x = x := by brute

set_option trace.brute.debug true in
theorem test : ∀ x : U8, x = x := by brute

example : ∀ x : BitVec 32, x ≤ 15#32 → x &&& 15 = x := by brute

set_option trace.brute.debug true in
example : ∀ x : BitVec 9, ∀ y : BitVec 8, x = x := by brute

set_option trace.brute.debug true in
example : ∀ x : BitVec 9, x < 1#9 → ∀ y : BitVec 8, x = x := by brute

set_option trace.brute.debug true in
example : ∀ x : BitVec 9, x < 1#9 → ∀ y : BitVec 8, y < 1#8 → x = x := by brute

set_option trace.brute.debug true in
example : ∀ x : BitVec 9, x < 1#9 → ∀ y : BitVec 8, y ≤ 1#8 → x = x := by brute

set_option trace.brute.debug true in
example : ∀ x : BitVec 8, x < 1#8 → ∀ y : BitVec 8, y ≤ x → x = x := by brute

example : ∀ x < 9, ∀ y ≤ x, x + y = y + x := by brute

set_option trace.brute.debug true in
example : ∀ x : BitVec 2, ∀ y : BitVec 1, ∀ z : BitVec 3, ∀ a : BitVec 4, x = x := by
  brute

set_option trace.brute.debug true in
example : ∀ x : BitVec 8, ∀ y : BitVec 7, ∀ z : BitVec 6, x = x := by brute

set_option trace.brute.debug true in
example : ∀ x : BitVec 8, x < 1#8 → ∀ y : BitVec 7, ∀ z : BitVec 6, x = x := by brute

example : ∀ a : BitVec 4, ∀ x : BitVec 3, ∀ y : BitVec 2, ∀ z : BitVec 1, x = x := by brute

set_option trace.brute.debug true in
example : ∀ a : BitVec 4, ∀ x : BitVec 3, ∀ y : BitVec 2, ∀ z : BitVec 1, x = x := by brute

set_option trace.brute.debug true in
example : ∀ a : BitVec 4, ∀ x : BitVec 3, ∀ y : BitVec 2, ∀ z < 1, x = x := by brute

set_option trace.brute.debug true in
example : ∀ a < 4, ∀ x < 5, ∀ y < x, ∀ z < y, x = x := by brute
