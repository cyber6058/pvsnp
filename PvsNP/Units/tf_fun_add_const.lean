import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.m2_pair_fun_specialize

/-- Fix the second input of the binary adder to the little-endian digits of five. -/
theorem PvsNP.Units.tf_fun_add_const :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 5)) := by
  let addBits := fun p : List Bool × List Bool =>
    Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) +
      Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))
  have h := (PvsNP.Units.m2_pair_fun_specialize addBits [true, false, true]
    PvsNP.Units.tf_fun_pair_add).1
  have five : Nat.ofDigits (2 : ℕ) ([true, false, true].map Bool.toNat) = 5 := by
    decide
  simpa only [addBits, five] using h
