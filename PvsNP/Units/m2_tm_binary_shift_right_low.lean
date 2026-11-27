import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.tf_fun_pair_add

namespace PvsNP.Units.m2_tm_binary_shift_right_low

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

def val (x : List Bool) : ℕ := Nat.ofDigits 2 (x.map Bool.toNat)

theorem val_bound (x : List Bool) : val x < 2 ^ x.length := by
  have digits : ∀ d ∈ x.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    cases b <;> decide
  simpa only [val, List.length_map] using Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2) digits

theorem val_append (u v : List Bool) :
    val (u ++ v) = val u + 2 ^ u.length * val v := by
  simp only [val, List.map_append, Nat.ofDigits_append, List.length_map]

theorem split (x : List Bool) (k : ℕ) :
    val x = val (x.take k) + 2 ^ k * val (x.drop k) := by
  by_cases hk : k ≤ x.length
  · simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left hk]
      using val_append (x.take k) (x.drop k)
  · have h : x.length ≤ k := by omega
    simp [List.take_of_length_le h, List.drop_of_length_le h, val]

theorem low_bound (x : List Bool) (k : ℕ) : val (x.take k) < 2 ^ k :=
  (val_bound _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (List.length_take_le k x))

theorem high (x : List Bool) (k : ℕ) : val x / 2 ^ k = val (x.drop k) := by
  conv_lhs => rw [split x k]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (low_bound x k), Nat.zero_add]

theorem low (x : List Bool) (k : ℕ) : val x % 2 ^ k = val (x.take k) := by
  conv_lhs => rw [split x k]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (low_bound x k)]

theorem canon : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (val x)) := by
  have pair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x, ([] : List Bool))) :=
    cpt_pair cpt_id (constList_polyTime [])
  have hm := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (x, ([] : List Bool)))
    (fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2)) pair PvsNP.Units.tf_fun_pair_add
  have z : val [] = 0 := rfl
  simpa only [Function.comp_def, z, Nat.add_zero] using hm

theorem canon_swap (f : List Bool × List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (val (f (p.2, p.1)))) := by
  have swapped := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (p.2, p.1)) f cpt_swap hf
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => f (p.2, p.1))
    (fun z : List Bool => Nat.bits (val z)) swapped canon

end PvsNP.Units.m2_tm_binary_shift_right_low

theorem PvsNP.Units.m2_tm_binary_shift_right_low :
PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) / 2 ^ p.2.length)) ∧
  PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) % 2 ^ p.2.length)) := by
  change PvsNP.PolyTimeComputable _ _ (fun p : List Bool × List Bool =>
    Nat.bits (PvsNP.Units.m2_tm_binary_shift_right_low.val p.1 / 2 ^ p.2.length)) ∧
    PvsNP.PolyTimeComputable _ _ (fun p : List Bool × List Bool =>
    Nat.bits (PvsNP.Units.m2_tm_binary_shift_right_low.val p.1 % 2 ^ p.2.length))
  simp only [PvsNP.Units.m2_tm_binary_shift_right_low.high, PvsNP.Units.m2_tm_binary_shift_right_low.low]
  exact ⟨PvsNP.Units.m2_tm_binary_shift_right_low.canon_swap _ PvsNP.Units.m2_take_drop_length_polytime.2,
    PvsNP.Units.m2_tm_binary_shift_right_low.canon_swap _ PvsNP.Units.m2_take_drop_length_polytime.1⟩
