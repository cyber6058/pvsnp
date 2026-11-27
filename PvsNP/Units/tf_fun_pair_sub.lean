import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tr_rel_val_coprime
import PvsNP.Units.m2_tm_self_delimiting_pair

/- Uses the canonical binary subtraction and comparison lemmas of the settled
tr_rel_val_coprime unit in makedotfun/pvsnp at 81a25475d739668f925eea59e7bef587de6cb214
(Apache License, Version 2.0). -/
namespace PvsNP.Units.tf_fun_pair_sub_aux

open PvsNP.Units.tr_rel_val_coprime
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def subtract (s : List Bool) : List Bool :=
  if decide (val (unpairB s).2 ≤ val (unpairB s).1) = true then
    binSub (canon (unpairB s).1) (canon (unpairB s).2)
  else []

theorem subtract_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString subtract := by
  have left : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).1) := cpt_unpairB1_1 cpt_id
  have right : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).2) := cpt_unpairB2_1 cpt_id
  have lhs : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => canon (unpairB s).1) := cpt_binAdd_fun _ _ left (cpt_const [])
  have rhs : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => canon (unpairB s).2) := cpt_binAdd_fun _ _ right (cpt_const [])
  exact PvsNP.Units.m2_ite_polytime _ _ _ (cpt_binLe_fun _ _ right left)
    (cpt_binSub_fun _ _ lhs rhs) (cpt_const [])

theorem pair_subtract (x y : List Bool) :
    subtract (pairB x y) = Nat.bits (val x - val y) := by
  unfold subtract
  rw [unpairB_pairB]
  by_cases fits : val y ≤ val x
  · simpa [fits, canon_eq] using (binSub_eq (m := val x) (n := val y) fits)
  · have zero : val x - val y = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp [fits, zero, Nat.zero_bits]

theorem poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => Nat.bits (val p.1 - val p.2)) := by
  have machine : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => subtract (pairB p.1 p.2)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) subtract
      PvsNP.Units.m2_tm_self_delimiting_pair.1 subtract_poly
  simpa only [pair_subtract] using machine

end PvsNP.Units.tf_fun_pair_sub_aux

theorem PvsNP.Units.tf_fun_pair_sub :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) - Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
  PvsNP.Units.tf_fun_pair_sub_aux.poly
