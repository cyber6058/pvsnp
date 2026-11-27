import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tr_rel_val_coprime
import PvsNP.Units.m2_tm_self_delimiting_pair

namespace PvsNP.Units.tf_fun_pair_max_aux

open PvsNP.Units.tr_rel_val_coprime
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def choose (s : List Bool) : List Bool :=
  if decide (val (unpairB s).1 ≤ val (unpairB s).2) = true then canon (unpairB s).2
  else canon (unpairB s).1

theorem choose_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString choose := by
  have l : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).1) := cpt_unpairB1_1 cpt_id
  have r : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).2) := cpt_unpairB2_1 cpt_id
  exact PvsNP.Units.m2_ite_polytime _ _ _ (cpt_binLe_fun _ _ l r)
    (cpt_binAdd_fun _ _ r (cpt_const [])) (cpt_binAdd_fun _ _ l (cpt_const []))

theorem output (x y : List Bool) : choose (pairB x y) = Nat.bits (max (val x) (val y)) := by
  unfold choose
  rw [unpairB_pairB]
  by_cases h : val x ≤ val y
  · simp [h, canon_eq, max_eq_right h]
  · have hy : val y ≤ val x := by omega
    simp [h, canon_eq, max_eq_left hy]

theorem poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => Nat.bits (max (val p.1) (val p.2))) := by
  have composed : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => choose (pairB p.1 p.2)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) choose
      PvsNP.Units.m2_tm_self_delimiting_pair.1 choose_poly
  simpa only [output] using composed

end PvsNP.Units.tf_fun_pair_max_aux

theorem PvsNP.Units.tf_fun_pair_max :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (max (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))
          (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) :=
  PvsNP.Units.tf_fun_pair_max_aux.poly
