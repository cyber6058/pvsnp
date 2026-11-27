import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.tf_fun_flatmap_all
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.tr_rel_len_dvd

namespace PvsNP.Units.tl_lang_count_coprime_p_aux

private def unary (b : Bool) (x : List Bool) := List.replicate (x.count b) true

private theorem falsePoly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (unary false) := by
  let emit := fun b : Bool => if b then ([] : List Bool) else [true]
  have same : (fun x : List Bool => x.flatMap emit) = unary false := by
    funext x
    induction x with
    | nil => rfl
    | cons b xs ih =>
      cases b <;> simp [emit, unary, List.count_cons, List.replicate_succ] at ih ⊢ <;> exact ih
  rw [← same]
  exact PvsNP.Units.tf_fun_flatmap_all emit

private def onCount (dvdTest : List Bool × List Bool → Bool) (b : Bool)
    (p : List Bool × List Bool) := dvdTest (p.2, unary b p.1)

private theorem countTestPoly (dvdTest : List Bool × List Bool → Bool)
    (hd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer dvdTest)
    (b : Bool) (hc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (unary b)) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (onCount dvdTest b) := by
  have hMap := PvsNP.Units.m2_prod_map_polytime id (unary b)
    PvsNP.Units.m2_prod_map_polytime.ident hc
  have hPair := PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.m2_tm_pair_swap_polytime hMap
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _ hPair hd

private def bad (dvdTest : List Bool × List Bool → Bool) (p : List Bool × List Bool) :=
  !decide ([true] = p.2) && (onCount dvdTest true p && onCount dvdTest false p)

private theorem badPoly (dvdTest : List Bool × List Bool → Bool)
    (hd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer dvdTest) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (bad dvdTest) := by
  have hOnePair := PvsNP.Units.m2_prod_map_polytime (fun _ => [true]) id
    (PvsNP.Units.m2_const_polytime [true]) PvsNP.Units.m2_prod_map_polytime.ident
  have hOne := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hOnePair PvsNP.Units.m2_eq_polytime
  have hBoth := PvsNP.Units.m2_tm_pair_bool_combine Bool.and _ _
    (countTestPoly dvdTest hd true PvsNP.Units.tf_fun_ones_unary)
    (countTestPoly dvdTest hd false falsePoly)
  exact PvsNP.Units.m2_tm_pair_bool_combine (fun one both => (!one) && both) _ _ hOne hBoth

private theorem bad_spec (dvdTest : List Bool × List Bool → Bool)
    (spec : ∀ p : List Bool × List Bool, p.1.length ∣ p.2.length ↔ dvdTest p = true)
    (x : List Bool) (k : ℕ) :
    bad dvdTest (x, List.replicate k true) = true ↔
      k ≠ 1 ∧ k ∣ x.count true ∧ k ∣ x.count false := by
  have bit (b : Bool) : onCount dvdTest b (x, List.replicate k true) = true ↔ k ∣ x.count b := by
    simpa only [onCount, unary, List.length_replicate] using
      (spec (List.replicate k true, unary b x)).symm
  have one : (([true] : List Bool) = List.replicate k true) ↔ k = 1 := by
    constructor
    · intro h
      simpa using (congrArg List.length h).symm
    · rintro rfl
      rfl
  simp only [bad, Bool.and_eq_true, bit, Bool.not_eq_true', decide_eq_false_iff_not, one]

private theorem bounded (x : List Bool) :
    Nat.gcd (x.count true) (x.count false) ≤ x.length := by
  by_cases hz : x.count true = 0
  · simpa [hz] using (List.count_le_length (l := x) (a := false))
  · exact (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hz)).trans List.count_le_length

private theorem gcd_iff (x : List Bool) :
    Nat.gcd (x.count true) (x.count false) = 1 ↔
      ¬ ∃ k : ℕ, k < x.length + 1 ∧ k ≠ 1 ∧ k ∣ x.count true ∧ k ∣ x.count false := by
  constructor
  · rintro h ⟨k, _, hk, ht, hf⟩
    apply hk
    apply Nat.eq_one_of_dvd_one
    rw [← h]
    exact Nat.dvd_gcd ht hf
  · intro h
    by_contra hn
    exact h ⟨Nat.gcd (x.count true) (x.count false), Nat.lt_succ_of_le (bounded x), hn,
      Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩

theorem language :
({x : List Bool | Nat.gcd (x.count true) (x.count false) = 1} : Language Bool) ∈ PvsNP.P := by
  obtain ⟨dvdTest, hd, spec⟩ := PvsNP.Units.tr_rel_len_dvd
  let found := fun x : List Bool =>
    (List.range (x.length + 1)).any (fun k => bad dvdTest (x, List.replicate k true))
  have findPoly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer found :=
    PvsNP.Units.m2_bounded_unary_search_polytime _ (badPoly dvdTest hd)
  refine ⟨_, PvsNP.Units.m2_bool_combine_polytime (fun b _ => !b) found found findPoly findPoly,
    fun x => ?_⟩
  change Nat.gcd (x.count true) (x.count false) = 1 ↔ (!found x) = true
  have hasFactor : found x = true ↔
      ∃ k : ℕ, k < x.length + 1 ∧ k ≠ 1 ∧ k ∣ x.count true ∧ k ∣ x.count false := by
    simp only [found, List.any_eq_true, List.mem_range, bad_spec dvdTest spec]
  rw [gcd_iff, ← hasFactor]
  cases found x <;> decide

end PvsNP.Units.tl_lang_count_coprime_p_aux

theorem PvsNP.Units.tl_lang_count_coprime_p :
({x : List Bool | Nat.gcd (x.count true) (x.count false) = 1} : Language Bool) ∈ PvsNP.P := by
  exact PvsNP.Units.tl_lang_count_coprime_p_aux.language
