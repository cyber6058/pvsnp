import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_closure_double_p
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_p_subset_exp

/-- Check that a word is a square, then test its first half for membership in the language. -/
theorem PvsNP.Units.tc_exp_double :
∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ u ∈ L, x = u ++ u) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L hL
  have firstHalf := PvsNP.Units.m2_exp_down_closed
    ({x : List Bool | x.take (x.length / 2) ∈ L} : Language Bool) L
    ⟨fun x => x.take (x.length / 2), PvsNP.Units.tc_closure_double_p.cpt_takeHalf,
      fun _ => Iff.rfl⟩ hL
  obtain ⟨k, f, M, accepts, bound⟩ := PvsNP.Units.m2_exp_inter _ _
    (PvsNP.Units.m2_p_subset_exp _ PvsNP.Units.m2_ww_in_p) firstHalf
  refine ⟨k, f, M, fun x => ?_, bound⟩
  change x ∈ ({s : List Bool | ∃ u ∈ L, s = u ++ u} : Language Bool) ↔ f x = true
  rw [PvsNP.Units.tc_closure_double_p.double_eq L]
  exact accepts x
