import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.tc_exp_concat

/-- An accepted prefix may be followed by an arbitrary word. -/
theorem PvsNP.Units.tc_exp_some_prefix :
∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ y : List Bool, y <+: x ∧ y ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L decL
  have arbitraryTail := PvsNP.Units.m2_p_subset_exp Set.univ PvsNP.Units.m2_p_trivial.2
  obtain ⟨k, f, M, accepts, bound⟩ :=
    PvsNP.Units.tc_exp_concat L Set.univ decL arbitraryTail
  refine ⟨k, f, M, ?_, bound⟩
  intro w
  refine Iff.trans ?_ (accepts w)
  constructor
  · rintro ⟨y, ⟨tail, hy⟩, hL⟩
    exact ⟨y, tail, hy.symm, hL, Set.mem_univ _⟩
  · rintro ⟨y, tail, hw, hL, _⟩
    exact ⟨y, ⟨tail, hw.symm⟩, hL⟩
