import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.tc_exp_concat

/-- A factor may be preceded and followed by arbitrary words. -/
theorem PvsNP.Units.tc_exp_some_factor :
∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ y : List Bool, y <:+: x ∧ y ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L decL
  have allWords := PvsNP.Units.m2_p_subset_exp Set.univ PvsNP.Units.m2_p_trivial.2
  let withSuffix : Language Bool :=
    {w | ∃ y s : List Bool, w = y ++ s ∧ y ∈ L ∧ s ∈ (Set.univ : Language Bool)}
  have suffixMachine := PvsNP.Units.tc_exp_concat L Set.univ decL allWords
  obtain ⟨k, f, M, accepts, bound⟩ :=
    PvsNP.Units.tc_exp_concat Set.univ withSuffix allWords suffixMachine
  refine ⟨k, f, M, ?_, bound⟩
  intro w
  refine Iff.trans ?_ (accepts w)
  constructor
  · rintro ⟨y, ⟨p, s, decomp⟩, hy⟩
    refine ⟨p, y ++ s, ?_, Set.mem_univ _, y, s, rfl, hy, Set.mem_univ _⟩
    simpa only [List.append_assoc] using decomp.symm
  · rintro ⟨p, rest, hw, _, hrest⟩
    change ∃ y s : List Bool, rest = y ++ s ∧ y ∈ L ∧ s ∈ (Set.univ : Language Bool) at hrest
    obtain ⟨y, s, hr, hy, _⟩ := hrest
    refine ⟨y, ⟨p, s, ?_⟩, hy⟩
    simp only [hw, hr, List.append_assoc]
