import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_lub
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_trans

namespace PvsNP.Units.m2_join_assoc_karp_aux

abbrev tagged (A B : Language Bool) : Language Bool :=
  {x | (∃ y ∈ A, x = false :: y) ∨ (∃ y ∈ B, x = true :: y)}

theorem merge (A B C D : Language Bool)
    (ha : PvsNP.KarpReducible A (tagged C D))
    (hb : PvsNP.KarpReducible B (tagged C D)) :
    PvsNP.KarpReducible (tagged A B) (tagged C D) := by
  apply PvsNP.Units.m2_join_lub A B (tagged C D) ha hb
  refine ⟨[], ?_⟩
  rintro (⟨y, _, impossible⟩ | ⟨y, _, impossible⟩) <;> cases impossible

theorem reassociate (A B C : Language Bool) :
    PvsNP.KarpReducible (tagged (tagged A B) C) (tagged A (tagged B C)) ∧
    PvsNP.KarpReducible (tagged A (tagged B C)) (tagged (tagged A B) C) := by
  have ab := PvsNP.Units.m2_join_karp_sides A B
  have bc := PvsNP.Units.m2_join_karp_sides B C
  have leftTree := PvsNP.Units.m2_join_karp_sides (tagged A B) C
  have rightTree := PvsNP.Units.m2_join_karp_sides A (tagged B C)
  constructor
  · apply merge
    · apply merge
      · exact rightTree.1
      · exact PvsNP.Units.m2_karp_trans _ _ _ bc.1 rightTree.2
    · exact PvsNP.Units.m2_karp_trans _ _ _ bc.2 rightTree.2
  · apply merge
    · exact PvsNP.Units.m2_karp_trans _ _ _ ab.1 leftTree.1
    · apply merge
      · exact PvsNP.Units.m2_karp_trans _ _ _ ab.2 leftTree.1
      · exact leftTree.2

end PvsNP.Units.m2_join_assoc_karp_aux

theorem PvsNP.Units.m2_join_assoc_karp :
∀ L₁ L₂ L₃ : Language Bool,
  PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool), x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool)
      ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool), x = true :: y)} : Language Bool) ∧
    PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool), x = true :: y)} : Language Bool)
      ({x : List Bool | (∃ y ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool), x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool) := by
  exact PvsNP.Units.m2_join_assoc_karp_aux.reassociate
