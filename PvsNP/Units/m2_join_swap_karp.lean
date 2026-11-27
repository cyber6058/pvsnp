import PvsNP.Defs

namespace PvsNP.Units.m2_join_swap_karp

private def swapHead : List Bool → List Bool
  | [] => []
  | b :: xs => (!b) :: xs

-- The input and output use the same stack. Only the top symbol is touched.
private abbrev machine : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstance
  m _ := .pop () (fun _ head => head)
    (.branch (fun head => head.isSome)
      (.push () (fun head => !(head.getD false)) (.load (fun _ => none) .halt))
      .halt)

private theorem oneStep (x : List Bool) :
    machine.step (Turing.initList machine x) =
      some (Turing.haltList machine (swapHead x)) := by
  cases x <;>
    apply congrArg (fun stk : Unit → List Bool =>
      some (⟨none, none, stk⟩ : machine.Cfg)) <;>
    funext k <;> cases k <;> rfl

private theorem swapPoly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString swapHead := by
  refine ⟨{
    tm := machine
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C 1
    outputsFun := ?_
  }⟩
  intro x
  refine { steps := 1, evals_in_steps := ?_, steps_le_m := ?_ }
  · have mapped (w : List Bool) :
        List.map (Equiv.refl Bool).invFun (PvsNP.encodeString w) = w := by
      simp [PvsNP.encodeString, Computability.encodingList]
    change machine.step (Turing.initList machine
        (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x))) =
      some (Turing.haltList machine
        (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString (swapHead x))))
    simpa only [mapped] using (oneStep x)
  · simp

end PvsNP.Units.m2_join_swap_karp

theorem PvsNP.Units.m2_join_swap_karp :
    ∀ L₁ L₂ : Language Bool,
      PvsNP.KarpReducible
        ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool)
        ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₁, x = true :: y)} : Language Bool) := by
  intro L₁ L₂
  refine ⟨PvsNP.Units.m2_join_swap_karp.swapHead,
    PvsNP.Units.m2_join_swap_karp.swapPoly, ?_⟩
  intro x
  change ((∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)) ↔
    ((∃ y ∈ L₂, PvsNP.Units.m2_join_swap_karp.swapHead x = false :: y) ∨
      (∃ y ∈ L₁, PvsNP.Units.m2_join_swap_karp.swapHead x = true :: y))
  cases x with
  | nil => simp [PvsNP.Units.m2_join_swap_karp.swapHead]
  | cons b xs =>
    cases b <;> simp [PvsNP.Units.m2_join_swap_karp.swapHead]
