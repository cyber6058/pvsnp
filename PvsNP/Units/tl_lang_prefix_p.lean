import Mathlib
import PvsNP.Defs
import CookLevin

/-
The helpers initList_eq and haltList_eq are adapted from the accepted unit
PvsNP/Units/m2_np_down_closed.lean of github.com/makedotfun/pvsnp at commit
5905c4924bb3bf8698c59a5ab078a07d9a489fff (Apache License 2.0), itself adapted from
github.com/brilliant-hq/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9
(Apache License 2.0), file lean/PEqualNP/Library/Machines/Run.lean. MODIFIED: restated inside the
namespace PvsNP.Units.m2_dfa_in_p. The automaton machine and its run are written for this unit.
-/

/-
SPDX-License-Identifier: Apache-2.0
Adapted from the settled PvsNP/Units/m2_dfa_in_p.lean in
https://github.com/makedotfun/pvsnp at 81a25475d739668f925eea59e7bef587de6cb214,
under the Apache License, Version 2.0. The source header above is retained verbatim.
Modifications: move the DFA machine and its proof
to this unit's helper namespace, and specialize it to the two-true-bit prefix.
-/

namespace PvsNP.Units.tl_lang_prefix_p_aux

open Turing

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

variable {Q : Type}

/-- What a pop does to the internal state: read a bit, or notice the end of the input. -/
def popFn (δ : Q → Bool → Q) (s : Q × Bool) (o : Option Bool) : Q × Bool :=
  match o with
  | some b => (δ s.1 b, true)
  | none => (s.1, false)

/-- The program: read the input bit by bit through the automaton, then write the answer. -/
def dfaProg (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool) :
    Unit → TM2.Stmt (fun _ : Unit => Bool) Unit (Q × Bool) :=
  fun _ => .pop () (popFn δ)
    (.branch (fun s => s.2)
      (.load (fun s => (s.1, false)) (.goto fun _ => ()))
      (.push () (fun s => F s.1) (.load (fun _ => (q₀, false)) .halt)))

/-- The machine. -/
def dfaTM [Fintype Q] (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Q × Bool
  initialState := (q₀, false)
  m := dfaProg δ q₀ F

/-- Configurations of the machine. -/
abbrev DCfg (Q : Type) : Type := TM2.Cfg (fun _ : Unit => Bool) Unit (Q × Bool)

theorem update_unit (S T : List Bool) :
    Function.update (fun _ : Unit => S) () T = fun _ => T := by
  funext k
  simp

theorem dfa_cons (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool) (q : Q) (x : Bool) (a : List Bool) :
    TM2.step (dfaProg δ q₀ F) (⟨some (), (q, false), fun _ => x :: a⟩ : DCfg Q) =
      some ⟨some (), (δ q x, false), fun _ => a⟩ := by
  simp only [TM2.step, dfaProg, TM2.stepAux]
  rw [update_unit]
  simp [popFn]

theorem dfa_nil (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool) (q : Q) :
    TM2.step (dfaProg δ q₀ F) (⟨some (), (q, false), fun _ => []⟩ : DCfg Q) =
      some ⟨none, (q₀, false), fun _ => [F q]⟩ := by
  simp only [TM2.step, dfaProg, TM2.stepAux]
  rw [update_unit]
  simp only [List.head?_nil, popFn, Bool.cond_false, List.tail_nil]
  rw [update_unit]

theorem dfa_loop (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool) (a : List Bool) (q : Q) :
    (flip bind (TM2.step (dfaProg δ q₀ F)))^[a.length + 1]
        (some (⟨some (), (q, false), fun _ => a⟩ : DCfg Q)) =
      some ⟨none, (q₀, false), fun _ => [F (a.foldl δ q)]⟩ := by
  induction a generalizing q with
  | nil => exact dfa_nil δ q₀ F q
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (dfaProg δ q₀ F))
        (some (⟨some (), (q, false), fun _ => x :: a⟩ : DCfg Q)) =
        some ⟨some (), (δ q x, false), fun _ => a⟩ := dfa_cons δ q₀ F q x a
    rw [e, ih]
    rfl

theorem dfa_run [Fintype Q] (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool) (a : List Bool) :
    (flip bind (TM2.step (dfaProg δ q₀ F)))^[a.length + 1]
        (some (initList (dfaTM δ q₀ F) a)) =
      some (haltList (dfaTM δ q₀ F) [F (a.foldl δ q₀)]) := by
  refine (congrArg (fun c => (flip bind (TM2.step (dfaProg δ q₀ F)))^[a.length + 1]
    (some c)) (initList_eq (dfaTM δ q₀ F) a)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (dfaTM δ q₀ F) [F (a.foldl δ q₀)])).symm)
  show (flip bind (TM2.step (dfaProg δ q₀ F)))^[a.length + 1]
    (some (⟨some (), (q₀, false), Function.update (fun _ => []) () a⟩ : DCfg Q)) =
    some (⟨none, (q₀, false), Function.update (fun _ => []) () [F (a.foldl δ q₀)]⟩ : DCfg Q)
  rw [update_unit, update_unit]
  exact dfa_loop δ q₀ F a q₀

/-- The automaton's yes/no function is computable in `n + 1` steps. -/
theorem dfa_polyTime [Fintype Q] (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x : List Bool => x)
      (fun b : Bool => [b]) (fun x : List Bool => F (x.foldl δ q₀))) :=
  ⟨{
    tm := dfaTM δ q₀ F
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun a =>
      { steps := a.length + 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun x => (flip bind (TM2.step (dfaProg δ q₀ F)))^[a.length + 1]
            (some (initList (dfaTM δ q₀ F) x))) (hm a)).trans
            ((dfa_run δ q₀ F a).trans
              (congrArg (fun x => some (haltList (dfaTM δ q₀ F) x))
                (hm [F (a.foldl δ q₀)]).symm))
        steps_le_m := by simp } }⟩

-- A state with first component true has made its permanent decision. Before then,
-- the second component records whether the first required true bit has been seen.
def advance (q : Bool × Bool) (bit : Bool) : Bool × Bool :=
  if q.1 then q else if bit then (q.2, true) else (true, false)

def accept (q : Bool × Bool) : Bool := q.1 && q.2

theorem locked (answer : Bool) (rest : List Bool) :
    rest.foldl advance (true, answer) = (true, answer) := by
  induction rest with
  | nil => rfl
  | cons b t ih => exact ih

theorem correct (x : List Bool) :
    ([true, true] <+: x) ↔ accept (x.foldl advance (false, false)) = true := by
  cases x with
  | nil => decide
  | cons bit₁ rest =>
    cases bit₁ with
    | false =>
      change _ ↔ accept (rest.foldl advance (true, false)) = true
      rw [locked]
      simp [List.IsPrefix, accept]
    | true =>
      cases rest with
      | nil => decide
      | cons bit₂ tail =>
        cases bit₂ with
        | false =>
          change _ ↔ accept (tail.foldl advance (true, false)) = true
          rw [locked]
          simp [List.IsPrefix, accept]
        | true =>
          change _ ↔ accept (tail.foldl advance (true, true)) = true
          rw [locked]
          simp [List.IsPrefix, accept]

theorem prefix_decidable : ({x : List Bool | [true, true] <+: x} : Language Bool) ∈ PvsNP.P :=
  ⟨fun x => accept (x.foldl advance (false, false)),
    dfa_polyTime advance (false, false) accept, correct⟩

end PvsNP.Units.tl_lang_prefix_p_aux

theorem PvsNP.Units.tl_lang_prefix_p :
({x : List Bool | [true, true] <+: x} : Language Bool) ∈ PvsNP.P := by
  exact PvsNP.Units.tl_lang_prefix_p_aux.prefix_decidable
