import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_clause_falsifiers_count

namespace PvsNP.Units.m3_models_count_union_bound

/-- Imposing a predicate can remove at most the elements on which it is false. -/
theorem filter_loss {α : Type} (p q : α → Bool) (xs : List α) :
    (xs.filter q).length ≤ (xs.filter (fun x => p x && q x)).length +
      (xs.filter (fun x => !p x)).length := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    cases hp : p a <;> cases hq : q a <;>
      simp [List.filter_cons, hp, hq] at * <;> omega

end PvsNP.Units.m3_models_count_union_bound

theorem PvsNP.Units.m3_models_count_union_bound :
∀ (n : ℕ) (N : cnf), (∀ C ∈ N, (C.map Prod.snd).Nodup ∧ ∀ l ∈ C, l.2 < n) →
  2 ^ n ≤ ((List.range n).sublists.filter (fun a => evalCnf a N)).length +
    (N.map (fun C => 2 ^ (n - C.length))).sum := by
  intro n N
  induction N with
  | nil =>
    simp [evalCnf, List.length_sublists]
  | cons C Cs ih =>
    intro h
    have hTail := ih (fun D hD => h D (List.mem_cons_of_mem C hD))
    obtain ⟨hnd, hlt⟩ := h C List.mem_cons_self
    have hLoss := PvsNP.Units.m3_models_count_union_bound.filter_loss
      (fun a => evalClause a C) (fun a => evalCnf a Cs) (List.range n).sublists
    rw [PvsNP.Units.m3_clause_falsifiers_count n C hnd hlt] at hLoss
    have hcons (a : assgn) : evalCnf a (C :: Cs) = (evalClause a C && evalCnf a Cs) := by
      simp [evalCnf]
    simp only [hcons, List.map_cons, List.sum_cons]
    omega
