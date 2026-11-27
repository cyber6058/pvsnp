import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_closure_double_p
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_conp_inter
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_subset_np

/-- Intersect the square words with the preimage of the language under the first-half map. -/
theorem PvsNP.Units.tc_closure_double_conp :
∀ L : Language Bool, L ∈ PvsNP.coNP → ({x : List Bool | ∃ u ∈ L, x = u ++ u} : Language Bool) ∈ PvsNP.coNP := by
  intro L hL
  have squares : ({x : List Bool | ∃ u : List Bool, x = u ++ u} : Language Bool) ∈ PvsNP.coNP :=
    PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_p_compl _ PvsNP.Units.m2_ww_in_p)
  rw [PvsNP.Units.tc_closure_double_p.double_eq L]
  apply PvsNP.Units.m2_conp_inter _ _ squares
  refine PvsNP.Units.m2_conp_down_closed _ L ?_ hL
  exact ⟨fun x => x.take (x.length / 2), PvsNP.Units.tc_closure_double_p.cpt_takeHalf,
    fun _ => Iff.rfl⟩
