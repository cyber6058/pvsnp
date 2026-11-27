import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_np_down_closed

open PvsNP.Units.m2_np_projection.PEqualNP.Library.Machines
open PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal

theorem PvsNP.Units.m2_self_concat_preimage :
    ∀ L : Language Bool,
      (L ∈ PvsNP.P → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.P) ∧
      (L ∈ PvsNP.NP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.NP) ∧
      (L ∈ PvsNP.coNP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.coNP) := by
  intro L
  have red : PvsNP.KarpReducible ({x : List Bool | x ++ x ∈ L} : Language Bool) L :=
    ⟨fun x => x ++ x, cpt_app2 cpt_id cpt_id, fun _ => Iff.rfl⟩
  exact ⟨m2_p_down_closed _ L red, m2_np_down_closed _ L red, m2_conp_down_closed _ L red⟩
