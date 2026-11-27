import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_closure_del_one_np
import PvsNP.Units.tc_exp_half
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_exp_union

/- Uses bumz's binary insertion map from the settled tc_closure_del_one_np
unit and the self-delimiting pair representation from fr_ladner in the
Apache-2.0 makedotfun/pvsnp library (81a25475d739668f925eea59e7bef587de6cb214). -/
namespace PvsNP.Units.tc_exp_del_one

open PvsNP.Units.tc_closure_del_one_np (one insert_polytime deletion_eq)
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

abbrev inExp (L : Language Bool) : Prop :=
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (tm : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
    (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, tm.time n ≤ 2 ^ (n ^ k) + k

-- Appending a witness w to this input gives exactly the encoding of (x,w).
def padInput (x : List Bool) : List Bool := pairB x []

theorem pad_concat (x w : List Bool) : padInput x ++ w = pairB x w := by
  simp [padInput, pairB, List.append_assoc]

theorem pad_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString padInput :=
  cpt_pairB2 cpt_id (cpt_const [])

def buildWord (b : Bool) (s : List Bool) : List Bool :=
  PvsNP.Units.tc_closure_del_one_np.insert b ((unpairB s).1, (unpairB (unpairB s).2).1)

theorem build_poly (b : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (buildWord b) := by
  have pairInputs : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun s : List Bool => ((unpairB s).1, (unpairB (unpairB s).2).1)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ (cpt_unpairB1_1 cpt_id)
      (cpt_unpairB1_1 (cpt_unpairB2_1 cpt_id))
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    _ (PvsNP.Units.tc_closure_del_one_np.insert b) pairInputs (insert_polytime b)

def witnessLanguage (L : Language Bool) (b : Bool) : Language Bool :=
  {z | ∃ w : List Bool, w.length = z.length ∧ buildWord b (z ++ w) ∈ L}

theorem witness_exp (L : Language Bool) (b : Bool) (hL : inExp L) :
    inExp (witnessLanguage L b) := by
  let pre : Language Bool := {s | buildWord b s ∈ L}
  have hp : inExp pre :=
    PvsNP.Units.m2_exp_down_closed pre L ⟨buildWord b, build_poly b, fun _ => Iff.rfl⟩ hL
  exact PvsNP.Units.tc_exp_half pre hp

theorem encodes_position (L : Language Bool) (b : Bool) (x : List Bool) :
    x ∈ one L b ↔ padInput x ∈ witnessLanguage L b := by
  change (∃ c : List Bool, c.length ≤ x.length ∧ PvsNP.Units.tc_closure_del_one_np.insert b (x, c) ∈ L) ↔
    ∃ w : List Bool, w.length = (padInput x).length ∧ buildWord b (padInput x ++ w) ∈ L
  constructor
  · rintro ⟨c, bound, hit⟩
    let w := pairB c (List.replicate (2 * (x.length - c.length)) false)
    refine ⟨w, ?_, ?_⟩
    · simp only [w, padInput, pairB_length, List.length_replicate, List.length_nil, Nat.add_zero]
      omega
    · simpa only [buildWord, pad_concat, w, unpairB_pairB] using hit
  · rintro ⟨w, length_eq, hit⟩
    have len : w.length = 2 * x.length + 1 := by
      simpa only [padInput, pairB_length, List.length_nil, Nat.add_zero] using length_eq
    have bound := unpairB_length w
    refine ⟨(unpairB w).1, by omega, ?_⟩
    simpa only [buildWord, pad_concat, unpairB_pairB] using hit

theorem closed (L : Language Bool) (hL : inExp L) :
    inExp {x : List Bool | ∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L} := by
  have fixed (b : Bool) : inExp (one L b) :=
    PvsNP.Units.m2_exp_down_closed (one L b) (witnessLanguage L b)
      ⟨padInput, pad_poly, encodes_position L b⟩ (witness_exp L b hL)
  rw [deletion_eq]
  exact PvsNP.Units.m2_exp_union _ _ (fixed false) (fixed true)

end PvsNP.Units.tc_exp_del_one

theorem PvsNP.Units.tc_exp_del_one :
∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  exact PvsNP.Units.tc_exp_del_one.closed
