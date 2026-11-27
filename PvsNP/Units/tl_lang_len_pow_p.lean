import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_bounded_unary_search_polytime

namespace PvsNP.Units.tl_lang_len_pow_p_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private theorem pairEncoding : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => pairB p.1 p.2) := by
  have he : PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
    funext ⟨a, b⟩
    simp [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair, PvsNP.encodePair,
      Computability.encodingProd, Computability.encodingList]
  rw [← he]
  exact cpt_pairB

private def leftSide (s : List Bool) : List Bool := mulU [true] (unpairB s).1

private def rightSide (s : List Bool) : List Bool := mulU (mulU (unpairB s).2 (unpairB s).2) (unpairB s).2

private def test (p : List Bool × List Bool) : Bool :=
  let s := pairB p.1 p.2
  decide (leftSide s = rightSide s)

private theorem testPoly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer test := by
  have hLeft : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString leftSide :=
    cpt_mulU2 (cpt_const [true]) cpt_unpairB1
  have hRight : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString rightSide :=
    cpt_mulU2 (cpt_mulU2 cpt_unpairB2 cpt_unpairB2) cpt_unpairB2
  have both := PvsNP.Units.m2_pair_build_polytime _ _ hLeft hRight
  have eqPoly := PvsNP.Units.m2_polytime_comp _ _ _ _ _ both PvsNP.Units.m2_eq_polytime
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _ pairEncoding eqPoly

private theorem test_spec (x : List Bool) (k : ℕ) :
    test (x, List.replicate k true) = true ↔ x.length = k ^ 3 := by
  simp [test, leftSide, rightSide, unpairB_pairB, mulU, un, List.replicate_left_inj, pow_succ]

theorem language :
({x : List Bool | ∃ k : ℕ, x.length = k ^ 3} : Language Bool) ∈ PvsNP.P := by
  refine ⟨_, PvsNP.Units.m2_bounded_unary_search_polytime test testPoly, fun x => ?_⟩
  change (∃ k : ℕ, x.length = k ^ 3) ↔
    (List.range (x.length + 1)).any (fun k => test (x, List.replicate k true)) = true
  simp only [List.any_eq_true, List.mem_range, test_spec]
  constructor
  · rintro ⟨k, h⟩
    refine ⟨k, ?_, h⟩
    have bound : k ≤ k ^ 3 := Nat.le_pow (by decide)
    omega
  · rintro ⟨k, _, h⟩
    exact ⟨k, h⟩

end PvsNP.Units.tl_lang_len_pow_p_aux

theorem PvsNP.Units.tl_lang_len_pow_p :
({x : List Bool | ∃ k : ℕ, x.length = k ^ 3} : Language Bool) ∈ PvsNP.P := by
  exact PvsNP.Units.tl_lang_len_pow_p_aux.language
