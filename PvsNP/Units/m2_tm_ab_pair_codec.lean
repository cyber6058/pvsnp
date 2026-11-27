import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_inv_hom_closed
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_self_delimiting_pair

namespace PvsNP.Units.m2_tm_ab_pair_codec_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def copies (x : List Bool) := x.flatMap (fun b => [b, b])
def encoded (x y : List Bool) := copies x ++ [false, true] ++ copies y

theorem encode_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => encoded p.1 p.2) := by
  have cp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString copies :=
    PvsNP.Units.m2_inv_hom_closed.cpt_flatMap (fun b => [b, b])
  have h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => encoded (unpairB s).1 (unpairB s).2) :=
    cpt_app2 (cpt_app2 (cpt_comp (cpt_unpairB1_1 cpt_id) cp) (cpt_const [false, true]))
      (cpt_comp (cpt_unpairB2_1 cpt_id) cp)
  have combine : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        encoded (unpairB (pairB p.1 p.2)).1 (unpairB (pairB p.1 p.2)).2) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) _ PvsNP.Units.m2_tm_self_delimiting_pair.1 h
  simpa only [unpairB_pairB] using combine

-- The state records whether the marker has passed and whether it holds a first bit.
def step (side : Bool) (s : Bool × Option Bool) (b : Bool) :
    (Bool × Option Bool) × Option Bool :=
  match s.2 with
  | none => ((s.1, some b), none)
  | some a =>
    if a = b then ((s.1, none), if side = s.1 then some a else none)
    else ((true, none), none)

def readHalf (side phase : Bool) (x : List Bool) : List Bool :=
  fstRun (step side) (fun _ => none) (phase, none) x

theorem read_poly (side : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (readHalf side false) :=
  PvsNP.Units.m2_transducer_polytime (Bool × Option Bool) (step side) (fun _ => none)
    (fstRun (step side) (fun _ => none)) (fun _ => rfl) (fun _ _ _ => rfl) (false, none)

theorem twice (side phase a : Bool) (tail : List Bool) :
    readHalf side phase (a :: a :: tail) =
      (if side = phase then [a] else []) ++ readHalf side phase tail := by
  cases side <;> cases phase <;> cases a <;> rfl

theorem marker (side : Bool) (tail : List Bool) :
    readHalf side false (false :: true :: tail) = readHalf side true tail := by
  cases side <;> rfl

theorem through (side phase : Bool) (x tail : List Bool) :
    readHalf side phase (copies x ++ tail) =
      (if side = phase then x else []) ++ readHalf side phase tail := by
  induction x with
  | nil => simp [copies]
  | cons a x ih =>
    change readHalf side phase (a :: a :: (copies x ++ tail)) = _
    rw [twice, ih]
    by_cases h : side = phase <;> simp [h]

theorem lastBlock (side phase : Bool) (x : List Bool) :
    readHalf side phase (copies x) = if side = phase then x else [] := by
  have empty : readHalf side phase [] = [] := rfl
  simpa [empty] using through side phase x []

theorem decoded (side : Bool) (x y : List Bool) :
    readHalf side false (encoded x y) = if side then y else x := by
  unfold encoded
  rw [List.append_assoc, through]
  change _ ++ readHalf side false (false :: true :: copies y) = _
  rw [marker, lastBlock]
  cases side <;> simp

end PvsNP.Units.m2_tm_ab_pair_codec_aux

open PvsNP.Units.m2_tm_ab_pair_codec_aux in
theorem PvsNP.Units.m2_tm_ab_pair_codec :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        p.1.flatMap (fun b => [b, b]) ++ [false, true] ++ p.2.flatMap (fun b => [b, b])) ∧
    ∃ D : List Bool → List Bool × List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair D ∧
      ∀ x y : List Bool, D (x.flatMap (fun b => [b, b]) ++ [false, true] ++ y.flatMap (fun b => [b, b])) = (x, y) := by
  refine ⟨encode_poly, fun s => (readHalf false false s, readHalf true false s),
    PvsNP.Units.m2_pair_build_polytime _ _ (read_poly false) (read_poly true), ?_⟩
  intro x y
  change (readHalf false false (encoded x y), readHalf true false (encoded x y)) = (x, y)
  simp only [decoded, Bool.false_eq_true, ite_false, ite_true]
