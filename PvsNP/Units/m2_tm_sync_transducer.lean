import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_pair_zip_polytime
import PvsNP.Units.m2_transducer_polytime

namespace PvsNP.Units.m2_tm_sync_transducer_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

def advance {Q : Type} (δ : Q → Bool → Bool → Q × Option Bool)
    (s : Q × Option Bool) (b : Bool) : (Q × Option Bool) × Option Bool :=
  match s.2 with
  | none => ((s.1, some b), none)
  | some a => (((δ s.1 a b).1, none), (δ s.1 a b).2)

def run {Q : Type} (δ : Q → Bool → Bool → Q × Option Bool) :
    Q × Option Bool → List Bool → List Bool :=
  fstRun (advance δ) (fun _ => none)

def interleave (x y : List Bool) : List Bool :=
  (List.zipWith (fun a b => [a, b]) x y).flatten

theorem poly {Q : Type} [Fintype Q] (δ : Q → Bool → Bool → Q × Option Bool) (q : Q) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (run δ (q, none)) :=
  PvsNP.Units.m2_transducer_polytime (Q × Option Bool) (advance δ) (fun _ => none)
    (run δ) (fun _ => rfl) (fun _ _ _ => rfl) (q, none)

theorem correct {Q : Type} (δ : Q → Bool → Bool → Q × Option Bool)
    (F : Q → List Bool → List Bool → List Bool)
    (hx : ∀ q y, F q [] y = [])
    (hy : ∀ q a x, F q (a :: x) [] = [])
    (hab : ∀ q a b x y, F q (a :: x) (b :: y) = (δ q a b).2.toList ++ F (δ q a b).1 x y)
    (q : Q) (x y : List Bool) : run δ (q, none) (interleave x y) = F q x y := by
  induction x generalizing q y with
  | nil =>
    exact (hx q y).symm
  | cons a x ih =>
    cases y with
    | nil => exact (hy q a x).symm
    | cons b y =>
      change (δ q a b).2.toList ++ run δ ((δ q a b).1, none) (interleave x y) =
        F q (a :: x) (b :: y)
      rw [hab, ih]

end PvsNP.Units.m2_tm_sync_transducer_aux

theorem PvsNP.Units.m2_tm_sync_transducer :
    ∀ (Q : Type) [Fintype Q] (δ : Q → Bool → Bool → Q × Option Bool)
      (F : Q → List Bool → List Bool → List Bool),
      (∀ (q : Q) (y : List Bool), F q [] y = []) →
      (∀ (q : Q) (a : Bool) (x : List Bool), F q (a :: x) [] = []) →
      (∀ (q : Q) (a b : Bool) (x y : List Bool),
        F q (a :: x) (b :: y) = (δ q a b).2.toList ++ F (δ q a b).1 x y) →
      ∀ q₀ : Q, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => F q₀ p.1 p.2) := by
  intro Q _ δ F hx hy hab q
  have composed : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        m2_tm_sync_transducer_aux.run δ (q, none) (m2_tm_sync_transducer_aux.interleave p.1 p.2)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      (fun p : List Bool × List Bool => m2_tm_sync_transducer_aux.interleave p.1 p.2)
      (m2_tm_sync_transducer_aux.run δ (q, none)) PvsNP.Units.m2_tm_pair_zip_polytime
      (m2_tm_sync_transducer_aux.poly δ q)
  simpa only [m2_tm_sync_transducer_aux.correct δ F hx hy hab] using composed
