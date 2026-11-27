import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_pair_add

namespace PvsNP.Units.tf_fun_div_const

def val (x : List Bool) : ℕ := Nat.ofDigits 2 (x.map Bool.toNat)

def readBE (a : ℕ) : List Bool → ℕ
  | [] => a
  | b :: t => readBE (2 * a + b.toNat) t

theorem read_snoc (a : ℕ) (t : List Bool) (b : Bool) :
    readBE a (t ++ [b]) = 2 * readBE a t + b.toNat := by
  induction t generalizing a with
  | nil => rfl
  | cons z t ih => exact ih (2 * a + z.toNat)

theorem read_reverse (x : List Bool) : readBE 0 x.reverse = val x := by
  induction x with
  | nil => rfl
  | cons b t ih =>
    rw [List.reverse_cons, read_snoc, ih]
    simp [val, Nat.ofDigits_cons, Nat.add_comm]

def rem3 (a : ℕ) : Fin 3 := ⟨a % 3, Nat.mod_lt _ (by decide)⟩

def digit (r : Fin 3) (b : Bool) : Bool := decide (3 ≤ 2 * r.val + b.toNat)

def nextRem (r : Fin 3) (b : Bool) : Fin 3 := rem3 (2 * r.val + b.toNat)

/-- Long division reads the most significant bit first and emits one quotient bit. -/
def emit (r : Fin 3) : List Bool → List Bool
  | [] => []
  | b :: t => digit r b :: emit (nextRem r b) t

theorem digit_value (r : Fin 3) (b : Bool) :
    (digit r b).toNat = (2 * r.val + b.toNat) / 3 := by
  fin_cases r <;> cases b <;> decide

theorem quotient_step (a : ℕ) (b : Bool) :
    2 * (a / 3) + (digit (rem3 a) b).toNat = (2 * a + b.toNat) / 3 := by
  rw [digit_value]
  change 2 * (a / 3) + (2 * (a % 3) + b.toNat) / 3 = _
  omega

theorem remainder_step (a : ℕ) (b : Bool) :
    nextRem (rem3 a) b = rem3 (2 * a + b.toNat) := by
  apply Fin.ext
  change (2 * (a % 3) + b.toNat) % 3 = (2 * a + b.toNat) % 3
  omega

theorem read_emit (t : List Bool) (a : ℕ) :
    readBE (a / 3) (emit (rem3 a) t) = readBE a t / 3 := by
  induction t generalizing a with
  | nil => rfl
  | cons b t ih =>
    simp only [emit, readBE, quotient_step, remainder_step]
    exact ih _

def raw (x : List Bool) : List Bool := (emit (rem3 0) x.reverse).reverse

theorem raw_value (x : List Bool) : val (raw x) = val x / 3 := by
  calc
    val (raw x) = readBE 0 (emit (rem3 0) x.reverse) := by
      rw [← read_reverse (raw x)]
      simp only [raw, List.reverse_reverse]
    _ = readBE 0 x.reverse / 3 := by simpa only [Nat.zero_div] using read_emit x.reverse 0
    _ = val x / 3 := by rw [read_reverse]

theorem raw_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString raw := by
  have h := PvsNP.Units.m2_transducer_polytime (Fin 3)
    (fun r b => (nextRem r b, some (digit r b))) (fun _ => none) emit
    (fun _ => rfl) (fun _ _ _ => rfl) (rem3 0)
  have first := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.reverse) (emit (rem3 0)) PvsNP.Units.m2_reverse_polytime h
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => emit (rem3 0) x.reverse) (fun x : List Bool => x.reverse)
    first PvsNP.Units.m2_reverse_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-- Adding zero removes redundant high-order zeros from the transducer output. -/
theorem quotient_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (val x / 3)) := by
  have pair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (raw x, ([] : List Bool))) :=
    cpt_pair raw_poly (constList_polyTime [])
  have machine := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (raw x, ([] : List Bool)))
    (fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2))
    pair PvsNP.Units.tf_fun_pair_add
  have nil_val : val [] = 0 := rfl
  simpa only [Function.comp_def, nil_val, Nat.add_zero, raw_value] using machine

end PvsNP.Units.tf_fun_div_const

theorem PvsNP.Units.tf_fun_div_const :
PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) / 3)) :=
  PvsNP.Units.tf_fun_div_const.quotient_poly
