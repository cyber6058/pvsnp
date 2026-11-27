import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tr_rel_val_coprime
import PvsNP.Units.tf_fun_pair_mul
import PvsNP.Units.m2_tm_self_delimiting_pair

/- The binary arithmetic, pairing and time-composition lemmas used here come from
the Apache-2.0 makedotfun/pvsnp library at 81a25475d739668f925eea59e7bef587de6cb214.
The search below tests one quotient bit per dividend bit. -/
namespace PvsNP.Units.tf_fun_pair_gcd_aux

open PvsNP.Units.tr_rel_val_coprime
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

abbrev Poly (f : List Bool → List Bool) :=
  PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f

def numerator (s : List Bool) : List Bool := (unpairB s).1
def denominator (s : List Bool) : List Bool := (unpairB s).2
def quotientValue (s : List Bool) : ℕ := val (numerator s) / val (denominator s)

def product (a b : List Bool) : List Bool := Nat.bits (val a * val b)

theorem poly_product {f g : List Bool → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun s => product (f s) (g s)) :=
  cpt_comp (f := fun x => (f x, g x))
    (g := fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2))
    (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.tf_fun_pair_mul

def packed (x r t : List Bool) : List Bool := pairB x (pairB r t)
def word (s : List Bool) : List Bool := (unpairB s).1
def prefixBits (s : List Bool) : List Bool := (unpairB (unpairB s).2).1
def todo (s : List Bool) : List Bool := (unpairB (unpairB s).2).2

-- The current quotient prefix is little endian. The untested low bits of a trial are zero.
def trial (s : List Bool) : List Bool :=
  (todo s).tail.map (fun _ => false) ++ true :: prefixBits s

def allowed (s : List Bool) : Bool := decide (val (product (trial s) (denominator (word s))) ≤ val (numerator (word s)))

def advance (s : List Bool) : List Bool :=
  if allowed s = true then packed (word s) (true :: prefixBits s) (todo s).tail
  else packed (word s) (false :: prefixBits s) (todo s).tail

theorem poly_advance : Poly advance := by
  have hw : Poly word := cpt_unpairB1_1 cpt_id
  have hp : Poly prefixBits := cpt_unpairB1_1 (cpt_unpairB2_1 cpt_id)
  have ht : Poly todo := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_id)
  have htail : Poly (fun s => (todo s).tail) := cpt_comp ht cpt_tailStr
  have htrial : Poly trial := cpt_app2 (cpt_comp htail cpt_zeroPad) (cpt_cons1 true hp)
  have hallow : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer allowed :=
    cpt_binLe_fun _ _ (poly_product htrial (cpt_unpairB2_1 hw)) (cpt_unpairB1_1 hw)
  have branch (b : Bool) : Poly (fun s => packed (word s) (b :: prefixBits s) (todo s).tail) :=
    cpt_pairB2 hw (cpt_pairB2 (cpt_cons1 b hp) htail)
  exact PvsNP.Units.m2_ite_polytime _ _ _ hallow (branch true) (branch false)

theorem advance_length (s : List Bool) : (advance s).length ≤ s.length + 4 := by
  have h₁ := unpairB_weighted s
  have h₂ := unpairB_weighted (unpairB s).2
  change 2 * (word s).length + (unpairB s).2.length ≤ s.length at h₁
  change 2 * (prefixBits s).length + (todo s).length ≤ (unpairB s).2.length at h₂
  unfold advance
  split <;> simp only [packed, pairB_length, List.length_cons, List.length_tail] <;> omega

theorem advance_packed (x r t : List Bool) (b : Bool) (positive : 0 < val (denominator x)) :
    advance (packed x r (b :: t)) =
      if (2 * val r + 1) * 2 ^ t.length ≤ quotientValue x
      then packed x (true :: r) t else packed x (false :: r) t := by
  have digit : val (trial (packed x r (b :: t))) = (2 * val r + 1) * 2 ^ t.length := by
    have zeros (n : ℕ) : val (List.replicate n false) = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, val_cons, ih]
    simp [trial, packed, todo, prefixBits, unpairB_pairB, val_append, val_cons, zeros] <;> ring
  have check : allowed (packed x r (b :: t)) =
      decide ((2 * val r + 1) * 2 ^ t.length ≤ quotientValue x) := by
    unfold allowed product
    rw [val_bits, digit]
    simp only [word, packed, unpairB_pairB, quotientValue, Nat.le_div_iff_mul_le positive]
  rw [advance, check]
  simp only [decide_eq_true_eq, word, prefixBits, todo, packed, unpairB_pairB, List.tail_cons]

-- With d positions remaining, the quotient lies in [val(r)*2^d, (val(r)+1)*2^d).
theorem finish (x r t : List Bool) (positive : 0 < val (denominator x))
    (lo : val r * 2 ^ t.length ≤ quotientValue x)
    (hi : quotientValue x < (val r + 1) * 2 ^ t.length) :
    val (prefixBits (advance^[t.length] (packed x r t))) = quotientValue x := by
  induction t generalizing r with
  | nil =>
    simp only [List.length_nil, pow_zero, Nat.mul_one] at lo hi
    simp only [List.length_nil, Function.iterate_zero_apply, prefixBits, packed, unpairB_pairB]
    omega
  | cons b t ih =>
    rw [List.length_cons, Function.iterate_succ_apply, advance_packed x r t b positive]
    rw [List.length_cons, pow_succ] at lo hi
    by_cases bit : (2 * val r + 1) * 2 ^ t.length ≤ quotientValue x
    · rw [if_pos bit]
      apply ih (true :: r)
      · simpa [val_cons, Nat.add_comm] using bit
      · simp only [val_cons, Bool.toNat_true]
        convert hi using 1 <;> ring
    · rw [if_neg bit]
      apply ih (false :: r)
      · simp only [val_cons, Bool.toNat_false, Nat.zero_add]
        convert lo using 1 <;> ring
      · simpa only [val_cons, Bool.toNat_false, Nat.zero_add] using Nat.lt_of_not_ge bit

def digits (s : List Bool) : List Bool :=
  prefixBits (advance^[(numerator s).length] (packed s [] (numerator s)))

theorem poly_digits : Poly digits := by
  have hn : Poly numerator := cpt_unpairB1_1 cpt_id
  have start : Poly (fun x => packed x [] (numerator x)) :=
    cpt_pairB2 cpt_id (cpt_pairB2 (cpt_const []) hn)
  have run : Poly (fun x => advance^[(numerator x).length] (packed x [] (numerator x))) :=
    cpt_iterGrow poly_advance 4 advance_length hn start
  exact cpt_unpairB1_1 (cpt_unpairB2_1 run)

theorem digits_correct (x : List Bool) (positive : 0 < val (denominator x)) :
    val (digits x) = quotientValue x := by
  apply finish x [] (numerator x) positive
  · simp [val]
  · simpa [quotientValue, val] using lt_of_le_of_lt (Nat.div_le_self (val (numerator x)) (val (denominator x)))
      (val_lt_two_pow (numerator x))

def quotient (s : List Bool) : List Bool :=
  if decide (val (denominator s) ≤ val []) = true then [] else canon (digits s)

theorem poly_quotient : Poly quotient := by
  have test : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide (val (denominator s) ≤ val [])) :=
    cpt_binLe_fun _ _ (cpt_unpairB2_1 cpt_id) (cpt_const [])
  exact PvsNP.Units.m2_ite_polytime _ _ _ test (cpt_const []) (cpt_binAdd_fun _ _ poly_digits (cpt_const []))

theorem value (x : List Bool) : quotient x = Nat.bits (quotientValue x) := by
  have zero : val [] = 0 := rfl
  by_cases h : val (denominator x) = 0
  · simp [quotient, quotientValue, h, zero, Nat.zero_bits]
  · have pos := Nat.pos_of_ne_zero h
    simp [quotient, zero, h, canon_eq, digits_correct x pos]

def remainder (s : List Bool) : List Bool :=
  binSub (canon (numerator s)) (product (denominator s) (quotient s))

theorem poly_remainder : Poly remainder :=
  cpt_binSub_fun _ _ (cpt_binAdd_fun _ _ (cpt_unpairB1_1 cpt_id) (cpt_const []))
    (poly_product (cpt_unpairB2_1 cpt_id) poly_quotient)

theorem on_pair (a b : List Bool) : remainder (pairB a b) = Nat.bits (val a % val b) := by
  unfold remainder product
  rw [value, val_bits, canon_eq]
  simp only [quotientValue, numerator, denominator, unpairB_pairB]
  rw [binSub_eq (Nat.mul_div_le (val a) (val b)), Nat.mod_eq_sub_mul_div]

theorem rem_spec (s : List Bool) :
    remainder s = Nat.bits (val (numerator s) % val (denominator s)) := by
  unfold remainder product
  rw [value, val_bits, canon_eq]
  unfold quotientValue
  rw [binSub_eq (Nat.mul_div_le _ _), Nat.mod_eq_sub_mul_div]

def euclid (s : List Bool) : List Bool :=
  pairB (remainder s) (remainder (pairB (denominator s) (remainder s)))

theorem euclid_poly : Poly euclid := by
  have inner : Poly (fun s => pairB (denominator s) (remainder s)) :=
    cpt_pairB2 (cpt_unpairB2_1 cpt_id) poly_remainder
  exact cpt_pairB2 poly_remainder (cpt_comp inner poly_remainder)

theorem euclid_length (s : List Bool) : (euclid s).length ≤ s.length + 1 := by
  have rBound : (remainder s).length ≤ (numerator s).length := by
    rw [rem_spec]
    exact bits_length_le_of_lt_two_pow (lt_of_le_of_lt (Nat.mod_le _ _) (val_lt_two_pow _))
  have tBound : (remainder (pairB (denominator s) (remainder s))).length ≤ (denominator s).length := by
    rw [on_pair]
    exact bits_length_le_of_lt_two_pow (lt_of_le_of_lt (Nat.mod_le _ _) (val_lt_two_pow _))
  have weight := unpairB_weighted s
  change 2 * (numerator s).length + (denominator s).length ≤ s.length at weight
  simp only [euclid, pairB_length]
  omega

theorem euclid_pair (a b : ℕ) : euclid (pairB (Nat.bits a) (Nat.bits b)) =
    pairB (Nat.bits (a % b)) (Nat.bits (b % (a % b))) := by
  simp only [euclid, on_pair, denominator, unpairB_pairB, val_bits]

theorem twice_gcd (a b : ℕ) : Nat.gcd (a % b) (b % (a % b)) = Nat.gcd a b := by
  calc
    _ = Nat.gcd (b % (a % b)) (a % b) := Nat.gcd_comm _ _
    _ = Nat.gcd (a % b) b := (Nat.gcd_rec _ _).symm
    _ = Nat.gcd b a := (Nat.gcd_rec _ _).symm
    _ = Nat.gcd a b := Nat.gcd_comm _ _

theorem small_mod (b r t : ℕ) (hr : 0 < r) (hle : r ≤ b) (hb : b < t + t) : b % r < t := by
  by_cases h : r ≤ t
  · exact lt_of_lt_of_le (Nat.mod_lt b hr) h
  · rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (show b - r < r by omega)]
    omega

def total (s : List Bool) := binAdd (numerator s) (denominator s)

theorem finished (k a b : ℕ) (bound : a = 0 ∨ b < 2 ^ k) :
    total (euclid^[k] (pairB (Nat.bits a) (Nat.bits b))) = Nat.bits (Nat.gcd a b) := by
  induction k generalizing a b with
  | zero =>
    have emptyValue : val [] = 0 := rfl
    rcases bound with ha | hb
    · subst a
      simp [total, numerator, denominator, unpairB_pairB, binAdd, val_bits, emptyValue]
    · have bz : b = 0 := by simpa using hb
      subst b
      simp [total, numerator, denominator, unpairB_pairB, binAdd, val_bits, emptyValue]
  | succ k ih =>
    rw [Function.iterate_succ_apply, euclid_pair]
    have nextBound : a % b = 0 ∨ b % (a % b) < 2 ^ k := by
      rcases bound with ha | hb
      · subst a
        exact Or.inl (Nat.zero_mod _)
      · by_cases rem : a % b = 0
        · exact Or.inl rem
        · right
          by_cases bz : b = 0
          · subst b
            simp
          · apply small_mod b (a % b) (2 ^ k) (Nat.pos_of_ne_zero rem)
              (Nat.le_of_lt (Nat.mod_lt a (Nat.pos_of_ne_zero bz)))
            simpa [pow_succ, Nat.mul_two] using hb
    rw [ih _ _ nextBound, twice_gcd]

def initial (s : List Bool) : List Bool := pairB (canon (numerator s)) (canon (denominator s))
def gcdBits (s : List Bool) : List Bool := total (euclid^[(denominator s).length] (initial s))

theorem gcd_poly : Poly gcdBits := by
  have hn : Poly numerator := cpt_unpairB1_1 cpt_id
  have hd : Poly denominator := cpt_unpairB2_1 cpt_id
  have hi : Poly initial := cpt_pairB2 (cpt_binAdd_fun _ _ hn (cpt_const []))
    (cpt_binAdd_fun _ _ hd (cpt_const []))
  have machine := cpt_iterGrow euclid_poly 1 euclid_length hd hi
  exact cpt_binAdd_fun _ _ (cpt_unpairB1_1 machine) (cpt_unpairB2_1 machine)

theorem gcd_pair (a b : List Bool) : gcdBits (pairB a b) = Nat.bits (Nat.gcd (val a) (val b)) := by
  simp only [gcdBits, initial, numerator, denominator, unpairB_pairB, canon_eq]
  exact finished b.length _ _ (Or.inr (val_lt_two_pow b))

theorem from_packed (F : List Bool → List Bool) (G : List Bool × List Bool → List Bool)
    (hF : Poly F) (hG : ∀ p : List Bool × List Bool, F (pairB p.1 p.2) = G p) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString G := by
  have composed : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => F (pairB p.1 p.2)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) F
      PvsNP.Units.m2_tm_self_delimiting_pair.1 hF
  rwa [funext hG] at composed

theorem poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => Nat.bits (Nat.gcd (val p.1) (val p.2))) :=
  from_packed gcdBits _ gcd_poly (fun p => gcd_pair p.1 p.2)

end PvsNP.Units.tf_fun_pair_gcd_aux

theorem PvsNP.Units.tf_fun_pair_gcd :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.gcd (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat)) (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) :=
  PvsNP.Units.tf_fun_pair_gcd_aux.poly
