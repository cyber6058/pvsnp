import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_poly_padding_iff
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_p_subset_exp

namespace PvsNP.Units.m2_exp_poly_padding_iff

open PvsNP.Units.m2_np_poly_padding_iff
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

abbrev inExp (L : Language Bool) : Prop :=
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
    (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k

abbrev padded (L : Language Bool) (m : ℕ) : Language Bool :=
  {s | ∃ y : List Bool, y ∈ L ∧ s = padPoly m y}

theorem decodePad (m : ℕ) (s : List Bool) : dropN (padPoly m s) = s :=
  dropN_un (s.length ^ m) s

theorem padMem (L : Language Bool) (m : ℕ) (x : List Bool) :
    x ∈ L ↔ padPoly m x ∈ padded L m := by
  constructor
  · exact fun hx => ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    have hxy : x = y := by simpa only [decodePad] using congrArg dropN he
    exact hxy.symm ▸ hy

theorem characterize (L : Language Bool) (m : ℕ) :
    padded L m = ({s : List Bool | ∃ x, s = padPoly m x} : Language Bool) ⊓
      {s : List Bool | dropN s ∈ L} := by
  ext s
  change (∃ y : List Bool, y ∈ L ∧ s = padPoly m y) ↔
    (∃ y : List Bool, s = padPoly m y) ∧ dropN s ∈ L
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, (decodePad m y).symm ▸ hy⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, (decodePad m y) ▸ hy, rfl⟩

theorem invariant (L : Language Bool) (m : ℕ) : inExp L ↔ inExp (padded L m) := by
  constructor
  · intro hL
    have shapes := PvsNP.Units.m2_p_subset_exp _ (shape_in_P m)
    have original := PvsNP.Units.m2_exp_down_closed
      ({s : List Bool | dropN s ∈ L} : Language Bool) L ⟨dropN, cpt_dropN, fun _ => Iff.rfl⟩ hL
    rw [characterize]
    exact PvsNP.Units.m2_exp_inter _ _ shapes original
  · intro hPad
    exact PvsNP.Units.m2_exp_down_closed L (padded L m)
      ⟨padPoly m, cpt_padPoly m, padMem L m⟩ hPad

end PvsNP.Units.m2_exp_poly_padding_iff

/-- Polynomial padding preserves exponential-time decidability in both directions. -/
theorem PvsNP.Units.m2_exp_poly_padding_iff :
∀ (L : Language Bool) (m : ℕ),
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ↔
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ ({s : List Bool | ∃ y : List Bool, y ∈ L ∧ s = List.replicate (y.length ^ m) true ++ false :: y} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) := by
  exact PvsNP.Units.m2_exp_poly_padding_iff.invariant
