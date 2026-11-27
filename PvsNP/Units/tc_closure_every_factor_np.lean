import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_reverse_closed
import PvsNP.Units.m2_np_all_prefixes

namespace PvsNP.Units.tc_closure_every_factor_np

theorem allSuffixes (L : Language Bool) (hL : L ∈ PvsNP.NP) :
    ({x : List Bool | ∀ s : List Bool, s <:+ x → s ∈ L} : Language Bool) ∈ PvsNP.NP := by
  let revL : Language Bool := {s | s.reverse ∈ L}
  let prefixes : Language Bool := {x | ∀ p : List Bool, p <+: x → p ∈ revL}
  have hRev : revL ∈ PvsNP.NP := PvsNP.Units.m2_np_reverse_closed L hL
  have hPrefixes : prefixes ∈ PvsNP.NP := PvsNP.Units.m2_np_all_prefixes revL hRev
  have eqv : ({x : List Bool | x.reverse ∈ prefixes} : Language Bool) =
      {x : List Bool | ∀ s : List Bool, s <:+ x → s ∈ L} := by
    ext x
    change (∀ p : List Bool, p <+: x.reverse → p.reverse ∈ L) ↔
      ∀ s : List Bool, s <:+ x → s ∈ L
    constructor
    · intro allPref s hs
      obtain ⟨t, ht⟩ := hs
      have hp : s.reverse <+: x.reverse :=
        ⟨t.reverse, by rw [← ht, List.reverse_append]⟩
      simpa only [List.reverse_reverse] using allPref s.reverse hp
    · intro allSuff p hp
      obtain ⟨t, ht⟩ := hp
      have hs : p.reverse <:+ x := ⟨t.reverse, by
        simpa only [List.reverse_append, List.reverse_reverse] using congrArg List.reverse ht⟩
      exact allSuff p.reverse hs
  rw [← eqv]
  exact PvsNP.Units.m2_np_reverse_closed prefixes hPrefixes

end PvsNP.Units.tc_closure_every_factor_np

/-- A factor is a prefix of a suffix. Apply the two universal closures successively. -/
theorem PvsNP.Units.tc_closure_every_factor_np :
∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  let prefixes : Language Bool := {s | ∀ y : List Bool, y <+: s → y ∈ L}
  have hP : prefixes ∈ PvsNP.NP := PvsNP.Units.m2_np_all_prefixes L hL
  have eqv : ({x : List Bool | ∀ s : List Bool, s <:+ x → s ∈ prefixes} : Language Bool) =
      {x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} := by
    ext x
    change (∀ s : List Bool, s <:+ x → ∀ y : List Bool, y <+: s → y ∈ L) ↔
      ∀ y : List Bool, y <:+: x → y ∈ L
    constructor
    · intro bySuffix y hy
      obtain ⟨p, t, ht⟩ := hy
      exact bySuffix (y ++ t) ⟨p, by simpa only [List.append_assoc] using ht⟩ y ⟨t, rfl⟩
    · intro byFactor s hs y hy
      obtain ⟨p, hp⟩ := hs
      obtain ⟨t, ht⟩ := hy
      exact byFactor y ⟨p, t, by simpa only [List.append_assoc, ht] using hp⟩
  rw [← eqv]
  exact PvsNP.Units.tc_closure_every_factor_np.allSuffixes prefixes hP
