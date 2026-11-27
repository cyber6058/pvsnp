import PvsNP.Defs

/-- Taking the complement of both languages preserves the reduction function. -/
theorem PvsNP.Units.m2_nphard_iff_compl_conphard :
    ∀ L : Language Bool, PvsNP.NPHard L ↔ ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' Lᶜ := by
  classical
  intro L
  constructor
  · intro hard K hK
    change Kᶜ ∈ PvsNP.NP at hK
    obtain ⟨f, hf, correct⟩ := hard Kᶜ hK
    refine ⟨f, hf, fun x => ?_⟩
    have h : (¬ x ∈ K) ↔ f x ∈ L := correct x
    change (x ∈ K) ↔ ¬ (f x ∈ L)
    simpa only [not_not] using (not_congr h)
  · intro hard K hK
    have hdual : Kᶜ ∈ PvsNP.coNP := by
      change (Kᶜ)ᶜ ∈ PvsNP.NP
      simpa only [compl_compl] using hK
    obtain ⟨f, hf, correct⟩ := hard Kᶜ hdual
    refine ⟨f, hf, fun x => ?_⟩
    have h : (¬ x ∈ K) ↔ ¬ (f x ∈ L) := correct x
    simpa only [not_not] using (not_congr h)
