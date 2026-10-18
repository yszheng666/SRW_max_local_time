import SRWTightness.SourceOriginalJointRootBound

open MeasureTheory
namespace SRWTightness

/-- Aggregate the two conditional comparisons for any common-space event, including the complete
remaining-success event, while retaining the original joint root-count law. -/
theorem source_event_original_joint_root_bound (t A γ : ℝ) (b w : Site) (I₀ I₁ ν J : ℕ)
    (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
    (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))
    (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
    (hcap₀ : sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ≤ 1)
    (hcap₁ : sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset w (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ≤ 1)
    (S : Set (Sample × (Site → ℕ → GaussianCoefficientSpace)))
    (G : Set ExteriorPathRecord) (Q : ExteriorPathRecord → ℕ → ℕ → ℝ) (E F : ℝ) :
    let Z := sourcePairExteriorRecord t b w ν J
    let X := sourceActualCount t b ν
    let Y := sourceActualCount t w ν
    let N := sourceEarlyRootCap t ν
    let p := sourceContinuationProbability t A γ b I₀ z₀ ν
    let q := sourceContinuationProbability t A γ w I₁ z₁ ν
    (∀ h, 0 < sourceEnlargedLaw.real {v | Z v.1 = h} → ∀ k l : ℕ, k ≤ N → l ≤ N →
      (sourceEnlargedLaw.restrict S).real {v | Z v.1 = h ∧ X v.1 = k ∧ Y v.1 = l} /
        sourceEnlargedLaw.real {v | Z v.1 = h} ≤ Real.exp E * (Q h k l * (p k * q l))) →
    (∀ h, 0 < sourceEnlargedLaw.real {v | Z v.1 = h} → ∀ k l : ℕ, k ≤ N → l ≤ N →
      Q h k l ≤ Real.exp F *
        (sourceEnlargedLaw.real {v | Z v.1 = h ∧ X v.1 = k ∧ Y v.1 = l} /
          sourceEnlargedLaw.real {v | Z v.1 = h})) →
    sourceEnlargedLaw.real {v | v ∈ S ∧ Z v.1 ∈ G ∧ X v.1 ≤ N ∧ Y v.1 ≤ N} ≤
      Real.exp (E + F) * ∫ ω,
        {u : Sample | Z u ∈ G ∧ X u ≤ N ∧ Y u ≤ N}.indicator
          (fun u ↦ p (X u) * q (Y u)) ω ∂pathLaw := by
  classical
  dsimp only
  intro hupper hlower
  letI : MeasurableSpace ExteriorPathRecord := ⊤
  have hZ : Measurable (sourcePairExteriorRecord t b w ν J) :=
    measurable_killedExteriorRecord _ _ _ _ _
  have hb := original_joint_root_bound sourceEnlargedLaw
    (fun v ↦ sourcePairExteriorRecord t b w ν J v.1)
    (fun v ↦ sourceActualCount t b ν v.1) (fun v ↦ sourceActualCount t w ν v.1)
    (hZ.comp measurable_fst) ((measurable_sourceActualCount t b ν).comp measurable_fst)
    ((measurable_sourceActualCount t w ν).comp measurable_fst)
    S G (sourceEarlyRootCap t ν)
    (sourceContinuationProbability t A γ b I₀ z₀ ν)
    (sourceContinuationProbability t A γ w I₁ z₁ ν)
    (fun k ↦ source_continuation_probability_mem t A γ b I₀ z₀ ν k hα hcap₀)
    (fun k ↦ source_continuation_probability_mem t A γ w I₁ z₁ ν k hα hcap₁)
    Q E F hupper hlower
  let f : Sample → ℝ := fun ω ↦
    {u : Sample | sourcePairExteriorRecord t b w ν J u ∈ G ∧
      sourceActualCount t b ν u ≤ sourceEarlyRootCap t ν ∧
      sourceActualCount t w ν u ≤ sourceEarlyRootCap t ν}.indicator
      (fun u ↦ sourceContinuationProbability t A γ b I₀ z₀ ν (sourceActualCount t b ν u) *
        sourceContinuationProbability t A γ w I₁ z₁ ν (sourceActualCount t w ν u)) ω
  have heq : (fun v : Sample × (Site → ℕ → GaussianCoefficientSpace) ↦
      {u | sourcePairExteriorRecord t b w ν J u.1 ∈ G ∧
        sourceActualCount t b ν u.1 ≤ sourceEarlyRootCap t ν ∧
        sourceActualCount t w ν u.1 ≤ sourceEarlyRootCap t ν}.indicator
        (fun u ↦ sourceContinuationProbability t A γ b I₀ z₀ ν (sourceActualCount t b ν u.1) *
          sourceContinuationProbability t A γ w I₁ z₁ ν (sourceActualCount t w ν u.1)) v) =
      (fun v ↦ f v.1) := by
    funext v
    simp only [f, Set.indicator_apply, Set.mem_setOf_eq]
  rw [heq] at hb
  simpa only [sourceEnlargedLaw, integral_fun_fst, probReal_univ, one_smul] using hb


end SRWTightness
