import SRWTightness.SourceLatePairSuccessBound

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- The late-distance condition internally places the second actual site in the common mark domain. -/
theorem source_late_pair_success_bound_sites
    (hPotential : PotentialKernelAsymptoticInput) (hUpper : GWBarrierUpperInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (b : Site),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      sourcePairLogMargin + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A →
      ∀ (I : ℕ),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      ∀ (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (w : Site),
      (z : Site) = b → A < Real.sqrt (normSq (w - b)) →
      Real.sqrt (normSq (w - b)) ≤ A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∃ i : ℕ, i ≤ I ∧
      4 * Real.sqrt (normSq (w - b)) ≤ A * diskEnergyGapRatio ^ i ∧
      A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * Real.sqrt (normSq (w - b)) ∧
      (∀ j : ℕ, j < i → A * diskEnergyGapRatio ^ j < 4 * Real.sqrt (normSq (w - b))) ∧
      ∀ (γ : ℝ) (J : ℕ)
        (z' : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ J))),
      (z' : Site) = w →
      sourceLowerTime (sourceLowerRadius t) / 2 ≤ sourceObservationTime t A I (I - i + 1) →
      ∀ [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      let h := sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)
      let ρ := Real.sqrt (normSq (w - b))
      sourceEnlargedLaw.real
        (sourceSiteSuccessEvent t A γ b I z ∩ sourceSiteSuccessEvent t A γ w J z') ≤
        (C / ((Real.exp t) ^ 2 * ρ ^ 2)) * ((1 + h ^ γ) / h) * Real.exp (-2 * h ^ γ) := by
  obtain ⟨C, hC, happ⟩ := source_late_pair_success_bound hPotential hUpper hKernel hGaussian hBE
  refine ⟨C, hC, ?_⟩
  filter_upwards [happ] with t happ
  intro A b hA ht hmargin I hI z w hz hρ hcut hblo hbhi
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hB := diskEnergyGapRatio_gt_four
  have hr0 := Real.sqrt_nonneg (normSq (w - b))
  have hm := (le_div_iff₀ (by linarith : 0 < 8 * diskEnergyGapRatio)).mp hcut
  have hrp : 0 < Real.sqrt (normSq (w - b)) := by linarith
  have hrlt : Real.sqrt (normSq (w - b)) < A * diskEnergyGapRatio ^ I := by
    nlinarith [mul_pos hrp (show 0 < 8 * diskEnergyGapRatio - 1 by linarith)]
  have hwm : w ∈ translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)) := by
    simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
    have hs := Real.sq_sqrt (normSq_nonneg (w - b))
    have hmpos := mul_pos (sub_pos.mpr hrlt)
      (show 0 < A * diskEnergyGapRatio ^ I + Real.sqrt (normSq (w - b)) by linarith)
    nlinarith
  exact happ A b hA ht hmargin I hI z ⟨w, hwm⟩ hz hρ hcut hblo hbhi

end SRWTightness
