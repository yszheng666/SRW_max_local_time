import SRWTightness.SourcePairSuccessProbabilityComparison
import SRWTightness.SourcePairRadiusMargin
import SRWTightness.SourcePairObservationIndex

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- The actual two-site success probability has the late-pair bound at the first covering node. -/
theorem source_late_pair_success_bound
    (hPotential : PotentialKernelAsymptoticInput) (hUpper : GWBarrierUpperInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (b : Site),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      sourcePairLogMargin + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A →
      ∀ (I : ℕ),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      ∀ (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      (z : Site) = b → A < Real.sqrt (normSq ((y : Site) - b)) →
      Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∃ i : ℕ, i ≤ I ∧
      4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i ∧
      A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)) ∧
      (∀ j : ℕ, j < i → A * diskEnergyGapRatio ^ j < 4 * Real.sqrt (normSq ((y : Site) - b))) ∧
      ∀ (γ : ℝ) (J : ℕ)
        (z' : translateFinset (y : Site) (diskFinset (A * diskEnergyGapRatio ^ J))),
      (z' : Site) = (y : Site) →
      sourceLowerTime (sourceLowerRadius t) / 2 ≤ sourceObservationTime t A I (I - i + 1) →
      ∀ [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      let h := sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)
      let ρ := Real.sqrt (normSq ((y : Site) - b))
      sourceEnlargedLaw.real
        (sourceSiteSuccessEvent t A γ b I z ∩ sourceSiteSuccessEvent t A γ (y : Site) J z') ≤
        (C / ((Real.exp t) ^ 2 * ρ ^ 2)) * ((1 + h ^ γ) / h) * Real.exp (-2 * h ^ γ) := by
  obtain ⟨C, hC, hrecord⟩ := source_pair_record_distance_upper hPotential hUpper hKernel hGaussian hBE
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrecord, source_pair_success_probability_le_record] with t hrecord hsuccess
  intro A b hA ht hmargin I hI z y hz hρ hcut hblo hbhi
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  obtain ⟨i, hi, hlo, hhi, hmin⟩ := source_pair_observation_index A
    (Real.sqrt (normSq ((y : Site) - b))) I (by linarith) hρ hcut
  have hm := source_pair_radius_margin A hA hmargin
  have hlog : sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A := by
    have hn : 0 ≤ sourcePairResidualError := le_max_left _ _
    linarith [hm.1]
  refine ⟨i, hi, hlo, hhi, hmin, ?_⟩
  intro γ J z' hz' hv instM instMS hjoint
  have hs := hsuccess A γ b (y : Site) I J i hA ht hlog hI hi z y z' rfl hz' hblo hbhi
  have hr := hrecord b A hA ht hm.1 hm.2 I hI i hi z y hz (by linarith)
    hlo hhi γ hv hblo hbhi hjoint
  have hp := hs.trans hr
  dsimp only at hp ⊢
  let h := sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)
  have he : Real.exp (-2 * t - 2 * h ^ γ) =
      ((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * h ^ γ) := by
    rw [show -2 * t - 2 * h ^ γ = -(t + t) + (-2 * h ^ γ) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_add]
    congr 1
    ring
  rw [he] at hp
  calc
    _ ≤ (C / (Real.sqrt (normSq ((y : Site) - b))) ^ 2) * ((1 + h ^ γ) / h) *
        (((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * h ^ γ)) := hp
    _ = _ := by
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring

end SRWTightness
