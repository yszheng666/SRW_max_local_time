import SRWTightness.SourceRadiusSuccessProbability
import SRWTightness.SourceSuccessCountBounds

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- The manuscript one-point estimate and positive bounded first moment on the common space. -/
theorem source_onepoint_with_margin (J : ℝ) (hPotential : PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (hLattice : LatticeAnnulusCountInput)
    (hJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K)) :
    ∃ A c C c₁ C₁ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧
      0 < c ∧ 0 < C ∧ 0 < c₁ ∧ 0 < C₁ ∧ ∀ᶠ R : ℝ in atTop,
      ∃ (I : sourceCandidateAnnulus R → ℕ)
        (z : ∀ b : sourceCandidateAnnulus R,
          translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))),
      (∀ b : sourceCandidateAnnulus R, (z b : Site) = (b : Site)) ∧
      (∀ (b : sourceCandidateAnnulus R) (i : ℕ),
        A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ i ≤ I b) ∧
      (∀ b : sourceCandidateAnnulus R,
        c * (R ^ 2)⁻¹ ≤ sourceEnlargedLaw.real
          (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b)) ∧
        sourceEnlargedLaw.real (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b)) ≤
          C * (R ^ 2)⁻¹) ∧
      c₁ ≤ (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ∧
        (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ≤ C₁ := by
  classical
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ := source_local_time_success_probability_radius_with_margin J
    hPotential hLower hUpper hReconstruct hBE hGaussian hReflection hBridge hReverse
    hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  obtain ⟨a, B, ha, hB, hm⟩ := source_success_count_bounds hLattice
  refine ⟨A, c, C, a * c, B * C, hA, hlog, hc, hC, mul_pos ha hc, mul_pos hB hC, ?_⟩
  filter_upwards [hp, hm, Real.tendsto_log_atTop.eventually
    source_local_time_success_nullMeasurable, eventually_gt_atTop (0 : ℝ)]
    with R hp hm hn hR
  have hchoose (b : sourceCandidateAnnulus R) :
      ∃ (i : ℕ) (z : translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ i))),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤
        sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ j ≤ i) ∧
      (z : Site) = (b : Site) ∧
      c * (R ^ 2)⁻¹ ≤ (pathLaw.prod (independentBridgeLaw ℕ)).real
        (sourceLocalTimeSuccessEvent (Real.log R) A γ b i z) ∧
      (pathLaw.prod (independentBridgeLaw ℕ)).real
        (sourceLocalTimeSuccessEvent (Real.log R) A γ b i z) ≤ C * (R ^ 2)⁻¹ := by
    have hb := (mem_sourceCandidateAnnulus R hR b).mp b.property
    obtain ⟨i, hi, z, hz, hbnd⟩ := hp b hb.1 hb.2
    let K := translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ i))
    letI : MeasurableSpace (List (Mark K)) := ⊤
    letI : MeasurableSingletonClass (List (Mark K)) := ⟨fun _ ↦ trivial⟩
    exact ⟨i, z, hi, hz, hbnd (hJoint K)⟩
  choose I z hI hz hlo hhi using hchoose
  have hcut (b : sourceCandidateAnnulus R) :
      1 ≤ A * diskEnergyGapRatio ^ I b ∧
      A * diskEnergyGapRatio ^ I b ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 := by
    have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
      (diskPointGaussianMinimumRadius_ge_base.trans hA)
    have hpow : 1 ≤ diskEnergyGapRatio ^ I b :=
      one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
    exact ⟨by nlinarith, (hI b (I b)).mpr le_rfl⟩
  refine ⟨I, z, hz, hI, ?_, hm A γ c C hγ hc hC I z hcut (fun b ↦ ⟨hlo b, hhi b⟩)⟩
  intro b
  have hb := (mem_sourceCandidateAnnulus R hR b).mp b.property
  have hs := hn A γ b (I b) (z b) hγ (hcut b).1 (hcut b).2
    (by simpa only [Real.exp_log hR] using hb.1)
    (by simpa only [Real.exp_log hR] using hb.2)
  rw [source_site_success_probability (Real.log R) A γ b (I b) (z b) hs]
  exact ⟨hlo b, hhi b⟩


/-- The manuscript one-point estimate and positive bounded first moment on the common space. -/
theorem source_onepoint (hPotential : PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (hLattice : LatticeAnnulusCountInput)
    (hJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K)) :
    ∃ A c C c₁ C₁ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      0 < c ∧ 0 < C ∧ 0 < c₁ ∧ 0 < C₁ ∧ ∀ᶠ R : ℝ in atTop,
      ∃ (I : sourceCandidateAnnulus R → ℕ)
        (z : ∀ b : sourceCandidateAnnulus R,
          translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))),
      (∀ b : sourceCandidateAnnulus R, (z b : Site) = (b : Site)) ∧
      (∀ (b : sourceCandidateAnnulus R) (i : ℕ),
        A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ i ≤ I b) ∧
      (∀ b : sourceCandidateAnnulus R,
        c * (R ^ 2)⁻¹ ≤ sourceEnlargedLaw.real
          (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b)) ∧
        sourceEnlargedLaw.real (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b)) ≤
          C * (R ^ 2)⁻¹) ∧
      c₁ ≤ (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ∧
        (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ≤ C₁ := by
  obtain ⟨A, c, C, c₁, C₁, hA, hlog, hc, hC, hc₁, hC₁, hp⟩ :=
    source_onepoint_with_margin 0 hPotential hLower hUpper hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf hLattice hJoint
  exact ⟨A, c, C, c₁, C₁, hA, hc, hC, hc₁, hC₁, hp⟩

end SRWTightness
