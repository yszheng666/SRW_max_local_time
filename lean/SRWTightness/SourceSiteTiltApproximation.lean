import SRWTightness.SourceObservationTilt
import SRWTightness.SourceObservationSpectralGap
import SRWTightness.SourceObservationDimension
import SRWTightness.SourceBoundedTiltApproximation
import SRWTightness.SourceTimePowerDecay

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology

namespace SRWTightness

noncomputable def sourceSiteTiltError (t : ℝ) : ℝ :=
  sourceTiltApproximationConstant 1 2 sourceObservationDimensionConstant (1 / 8) *
    sourceLowerTime (sourceLowerRadius t) ^ 5 / t

/-- The actual site-tilt comparison error is negligible relative to the terminal probability scale. -/
theorem sourceSiteTiltError_times_time_tendsto_zero :
    Tendsto (fun t : ℝ ↦ sourceSiteTiltError t * sourceLowerTime (sourceLowerRadius t))
      atTop (𝓝 0) := by
  have hh := (sourceLowerTime_pow_div_t_tendsto_zero 6).const_mul
    (sourceTiltApproximationConstant 1 2 sourceObservationDimensionConstant (1 / 8))
  simp only [mul_zero] at hh
  convert hh using 1
  funext t
  unfold sourceSiteTiltError
  ring

/-- Actual ordered source observations tilted by twice the center coordinate, with all application
conditions discharged. Only the stated external convex CLT remains a premise. -/
theorem source_site_tilt_approximation
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A) :
    ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let D := translateFinset b (diskFinset R)
      ∃ z : M, (z : Site) = b ∧ ∀ (k : ℕ) (u : ℝ), t ≤ u → u ^ 2 / 2 = (k : ℝ) →
        let F := fun i : Fin ((I + 1) + 1) ↦
          normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
            z k α (2 / Real.pi) u (diskObservationIndex (I + 1) i)
        let μ := markProductLaw D M α k
        let ρ := μ.tilted (fun Y ↦ 2 * normalizedMarkSum M k α (2 / Real.pi) u z Y)
        let Sigma : Matrix (Fin ((I + 1) + 1)) (Fin ((I + 1) + 1)) ℝ :=
          fun i j ↦ covariance (F i) (F j) μ
        let target := fun i : Fin ((I + 1) + 1) ↦
          2 * geometricDiskPointTime R A diskEnergyGapRatio α (I + 1) (i.val + 1)
        IsProbabilityMeasure ρ ∧ Sigma.PosDef ∧
        (∀ (s : Set (Fin ((I + 1) + 1) → ℝ)), MeasurableSet s → Convex ℝ s →
          |(ρ.map (fun Y i ↦ F i Y)).real s - (gaussianMeanCoordinateLaw target Sigma).real s| ≤
            sourceSiteTiltError t) ∧
        (∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
          (s : Set ((Fin ((I + 1) + 1) → ℝ) × Ξ)), MeasurableSet s →
          (∀ᵐ y ∂ν, Convex ℝ ((fun x ↦ (x, y)) ⁻¹' s)) →
          |((ρ.map (fun Y i ↦ F i Y)).prod ν).real s -
            ((gaussianMeanCoordinateLaw target Sigma).prod ν).real s| ≤ sourceSiteTiltError t) := by
  filter_upwards [eventually_ge_atTop (sourceGaussianThreshold A),
    source_bounded_tilt_approximation hBE 1 2 sourceObservationDimensionConstant (1 / 8)
      (by norm_num) (by norm_num) sourceObservationDimensionConstant_pos (by norm_num)] with t ht happ
  intro b
  obtain ⟨I, hI, z, hz, hw, hw1, htilt⟩ := source_observation_site_tilt b t A hA ht
  obtain ⟨J, hJ, hcap⟩ := source_reference_capacity b t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  obtain ⟨J, hJ, z', hz', hlo⟩ := source_observation_covariance_lower b t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  have hzz : z' = z := Subtype.ext (hz'.trans hz.symm)
  subst z'
  have ha : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have htbase : sourceScaleThreshold A ≤ t := (le_max_left _ _).trans ht
  have ht2 := (sourceScaleThreshold_conditions t A ha htbase).1
  have hm0 := sourceLowerRadius_pos t
  have hq : 0 < diskEnergyGapRatio := by linarith [diskEnergyGapRatio_gt_four]
  have hr0 : 0 ≤ A * diskEnergyGapRatio ^ I := by positivity
  have hr : A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t :=
    ((hI I).mpr le_rfl).trans (div_le_self hm0.le (one_le_pow₀ (by linarith)))
  have hMD : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)) ⊆
      translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)) := by
    apply Finset.image_subset_image
    exact diskFinset_mono _ _ hr0 (by nlinarith [Real.exp_one_gt_two])
  refine ⟨I, hI, z, hz, ?_⟩
  intro k u hu hk
  have hu0 : 0 < u := by linarith
  have hlow := hlo k u hu0 hk
  have htilt' := htilt k u hu0 hk
  have hh := happ (Fin ((I + 1) + 1)) b _ hMD hcap
    (source_observation_dimension t A hA ht I hI) u (by simpa using hu) k hk
    _ hw hw1 (siteTiltCoefficient (Fin.last (I + 1)))
    (by simp) (by
      intro x
      simpa only [orderedObservationWeight, normalizedWeightedSum_observationWeight,
        dotProduct, Matrix.mulVec, Matrix.of_apply] using hlow x)
  dsimp only at hh ⊢
  have hfun := funext htilt'.1
  have htarget := funext htilt'.2
  rw [hfun, htarget] at hh
  have hresult := And.intro hh.1 (And.intro hh.2.1 hh.2.2.2)
  simpa only [orderedObservationWeight, normalizedWeightedSum_observationWeight,
    sourceSiteTiltError] using hresult

end SRWTightness
