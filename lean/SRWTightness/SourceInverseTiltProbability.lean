import SRWTightness.SourceInverseTiltFactor
import SRWTightness.SourceSiteTiltApproximation
import SRWTightness.InverseTiltEvent

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- The original source mark probability and its site-tilted probability differ by the exact
terminal exponential scale, uniformly over every measurable event inside the site window. -/
theorem source_inverse_tilt_probability
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A) :
    ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let m := sourceLowerRadius t
      let d := sourceLowerTime m
      let R := Real.exp 1 * m + 14
      let α := sourceReferenceIntensity m 14
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let D := translateFinset b (diskFinset R)
      ∃ z : M, (z : Site) = b ∧ ∀ q : ℝ, Real.sqrt d ≤ q → q ≤ 2 * Real.sqrt d →
        let u := sourceTerminalRoot t q
        ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
        let F := normalizedMarkSum M k α (2 / Real.pi) u z
        let μ := markProductLaw D M α k
        let ρ := μ.tilted (fun Y ↦ 2 * F Y)
        ∀ (E : Set (MarkSamples M k)), MeasurableSet E →
          (∀ Y ∈ E, sourceTerminalThreshold t u ≤ F Y ∧ F Y ≤ sourceTerminalThreshold t u + 1) →
          Real.exp (-sourceInverseTiltExponentConstant) * Real.exp (-2 * d - 2 * q) *
            ρ.real E ≤ μ.real E ∧
          μ.real E ≤ Real.exp sourceInverseTiltExponentConstant * Real.exp (-2 * d - 2 * q) *
            ρ.real E := by
  filter_upwards [source_site_tilt_approximation hBE A hA, source_inverse_tilt_factor,
    source_deficit_large_conditions, eventually_ge_atTop (sourceGaussianThreshold A)]
    with t htilt hfactor ht htA
  intro b
  obtain ⟨I, hI, z, hz, happ⟩ := htilt b
  obtain ⟨J, hJ, hcap⟩ := source_reference_capacity b t A hA htA
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  have ha : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have hm0 := sourceLowerRadius_pos t
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14 hm0
    (by norm_num) (by linarith)).1
  have hq0 : 0 < diskEnergyGapRatio := by linarith [diskEnergyGapRatio_gt_four]
  have hr0 : 0 ≤ A * diskEnergyGapRatio ^ I := by positivity
  have hr : A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t :=
    ((hI I).mpr le_rfl).trans (div_le_self hm0.le (one_le_pow₀ (by linarith)))
  have hMD : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)) ⊆
      translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)) := by
    apply Finset.image_subset_image
    exact diskFinset_mono _ _ hr0 (by nlinarith [Real.exp_one_gt_two])
  refine ⟨I, hI, z, hz, ?_⟩
  dsimp only
  intro q hq hq2 k hk E hE hwindow
  have hu := sourceTerminalRoot_bounds t q ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hq hq2
  have hprob := (happ k _ hu.1 hk).1
  let μ := markProductLaw (translateFinset b (diskFinset
    (Real.exp 1 * sourceLowerRadius t + 14)))
    (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (sourceReferenceIntensity (sourceLowerRadius t) 14) k
  let X := fun Y ↦ 2 * normalizedMarkSum _ k
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi) (sourceTerminalRoot t q) z Y
  letI : IsProbabilityMeasure μ := markProductLaw_isProbabilityMeasure _ _ _ hα.le hcap k
  letI : IsProbabilityMeasure (μ.tilted X) := hprob
  have hX : Integrable (fun Y ↦ Real.exp (X Y)) μ := by
    by_contra hnot
    have hh := congrArg (fun ν : Measure (MarkSamples _ k) ↦ ν Set.univ)
      (tilted_of_not_integrable hnot)
    simpa using hh
  apply inverse_tilt_event_bounds μ X hX E hE
  · intro Y hY
    exact (hfactor b _ hMD hcap q hq hq2 k hk z hz _
      (hwindow Y hY).1 (hwindow Y hY).2).1
  · intro Y hY
    exact (hfactor b _ hMD hcap q hq hq2 k hk z hz _
      (hwindow Y hY).1 (hwindow Y hY).2).2

end SRWTightness
