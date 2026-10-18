import SRWTightness.SourceEarlyShortCapacity

open Filter
namespace SRWTightness

/-- The short capacity denominator is uniformly close to g and bounded away from zero. -/
theorem source_early_capacity_denominator (hinput : PotentialKernelAsymptoticInput) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t → ∀ b : Site,
      ∃ d : ℝ, (2 / Real.pi) / 2 ≤ d ∧
        |d - (2 / Real.pi)| ≤ D / sourceCommonPairInnerRadius t ν ∧
        capacity
          (sourceExitDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
          (sourceEntranceDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν) = d⁻¹ := by
  obtain ⟨L, hL, hc⟩ := source_early_short_capacity hinput
  let g : ℝ := 2 / Real.pi
  let D : ℝ := 56 * g + L
  have hg : 0 < g := by dsimp [g]; positivity
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  filter_upwards [hc, source_early_common_intensity, source_early_level_bounds,
    sourceLowerRadius_tendsto_atTop.eventually
      (eventually_ge_atTop (max 1 (2 * D / g)))] with t hc hi hl hm
  intro ν hν b
  obtain ⟨δ, hδ, heq⟩ := hc ν hν b
  let d := sourceCommonPairIntensity t ν + δ
  have hr := hm.trans (sourceCommonPairInnerRadius_ge_lower t ν (hl.2 ν hν).1)
  have hr0 : 0 < sourceCommonPairInnerRadius t ν :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_left _ _).trans hr)
  have herr : |d - g| ≤ D / sourceCommonPairInnerRadius t ν := by
    calc
      _ = |(sourceCommonPairIntensity t ν - g) + δ| := by dsimp [d]; congr 1; ring
      _ ≤ |sourceCommonPairIntensity t ν - g| + |δ| := abs_add_le _ _
      _ ≤ (56 * g) / sourceCommonPairInnerRadius t ν +
          L / sourceCommonPairInnerRadius t ν := add_le_add (hi ν hν).2.2.2 hδ
      _ = _ := by dsimp [D]; ring
  have hsmall : D / sourceCommonPairInnerRadius t ν ≤ g / 2 := by
    apply (div_le_iff₀ hr0).mpr
    have hlarge := (div_le_iff₀ hg).mp ((le_max_right _ _).trans hr)
    nlinarith
  refine ⟨d, ?_, herr, ?_⟩
  · have hh := (abs_le.mp herr).1
    dsimp [g] at hg ⊢
    linarith
  · rw [← (hi ν hν).1] at heq
    exact heq

end SRWTightness
