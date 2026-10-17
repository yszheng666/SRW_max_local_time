import SRWTightness.SourceObservationTime

namespace SRWTightness

/-- Actual source diagonal errors are nonnegative, summably small and individually at most 1/8. -/
theorem source_gaussian_error_bounds (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) :
    let e := geometricDiskPointError b A (Real.exp 1 * sourceLowerRadius t + 14)
      diskEnergyGapRatio (2 / Real.pi) (I + 1)
    (∀ i, 0 ≤ e i) ∧
    (∑ i, e i) ≤ (diskEquilibriumWeightConstant / A) / (2 / Real.pi) ∧
    (∀ i, e i ≤ 1 / 8) := by
  obtain ⟨J, hJ, hα, hR⟩ := source_gaussian_parameters t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  obtain ⟨ha, hq, hsep, houter, htime, hrest⟩ := diskGaussianParameterChoice A
    (Real.exp 1 * sourceLowerRadius t + 14)
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (I + 1)
    (diskPointGaussianMinimumRadius_ge_base.trans hA) hα (by simpa using hR)
  let e := geometricDiskPointError b A (Real.exp 1 * sourceLowerRadius t + 14)
    diskEnergyGapRatio (2 / Real.pi) (I + 1)
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have he (i : Fin ((I + 1) + 1)) : 0 ≤ e i :=
    geometricDiskPointError_nonneg b A _ diskEnergyGapRatio _ hg.le (I + 1) i
  have hsum : (∑ i, e i) ≤ (diskEquilibriumWeightConstant / A) / (2 / Real.pi) := by
    dsimp [e]
    rw [geometricDiskPointError_sum]
    exact equilibriumDiscreteError_geometric_sum_upper b A _ diskEnergyGapRatio _
      ha hq hg hsep
  have hs : (∑ i, e i) ≤ (1 / 8 : ℝ) := by
    apply hsum.trans
    apply (div_le_iff₀ hg).mpr
    have hh := diskPointGaussianMinimumRadius_small_error A hA
    nlinarith
  exact ⟨he, hsum, fun i ↦
    (Finset.single_le_sum (fun j _ ↦ he j) (Finset.mem_univ i)).trans hs⟩

end SRWTightness
