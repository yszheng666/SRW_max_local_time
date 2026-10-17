import SRWTightness.SourceTerminalCapacityHalf
import SRWTightness.SourceGaussianParameters

namespace SRWTightness

/-- The manuscript cutoff a<=m/t^6 supplies the logarithmic capacity separation. -/
theorem source_capacity_half_cutoff (b : Site) (m H a t : ℝ) (K : Finset Site)
    (ht : 2 ≤ t) (ha : 1 ≤ a) (hcut : a ≤ m / t ^ 6)
    (hH : 0 ≤ H) (hHm : 5 * H ≤ m) (hK : K ⊆ translateFinset b (diskFinset a))
    (hlog : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤ 6 * Real.log t) :
    sourceReferenceIntensity m H *
      capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 := by
  have ht0 : 0 < t := by linarith
  have ha0 : 0 < a := by linarith
  have ht6 : t ≤ t ^ 6 := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ t) (by norm_num : 1 ≤ 6)
  have hmul := (le_div_iff₀ (pow_pos ht0 6)).mp hcut
  have hma : 2 * a ≤ m := by nlinarith
  apply source_terminal_capacity_half b m H a K ha hma hH hHm hK
  have hl := Real.log_le_log (mul_pos ha0 (pow_pos ht0 6)) hmul
  rw [Real.log_mul ha0.ne' (pow_pos ht0 6).ne', Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

/-- An explicit source-time threshold ensuring half-mass for every observation below the cutoff. -/
noncomputable def sourceCapacityHalfThreshold : ℝ :=
  max (sourceScaleThreshold 4)
    (Real.exp ((diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4) / 6))

/-- Actual source radius and H0=14 satisfy the terminal half-mass condition uniformly in K. -/
theorem source_capacity_half_profile (b : Site) (t a : ℝ) (K : Finset Site)
    (ht : sourceCapacityHalfThreshold ≤ t) (ha : 1 ≤ a)
    (hcut : a ≤ sourceLowerRadius t / t ^ 6) (hK : K ⊆ translateFinset b (diskFinset a)) :
    sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K ≤ 1 / 2 := by
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_left _ _).trans ht
  have hc := sourceScaleThreshold_conditions t 4 (by norm_num) htbase
  have ht0 : 0 < t := by linarith [hc.1]
  have he : Real.exp ((diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4) / 6) ≤ t :=
    (le_max_right _ _).trans ht
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  apply source_capacity_half_cutoff b _ 14 a t K hc.1 ha hcut (by norm_num)
    (by linarith [hc.2.2.1]) hK
  linarith

/-- The maximal source observation disk and all its subsets have reference mass at most one half. -/
theorem source_reference_capacity_half (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A)
    (ht : max (sourceGaussianThreshold A) sourceCapacityHalfThreshold ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∀ K : Finset Site, K ⊆ translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)) →
      sourceReferenceIntensity (sourceLowerRadius t) 14 *
        capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K ≤ 1 / 2 := by
  obtain ⟨I, hI, _, _⟩ := source_gaussian_parameters t A hA ((le_max_left _ _).trans ht)
  refine ⟨I, hI, ?_⟩
  intro K hK
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hpow : 1 ≤ diskEnergyGapRatio ^ I := one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
  exact source_capacity_half_profile b t _ K ((le_max_right _ _).trans ht)
    (by nlinarith) ((hI I).mpr le_rfl) hK

end SRWTightness
