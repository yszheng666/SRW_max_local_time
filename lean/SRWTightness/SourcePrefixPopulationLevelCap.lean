import SRWTightness.SourceCommonPrefixPopulationCap

namespace SRWTightness

/-- A common prefix barrier bounds every tree population by its own squared depth, retaining
the level dependence needed for the distance-dependent early gap. -/
theorem source_prefix_population_level_cap (t : ℝ) (n : ℕ)
    (hθ : 0 ≤ sourceBarrierSlope t ∧ sourceBarrierSlope t ≤ 4)
    (hT : (n : ℝ) ≤ sourceTotalTime t) (M : Type*) (r : FiniteExcursionRecord M n)
    (hr : ∀ k : ℕ, 0 < k → k ≤ n →
      geometricGWHeight (finiteRecordPopulationList n r) k ≤
        4 + sourceBarrierSlope t * k -
          (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) :
    ∀ i ≤ n, (finiteRecordLevelPopulation n r i : ℝ) ≤ 8 * ((n : ℝ) + 1) ^ 2 := by
  intro i hi
  have hheight : geometricGWHeight (finiteRecordPopulationList n r) (n - i) ≤
      4 * ((n : ℝ) + 1) := by
    by_cases hk : n - i = 0
    · rw [hk, geometricGWHeight, finite_record_gw_population n r 0 (Nat.zero_le _),
        Nat.sub_zero, finiteRecordLevelPopulation_root]
      have hs : Real.sqrt 2 ≤ 2 := by norm_num
      norm_num only [Nat.cast_one, mul_one]
      linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg _]
    · have hkn : n - i ≤ n := by omega
      have hkR : ((n - i : ℕ) : ℝ) ≤ n := by exact_mod_cast hkn
      have hcurv := Real.rpow_nonneg
        (le_min (Nat.cast_nonneg (n - i)) (sub_nonneg.mpr (hkR.trans hT))) (2 / 5 : ℝ)
      have hh := hr (n - i) (by omega) hkn
      have hline := mul_le_mul_of_nonneg_left hkR hθ.1
      have hlast := mul_le_mul_of_nonneg_right hθ.2 (Nat.cast_nonneg n)
      linarith
  rw [geometricGWHeight, finite_record_gw_population n r (n - i) (by omega),
    Nat.sub_sub_self hi] at hheight
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (finiteRecordLevelPopulation n r i : ℝ) by positivity)
  have hn := Real.sqrt_nonneg (2 * (finiteRecordLevelPopulation n r i : ℝ))
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  nlinarith

end SRWTightness
