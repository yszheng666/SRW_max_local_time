import SRWTightness.GWTubeContainment

namespace SRWTightness

/-- Two endpoint depth shifts are absorbed by linear quarter-power margins. -/
theorem gw_upper_shifted_curvature (L j k d : ℝ) (hL : 0 < L)
    (hj : 0 ≤ j) (hjL : j ≤ L) (hk : 0 ≤ k) (hd : 0 ≤ d) :
    (min (k + j) (L - j + d)) ^ (1 / 4 : ℝ) ≤
      (min j (L - j)) ^ (1 / 4 : ℝ) +
        2 * k ^ (1 / 4 : ℝ) * (1 - j / L) + 2 * d ^ (1 / 4 : ℝ) * j / L := by
  have hkq := Real.rpow_nonneg hk (1 / 4 : ℝ)
  have hdq := Real.rpow_nonneg hd (1 / 4 : ℝ)
  have hratio : 0 ≤ 1 - j / L := by
    have := (div_le_one hL).mpr hjL
    linarith
  by_cases hhalf : 2 * j ≤ L
  · have hcorr : k ^ (1 / 4 : ℝ) ≤ 2 * k ^ (1 / 4 : ℝ) * (1 - j / L) := by
      have hfrac : j / L ≤ 1 / 2 := (div_le_iff₀ hL).mpr (by linarith)
      nlinarith
    have hother : 0 ≤ 2 * d ^ (1 / 4 : ℝ) * j / L := by positivity
    rw [min_eq_left (show j ≤ L - j by linarith)]
    calc
      _ ≤ (k + j) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow
        (le_min (by linarith) (by linarith)) (min_le_left _ _) (by norm_num)
      _ ≤ k ^ (1 / 4 : ℝ) + j ^ (1 / 4 : ℝ) :=
        Real.rpow_add_le_add_rpow hk hj (by norm_num) (by norm_num)
      _ ≤ _ := by linarith
  · have hcorr : d ^ (1 / 4 : ℝ) ≤ 2 * d ^ (1 / 4 : ℝ) * j / L := by
      have hfrac : 1 / 2 ≤ j / L := (le_div_iff₀ hL).mpr (by linarith)
      have := mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ 2 * d ^ (1 / 4 : ℝ))
      nlinarith [show 2 * d ^ (1 / 4 : ℝ) * (j / L) =
        2 * d ^ (1 / 4 : ℝ) * j / L by ring]
    have hother : 0 ≤ 2 * k ^ (1 / 4 : ℝ) * (1 - j / L) := by positivity
    rw [min_eq_right (show L - j ≤ j by linarith)]
    calc
      _ ≤ (L - j + d) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow
        (le_min (by linarith) (by linarith)) (min_le_right _ _) (by norm_num)
      _ ≤ (L - j) ^ (1 / 4 : ℝ) + d ^ (1 / 4 : ℝ) :=
        Real.rpow_add_le_add_rpow (by linarith) hd (by norm_num) (by norm_num)
      _ ≤ _ := by linarith

/-- The source upper barrier fits the branching barrier with the manuscript endpoint shifts. -/
theorem gw_upper_shifted_barrier (L j : ℕ) (hL : 0 < L) (hjL : j ≤ L)
    (θ A x k d : ℝ) (hx : 0 ≤ x) (hk : 0 ≤ k) (hd : 0 ≤ d) :
    θ * (k + j) + A + (min (k + j) ((L : ℝ) - j + d)) ^ (1 / 4 : ℝ) ≤
      gwBarrierLine (x + A + θ * k + 2 * k ^ (1 / 4 : ℝ))
        (θ * (k + L) + A + 2 * d ^ (1 / 4 : ℝ)) j L +
          gwBarrierCurvature (1 / 2 - 1 / 4) j L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hjL' : (j : ℝ) ≤ L := by exact_mod_cast hjL
  have hc := gw_upper_shifted_curvature L j k d hL0 hj0 hjL' hk hd
  have hnon : 0 ≤ x * (1 - (j : ℝ) / L) := by
    have := (div_le_one hL0).mpr hjL'
    positivity
  have he : gwBarrierLine (x + A + θ * k + 2 * k ^ (1 / 4 : ℝ))
      (θ * (k + L) + A + 2 * d ^ (1 / 4 : ℝ)) j L =
      θ * (k + j) + A + x * (1 - (j : ℝ) / L) +
        2 * k ^ (1 / 4 : ℝ) * (1 - (j : ℝ) / L) +
          2 * d ^ (1 / 4 : ℝ) * j / L := by
    unfold gwBarrierLine
    field_simp
    <;> ring
  rw [he]
  unfold gwBarrierCurvature
  norm_num
  linarith

end SRWTightness
