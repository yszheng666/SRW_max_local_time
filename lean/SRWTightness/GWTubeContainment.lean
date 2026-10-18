import SRWTightness.ExternalGWBarrier
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- The source total-time curvature is controlled by the shorter GW curvature and line shift. -/
theorem gw_source_curvature_comparison (L j d γ : ℝ) (hL : 0 < L)
    (hj : 0 ≤ j) (hjL : j ≤ L) (hd : 0 ≤ d) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (min j (L + d - j)) ^ γ ≤ (min j (L - j)) ^ γ + 2 * d ^ γ * j / L := by
  have hdγ := Real.rpow_nonneg hd γ
  by_cases hhalf : 2 * j ≤ L
  · rw [min_eq_left (show j ≤ L + d - j by linarith),
      min_eq_left (show j ≤ L - j by linarith)]
    have hh : 0 ≤ 2 * d ^ γ * j / L := by positivity
    linarith
  · have hratio : 1 ≤ 2 * j / L := (le_div_iff₀ hL).mpr (by linarith)
    have hcorr : d ^ γ ≤ 2 * d ^ γ * j / L := by
      have hh := mul_le_mul_of_nonneg_left hratio hdγ
      nlinarith [show d ^ γ * (2 * j / L) = 2 * d ^ γ * j / L by ring]
    rw [min_eq_right (show L - j ≤ j by linarith)]
    calc
      _ ≤ ((L - j) + d) ^ γ := Real.rpow_le_rpow
        (le_min hj (by linarith)) (by linarith [min_le_right j (L + d - j)]) hγ
      _ ≤ (L - j) ^ γ + d ^ γ := Real.rpow_add_le_add_rpow
        (by linarith) hd hγ hγ1
      _ ≤ _ := add_le_add le_rfl hcorr

/-- The source-shifted lower GW tube lies below the successful coarse barrier. -/
theorem gw_source_tube_upper_le_barrier (L j : ℕ) (hL : 0 < L) (hjL : j ≤ L)
    (θ d : ℝ) (hd : 0 ≤ d) :
    gwBarrierLine 4 (4 + θ * L - 2 * d ^ (2 / 5 : ℝ)) j L -
      gwBarrierCurvature (1 / 2 - 1 / 10) j L ≤
        4 + θ * j - (min (j : ℝ) ((L : ℝ) + d - j)) ^ (2 / 5 : ℝ) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hj : (0 : ℝ) ≤ j := by positivity
  have hjL' : (j : ℝ) ≤ L := by exact_mod_cast hjL
  have hh := gw_source_curvature_comparison (L : ℝ) j d (2 / 5) hL0 hj hjL' hd
    (by norm_num) (by norm_num)
  have he : gwBarrierLine 4 (4 + θ * L - 2 * d ^ (2 / 5 : ℝ)) j L =
      4 + θ * j - 2 * d ^ (2 / 5 : ℝ) * j / L := by
    unfold gwBarrierLine
    field_simp
    <;> ring
  rw [he]
  unfold gwBarrierCurvature
  norm_num at *
  linarith

end SRWTightness
