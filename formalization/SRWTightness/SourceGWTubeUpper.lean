import SRWTightness.GWTubeLattice
import SRWTightness.SourceDeficitBand

open Filter
open scoped Topology

namespace SRWTightness

/-- A sufficiently steep upper endpoint keeps the source tube above height four. -/
theorem gw_tube_upper_ge_four (L j : ℕ) (hj : 0 < j) (hjL : j < L)
    (b : ℝ) (hb : 4 + (3 / 2 : ℝ) * L ≤ b) :
    4 ≤ gwBarrierLine 4 b j L - gwBarrierCurvature (1 / 2 - 1 / 10) j L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjL1 : (j : ℝ) + 1 ≤ L := by exact_mod_cast hjL
  have hv : 0 ≤ min (j : ℝ) ((L : ℝ) - j) := le_min (by positivity) (by linarith)
  have hcurve := (Real.rpow_le_rpow hv (min_le_left _ _)
    (show (0 : ℝ) ≤ 1 / 2 - 1 / 10 by norm_num)).trans
      (Real.rpow_le_self_of_one_le hj1 (by norm_num : (1 / 2 - 1 / 10 : ℝ) ≤ 1))
  have hslope : (3 / 2 : ℝ) ≤ (b - 4) / (L : ℝ) :=
    (le_div_iff₀ hL0).mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_right hslope (show (0 : ℝ) ≤ j by positivity)
  unfold gwBarrierLine gwBarrierCurvature
  have he : (b - 4) * (j : ℝ) / (L : ℝ) = ((b - 4) / (L : ℝ)) * j := by ring
  rw [he]
  nlinarith

/-- Actual source scales make the upper tube line sufficiently steep, uniformly in time. -/
theorem source_gw_tube_upper :
    ∀ᶠ t : ℝ in atTop, ∀ L : ℕ,
      (L : ℝ) = (sourceCoarseGeneration t : ℝ) →
      let d := sourceLowerTime (sourceLowerRadius t)
      let b := 4 + sourceBarrierSlope t * L - 2 * d ^ (2 / 5 : ℝ)
      ∀ j : ℕ, 0 < j → j < L →
        4 ≤ gwBarrierLine 4 b j L - gwBarrierCurvature (1 / 2 - 1 / 10) j L := by
  have herr := (tendsto_order.1 sourceBarrierSlope_weighted_tendsto_zero).2
    (1 / 10 : ℝ) (by norm_num)
  filter_upwards [source_deficit_large_conditions, herr] with t ht herr
  obtain ⟨ht, htE, hdsmall, hlog⟩ := ht
  have hd := sourceLowerTime_ge_one t ht
  have hT := sourceTotalTime_ge_half t ht htE
  unfold sourceTotalTime at hT
  have hN : 5 * sourceLowerTime (sourceLowerRadius t) ≤
      (sourceCoarseGeneration t : ℝ) := by linarith
  have habs := abs_nonneg (sourceBarrierSlope t - 2)
  have hs : (19 / 10 : ℝ) ≤ sourceBarrierSlope t := by
    have hh := (abs_le.mp (show |sourceBarrierSlope t - 2| ≤ 1 / 10 by nlinarith)).1
    linarith
  have hpow := Real.rpow_le_self_of_one_le hd (by norm_num : (2 / 5 : ℝ) ≤ 1)
  intro L hL
  dsimp only
  intro j hj hjL
  apply gw_tube_upper_ge_four L j hj hjL
  rw [hL]
  have hN0 : 0 ≤ (sourceCoarseGeneration t : ℝ) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hN0]

end SRWTightness
