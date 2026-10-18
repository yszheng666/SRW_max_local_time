import SRWTightness.GWPositiveLattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Ordered endpoint lines remain ordered at every time between the endpoints. -/
theorem gw_barrier_line_mono (L j : ℕ) (hL : 0 < L) (hj : j ≤ L)
    (x y a b : ℝ) (ha : x ≤ a) (hb : y ≤ b) :
    gwBarrierLine x y j L ≤ gwBarrierLine a b j L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hjL : (j : ℝ) ≤ L := by exact_mod_cast hj
  have hr0 : 0 ≤ (j : ℝ) / (L : ℝ) := by positivity
  have hr1 : (j : ℝ) / (L : ℝ) ≤ 1 := (div_le_one hL0).mpr hjL
  have h1 := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hr1)
  have h2 := mul_nonneg (sub_nonneg.mpr hb) hr0
  unfold gwBarrierLine
  simp only [mul_div_assoc]
  nlinarith

/-- The manuscript's curvature constants give a gap of at least nine at every interior layer. -/
theorem gw_tube_curvature_gap (L j : ℕ) (hj : 0 < j) (hjL : j < L) :
    9 ≤ 10 * gwBarrierCurvature (1 / 2 + 1 / 10) j L -
      gwBarrierCurvature (1 / 2 - 1 / 10) j L := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjL1 : (j : ℝ) + 1 ≤ L := by exact_mod_cast hjL
  have hv : (1 : ℝ) ≤ min (j : ℝ) ((L : ℝ) - j) := le_min hj1 (by linarith)
  have hsmall := Real.one_le_rpow hv (show (0 : ℝ) ≤ 1 / 2 - 1 / 10 by norm_num)
  have horder := Real.rpow_le_rpow_of_exponent_le hv
    (show (1 / 2 - 1 / 10 : ℝ) ≤ 1 / 2 + 1 / 10 by norm_num)
  unfold gwBarrierCurvature
  linarith

/-- Source curvature constants and ordered lines supply the tube's interior lattice condition. -/
theorem gw_tube_lattice_of_upper (L j : ℕ) (hj : 0 < j) (hjL : j < L)
    (x y a b : ℝ) (ha : x ≤ a) (hb : y ≤ b)
    (hupper : 4 ≤ gwBarrierLine a b j L -
      gwBarrierCurvature (1 / 2 - 1 / 10) j L) :
    gwPositiveLatticeIntersects
      (gwBarrierLine x y j L - 10 * gwBarrierCurvature (1 / 2 + 1 / 10) j L)
      (gwBarrierLine a b j L - gwBarrierCurvature (1 / 2 - 1 / 10) j L) := by
  have hline := gw_barrier_line_mono L j (by omega) (by omega) x y a b ha hb
  have hgap := gw_tube_curvature_gap L j hj hjL
  apply gw_positive_lattice_wide_interval _ _ hupper
  linarith

end SRWTightness
