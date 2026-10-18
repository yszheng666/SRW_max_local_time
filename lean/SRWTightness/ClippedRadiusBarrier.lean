import SRWTightness.InverseRadiusBarrier
import SRWTightness.GeometryTriangle
import SRWTightness.LatticeNorm

namespace SRWTightness

theorem normSq_step_lower (z : Site) (d : Direction) (a : ℝ) (ha : 1 ≤ a)
    (hz : a ^ 2 ≤ normSq z) : (a - 1) ^ 2 ≤ normSq (z + step d) := by
  let r := Real.sqrt (normSq (z + step d))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have he : r ^ 2 = normSq (z + step d) := Real.sq_sqrt (normSq_nonneg _)
  have hn : normSq (-step d) ≤ (1 : ℝ) ^ 2 := by
    fin_cases d <;> simp [step, normSq, Fin.ext_iff]
  have ht := normSq_add_bound (z + step d) (-step d) hr (by norm_num : (0 : ℝ) ≤ 1)
    he.symm.le hn
  simp only [add_neg_cancel_right] at ht
  have har : a ≤ r + 1 := (sq_le_sq₀ (by linarith : 0 ≤ a) (by linarith : 0 ≤ r + 1)).mp (hz.trans ht)
  have hl : a - 1 ≤ r := by linarith
  rw [← he]
  exact (sq_le_sq₀ (by linarith : 0 ≤ a - 1) hr).mpr hl

noncomputable def clippedRadiusBarrier (a : ℝ) (z : Site) : ℝ :=
  max 0 (1 - (a - 1) ^ 2 / normSq z)

theorem clippedRadiusBarrier_nonneg (a : ℝ) (z : Site) : 0 ≤ clippedRadiusBarrier a z :=
  le_max_left _ _

theorem clippedRadiusBarrier_eq (a : ℝ) (ha : 2 ≤ a) (z : Site)
    (hz : (a - 1) ^ 2 ≤ normSq z) :
    clippedRadiusBarrier a z = 1 - (a - 1) ^ 2 / normSq z := by
  have hn : 0 < normSq z := (sq_pos_of_pos (by linarith : 0 < a - 1)).trans_le hz
  have hh : (a - 1) ^ 2 / normSq z ≤ 1 := (div_le_one hn).mpr hz
  exact max_eq_right (by linarith)

theorem clippedRadiusBarrier_supermean (a : ℝ) (ha : 4 ≤ a) (z : Site)
    (hz : a ^ 2 ≤ normSq z) :
    (1 / 4 : ℝ) * ∑ d : Direction, clippedRadiusBarrier a (z + step d) ≤ clippedRadiusBarrier a z := by
  have hnear (d : Direction) := normSq_step_lower z d a (by linarith) hz
  have hz' : (a - 1) ^ 2 ≤ normSq z := by nlinarith
  rw [clippedRadiusBarrier_eq a (by linarith) z hz']
  simp_rw [clippedRadiusBarrier_eq a (by linarith) _ (hnear _)]
  exact inverse_normSq_barrier_supermean z (by nlinarith) ((a - 1) ^ 2) (sq_nonneg _)

theorem clippedRadiusBarrier_outer_lower (a : ℝ) (ha : 4 ≤ a) (z : Site)
    (hz : (2 * a) ^ 2 ≤ normSq z) : (3 / 4 : ℝ) ≤ clippedRadiusBarrier a z := by
  have hpos : 0 < normSq z := by nlinarith
  have hh : (a - 1) ^ 2 / normSq z ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  exact (by linarith : (3 / 4 : ℝ) ≤ 1 - (a - 1) ^ 2 / normSq z).trans (le_max_right _ _)

theorem clippedRadiusBarrier_near_upper (a : ℝ) (ha : 4 ≤ a) (z : Site)
    (hzlo : a ^ 2 ≤ normSq z) (hzhi : normSq z ≤ (a + 1) ^ 2) :
    clippedRadiusBarrier a z ≤ 4 / a := by
  rw [clippedRadiusBarrier_eq a (by linarith) z (by nlinarith)]
  have hpos : 0 < normSq z := by nlinarith
  have hap : 0 < a := by linarith
  have hb : (a - 1) ^ 2 / (a + 1) ^ 2 ≤ (a - 1) ^ 2 / normSq z :=
    div_le_div_of_nonneg_left (sq_nonneg _) hpos hzhi
  have he : 1 - (a - 1) ^ 2 / (a + 1) ^ 2 = 4 * a / (a + 1) ^ 2 := by
    field_simp
    ring
  have hc : 4 * a / (a + 1) ^ 2 ≤ 4 / a := by
    apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < a + 1)) hap).mpr
    nlinarith
  linarith

end SRWTightness
