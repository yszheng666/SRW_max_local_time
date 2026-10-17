import SRWTightness.DiskGreenOffCenterUpper

namespace SRWTightness

/-- Separation converts the off-center Green estimate into a uniform logarithmic bound. -/
theorem translated_disk_green_separated_upper (b x y : Site) (R s : ℝ)
    (hR : 1 ≤ R) (hs : 0 < s)
    (hx : x ∈ translateFinset b (diskFinset R))
    (hy : y ∈ translateFinset b (diskFinset R))
    (hsep : s ≤ Real.sqrt (normSq (y - x))) :
    killedGreen (translateFinset b (diskFinset R)) x y ≤
      (2 / Real.pi) * Real.log (2 * R / s) + diskGreenAdditiveConstant := by
  have hr0 : 0 < R := by linarith
  have hmax : s ≤ max (Real.sqrt (normSq (y - x))) 1 :=
    hsep.trans (le_max_left _ _)
  have hratio := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * R) hs hmax
  have hlog := Real.log_le_log
    (div_pos (by positivity : 0 < 2 * R) (hs.trans_le hmax)) hratio
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ (2 / Real.pi : ℝ) by positivity)
  have hbase := translated_disk_green_off_center_upper b x y R hR hx hy
  linarith

end SRWTightness
