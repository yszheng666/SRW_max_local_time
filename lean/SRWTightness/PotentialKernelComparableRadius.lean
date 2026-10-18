import SRWTightness.PotentialKernelRadialBounds

namespace SRWTightness

/-- Fixed-factor radial bounds give a uniform logarithmic potential error at every lattice scale. -/
theorem potentialKernel_comparable_radius (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R) (z : Site)
    (hlo : a * R ≤ Real.sqrt (normSq z)) (hhi : Real.sqrt (normSq z) ≤ b * R) :
    |potentialKernel z - (2 / Real.pi) * Real.log R| ≤
      potentialUpperConstant + potentialLowerConstant +
        (2 / Real.pi) * (|Real.log a| + |Real.log b|) := by
  have hz : z ≠ 0 := by
    intro he
    subst z
    have hh : Real.sqrt (normSq (0 : Site)) = 0 := by norm_num [normSq]
    rw [hh] at hlo
    exact (not_le_of_gt (mul_pos ha hR)) hlo
  have hn := one_le_normSq_of_ne_zero z hz
  have hrho : 0 < Real.sqrt (normSq z) := lt_of_lt_of_le (mul_pos ha hR) hlo
  have hu := potentialKernel_log_upper z hn
  have hl := potentialKernel_ge_log_radius z
  rw [max_eq_left (Real.one_le_sqrt.mpr hn)] at hl
  have hlog := Real.log_sqrt (normSq_nonneg z)
  have hlog' : Real.log (normSq z) / Real.pi =
      (2 / Real.pi) * Real.log (Real.sqrt (normSq z)) := by rw [hlog]; ring
  rw [hlog'] at hu
  have hlow := Real.log_le_log (mul_pos ha hR) hlo
  have hhigh := Real.log_le_log hrho hhi
  rw [Real.log_mul ha.ne' hR.ne'] at hlow
  rw [Real.log_mul hb.ne' hR.ne'] at hhigh
  have hg : 0 ≤ 2 / Real.pi := by positivity
  have h1 := mul_le_mul_of_nonneg_left hlow hg
  have h2 := mul_le_mul_of_nonneg_left hhigh hg
  have h3 := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log a)) hg
  have h4 := mul_le_mul_of_nonneg_left (le_abs_self (Real.log b)) hg
  have h5 := mul_nonneg hg (abs_nonneg (Real.log a))
  have h6 := mul_nonneg hg (abs_nonneg (Real.log b))
  have hU := potentialUpperConstant_pos
  have hL := potentialLowerConstant_pos
  unfold potentialUpperConstant at hU ⊢
  apply abs_le.mpr
  constructor <;> nlinarith

end SRWTightness
