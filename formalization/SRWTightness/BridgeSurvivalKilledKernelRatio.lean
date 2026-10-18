import SRWTightness.KilledGaussianReflectionIntegral

open ProbabilityTheory
namespace SRWTightness

/-- The bridge heat-kernel weight times its survival ratio gives the killed-kernel ratio. -/
theorem bridge_survival_killed_kernel_ratio (T r q b a : ℝ) (hT : 0 < T) (hrT : r < T) :
    (gaussianPDFReal a (T - r).toNNReal b / gaussianPDFReal 0 T.toNNReal b) *
      ((1 - Real.exp (-(2 * (q - a) * (q - b) / (T - r)))) /
        (1 - Real.exp (-(2 * q * (q - b) / T)))) =
      killedBrownianDensity (T - r) (q - a) (q - b) /
        killedBrownianDensity T q (q - b) := by
  have hg : gaussianPDFReal a (T - r).toNNReal b =
      gaussianPDFReal 0 (T - r).toNNReal (b - a) := by
    simp only [gaussianPDFReal_def, sub_zero]
  have hab : q - a - (b - a) = q - b := by ring
  have hn := killed_gaussian_reflection_density (T - r) (q - a) (b - a)
    (sub_pos.mpr hrT)
  rw [hab, ← hg] at hn
  rw [div_mul_div_comm, hn, killed_gaussian_reflection_density T q b hT]

end SRWTightness
