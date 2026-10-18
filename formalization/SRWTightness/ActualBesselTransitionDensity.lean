import SRWTightness.BesselDensityLaw
import SRWTightness.RealNonnegativeQuadraticLaplaceUniqueness
import SRWTightness.BesselQuadraticLaplace
import SRWTightness.PositiveBridgeDomination

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual Gaussian radial construction has the literal manuscript Bessel transition density. -/
theorem actual_bessel_transition_density (T x s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hs : 0 < s) (hsT : s ≤ T) :
    HasLaw (actualBesselThree T x s) (besselDensityLaw s x)
      (independentBridgeLaw (Fin 3)) := by
  let μ := independentBridgeLaw (Fin 3)
  have hm := actualBesselThree_measurable T x s
  letI := bessel_density_law_probability s x hs hx
  refine ⟨hm.aemeasurable, ?_⟩
  apply real_nonnegative_quadratic_laplace_uniqueness
  · apply (ae_map_iff hm.aemeasurable measurableSet_Ici).mpr
    exact ae_of_all _ (fun ω ↦ Real.sqrt_nonneg _)
  · exact (bessel_density_law_positive s x).mono (fun y hy ↦ hy.le)
  · intro n
    rw [integral_map hm.aemeasurable
      (by fun_prop : AEStronglyMeasurable
        (fun y : ℝ ↦ Real.exp (-(n : ℝ) * y ^ 2)) (μ.map (actualBesselThree T x s))),
      bessel_density_law_integral s x hs hx]
    rw [bessel_three_quadratic_laplace T x s n hT hs hsT (Nat.cast_nonneg n)]
    simpa only [mul_comm] using
      (bessel_density_quadratic_laplace s x n hs hx (Nat.cast_nonneg n)).symm

end SRWTightness
