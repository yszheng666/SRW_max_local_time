import SRWTightness.BesselDensityLaw
import SRWTightness.RealNonnegativeQuadraticLaplaceUniqueness
import SRWTightness.GaussianVectorQuadraticLaplace

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A three-coordinate Gaussian radial law depends on the mean vector only through its norm. -/
theorem gaussian_radial_transition_density (m : Fin 3 → ℝ) (s x : ℝ)
    (hs : 0 < s) (hx : 0 < x) (hm : ∑ i, (m i) ^ 2 = x ^ 2) :
    HasLaw (fun z : Fin 3 → ℝ ↦ Real.sqrt (∑ i, (z i) ^ 2))
      (besselDensityLaw s x) (Measure.pi (fun i ↦ gaussianReal (m i) s.toNNReal)) := by
  let μ := Measure.pi (fun i ↦ gaussianReal (m i) s.toNNReal)
  let R : (Fin 3 → ℝ) → ℝ := fun z ↦ Real.sqrt (∑ i, (z i) ^ 2)
  have hR : Measurable R := by unfold R; fun_prop
  letI := bessel_density_law_probability s x hs hx
  refine ⟨hR.aemeasurable, ?_⟩
  apply real_nonnegative_quadratic_laplace_uniqueness
  · apply (ae_map_iff hR.aemeasurable measurableSet_Ici).mpr
    exact ae_of_all _ (fun z ↦ Real.sqrt_nonneg _)
  · exact (bessel_density_law_positive s x).mono (fun y hy ↦ hy.le)
  · intro n
    rw [integral_map hR.aemeasurable
      (by fun_prop : AEStronglyMeasurable
        (fun y : ℝ ↦ Real.exp (-(n : ℝ) * y ^ 2)) (μ.map R)),
      bessel_density_law_integral s x hs hx]
    have hsq (z : Fin 3 → ℝ) : R z ^ 2 = ∑ i, (z i) ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (z i)))
    simp_rw [hsq]
    rw [gaussian_vector_quadratic_laplace m s n hs (Nat.cast_nonneg n), hm]
    simpa only [Fintype.card_fin, mul_comm] using
      (bessel_density_quadratic_laplace s x n hs hx (Nat.cast_nonneg n)).symm

end SRWTightness
