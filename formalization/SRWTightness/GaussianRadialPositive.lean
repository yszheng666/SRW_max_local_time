import SRWTightness.GaussianVectorQuadraticLaplace

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A nondegenerate three-coordinate Gaussian has a strictly positive radial norm almost surely. -/
theorem gaussian_three_radial_positive (m : Fin 3 → ℝ) (s : ℝ) (hs : 0 < s) :
    ∀ᵐ z ∂Measure.pi (fun i ↦ gaussianReal (m i) s.toNNReal),
      0 < Real.sqrt (∑ i, (z i) ^ 2) := by
  letI : NullSingletonClass (gaussianReal (m 0) s.toNNReal) :=
    nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hs))
  have hn : ∀ᵐ a ∂gaussianReal (m 0) s.toNNReal, a ≠ 0 := by simp [ae_iff]
  have hh := (measurePreserving_eval (fun i ↦ gaussianReal (m i) s.toNNReal)
    (0 : Fin 3)).quasiMeasurePreserving.ae hn
  filter_upwards [hh] with z hz
  apply Real.sqrt_pos.mpr
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ sq_nonneg _)).mpr
  exact ⟨0, Finset.mem_univ _, sq_pos_of_ne_zero hz⟩

end SRWTightness
