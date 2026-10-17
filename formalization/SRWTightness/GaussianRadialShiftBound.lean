import SRWTightness.GaussianRadialInverseMoment

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Translation of independent centered Gaussian coordinates gives their prescribed mean vector. -/
theorem gaussian_vector_translation_law {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : NNReal) :
    HasLaw (fun z : ι → ℝ ↦ fun i ↦ m i + z i)
      (Measure.pi (fun i ↦ gaussianReal (m i) v))
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 v)) := by
  have hh (i : ι) := gaussianReal_const_add
    (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 v) i).hasLaw (m i)
  simp only [zero_add] at hh
  have hM (i : ι) : Measurable (fun z : ℝ ↦ m i + z) :=
    measurable_const.add measurable_id
  exact (iIndepFun_pi (fun i ↦ (hM i).aemeasurable)).hasLaw_pi hh

/-- Adding independent Gaussian noise decreases the reciprocal
of a nonzero three-dimensional radius. -/
theorem gaussian_three_radial_shift_bound (m : Fin 3 → ℝ) (s : ℝ) (hs : 0 < s)
    (hm : 0 < ∑ i, (m i) ^ 2) :
    (∫ z : Fin 3 → ℝ, (Real.sqrt (∑ i, (m i + z i) ^ 2))⁻¹
      ∂Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 s.toNNReal)) ≤
        (Real.sqrt (∑ i, (m i) ^ 2))⁻¹ := by
  have hi := gaussian_three_radial_inverse_moment m s hs hm
  have he := (gaussian_vector_translation_law m s.toNNReal).integral_comp
    hi.1.aestronglyMeasurable
  exact he.trans_le hi.2

end SRWTightness
