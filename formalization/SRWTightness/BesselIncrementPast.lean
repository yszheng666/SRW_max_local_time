import SRWTightness.GaussianPathIncrementPast
import SRWTightness.IndependentCoordinatePairs
import SRWTightness.ExternalBesselThree

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- All three future scaled Brownian increments are independent of the entire vector past. -/
theorem bessel_vector_increment_indep_past (T r t : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    IndepFun
      (fun ω : Fin 3 → GaussianCoefficientSpace ↦ fun i (u : Set.Icc (0 : ℝ) r) ↦
        Real.sqrt T * gaussianDyadicPath (ω i) (u / T))
      (fun ω : Fin 3 → GaussianCoefficientSpace ↦ fun i ↦ Real.sqrt T *
        (gaussianDyadicPath (ω i) (t / T) - gaussianDyadicPath (ω i) (r / T)))
      (independentBridgeLaw (Fin 3)) := by
  let e : Set.Icc (0 : ℝ) r → Set.Icc (0 : ℝ) (r / T) := fun u ↦
    ⟨u / T, div_nonneg u.property.1 hT.le,
      (div_le_div_iff_of_pos_right hT).mpr u.property.2⟩
  have hbase := gaussian_path_increment_indep_past (r / T) (t / T)
    (div_nonneg hr hT.le) ((div_le_div_iff_of_pos_right hT).mpr hrt)
    ((div_le_one hT).mpr ht)
  have hmap : Measurable (fun p : Set.Icc (0 : ℝ) (r / T) → ℝ ↦
      fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * p (e u)) := by
    apply measurable_pi_lambda
    intro u
    exact measurable_const.mul (measurable_pi_apply (e u))
  have hi := hbase.comp hmap
    (show Measurable (fun y : ℝ ↦ Real.sqrt T * y) from measurable_const.mul measurable_id)
  have hf : Measurable (fun ω : GaussianCoefficientSpace ↦
      fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) := by
    apply measurable_pi_lambda
    intro u
    exact measurable_const.mul (gaussianDyadicPath_measurable _)
  have hg : Measurable (fun ω : GaussianCoefficientSpace ↦ Real.sqrt T *
      (gaussianDyadicPath ω (t / T) - gaussianDyadicPath ω (r / T))) :=
    measurable_const.mul ((gaussianDyadicPath_measurable _).sub (gaussianDyadicPath_measurable _))
  exact independent_coordinate_pairs gaussianCoefficientLaw _ _ hf hg hi

end SRWTightness
