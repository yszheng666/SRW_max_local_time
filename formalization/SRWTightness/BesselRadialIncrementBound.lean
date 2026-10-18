import SRWTightness.ExternalBesselThree
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory WithLp

namespace SRWTightness

/-- The squared difference of Euclidean radii is bounded by the squared displacement. -/
theorem radial_squared_increment_bound {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (Real.sqrt (∑ i, a i ^ 2) - Real.sqrt (∑ i, b i ^ 2)) ^ 2 ≤
      ∑ i, (a i - b i) ^ 2 := by
  let x : EuclideanSpace ℝ ι := toLp 2 a
  let y : EuclideanSpace ℝ ι := toLp 2 b
  calc
    _ = (‖x‖ - ‖y‖) ^ 2 := by simp [EuclideanSpace.norm_eq, x, y]
    _ ≤ ‖x - y‖ ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (‖x‖ - ‖y‖)) (norm_nonneg (x - y))).mpr
        (abs_norm_sub_norm_le x y)
      simpa only [sq_abs] using hh
    _ = _ := by simp [EuclideanSpace.real_norm_sq_eq, x, y]

/-- Pathwise radial increments of the actual process are bounded by the coordinate increments. -/
theorem bessel_three_increment_pathwise (T x r s : ℝ)
    (ω : Fin 3 → GaussianCoefficientSpace) :
    (actualBesselThree T x s ω - actualBesselThree T x r ω) ^ 2 ≤
      ∑ i : Fin 3, (Real.sqrt T * (gaussianDyadicPath (ω i) (s / T) -
        gaussianDyadicPath (ω i) (r / T))) ^ 2 := by
  have hh := radial_squared_increment_bound
    (fun i : Fin 3 ↦ (if i = 0 then x else 0) +
      Real.sqrt T * gaussianDyadicPath (ω i) (s / T))
    (fun i : Fin 3 ↦ (if i = 0 then x else 0) +
      Real.sqrt T * gaussianDyadicPath (ω i) (r / T))
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SRWTightness
