import SRWTightness.ScaledGaussianFirstCrossingReflection
import SRWTightness.FiniteReflectionProbabilityBounds

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Actual Brownian paths satisfy finite-grid reflection bounds with the mesh-increment error. -/
theorem scaled_gaussian_grid_reflection_bounds (T q b δ : ℝ) (hT : 0 < T)
    (hq : 0 < q) (hb : b < q) (hδ : 0 ≤ δ) (n : ℕ) (τ : ℕ → ℝ)
    (hτ : Monotone τ) (hzero : τ 0 = 0) (hmem : ∀ k, τ k ∈ Set.Icc (0 : ℝ) T) :
    let W := fun k ω ↦ Real.sqrt T * gaussianDyadicPath ω (τ k / T)
    gaussianCoefficientLaw.real {ω | (∃ k ≤ n, q ≤ W k ω) ∧ W n ω ≤ b} ≤
      gaussianCoefficientLaw.real {ω | 2 * q - b ≤ W n ω} ∧
    gaussianCoefficientLaw.real {ω | 2 * (q + δ) - b ≤ W n ω} -
      gaussianCoefficientLaw.real {ω | ∃ j < n, δ < W (j + 1) ω - W j ω} ≤
      gaussianCoefficientLaw.real {ω | (∃ k ≤ n, q ≤ W k ω) ∧ W n ω ≤ b} := by
  dsimp only
  let W : ℕ → GaussianCoefficientSpace → ℝ :=
    fun k ω ↦ Real.sqrt T * gaussianDyadicPath ω (τ k / T)
  have hm (k : ℕ) : Measurable (W k) :=
    measurable_const.mul (gaussianDyadicPath_measurable _)
  apply finite_reflection_probability_bounds gaussianCoefficientLaw W hm n q b δ
  · intro ω
    simpa only [W, hzero, zero_div, gaussianDyadicPath_zero, mul_zero] using hq
  · exact hb
  · exact hδ
  · intro k hkn
    let σ : Fin k → Set.Icc (0 : ℝ) (τ k) :=
      fun j ↦ ⟨τ j, (hmem j).1, hτ (Nat.le_of_lt j.isLt)⟩
    have he := scaled_gaussian_first_crossing_reflection T (τ k) (τ n) q b hT
      (hmem k).1 (hτ hkn) (hmem n).2 k σ
    have hf (ω : GaussianCoefficientSpace) :
        (∀ j : Fin k, Real.sqrt T * gaussianDyadicPath ω ((σ j : ℝ) / T) < q) ↔
          ∀ j < k, W j ω < q := by
      constructor
      · intro h j hj
        exact h ⟨j, hj⟩
      · intro h j
        exact h j j.isLt
    simpa only [firstCrossingEvent, hf, W, Set.setOf_and] using he

end SRWTightness
