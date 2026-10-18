import SRWTightness.InverseTiltProduct
import SRWTightness.PairInverseTiltWindow

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The unsplit pair event needs only an exponential moment and its cumulant bound. -/
theorem pair_chernoff_bound {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (F G S : Ω → ℝ)
    (hX : Integrable (fun ω ↦ Real.exp (2 * F ω + 2 * G ω - 2 * S ω)) μ)
    (E : Set (Ω × Ξ)) (hE : MeasurableSet E)
    (At d v q f C ε : ℝ)
    (hΛ : cgf (fun ω ↦ 2 * F ω + 2 * G ω - 2 * S ω) μ 1 ≤ 4 * d - 2 * v + C)
    (hAt : 2 * d + q - ε ≤ At)
    (hF : ∀ ω ∈ E, At ≤ F ω.1) (hG : ∀ ω ∈ E, At ≤ G ω.1)
    (hS : ∀ ω ∈ E, S ω.1 ≤ 2 * v + q - f) :
    (μ.prod ν).real E ≤
      Real.exp (C + 4 * ε) * Real.exp (-2 * d - 2 * (d - v) - 2 * q - 2 * f) := by
  let X := fun ω ↦ 2 * F ω + 2 * G ω - 2 * S ω
  let U := Real.exp (C + 4 * ε) * Real.exp (-2 * d - 2 * (d - v) - 2 * q - 2 * f)
  have hU : ∀ ω ∈ E, Real.exp (cgf X μ 1 - X ω.1) ≤ U := by
    intro ω hω
    simpa [X, U] using pair_inverse_tilt_window
      (cgf X μ 1) (F ω.1) (G ω.1) (S ω.1) At d v q f 0 0 0 C ε
      hΛ hAt (by simpa using hF ω hω) (by simpa using hG ω hω)
      (by simpa using hS ω hω)
  have hb := (inverse_tilt_product_event_bounds μ ν X hX E hE 0 U
    (fun ω _ ↦ (Real.exp_pos _).le) hU).2
  letI := isProbabilityMeasure_tilted hX
  exact hb.trans (mul_le_of_le_one_right (by positivity) measureReal_le_one)

end SRWTightness
