import SRWTightness.ScaledGaussianGridReflectionBounds
import SRWTightness.ScaledGaussianGridIncrementDecay
import SRWTightness.DyadicGridCrossingMonotone
import SRWTightness.MonotoneEventProbabilitySqueeze
import SRWTightness.ScaledGaussianEndpointTail

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The countable union of dyadic crossing events has the exact reflected Gaussian endpoint tail. -/
theorem scaled_gaussian_dyadic_reflection (T q b : ℝ) (hT : 0 < T)
    (hq : 0 < q) (hb : b < q) :
    gaussianCoefficientLaw.real {ω |
      (∃ n : ℕ, ∃ k ≤ 2 ^ n,
        q ≤ Real.sqrt T * gaussianDyadicPath ω (stoppedUniformTimeGrid 0 T (2 ^ n) k / T)) ∧
      Real.sqrt T * gaussianDyadicPath ω (T / T) ≤ b} =
      (gaussianReal 0 T.toNNReal).real (Set.Ici (2 * q - b)) := by
  let W : ℝ → GaussianCoefficientSpace → ℝ :=
    fun t ω ↦ Real.sqrt T * gaussianDyadicPath ω (t / T)
  let E : ℕ → Set GaussianCoefficientSpace := fun n ↦ {ω |
    (∃ k ≤ 2 ^ n, q ≤ W (stoppedUniformTimeGrid 0 T (2 ^ n) k) ω) ∧ W T ω ≤ b}
  let g : ℝ → ℝ := fun δ ↦ gaussianCoefficientLaw.real {ω | 2 * (q + δ) - b ≤ W T ω}
  let e : ℝ → ℕ → ℝ := fun δ n ↦ gaussianCoefficientLaw.real {ω | ∃ j < 2 ^ n,
    δ < W (stoppedUniformTimeGrid 0 T (2 ^ n) (j + 1)) ω -
      W (stoppedUniformTimeGrid 0 T (2 ^ n) j) ω}
  have hm : Monotone E := by
    intro n m hnm ω hω
    exact ⟨dyadic_grid_crossing_monotone W 0 T q hnm hω.1, hω.2⟩
  have hg : ContinuousAt g 0 :=
    ((scaled_gaussian_endpoint_tail_continuous T hT).comp
      ((continuous_const.mul (continuous_const.add continuous_id)).sub
        continuous_const)).continuousAt
  have he (δ : ℝ) (hδ : 0 < δ) := scaled_gaussian_grid_increment_decay T δ hT hδ
  have hbnd (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
      gaussianCoefficientLaw.real (E n) ≤ g 0 ∧
        g δ - e δ n ≤ gaussianCoefficientLaw.real (E n) := by
    have hN : 0 < 2 ^ n := by positivity
    have h := scaled_gaussian_grid_reflection_bounds T q b δ hT hq hb hδ.le (2 ^ n)
      (stoppedUniformTimeGrid 0 T (2 ^ n)) (stoppedUniformTimeGrid_mono 0 T (2 ^ n) hT.le)
      (stoppedUniformTimeGrid_zero 0 T (2 ^ n))
      (fun k ↦ stoppedUniformTimeGrid_mem 0 T (2 ^ n) k hT.le hN)
    simpa only [stoppedUniformTimeGrid_endpoint 0 T (2 ^ n) hN, E, g, e, W, add_zero] using h
  have hlim := monotone_event_probability_squeeze gaussianCoefficientLaw E hm g hg e he
    (fun n ↦ (hbnd n 1 (by norm_num)).1) (fun δ hδ n ↦ (hbnd n δ hδ).2)
  have hU : (⋃ n, E n) = {ω |
      (∃ n : ℕ, ∃ k ≤ 2 ^ n, q ≤ W (stoppedUniformTimeGrid 0 T (2 ^ n) k) ω) ∧
        W T ω ≤ b} := by
    ext ω
    simp only [Set.mem_iUnion, E, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn, hb'⟩
      exact ⟨⟨n, hn⟩, hb'⟩
    · rintro ⟨⟨n, hn⟩, hb'⟩
      exact ⟨n, hn, hb'⟩
  rw [hU] at hlim
  simpa only [g, W, add_zero, scaled_gaussian_endpoint_tail T _ hT] using hlim

end SRWTightness
