import SRWTightness.ScaledGaussianStrictDyadicReflection
import SRWTightness.DyadicStrictCrossingMeasurable

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Strict continuous-time crossing with a low endpoint has the reflected Gaussian tail. -/
theorem scaled_gaussian_continuous_reflection (T q b : ℝ) (hT : 0 < T)
    (hq : 0 < q) (hb : b < q) :
    gaussianCoefficientLaw.real {ω |
      (∃ t ∈ Set.Icc (0 : ℝ) T, q < Real.sqrt T * gaussianDyadicPath ω (t / T)) ∧
      Real.sqrt T * gaussianDyadicPath ω (T / T) ≤ b} =
      (gaussianReal 0 T.toNNReal).real (Set.Ici (2 * q - b)) := by
  rw [← scaled_gaussian_strict_dyadic_reflection T q b hT hq hb]
  apply measureReal_congr
  filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
  apply propext
  exact and_congr_left (fun _ ↦ continuous_strict_crossing_iff_uniform_dyadic
    (fun t ↦ Real.sqrt T * gaussianDyadicPath ω (t / T))
    (continuous_const.mul (hω.comp (continuous_id.div_const T))) T q hT)

/-- The continuous flat-barrier and low-endpoint probability
is the Gaussian reflection difference. -/
theorem scaled_gaussian_flat_endpoint_cdf (T q b : ℝ) (hT : 0 < T)
    (hq : 0 < q) (hb : b < q) :
    gaussianCoefficientLaw.real {ω |
      (∀ t ∈ Set.Icc (0 : ℝ) T, Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ q) ∧
      Real.sqrt T * gaussianDyadicPath ω (T / T) ≤ b} =
      (gaussianReal 0 T.toNNReal).real (Set.Iic b) -
        (gaussianReal 0 T.toNNReal).real (Set.Ici (2 * q - b)) := by
  let W : ℝ → GaussianCoefficientSpace → ℝ :=
    fun t ω ↦ Real.sqrt T * gaussianDyadicPath ω (t / T)
  let E : Set GaussianCoefficientSpace := {ω | W T ω ≤ b}
  let S : Set GaussianCoefficientSpace := {ω |
    (∃ n : ℕ, ∃ k ≤ 2 ^ n, q < W (stoppedUniformTimeGrid 0 T (2 ^ n) k) ω) ∧ W T ω ≤ b}
  have hm (t : ℝ) : Measurable (W t) :=
    measurable_const.mul (gaussianDyadicPath_measurable _)
  have hS : MeasurableSet S :=
    (uniform_dyadic_strict_crossing_measurable W hm 0 T q).inter
      (measurableSet_le (hm T) measurable_const)
  have hsub : S ⊆ E := fun _ h ↦ h.2
  have hprob : gaussianCoefficientLaw.real S =
      (gaussianReal 0 T.toNNReal).real (Set.Ici (2 * q - b)) :=
    scaled_gaussian_strict_dyadic_reflection T q b hT hq hb
  have hE : gaussianCoefficientLaw.real E = (gaussianReal 0 T.toNNReal).real (Set.Iic b) := by
    have he := congrArg (fun μ : Measure ℝ ↦ μ.real (Set.Iic b))
      (scaled_gaussian_endpoint_hasLaw T hT).map_eq
    rw [map_measureReal_apply (hm T) measurableSet_Iic] at he
    exact he
  have he : {ω | (∀ t ∈ Set.Icc (0 : ℝ) T, W t ω ≤ q) ∧ W T ω ≤ b} =ᵐ[
      gaussianCoefficientLaw] (E \ S : Set GaussianCoefficientSpace) := by
    filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
    apply propext
    have hx := continuous_strict_crossing_iff_uniform_dyadic (fun t ↦ W t ω)
      (continuous_const.mul (hω.comp (continuous_id.div_const T))) T q hT
    have hf : (∀ t ∈ Set.Icc (0 : ℝ) T, W t ω ≤ q) ↔
        ¬∃ t ∈ Set.Icc (0 : ℝ) T, q < W t ω := by
      simp only [not_exists, not_and, not_lt]
    change ((∀ t ∈ Set.Icc (0 : ℝ) T, W t ω ≤ q) ∧ W T ω ≤ b) ↔
      W T ω ≤ b ∧ ¬((∃ n : ℕ, ∃ k ≤ 2 ^ n,
        q < W (stoppedUniformTimeGrid 0 T (2 ^ n) k) ω) ∧ W T ω ≤ b)
    rw [← hx, hf]
    constructor
    · intro h
      exact ⟨h.2, fun hbad ↦ h.1 hbad.1⟩
    · intro h
      exact ⟨fun hbad ↦ h.2 ⟨hbad, h.1⟩, h.1⟩
  rw [measureReal_congr he, measureReal_sdiff hsub hS, hE, hprob]

end SRWTightness
