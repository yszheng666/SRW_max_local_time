import SRWTightness.LaplaceUniquenessNNReal

open MeasureTheory
open scoped NNReal

namespace SRWTightness

 def nonnegativeProjection {ι : Type*} (x : ι → ℝ) : ι → ℝ≥0 :=
  fun i ↦ Real.toNNReal (x i)

 def nonnegativeInclusion {ι : Type*} (x : ι → ℝ≥0) : ι → ℝ := fun i ↦ x i

 theorem measurable_nonnegativeProjection {ι : Type*} :
    Measurable (nonnegativeProjection (ι := ι)) := by unfold nonnegativeProjection; fun_prop

 theorem measurable_nonnegativeInclusion {ι : Type*} :
    Measurable (nonnegativeInclusion (ι := ι)) := by unfold nonnegativeInclusion; fun_prop

 theorem nonnegativeProjection_map_inverse {ι : Type*} (μ : Measure (ι → ℝ))
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) :
    (μ.map nonnegativeProjection).map nonnegativeInclusion = μ := by
  rw [Measure.map_map measurable_nonnegativeInclusion measurable_nonnegativeProjection]
  calc
    μ.map (nonnegativeInclusion ∘ nonnegativeProjection) = μ.map id := by
      apply Measure.map_congr
      filter_upwards [hμ] with x hx
      funext i
      exact Real.coe_toNNReal _ (hx i)
    _ = μ := by rw [Measure.map_id]

 theorem nonnegativeProjection_laplace {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) (f : ι → ℝ) :
    (∫ x : ι → ℝ≥0, Real.exp (-(∑ i, f i * (x i : ℝ))) ∂μ.map nonnegativeProjection) =
      ∫ x : ι → ℝ, Real.exp (-(∑ i, f i * x i)) ∂μ := by
  have hm : Measurable (fun x : ι → ℝ≥0 ↦ Real.exp (-(∑ i, f i * (x i : ℝ)))) := by fun_prop
  rw [integral_map measurable_nonnegativeProjection.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hμ] with x hx
  dsimp only [nonnegativeProjection]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.coe_toNNReal _ (hx i)]

/-- Uniqueness of the multivariate Laplace transform for measures supported on nonnegative vectors. -/
theorem measure_eq_of_laplace_eq_nonneg {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) (hν : ∀ᵐ x ∂ν, ∀ i, 0 ≤ x i)
    (h : ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) →
      (∫ x, Real.exp (-(∑ i, f i * x i)) ∂μ) =
        ∫ x, Real.exp (-(∑ i, f i * x i)) ∂ν) : μ = ν := by
  have he : μ.map nonnegativeProjection = ν.map nonnegativeProjection := by
    apply measure_eq_of_laplace_eq_nnreal
    intro f hf
    rw [nonnegativeProjection_laplace μ hμ f, nonnegativeProjection_laplace ν hν f]
    exact h f hf
  rw [← nonnegativeProjection_map_inverse μ hμ, ← nonnegativeProjection_map_inverse ν hν, he]

end SRWTightness
