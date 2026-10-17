import SRWTightness.ExternalRaicInterface

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

/-- Apply the external convex CLT only after checking the actual whitened vector data. -/
theorem raic_whitened_comparison {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (hBE : RaicConvexCLTInput Ω ι)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (n : ℕ)
    (X : Fin n → Ω → EuclideanSpace ℝ ι) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X ρ)
    (hmom : ∀ j, Integrable (X j) ρ ∧ (∫ ω, X j ω ∂ρ) = 0 ∧ MemLp (X j) 2 ρ)
    (hcov : ∀ r s : ι, (∑ j, covariance (fun ω ↦ X j ω r) (fun ω ↦ X j ω s) ρ) =
      if r = s then 1 else 0)
    (hthird : ∀ j, Integrable (fun ω ↦ ‖X j ω‖ ^ 3) ρ)
    (F : Ω → ι → ℝ) (hF : Measurable F) (m : ι → ℝ)
    (K : Matrix ι ι ℝ) (hK : K.PosDef)
    (hsum : ∀ ω, (∑ j, X j ω) =
      toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt K)⁻¹) (toLp 2 (F ω - m)))
    (δ : ℝ) (hδ : (42 * (Fintype.card ι : ℝ) ^ (1 / 4 : ℝ) + 16) *
      (∑ j, ∫ ω, ‖X j ω‖ ^ 3 ∂ρ) ≤ δ)
    (A : Set (ι → ℝ)) (hA : MeasurableSet A) (hc : Convex ℝ A) :
    |(ρ.map F).real A - (gaussianMeanCoordinateLaw m K).real A| ≤ δ := by
  apply convex_gaussian_whitening_comparison ρ F hF m K hK δ _ A hA hc
  intro S hS hcS
  have hh := (hBE ρ inferInstance n X hX hind hmom hcov hthird S hS hcS).trans hδ
  have he : (fun ω i ↦ (∑ j, X j ω) i) =
      (fun ω ↦ (CFC.sqrt K)⁻¹ *ᵥ (F ω - m)) := by
    funext ω i
    rw [hsum]
    rfl
  rwa [he] at hh

end SRWTightness
