import SRWTightness.GaussianGridTerminalCorrection
import SRWTightness.ConditionalMomentIntegral
import SRWTightness.GaussianSmallDiagonalComparison

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The terminal correction moment yields a lower bound under the perturbed covariance. -/
theorem gaussianGrid_terminal_sigma_lower (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < (n + 1) + 1, 1 ≤ T (j + 1) - T j)
    (At V d q a ε R γ C : ℝ) (hε : 0 ≤ ε) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hAt : |At - (2 * d + q)| ≤ ε) (hV : |V - d| ≤ R)
    (e : Fin ((n + 1) + 1) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hesmall : ∀ i, e i ≤ 1 / 8) :
    let K := brownianTimeMatrix T ((n + 1) + 1)
    let μ := (gaussianCoordinateLaw K).prod (independentBridgeLaw ℕ)
    let E := gaussianGridTerminalEvent T (n + 1) (q - a - 1) (q - a) At V q d γ
    0 < μ.real E →
    (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ T (n + 1) →
      Integrable (fun p ↦ (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2) (cond μ E) ∧
      (∫ p, (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2 ∂cond μ E) ≤ C * (s - r)) →
    Real.exp (-((8 * max C ((|a| + 2 + ε + 2 * R) ^ 2)) * ∑ i, e i) / 2) *
      μ.real E ≤ ((gaussianCoordinateLaw (K - Matrix.diagonal e)).prod
        (independentBridgeLaw ℕ)).real E := by
  dsimp only
  intro hpos hm
  let K := brownianTimeMatrix T ((n + 1) + 1)
  let μ := (gaussianCoordinateLaw K).prod (independentBridgeLaw ℕ)
  let E := gaussianGridTerminalEvent T (n + 1) (q - a - 1) (q - a) At V q d γ
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hc := gaussianGrid_terminal_correction T n hT hgap At V d q a ε R γ C
    hε hR hC hAt hV e he hesmall hpos hm
  have hi := conditional_moment_event_integral μ E
    (fun p ↦ gaussianInverseCorrection K (K - Matrix.diagonal e) p.1) hpos hc.1 _ hc.2
  have hK : K.PosDef := by
    dsimp [K]
    rw [brownianTimeMatrix_eq_increment T hT _ (fun k hk ↦ by linarith [hgap k hk])]
    exact incrementCovariance_posDef _ 1 (by norm_num) (fun i ↦ hgap i.val i.isLt)
  have hlo (y : Fin ((n + 1) + 1) → ℝ) :
      (1 / 4 : ℝ) * (∑ i, y i ^ 2) ≤ y ⬝ᵥ (K *ᵥ y) := by
    have hh := brownianTimeMatrix_quadratic_lower T hT _ 1 (by norm_num) hgap y
    simpa only [K, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hh
  have hs : ∀ i, e i ≤ (1 / 4 : ℝ) / 2 := by
    intro i
    linarith [hesmall i]
  have hd := gaussian_smallDiagonal_event_comparison (independentBridgeLaw ℕ) K hK
    (1 / 4) (by norm_num) hlo e he hs
  exact hd.2.2 E (gaussianGridTerminalEvent_measurable _ _ _ _ _ _ _ _ _) _ hi.2

end SRWTightness
