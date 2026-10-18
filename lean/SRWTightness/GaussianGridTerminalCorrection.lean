import SRWTightness.GaussianGridCorrectionMoment
import SRWTightness.GaussianGridFinalConditionalMoment

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Terminal conditional path moments control the covariance correction on the same event. -/
theorem gaussianGrid_terminal_correction (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
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
    Integrable (fun p ↦ gaussianInverseCorrection K (K - Matrix.diagonal e) p.1)
      (cond μ E) ∧
      (∫ p, gaussianInverseCorrection K (K - Matrix.diagonal e) p.1 ∂cond μ E) ≤
        (8 * max C ((|a| + 2 + ε + 2 * R) ^ 2)) * ∑ i, e i := by
  dsimp only
  intro hpos hm
  have hf := gaussianGrid_final_conditional_moment T (n + 1) At V d q a ε R
    hε hR hAt hV γ hpos
  exact gaussianGrid_correction_moment T n hT hgap _ C
    ((|a| + 2 + ε + 2 * R) ^ 2) hC (sq_nonneg _) hm hf e he hesmall

end SRWTightness
