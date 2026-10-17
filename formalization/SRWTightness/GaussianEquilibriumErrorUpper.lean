import SRWTightness.GaussianSmallDiagonalComparison
import SRWTightness.EquilibriumDiscreteErrorBounds

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- A summable actual equilibrium-weight bound gives dimension-independent event comparison.
The displayed geometric weight estimate remains the analytic input to establish for disk scales. -/
theorem gaussian_equilibrium_error_upper {n : ℕ} {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν]
    (D : Finset Site) (A : Fin n → Finset Site) (hAD : ∀ i, A i ⊆ D)
    (hne : ∀ i, (A i).Nonempty) (g W : ℝ) (hg : 0 < g) (hW : 0 ≤ W)
    (hweight : ∀ i x, x ∈ A i → equilibriumWeight D (A i) x ≤ W * (1 / 2 : ℝ) ^ i.val)
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : Fin n → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (hsmall : W ≤ g * c) :
    (K - Matrix.diagonal (fun i ↦ equilibriumDiscreteError D (A i) g)).PosDef ∧
      (gaussianCoordinateLaw (K - Matrix.diagonal (fun i ↦ equilibriumDiscreteError D (A i) g))).prod ν ≤
        ENNReal.ofReal (Real.exp (W / (g * c))) • ((gaussianCoordinateLaw K).prod ν) := by
  let e : Fin n → ℝ := fun i ↦ equilibriumDiscreteError D (A i) g
  have he (i : Fin n) : 0 ≤ e i := equilibriumDiscreteError_nonneg D (A i) g hg.le
  have hb (i : Fin n) : e i ≤ c / 2 := by
    have hw (x : Site) (hx : x ∈ A i) : equilibriumWeight D (A i) x ≤ W :=
      (hweight i x hx).trans (mul_le_of_le_one_right hW (pow_le_one₀ (by norm_num) (by norm_num)))
    have hh := equilibriumDiscreteError_le_weight_bound D (A i) (hAD i) (hne i) g W hg hw
    apply hh.trans
    apply (div_le_iff₀ (by positivity : 0 < 2 * g)).mpr
    nlinarith
  have hs := equilibriumDiscreteError_sum_le_of_geometric_weight D A hAD hne g W hg hW hweight
  have hsum : (∑ i, e i) / c ≤ W / (g * c) := by
    calc
      _ ≤ (W / g) / c := div_le_div_of_nonneg_right hs hc.le
      _ = _ := by ring
  have hh := gaussian_smallDiagonal_event_comparison ν K hK c hc hlo e he hb
  refine ⟨hh.1, hh.2.1.trans ?_⟩
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hsum)) _

end SRWTightness
