import SRWTightness.GeometricDiskWeightBounds
import SRWTightness.GaussianEquilibriumErrorUpper

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Actual disk weights discharge the summability input at every fixed geometric ratio at least two. -/
theorem gaussian_disk_geometric_error_upper {n : ℕ} {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (b : Site) (A R q g : ℝ) (hA : 4 ≤ A)
    (hq : 2 ≤ q) (hg : 0 < g) (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R)
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : Fin n → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (hsmall : diskEquilibriumWeightConstant / A ≤ g * c) :
    (K - Matrix.diagonal (fun i : Fin n ↦ equilibriumDiscreteError
      (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset (A * q ^ i.val))) g)).PosDef ∧
    (gaussianCoordinateLaw (K - Matrix.diagonal (fun i : Fin n ↦ equilibriumDiscreteError
      (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset (A * q ^ i.val))) g))).prod ν ≤
      ENNReal.ofReal (Real.exp ((diskEquilibriumWeightConstant / A) / (g * c))) •
        ((gaussianCoordinateLaw K).prod ν) := by
  have hA0 : 0 < A := by linarith
  have hq0 : 0 < q := by linarith
  have ha (i : Fin n) : 0 < A * q ^ i.val := by positivity
  have hKD (i : Fin n) : translateFinset b (diskFinset (A * q ^ i.val)) ⊆
      translateFinset b (diskFinset R) := by
    apply Finset.image_subset_image
    exact diskFinset_mono _ _ (ha i).le (by linarith [hsep i, ha i])
  have hne (i : Fin n) : (translateFinset b (diskFinset (A * q ^ i.val))).Nonempty :=
    Finset.Nonempty.image ⟨0, zero_mem_diskFinset _ (ha i)⟩ _
  exact gaussian_equilibrium_error_upper ν _ _ hKD hne g _ hg
    (div_nonneg diskEquilibriumWeightConstant_pos.le hA0.le)
    (fun i x _ ↦ equilibriumWeight_geometric_ratio_upper b A R q hA hq i.val (hsep i) x)
    K hK c hc hlo hsmall

end SRWTightness
