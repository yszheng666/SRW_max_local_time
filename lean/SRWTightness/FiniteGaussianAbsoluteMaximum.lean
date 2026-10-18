import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Order.Lattice

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual maximum absolute coordinate on a nonempty finite observation set. -/
noncomputable def finiteGaussianAbsMaximum {ι : Type*} [Fintype ι]
    (J : Finset ι) (hJ : J.Nonempty) (φ : EuclideanSpace ℝ ι) : ℝ :=
  J.sup' hJ (fun x ↦ |φ x|)

theorem continuous_finiteGaussianAbsMaximum {ι : Type*} [Fintype ι]
    (J : Finset ι) (hJ : J.Nonempty) : Continuous (finiteGaussianAbsMaximum J hJ) := by
  unfold finiteGaussianAbsMaximum
  exact Continuous.finset_sup'_apply hJ (fun x _ ↦ by fun_prop)

theorem finiteGaussianAbsMaximum_nonneg {ι : Type*} [Fintype ι]
    (J : Finset ι) (hJ : J.Nonempty) (φ : EuclideanSpace ℝ ι) :
    0 ≤ finiteGaussianAbsMaximum J hJ φ := by
  obtain ⟨x, hx⟩ := hJ
  exact (abs_nonneg (φ x)).trans (Finset.le_sup' (fun y ↦ |φ y|) hx)

/-- The supremum event is exactly the finite union controlled by the increment estimate. -/
theorem le_finiteGaussianAbsMaximum_iff {ι : Type*} [Fintype ι]
    (J : Finset ι) (hJ : J.Nonempty) (φ : EuclideanSpace ℝ ι) (u : ℝ) :
    u ≤ finiteGaussianAbsMaximum J hJ φ ↔ ∃ x ∈ J, u ≤ |φ x| := by
  unfold finiteGaussianAbsMaximum
  exact Finset.le_sup'_iff hJ

end SRWTightness
