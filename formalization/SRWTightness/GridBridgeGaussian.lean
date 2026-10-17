import SRWTightness.LocalizedBridgeCovariance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem gaussianLaw_measurePreserving {Ω Ξ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [TopologicalSpace E]
    [AddCommMonoid E] [Module ℝ E] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure Ξ) (X : Ω → E) (f : Ξ → Ω)
    (hX : HasGaussianLaw X μ) (hm : Measurable X) (hf : MeasurePreserving f ν μ) :
    HasGaussianLaw (fun ω ↦ X (f ω)) ν where
  isGaussian_map := by
    change IsGaussian (ν.map (X ∘ f))
    rw [← Measure.map_map hm hf.measurable, hf.map_eq]
    exact hX.isGaussian_map

/-- Every finite collection of times of the actual independent grid bridge is jointly Gaussian. -/
theorem timeGridBridge_gaussian (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) :
    IsGaussianProcess (fun v ω ↦ timeGridBridge T n ω v) (independentBridgeLaw ℕ) where
  hasGaussianLaw I := by
    classical
    let Y : ℕ → GaussianCoefficientSpace → (I → ℝ) :=
      fun j ω v ↦ localizedIntervalBridge (T j) (T (j + 1)) v ω
    have hm (j : ℕ) : Measurable (Y j) :=
      measurable_pi_lambda _ (fun v ↦ localizedIntervalBridge_measurable _ _ _)
    have hg (j : Fin n) : HasGaussianLaw (fun ω : ℕ → GaussianCoefficientSpace ↦ Y j (ω j))
        (independentBridgeLaw ℕ) := by
      apply gaussianLaw_measurePreserving gaussianCoefficientLaw (independentBridgeLaw ℕ)
        (Y j) (fun ω ↦ ω j)
      · exact (localizedIntervalBridge_gaussian _ _ (hgap j j.isLt)).hasGaussianLaw I
      · exact hm j
      · exact measurePreserving_eval_infinitePi (fun _ : ℕ ↦ gaussianCoefficientLaw) j
    have hind : iIndepFun (fun j : Fin n ↦ fun ω : ℕ → GaussianCoefficientSpace ↦ Y j (ω j))
        (independentBridgeLaw ℕ) :=
      (iIndepFun_infinitePi hm).precomp Fin.val_injective
    have hsum := hind.hasGaussianLaw_fun_sum hg
    have he : (fun ω : ℕ → GaussianCoefficientSpace ↦ ∑ j : Fin n, Y j (ω j)) =
        (fun ω ↦ I.restrict (fun v ↦ timeGridBridge T n ω v)) := by
      ext ω v
      simp only [Finset.sum_apply, Y, Finset.restrict_def, timeGridBridge]
      exact Fin.sum_univ_eq_sum_range
        (fun j : ℕ ↦ localizedIntervalBridge (T j) (T (j + 1)) v (ω j)) n
    rw [he] at hsum
    exact hsum

end SRWTightness
