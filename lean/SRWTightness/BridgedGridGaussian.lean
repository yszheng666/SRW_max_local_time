import SRWTightness.GridInterpolationGaussian
import SRWTightness.GridBridgeGaussian
import SRWTightness.BridgedGridCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem timeGridInterpolation_measurable_nodes {Ω : Type*} [MeasurableSpace Ω]
    (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ j ≤ n, Measurable (X j)) (v : ℝ) :
    Measurable (fun ω ↦ timeGridInterpolation T (fun j ↦ X j ω) n v) := by
  unfold timeGridInterpolation
  refine (hX 0 (by omega)).add (Finset.measurable_sum _ fun j hj ↦ ?_)
  have hj' := Finset.mem_range.mp hj
  exact measurable_const.mul ((hX (j + 1) (by omega)).sub (hX j (by omega)))

/-- Gaussian nodes and the actual independent bridges give a jointly Gaussian glued path. -/
theorem bridgedGridPath_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1))
    (hX : HasGaussianLaw (fun ω (j : Fin (n + 1)) ↦ X j ω) μ)
    (hXm : ∀ j ≤ n, Measurable (X j)) :
    IsGaussianProcess (fun v p ↦ bridgedGridPath T X n p v)
      (μ.prod (independentBridgeLaw ℕ)) where
  hasGaussianLaw I := by
    let F : Ω → (I → ℝ) := fun ω v ↦ timeGridInterpolation T (fun j ↦ X j ω) n v
    let G : (ℕ → GaussianCoefficientSpace) → (I → ℝ) := fun ω v ↦ timeGridBridge T n ω v
    have hmF : Measurable F := measurable_pi_lambda _
      (fun v ↦ timeGridInterpolation_measurable_nodes T X n hXm v)
    have hmG : Measurable G := measurable_pi_lambda _ (fun v ↦ timeGridBridge_measurable T n v)
    have hF : HasGaussianLaw F μ := (timeGridInterpolation_gaussian μ T X n hX).hasGaussianLaw I
    have hG : HasGaussianLaw G (independentBridgeLaw ℕ) := (timeGridBridge_gaussian T n hgap).hasGaussianLaw I
    have hFp := gaussianLaw_measurePreserving μ (μ.prod (independentBridgeLaw ℕ)) F Prod.fst
      hF hmF measurePreserving_fst
    have hGp := gaussianLaw_measurePreserving (independentBridgeLaw ℕ)
      (μ.prod (independentBridgeLaw ℕ)) G Prod.snd hG hmG measurePreserving_snd
    have hh := iIndepFun.hasGaussianLaw_fun_add hFp hGp (indepFun_prod hmF hmG)
    exact hh

end SRWTightness
