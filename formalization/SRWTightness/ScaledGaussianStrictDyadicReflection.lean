import SRWTightness.ScaledGaussianDyadicReflection

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SRWTightness

/-- Strict dyadic crossing has the same exact reflected endpoint tail. -/
theorem scaled_gaussian_strict_dyadic_reflection (T q b : ℝ) (hT : 0 < T)
    (hq : 0 < q) (hb : b < q) :
    gaussianCoefficientLaw.real {ω |
      (∃ n : ℕ, ∃ k ≤ 2 ^ n,
        q < Real.sqrt T * gaussianDyadicPath ω (stoppedUniformTimeGrid 0 T (2 ^ n) k / T)) ∧
      Real.sqrt T * gaussianDyadicPath ω (T / T) ≤ b} =
      (gaussianReal 0 T.toNNReal).real (Set.Ici (2 * q - b)) := by
  let S : Set GaussianCoefficientSpace := {ω |
    (∃ n : ℕ, ∃ k ≤ 2 ^ n,
      q < Real.sqrt T * gaussianDyadicPath ω (stoppedUniformTimeGrid 0 T (2 ^ n) k / T)) ∧
    Real.sqrt T * gaussianDyadicPath ω (T / T) ≤ b}
  let C : ℝ → Set GaussianCoefficientSpace := fun c ↦ {ω |
    (∃ n : ℕ, ∃ k ≤ 2 ^ n,
      c ≤ Real.sqrt T * gaussianDyadicPath ω (stoppedUniformTimeGrid 0 T (2 ^ n) k / T)) ∧
    Real.sqrt T * gaussianDyadicPath ω (T / T) ≤ b}
  have hu : gaussianCoefficientLaw.real S ≤
      (gaussianReal 0 T.toNNReal).real (Set.Ici (2 * q - b)) := by
    rw [← scaled_gaussian_dyadic_reflection T q b hT hq hb]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    rintro ω ⟨⟨n, k, hk, hcross⟩, hend⟩
    exact ⟨⟨n, k, hk, hcross.le⟩, hend⟩
  have hl (δ : ℝ) (hδ : 0 < δ) :
      (gaussianReal 0 T.toNNReal).real (Set.Ici (2 * (q + δ) - b)) ≤
        gaussianCoefficientLaw.real S := by
    rw [← scaled_gaussian_dyadic_reflection T (q + δ) b hT (by linarith) (by linarith)]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    rintro ω ⟨⟨n, k, hk, hcross⟩, hend⟩
    exact ⟨⟨n, k, hk, by linarith⟩, hend⟩
  apply le_antisymm hu
  have hg : Continuous (fun δ : ℝ ↦ gaussianCoefficientLaw.real
      {ω | 2 * (q + δ) - b ≤ Real.sqrt T * gaussianDyadicPath ω (T / T)}) :=
    (scaled_gaussian_endpoint_tail_continuous T hT).comp
      ((continuous_const.mul (continuous_const.add continuous_id)).sub continuous_const)
  have ht := hg.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht' : Tendsto (fun n : ℕ ↦ (gaussianReal 0 T.toNNReal).real
      (Set.Ici (2 * (q + 1 / ((n : ℝ) + 1)) - b))) atTop
      (nhds ((gaussianReal 0 T.toNNReal).real (Set.Ici (2 * q - b)))) := by
    simpa only [Function.comp_def, scaled_gaussian_endpoint_tail T _ hT, add_zero] using ht
  exact le_of_tendsto ht' (Eventually.of_forall (fun n ↦ hl _ (by positivity)))

end SRWTightness
