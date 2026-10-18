import SRWTightness.BridgedGridGaussian

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem independentLocalizedBridge_mean (a b v : ℝ) (hab : a < b) (j : ℕ) :
    (∫ ω : ℕ → GaussianCoefficientSpace, localizedIntervalBridge a b v (ω j)
      ∂independentBridgeLaw ℕ) = 0 := by
  have hm : (independentBridgeLaw ℕ).map (fun ω ↦ ω j) = gaussianCoefficientLaw :=
    Measure.infinitePi_map_eval _ j
  have hh := integral_map (μ := independentBridgeLaw ℕ) (φ := fun ω ↦ ω j)
    (f := localizedIntervalBridge a b v) (measurable_pi_apply j).aemeasurable
    (localizedIntervalBridge_measurable a b v).aestronglyMeasurable
  rw [hm] at hh
  exact hh.symm.trans (localizedIntervalBridge_mean a b v hab)

theorem timeGridBridge_mean (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (v : ℝ) :
    (∫ ω, timeGridBridge T n ω v ∂independentBridgeLaw ℕ) = 0 := by
  unfold timeGridBridge
  rw [integral_finsetSum _ (fun j hj ↦
    (independentLocalizedBridge_memLp _ _ v (hgap j (Finset.mem_range.mp hj)) j).integrable (by norm_num))]
  apply Finset.sum_eq_zero
  intro j hj
  exact independentLocalizedBridge_mean _ _ v (hgap j (Finset.mem_range.mp hj)) j

theorem timeGridInterpolation_mean_zero_inside {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k < n) (v : ℝ)
    (hl : T k ≤ v) (hu : v ≤ T (k + 1))
    (hX : ∀ j ≤ n, MemLp (X j) 2 μ) (hm : ∀ j ≤ n, (∫ ω, X j ω ∂μ) = 0) :
    (∫ ω, timeGridInterpolation T (fun j ↦ X j ω) n v ∂μ) = 0 := by
  simp_rw [timeGridInterpolation_interval T _ n k hgap hk v hl hu]
  rw [integral_add
    (((hX k (by omega)).const_mul _).integrable (by norm_num))
    (((hX (k + 1) (by omega)).const_mul _).integrable (by norm_num)),
    integral_const_mul, integral_const_mul, hm k (by omega), hm (k + 1) (by omega)]
  simp

theorem bridgedGridPath_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hn : 0 < n) (hgap : ∀ j < n, T j < T (j + 1)) (v : ℝ)
    (hl : T 0 ≤ v) (hu : v ≤ T n)
    (hX : ∀ j ≤ n, MemLp (X j) 2 μ) (hm : ∀ j ≤ n, (∫ ω, X j ω ∂μ) = 0) :
    (∫ p, bridgedGridPath T X n p v ∂μ.prod (independentBridgeLaw ℕ)) = 0 := by
  obtain ⟨k, hk, hkl, hku⟩ := exists_timeGridInterval T n hn v hl hu
  have hi := timeGridInterpolation_memLp μ T X n k hgap hk v hkl hku
    (hX k (by omega)) (hX (k + 1) (by omega))
  have hb := timeGridBridge_memLp_inside T n k hgap hk v hkl hku
  unfold bridgedGridPath
  rw [integral_add ((hi.comp_fst _).integrable (by norm_num))
    ((hb.comp_snd μ).integrable (by norm_num)), integral_fun_fst (μ := μ) (ν := independentBridgeLaw ℕ)
      (fun ω ↦ timeGridInterpolation T (fun j ↦ X j ω) n v),
    integral_fun_snd (μ := μ) (ν := independentBridgeLaw ℕ) (fun ω ↦ timeGridBridge T n ω v),
    timeGridInterpolation_mean_zero_inside μ T X n k hgap hk v hkl hku hX hm,
    timeGridBridge_mean T n hgap v]
  simp

theorem bridgedGridPath_ae_continuous {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) :
    ∀ᵐ p ∂μ.prod (independentBridgeLaw ℕ), Continuous (bridgedGridPath T X n p) := by
  have hh : ∀ᵐ p ∂μ.prod (independentBridgeLaw ℕ), Continuous (timeGridBridge T n p.2) :=
    measurePreserving_snd.quasiMeasurePreserving.ae (timeGridBridge_ae_continuous T n)
  filter_upwards [hh] with p hp
  exact (timeGridInterpolation_continuous T (fun j ↦ X j p.1) n).add hp

theorem bridgedGridPath_node {Ω : Type*} (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k ≤ n)
    (p : Ω × (ℕ → GaussianCoefficientSpace)) :
    bridgedGridPath T X n p (T k) = X k p.1 := by
  rw [bridgedGridPath, timeGridInterpolation_node T _ n k hgap hk,
    timeGridBridge_node T n k hgap hk, add_zero]

end SRWTightness
