import SRWTightness.GridBrownianCovariance
import SRWTightness.LocalizedBridgeCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem covariance_product_sums {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X Z : Ω → ℝ) (Y W : Ξ → ℝ)
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) (hY : MemLp Y 2 ν) (hW : MemLp W 2 ν) :
    cov[fun p : Ω × Ξ ↦ X p.1 + Y p.2, fun p ↦ Z p.1 + W p.2; μ.prod ν] =
      cov[X, Z; μ] + cov[Y, W; ν] := by
  have hf : cov[fun p : Ω × Ξ ↦ X p.1, fun p ↦ Z p.1; μ.prod ν] = cov[X, Z; μ] := by
    have hh := covariance_map_fun (μ := μ.prod ν) (Z := Prod.fst) (X := X) (Y := Z)
      (by simpa using hX.aestronglyMeasurable) (by simpa using hZ.aestronglyMeasurable)
      measurable_fst.aemeasurable
    simpa using hh.symm
  have hg : cov[fun p : Ω × Ξ ↦ Y p.2, fun p ↦ W p.2; μ.prod ν] = cov[Y, W; ν] := by
    have hh := covariance_map_fun (μ := μ.prod ν) (Z := Prod.snd) (X := Y) (Y := W)
      (by simpa using hY.aestronglyMeasurable) (by simpa using hW.aestronglyMeasurable)
      measurable_snd.aemeasurable
    simpa using hh.symm
  have hz : cov[fun p : Ω × Ξ ↦ Y p.2, fun p ↦ Z p.1; μ.prod ν] = 0 := by
    rw [covariance_comm]
    exact covariance_fst_snd_prod hZ hY
  have hh := covariance_two_linear_combinations (μ.prod ν)
    (fun p ↦ X p.1) (fun p ↦ Y p.2) (fun p ↦ Z p.1) (fun p ↦ W p.2)
    (hX.comp_fst ν) (hY.comp_snd μ) (hZ.comp_fst ν) (hW.comp_snd μ) 1 1 1 1
  simpa only [one_mul, hf, hg, hz, covariance_fst_snd_prod hX hW, add_zero, zero_add] using hh

noncomputable def bridgedGridPath {Ω : Type*} (T : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (n : ℕ) (p : Ω × (ℕ → GaussianCoefficientSpace)) (v : ℝ) : ℝ :=
  timeGridInterpolation T (fun j ↦ X j p.1) n v + timeGridBridge T n p.2 v

theorem timeGridBridge_memLp_inside (T : ℕ → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k < n) (v : ℝ)
    (hl : T k ≤ v) (hu : v ≤ T (k + 1)) :
    MemLp (fun ω ↦ timeGridBridge T n ω v) 2 (independentBridgeLaw ℕ) := by
  rw [funext (timeGridBridge_inside T n k hgap hk v hl hu)]
  exact independentLocalizedBridge_memLp _ _ v (hgap k hk) k

theorem bridgedGridPath_covariance_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n i j : ℕ)
    (hgap : ∀ k < n, T k < T (k + 1)) (hi : i < n) (hj : j < n) (s t : ℝ)
    (hs : T i ≤ s) (hs' : s ≤ T (i + 1)) (ht : T j ≤ t) (ht' : t ≤ T (j + 1))
    (hX : ∀ k ≤ n, MemLp (X k) 2 μ) :
    cov[fun p ↦ bridgedGridPath T X n p s, fun p ↦ bridgedGridPath T X n p t;
      μ.prod (independentBridgeLaw ℕ)] =
      cov[fun ω ↦ timeGridInterpolation T (fun k ↦ X k ω) n s,
        fun ω ↦ timeGridInterpolation T (fun k ↦ X k ω) n t; μ] +
      cov[fun ω ↦ timeGridBridge T n ω s, fun ω ↦ timeGridBridge T n ω t;
        independentBridgeLaw ℕ] := by
  exact covariance_product_sums μ (independentBridgeLaw ℕ) _ _ _ _
    (timeGridInterpolation_memLp μ T X n i hgap hi s hs hs' (hX i (by omega)) (hX (i+1) (by omega)))
    (timeGridInterpolation_memLp μ T X n j hgap hj t ht ht' (hX j (by omega)) (hX (j+1) (by omega)))
    (timeGridBridge_memLp_inside T n i hgap hi s hs hs')
    (timeGridBridge_memLp_inside T n j hgap hj t ht ht')

end SRWTightness
