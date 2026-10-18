import SRWTightness.TimeGridInterpolationNodes
import Mathlib.Probability.Moments.Covariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem covariance_two_linear_combinations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y Z W : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ)
    (a b c d : ℝ) :
    cov[fun ω ↦ a * X ω + b * Y ω, fun ω ↦ c * Z ω + d * W ω; μ] =
      a * c * cov[X, Z; μ] + a * d * cov[X, W; μ] +
      (b * c * cov[Y, Z; μ] + b * d * cov[Y, W; μ]) := by
  change cov[a • X + b • Y, c • Z + d • W; μ] = _
  rw [covariance_add_left (hX.const_smul a) (hY.const_smul b)
    ((hZ.const_smul c).add (hW.const_smul d)),
    covariance_add_right (hX.const_smul a) (hZ.const_smul c) (hW.const_smul d),
    covariance_add_right (hY.const_smul b) (hZ.const_smul c) (hW.const_smul d)]
  simp only [covariance_smul_left, covariance_smul_right]
  ring

theorem timeGridInterpolation_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k < n) (v : ℝ)
    (hl : T k ≤ v) (hu : v ≤ T (k + 1))
    (hX : MemLp (X k) 2 μ) (hY : MemLp (X (k + 1)) 2 μ) :
    MemLp (fun ω ↦ timeGridInterpolation T (fun j ↦ X j ω) n v) 2 μ := by
  have he : (fun ω ↦ timeGridInterpolation T (fun j ↦ X j ω) n v) =
      fun ω ↦ (1 - (v - T k) / (T (k + 1) - T k)) * X k ω +
        ((v - T k) / (T (k + 1) - T k)) * X (k + 1) ω :=
    funext fun ω ↦ timeGridInterpolation_interval T (fun j ↦ X j ω) n k hgap hk v hl hu
  rw [he]
  exact (hX.const_mul _).add (hY.const_mul _)

theorem timeGridInterpolation_covariance_nodes {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n i j : ℕ)
    (hgap : ∀ k < n, T k < T (k + 1)) (hi : i < n) (hj : j < n) (s t : ℝ)
    (hs : T i ≤ s) (hs' : s ≤ T (i + 1)) (ht : T j ≤ t) (ht' : t ≤ T (j + 1))
    (hX : ∀ k ≤ n, MemLp (X k) 2 μ) :
    let r := (s - T i) / (T (i + 1) - T i)
    let u := (t - T j) / (T (j + 1) - T j)
    cov[fun ω ↦ timeGridInterpolation T (fun k ↦ X k ω) n s,
      fun ω ↦ timeGridInterpolation T (fun k ↦ X k ω) n t; μ] =
      (1-r)*(1-u)*cov[X i, X j; μ] + (1-r)*u*cov[X i, X (j+1); μ] +
      (r*(1-u)*cov[X (i+1), X j; μ] + r*u*cov[X (i+1), X (j+1); μ]) := by
  have he k hk v hv hv' : (fun ω ↦ timeGridInterpolation T (fun l ↦ X l ω) n v) =
      fun ω ↦ (1 - (v - T k) / (T (k + 1) - T k)) * X k ω +
        ((v - T k) / (T (k + 1) - T k)) * X (k + 1) ω :=
    funext fun ω ↦ timeGridInterpolation_interval T (fun l ↦ X l ω) n k hgap hk v hv hv'
  dsimp only
  rw [he i hi s hs hs', he j hj t ht ht']
  exact covariance_two_linear_combinations μ _ _ _ _ (hX i (by omega))
    (hX (i+1) (by omega)) (hX j (by omega)) (hX (j+1) (by omega)) _ _ _ _

end SRWTightness
