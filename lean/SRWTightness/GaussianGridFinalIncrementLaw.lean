import SRWTightness.GaussianGridFinalIncrement

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem gaussianGridSite_covariance_self (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) :
    cov[fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ p.1 (Fin.last n), fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ p.1 (Fin.last n);
      (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)] = T (n + 1) := by
  let K := brownianTimeMatrix T (n + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hm := gaussianCoordinateLaw_coordinate_memLp_two K (Fin.last n)
  have hh := covariance_product_sums (gaussianCoordinateLaw K) (independentBridgeLaw ℕ)
    (fun x ↦ x (Fin.last n)) (fun x ↦ x (Fin.last n)) (fun _ ↦ 0) (fun _ ↦ 0)
    hm hm (memLp_const 0) (memLp_const 0)
  simp only [add_zero, covariance_const_left] at hh
  rw [hh, gaussianCoordinateLaw_covariance K
    (brownianTimeMatrix_posDef_of_unit_gaps T (n + 1) hT hgap).posSemidef]
  simp [K, brownianTimeMatrix]

theorem gaussianGridFinalIncrement_mean (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hT : T 0 = 0) (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) :
    (∫ p, gaussianGridFinalIncrement T n p
      ∂(gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)) = 0 := by
  let K := brownianTimeMatrix T (n + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  have hG := gaussianGridEndpointProcess_gaussian T n hg
  unfold gaussianGridFinalIncrement
  have hsite : Integrable (fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ p.1 (Fin.last n))
      ((gaussianCoordinateLaw K).prod (independentBridgeLaw ℕ)) :=
    (hG.hasGaussianLaw_eval none).integrable
  have hpath : Integrable (fun p ↦ gaussianGridPath T n p (T n))
      ((gaussianCoordinateLaw K).prod (independentBridgeLaw ℕ)) :=
    (hG.hasGaussianLaw_eval (some (T n))).integrable
  rw [integral_sub hsite hpath,
    integral_fun_fst (μ := gaussianCoordinateLaw K) (ν := independentBridgeLaw ℕ)
      (fun x ↦ x (Fin.last n)), gaussianCoordinateLaw_mean,
    gaussianGridPath_mean T n hn hg (T n) (timeGridTime_mono T n hg (Nat.zero_le n) le_rfl) le_rfl]
  simp

theorem gaussianGridFinalIncrement_variance (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hT : T 0 = 0) (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) :
    Var[gaussianGridFinalIncrement T n;
      (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)] =
        T (n + 1) - T n := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T (n + 1))
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  have hG := gaussianGridEndpointProcess_gaussian T n hg
  have h0 : 0 ≤ T n := by
    simpa only [hT] using timeGridTime_mono T n hg (Nat.zero_le n) le_rfl
  have hs := (hG.hasGaussianLaw_eval none).memLp_two
  have hb := (hG.hasGaussianLaw_eval (some (T n))).memLp_two
  change MemLp (fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦
    p.1 (Fin.last n)) 2 _ at hs
  change MemLp (fun p ↦ gaussianGridPath T n p (T n)) 2 _ at hb
  unfold gaussianGridFinalIncrement
  rw [variance_fun_sub hs hb, ← covariance_self hs.aemeasurable, ← covariance_self hb.aemeasurable]
  change cov[fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ p.1 (Fin.last n), fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ p.1 (Fin.last n); _] -
    2 * cov[fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ p.1 (Fin.last n), fun p ↦ gaussianGridPath T n p (T n); _] +
    cov[fun p ↦ gaussianGridPath T n p (T n), fun p ↦ gaussianGridPath T n p (T n); _] = _
  rw [gaussianGridSite_covariance_self T n hT hgap,
    covariance_comm (fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ p.1 (Fin.last n)) (fun p ↦ gaussianGridPath T n p (T n)),
    gaussianGridPath_site_covariance T n hn hT hgap (T n) h0 le_rfl,
    gaussianGridPath_covariance T n hn hT hgap (T n) (T n) h0 le_rfl h0 le_rfl, min_self]
  ring

theorem gaussianGridFinalIncrement_law (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hT : T 0 = 0) (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) :
    ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)).map
      (gaussianGridFinalIncrement T n) = gaussianReal 0 (T (n + 1) - T n).toNNReal := by
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  have hh := ((gaussianGridFinalIncrement_joint T n hg).hasGaussianLaw_eval (Sum.inr ())).map_eq_gaussianReal
  simp only [Sum.elim_inr] at hh
  rw [gaussianGridFinalIncrement_mean T n hn hT hgap,
    gaussianGridFinalIncrement_variance T n hn hT hgap] at hh
  exact hh

end SRWTightness
