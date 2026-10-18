import SRWTightness.GaussianGridEndpointJoint
import SRWTightness.GaussianGridEndpointCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def gaussianGridFinalIncrement (T : ℕ → ℝ) (n : ℕ)
    (p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) : ℝ :=
  p.1 (Fin.last n) - gaussianGridPath T n p (T n)

theorem gaussianGridFinalIncrement_joint (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) :
    IsGaussianProcess
      (Sum.elim (fun v : Set.Icc (0 : ℝ) (T n) ↦ fun p ↦ gaussianGridPath T n p v)
        (fun _ : Unit ↦ gaussianGridFinalIncrement T n))
      ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)) := by
  classical
  apply (gaussianGridEndpointProcess_gaussian T n hgap).of_isGaussianProcess
  rintro (v | u)
  · refine ⟨{some (v : ℝ)}, ContinuousLinearMap.proj ⟨some (v : ℝ), by simp⟩, ?_⟩
    intro p
    rfl
  · refine ⟨{none, some (T n)},
      { toFun x := x ⟨none, by simp⟩ - x ⟨some (T n), by simp⟩
        map_add' x y := by simp; ring
        map_smul' c x := by simp; ring }, ?_⟩
    intro p
    rfl

theorem gaussianGridFinalIncrement_covariance (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hT : T 0 = 0) (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j)
    (v : ℝ) (hv : 0 ≤ v) (hv' : v ≤ T n) :
    cov[fun p ↦ gaussianGridPath T n p v, gaussianGridFinalIncrement T n;
      (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)] = 0 := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T (n + 1))
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  have hG := gaussianGridEndpointProcess_gaussian T n hg
  have h0 : 0 ≤ T n := by
    have hh := timeGridTime_mono T (n + 1) (fun j hj ↦ by linarith [hgap j hj])
      (Nat.zero_le n) (by omega : n ≤ n + 1)
    simpa only [hT] using hh
  unfold gaussianGridFinalIncrement
  have hc := covariance_fun_sub_right (hG.hasGaussianLaw_eval (some v)).memLp_two
    (hG.hasGaussianLaw_eval none).memLp_two (hG.hasGaussianLaw_eval (some (T n))).memLp_two
  change cov[fun p ↦ gaussianGridPath T n p v,
    fun p ↦ p.1 (Fin.last n) - gaussianGridPath T n p (T n); _] =
    cov[fun p ↦ gaussianGridPath T n p v, fun p ↦ p.1 (Fin.last n); _] -
    cov[fun p ↦ gaussianGridPath T n p v, fun p ↦ gaussianGridPath T n p (T n); _] at hc
  rw [hc, gaussianGridPath_site_covariance T n hn hT hgap v hv hv',
    gaussianGridPath_covariance T n hn hT hgap v (T n) hv hv' h0 le_rfl,
    min_eq_left hv', sub_self]

/-- The final Gaussian increment is independent of the entire preceding path. -/
theorem gaussianGridFinalIncrement_indep_path (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hT : T 0 = 0) (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) :
    IndepFun (fun p (v : Set.Icc (0 : ℝ) (T n)) ↦ gaussianGridPath T n p v)
      (gaussianGridFinalIncrement T n)
      ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)) := by
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  have hG := gaussianGridFinalIncrement_joint T n hg
  have hh := IsGaussianProcess.indepFun_of_covariance_eq_zero hG
    (fun v ↦ hG.aemeasurable (Sum.inl v)) (fun u ↦ hG.aemeasurable (Sum.inr u))
    (fun v _ ↦ gaussianGridFinalIncrement_covariance T n hn hT hgap v v.property.1 v.property.2)
  exact hh.comp measurable_id (measurable_pi_apply ())

end SRWTightness
