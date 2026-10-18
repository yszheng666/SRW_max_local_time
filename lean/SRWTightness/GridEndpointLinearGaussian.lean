import SRWTightness.GaussianGridPath

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

noncomputable def observationMeshCLM (n j : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  if h : 0 < j ∧ j ≤ n then ContinuousLinearMap.proj ⟨j - 1, by omega⟩ else 0

theorem observationMeshCLM_apply (n j : ℕ) (x : Fin (n + 1) → ℝ) :
    observationMeshCLM n j x = observationMeshValue x j := by
  by_cases h : 0 < j ∧ j ≤ n
  · simp [observationMeshCLM, observationMeshValue, h]
  · simp [observationMeshCLM, observationMeshValue, h]

noncomputable def observationInterpolationCLM (T : ℕ → ℝ) (n : ℕ) (v : ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  observationMeshCLM n 0 + ∑ j ∈ Finset.range n,
    timeGridRamp (T j) (T (j + 1)) v • (observationMeshCLM n (j + 1) - observationMeshCLM n j)

theorem observationInterpolationCLM_apply (T : ℕ → ℝ) (n : ℕ) (v : ℝ)
    (x : Fin (n + 1) → ℝ) :
    observationInterpolationCLM T n v x = timeGridInterpolation T (observationMeshValue x) n v := by
  simp [observationInterpolationCLM, observationMeshCLM_apply, timeGridInterpolation]

/-- The interpolation and the retained terminal-site coordinate are jointly Gaussian. -/
theorem gaussianGridInterpolation_joint_site (T : ℕ → ℝ) (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    IsGaussianProcess (fun o : Option ℝ ↦ fun x : Fin (n + 1) → ℝ ↦
      o.elim (x (Fin.last n)) (fun v ↦ timeGridInterpolation T (observationMeshValue x) n v))
      (gaussianCoordinateLaw K) where
  hasGaussianLaw I := by
    classical
    let L : (Fin (n + 1) → ℝ) →L[ℝ] (I → ℝ) :=
      ContinuousLinearMap.pi fun o ↦ o.val.elim (ContinuousLinearMap.proj (Fin.last n))
        (observationInterpolationCLM T n)
    apply ((gaussianCoordinateLaw_joint K).map L).congr
    filter_upwards [] with x
    ext o
    cases ho : o.val <;> simp [L, ho, Finset.restrict_def, observationInterpolationCLM_apply]

end SRWTightness
