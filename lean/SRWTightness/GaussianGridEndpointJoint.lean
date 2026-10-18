import SRWTightness.GridEndpointLinearGaussian
import SRWTightness.GridBridgeGaussian

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

theorem gaussianProcess_option_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℝ → Ω → ℝ) (hX : IsGaussianProcess X μ) :
    IsGaussianProcess (fun o : Option ℝ ↦ fun ω ↦ o.elim 0 (fun v ↦ X v ω)) μ := by
  classical
  apply hX.of_isGaussianProcess
  intro o
  cases o with
  | none =>
    refine ⟨∅, 0, ?_⟩
    intro ω
    rfl
  | some v =>
    refine ⟨{v}, ContinuousLinearMap.proj ⟨v, by simp⟩, ?_⟩
    intro ω
    rfl

noncomputable def gaussianGridEndpointProcess (T : ℕ → ℝ) (n : ℕ) (o : Option ℝ)
    (p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) : ℝ :=
  o.elim (p.1 (Fin.last n)) (fun v ↦ gaussianGridPath T n p v)

theorem gaussianGridEndpointProcess_gaussian (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) :
    IsGaussianProcess (gaussianGridEndpointProcess T n)
      ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)) where
  hasGaussianLaw I := by
    let K := brownianTimeMatrix T (n + 1)
    let μ := gaussianCoordinateLaw K
    let ν := independentBridgeLaw ℕ
    letI := gaussianCoordinateLaw_isProbabilityMeasure K
    let F : (Fin (n + 1) → ℝ) → (I → ℝ) := fun x o ↦
      o.val.elim (x (Fin.last n)) (fun v ↦ timeGridInterpolation T (observationMeshValue x) n v)
    let G : (ℕ → GaussianCoefficientSpace) → (I → ℝ) := fun ω o ↦
      o.val.elim 0 (fun v ↦ timeGridBridge T n ω v)
    have hmF : Measurable F := by
      apply measurable_pi_lambda
      intro o
      cases ho : o.val
      · simpa only [F, ho, Option.elim_none] using measurable_pi_apply (Fin.last n)
      · simpa only [F, ho, Option.elim_some] using
          timeGridInterpolation_measurable_nodes T (fun j x ↦ observationMeshValue x j) n
            (fun j _ ↦ observationMeshValue_measurable n j) _
    have hmG : Measurable G := by
      apply measurable_pi_lambda
      intro o
      cases ho : o.val
      · simpa only [G, ho, Option.elim_none] using
          (measurable_const : Measurable (fun _ : ℕ → GaussianCoefficientSpace ↦ (0 : ℝ)))
      · simpa only [G, ho, Option.elim_some] using timeGridBridge_measurable T n _
    have hF : HasGaussianLaw F μ := (gaussianGridInterpolation_joint_site T n K).hasGaussianLaw I
    have hG : HasGaussianLaw G ν :=
      (gaussianProcess_option_zero ν _ (timeGridBridge_gaussian T n hgap)).hasGaussianLaw I
    have hFp := gaussianLaw_measurePreserving μ (μ.prod ν) F Prod.fst hF hmF measurePreserving_fst
    have hGp := gaussianLaw_measurePreserving ν (μ.prod ν) G Prod.snd hG hmG measurePreserving_snd
    apply (iIndepFun.hasGaussianLaw_fun_add hFp hGp (indepFun_prod hmF hmG)).congr
    filter_upwards [] with p
    ext o
    cases ho : o.val <;>
      simp [F, G, ho, Finset.restrict_def, gaussianGridEndpointProcess, gaussianGridPath, bridgedGridPath]

end SRWTightness
