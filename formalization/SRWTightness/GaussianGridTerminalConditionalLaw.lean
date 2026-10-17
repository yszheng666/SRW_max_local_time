import SRWTightness.GaussianGridTerminalEventLaw
import SRWTightness.ConditionalMapMoment

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Every measurable terminal path observable transfers with its conditional moment to the actual grid. -/
theorem gaussianGrid_terminal_conditional_observable
    (hReconstruct : BrownianBridgeReconstructionInput)
    (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) (l u At V q d γ : ℝ)
    (f : ((ℝ × (Set.Icc (0 : ℝ) (T n) → ℝ)) × ℝ) → ℝ) (hf : Measurable f)
    (hi : Integrable
      (fun p : (ℝ × GaussianCoefficientSpace) × ℝ ↦
        f ((p.1.1, fun v ↦ endpointBrownianBridge (T n) p.1.1 v p.1.2), p.2))
      (ProbabilityTheory.cond
        (((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).prod
          (gaussianReal 0 (T (n + 1) - T n).toNNReal))
        (terminalBridgeProductEvent (T n) l u At V q d γ))) :
    let μ := (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)
    let E := gaussianGridTerminalEvent T n l u At V q d γ
    let g := fun p ↦ f ((gaussianGridPath T n p (T n),
      fun v : Set.Icc (0 : ℝ) (T n) ↦ gaussianGridPath T n p v), gaussianGridFinalIncrement T n p)
    Integrable g (ProbabilityTheory.cond μ E) ∧
      (∫ p, g p ∂ProbabilityTheory.cond μ E) =
      ∫ p, f ((p.1.1, fun v ↦ endpointBrownianBridge (T n) p.1.1 v p.1.2), p.2)
        ∂ProbabilityTheory.cond
          (((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).prod
            (gaussianReal 0 (T (n + 1) - T n).toNNReal))
          (terminalBridgeProductEvent (T n) l u At V q d γ) := by
  let μ := (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)
  let η := (gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw
  let ν := gaussianReal 0 (T (n + 1) - T n).toNNReal
  let F := fun p ↦ ((gaussianGridPath T n p (T n),
    fun v : Set.Icc (0 : ℝ) (T n) ↦ gaussianGridPath T n p v), gaussianGridFinalIncrement T n p)
  let G := fun p : ℝ × GaussianCoefficientSpace ↦
    (p.1, fun v : Set.Icc (0 : ℝ) (T n) ↦ endpointBrownianBridge (T n) p.1 v p.2)
  have hm (v : ℝ) : Measurable
      (fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ gaussianGridPath T n p v) :=
    ((timeGridInterpolation_measurable_nodes T (fun j x ↦ observationMeshValue x j) n
      (fun j _ ↦ observationMeshValue_measurable n j) v).comp measurable_fst).add
      ((timeGridBridge_measurable T n v).comp measurable_snd)
  have hF : Measurable F :=
    ((hm (T n)).prodMk (measurable_pi_lambda _ (fun v : Set.Icc (0 : ℝ) (T n) ↦ hm v))).prodMk
      (((measurable_pi_apply (Fin.last n)).comp measurable_fst).sub (hm (T n)))
  have hG : Measurable G := by
    apply measurable_fst.prodMk
    apply measurable_pi_iff.mpr
    intro v
    exact ((actualIntervalBridge_measurable (T n) v).comp measurable_snd).add
      (measurable_const.mul measurable_fst)
  have hlaw : μ.map F = (η.map G).prod ν :=
    gaussianGrid_terminal_joint_law hReconstruct T n hn hT hgap
  have hprod := Measure.map_prod_map η ν hG measurable_id
  simp only [Measure.map_id] at hprod
  rw [hprod] at hlaw
  have he : F ⁻¹' terminalPathEvent (T n) l u At V q d γ =
      gaussianGridTerminalEvent T n l u At V q d γ := by
    ext p
    change (p ∈ gaussianGridEndpointCurveEvent T n l u q d γ ∧
      gaussianGridFinalIncrement T n p ∈ Set.Icc
        (At - 2 * V - gaussianGridPath T n p (T n))
        (At - 2 * V - gaussianGridPath T n p (T n) + 1)) ↔
      (p ∈ gaussianGridEndpointCurveEvent T n l u q d γ ∧
        At ≤ 2 * V + p.1 (Fin.last n) ∧ 2 * V + p.1 (Fin.last n) ≤ At + 1)
    exact and_congr_right (fun _ ↦ (gaussianGrid_site_window_increment T n At V p).symm)
  let S := terminalPathEvent (T n) l u At V q d γ
  have hS : MeasurableSet S := terminalPathEvent_measurable _ _ _ _ _ _ _ _
  have hi' : Integrable (fun p ↦ f (Prod.map G id p))
      (ProbabilityTheory.cond (η.prod ν) ((Prod.map G id) ⁻¹' S)) := hi
  have hc : Integrable f (ProbabilityTheory.cond ((η.prod ν).map (Prod.map G id)) S) := by
    rw [← conditional_map_preimage _ _ (hG.prodMap measurable_id) _ hS]
    exact (integrable_map_measure hf.aestronglyMeasurable
      (hG.prodMap measurable_id).aemeasurable).mpr hi'
  have hb := conditional_map_moment (η.prod ν) (Prod.map G id)
    (hG.prodMap measurable_id) S hS f hf hc
  rw [← hlaw] at hc
  have ha := conditional_map_moment μ F hF S hS f hf hc
  rw [hlaw] at ha
  change Integrable (fun p ↦ f (F p)) (ProbabilityTheory.cond μ
    (gaussianGridTerminalEvent T n l u At V q d γ)) ∧ _
  have he' : F ⁻¹' S = gaussianGridTerminalEvent T n l u At V q d γ := he
  rw [he'] at ha
  exact ⟨ha.1, ha.2.trans hb.2.symm⟩

end SRWTightness
