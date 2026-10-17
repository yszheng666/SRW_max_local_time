import SRWTightness.GaussianGridFinalWindowBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual grid terminal event is measurable for every choice of parameters. -/
theorem gaussianGridTerminalEvent_measurable (T : ℕ → ℝ) (n : ℕ)
    (l u At V q d γ : ℝ) :
    MeasurableSet (gaussianGridTerminalEvent T n l u At V q d γ) := by
  have hm (v : ℝ) : Measurable
      (fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ gaussianGridPath T n p v) :=
    ((timeGridInterpolation_measurable_nodes T (fun j x ↦ observationMeshValue x j) n
      (fun j _ ↦ observationMeshValue_measurable n j) v).comp measurable_fst).add
      ((timeGridBridge_measurable T n v).comp measurable_snd)
  have hsite : Measurable
      (fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦
        2 * V + p.1 (Fin.last n)) :=
    measurable_const.add ((measurable_pi_apply (Fin.last n)).comp measurable_fst)
  unfold gaussianGridTerminalEvent gaussianGridEndpointCurveEvent
  simp only [Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]
  exact ((measurableSet_Icc.preimage (hm (T n))).inter
    (MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun _ ↦ measurableSet_le (hm _) measurable_const)).inter
    ((measurableSet_le measurable_const hsite).inter (measurableSet_le hsite measurable_const))

/-- The final increment has a bounded conditional second moment under the actual terminal event. -/
theorem gaussianGrid_final_conditional_moment (T : ℕ → ℝ) (n : ℕ)
    (At V d q a ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hAt : |At - (2 * d + q)| ≤ ε) (hV : |V - d| ≤ K) (γ : ℝ)
    (hpos : 0 < ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod
      (independentBridgeLaw ℕ)).real
      (gaussianGridTerminalEvent T n (q - a - 1) (q - a) At V q d γ)) :
    let μ := (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)
    let E := gaussianGridTerminalEvent T n (q - a - 1) (q - a) At V q d γ
    Integrable (fun p ↦ (gaussianGridFinalIncrement T n p) ^ 2) (ProbabilityTheory.cond μ E) ∧
      (∫ p, (gaussianGridFinalIncrement T n p) ^ 2 ∂ProbabilityTheory.cond μ E) ≤
        (|a| + 2 + ε + 2 * K) ^ 2 := by
  let μ := (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)
  let E := gaussianGridTerminalEvent T n (q - a - 1) (q - a) At V q d γ
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T (n + 1))
  haveI : IsProbabilityMeasure μ := inferInstance
  have hs0 : μ E ≠ 0 := by
    intro h
    change 0 < μ.real E at hpos
    simp [Measure.real, h] at hpos
  letI := ProbabilityTheory.cond_isProbabilityMeasure (μ := μ) hs0
  have hm : Measurable (fun p ↦ (gaussianGridFinalIncrement T n p) ^ 2) := by
    have hp : Measurable
        (fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦
          gaussianGridPath T n p (T n)) :=
      ((timeGridInterpolation_measurable_nodes T (fun j x ↦ observationMeshValue x j) n
        (fun j _ ↦ observationMeshValue_measurable n j) (T n)).comp measurable_fst).add
        ((timeGridBridge_measurable T n (T n)).comp measurable_snd)
    exact (((measurable_pi_apply (Fin.last n)).comp measurable_fst).sub hp).pow_const 2
  have hb : ∀ᵐ p ∂ProbabilityTheory.cond μ E,
      (gaussianGridFinalIncrement T n p) ^ 2 ≤ (|a| + 2 + ε + 2 * K) ^ 2 :=
    ProbabilityTheory.ae_cond_of_forall_mem
      (gaussianGridTerminalEvent_measurable _ _ _ _ _ _ _ _ _)
      (fun p hp ↦ (gaussianGrid_final_window_bound T n At V d q a ε K hε hK hAt hV γ p hp).2)
  have hi := (integrable_const ((|a| + 2 + ε + 2 * K) ^ 2)).mono_nonneg
    hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun p ↦ sq_nonneg _)) hb
  refine ⟨hi, ?_⟩
  exact (integral_mono_ae hi (integrable_const _) hb).trans_eq (by simp)

end SRWTightness
