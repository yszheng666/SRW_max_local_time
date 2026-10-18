import SRWTightness.ExternalBrownianReconstruction
import SRWTightness.EndpointBridgeProductEvent

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The endpoint and countable curve test on restricted paths. -/
def endpointPathBarrierEvent (T l u q d γ : ℝ) :
    Set (ℝ × (Set.Icc (0 : ℝ) T → ℝ)) :=
  {p | p.1 ∈ Set.Icc l u ∧ ∀ n j : ℕ, ∀ h : (j : ℝ) / 2 ^ n ≤ T,
    p.2 ⟨(j : ℝ) / 2 ^ n, by positivity, h⟩ ≤ q - (d - (j : ℝ) / 2 ^ n) ^ γ}

theorem endpointPathBarrierEvent_measurable (T l u q d γ : ℝ) :
    MeasurableSet (endpointPathBarrierEvent T l u q d γ) := by
  unfold endpointPathBarrierEvent
  simp only [Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter (measurableSet_Icc.preimage measurable_fst)
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  exact measurableSet_le ((measurable_pi_apply _).comp measurable_snd) measurable_const

/-- The endpoint-window and dyadic curved barrier for the actual Gaussian grid path. -/
def gaussianGridEndpointCurveEvent (T : ℕ → ℝ) (n : ℕ) (l u q d γ : ℝ) :
    Set ((Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :=
  {p | gaussianGridPath T n p (T n) ∈ Set.Icc l u ∧
    ∀ k j : ℕ, (j : ℝ) / 2 ^ k ≤ T n →
      gaussianGridPath T n p ((j : ℝ) / 2 ^ k) ≤ q - (d - (j : ℝ) / 2 ^ k) ^ γ}

/-- Standard reconstruction transfers the actual grid event to the endpoint/bridge product event. -/
theorem gaussianGrid_endpoint_curve_probability (hReconstruct : BrownianBridgeReconstructionInput)
    (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) (l u q d γ : ℝ) :
    ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)).real
      (gaussianGridEndpointCurveEvent T n l u q d γ) =
      ((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).real
        (endpointBridgeProductEvent (T n) l u q d γ) := by
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  have hm (v : ℝ) : Measurable
      (fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ gaussianGridPath T n p v) :=
    ((timeGridInterpolation_measurable_nodes T (fun j x ↦ observationMeshValue x j) n
      (fun j _ ↦ observationMeshValue_measurable n j) v).comp measurable_fst).add
      ((timeGridBridge_measurable T n v).comp measurable_snd)
  have hleft := (hm (T n)).prodMk
    (measurable_pi_lambda (fun p (v : Set.Icc (0 : ℝ) (T n)) ↦ gaussianGridPath T n p v)
      (fun v ↦ hm v))
  have hright : Measurable (fun p : ℝ × GaussianCoefficientSpace ↦
      (p.1, fun v : Set.Icc (0 : ℝ) (T n) ↦ endpointBrownianBridge (T n) p.1 v p.2)) := by
    apply measurable_fst.prodMk
    apply measurable_pi_iff.mpr
    intro v
    exact ((actualIntervalBridge_measurable (T n) v).comp measurable_snd).add
      (measurable_const.mul measurable_fst)
  have hh := congrArg (fun μ ↦ μ.real (endpointPathBarrierEvent (T n) l u q d γ))
    (gaussianGrid_endpoint_bridge_law hReconstruct T n hn hT hgap)
  rw [map_measureReal_apply hleft (endpointPathBarrierEvent_measurable _ _ _ _ _ _),
    map_measureReal_apply hright (endpointPathBarrierEvent_measurable _ _ _ _ _ _)] at hh
  exact hh

end SRWTightness
