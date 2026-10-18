import SRWTightness.FiniteGaussianBridgeLaw
import SRWTightness.FiniteGaussianPrefixRestriction
import SRWTightness.GaussianGridBridgeEventLaw

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The original full-mesh prefix event transfers to the actual endpoint/bridge event. -/
theorem finiteGaussian_flat_probability (hReconstruct : BrownianBridgeReconstructionInput)
    (T : ℕ → ℝ) (n M : ℕ) (last : Fin n) (hlast : last.val + 1 = n)
    (hnM : n ≤ M) (hT : T 0 = 0) (hgap : ∀ j < M, T j < T (j + 1))
    (q a b : ℝ) :
    ((gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ)).real
      (finiteGaussianPrefixWindow T n M last q a b) =
      ((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).real
        (endpointBridgeProductEvent (T n) a b (q + 1) 0 0) := by
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ hgap j (by omega)
  have hpref : finiteGaussianPrefixWindow T n M last q a b =
      finiteGaussianPrefixWindow T n n last q a b := by
    ext p
    apply and_congr_right
    intro hp
    apply forall_congr'
    intro r
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    rw [finiteGaussianBridgedPath_prefix T n M hnM hgap p.1 p.2 _ hj]
  rw [hpref]
  have hm := finiteGaussianBridgedPath_measurable T n n
  have hleft := (hm (T n)).prodMk
    (measurable_pi_lambda _ (fun v : Set.Icc (0 : ℝ) (T n) ↦ hm v))
  have hright : Measurable (fun p : ℝ × GaussianCoefficientSpace ↦
      (p.1, fun v : Set.Icc (0 : ℝ) (T n) ↦ endpointBrownianBridge (T n) p.1 v p.2)) := by
    apply measurable_fst.prodMk
    apply measurable_pi_iff.mpr
    intro v
    exact ((actualIntervalBridge_measurable (T n) v).comp measurable_snd).add
      (measurable_const.mul measurable_fst)
  have hh := congrArg (fun μ ↦ μ.real (endpointPathBarrierEvent (T n) a b (q + 1) 0 0))
    (finiteGaussian_endpoint_bridge_law hReconstruct T n (by omega) hT hg)
  rw [map_measureReal_apply hleft (endpointPathBarrierEvent_measurable _ _ _ _ _ _),
    map_measureReal_apply hright (endpointPathBarrierEvent_measurable _ _ _ _ _ _)] at hh
  have hnode (p : (Fin n → ℝ) × (ℕ → GaussianCoefficientSpace)) :
      finiteGaussianBridgedPath T n n p.1 p.2 (T n) = p.1 last := by
    simpa only [hlast] using finiteGaussianBridgedPath_node T n hg p.1 p.2 last
  simpa only [endpointPathBarrierEvent, endpointBridgeProductEvent,
    finiteGaussianPrefixWindow, Set.preimage_setOf_eq, Real.rpow_zero,
    add_sub_cancel_right, hnode] using hh

end SRWTightness
