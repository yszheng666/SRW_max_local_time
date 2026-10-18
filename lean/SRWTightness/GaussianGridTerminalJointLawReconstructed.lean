import SRWTightness.GaussianGridTerminalJointLaw
import SRWTightness.GaussianGridBridgeLawInternal

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem gaussianGrid_terminal_joint_law_reconstructed
    (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) :
    ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)).map
      (fun p ↦ ((gaussianGridPath T n p (T n),
        fun v : Set.Icc (0 : ℝ) (T n) ↦ gaussianGridPath T n p v),
        gaussianGridFinalIncrement T n p)) =
      (((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).map
        (fun p ↦ (p.1, fun v : Set.Icc (0 : ℝ) (T n) ↦
          endpointBrownianBridge (T n) p.1 v p.2))).prod
        (gaussianReal 0 (T (n + 1) - T n).toNNReal) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T (n + 1))
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  have hTn : 0 ≤ T n := by
    simpa only [hT] using timeGridTime_mono T n hg (Nat.zero_le n) le_rfl
  have hm (v : ℝ) : Measurable
      (fun p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ gaussianGridPath T n p v) :=
    ((timeGridInterpolation_measurable_nodes T (fun j x ↦ observationMeshValue x j) n
      (fun j _ ↦ observationMeshValue_measurable n j) v).comp measurable_fst).add
      ((timeGridBridge_measurable T n v).comp measurable_snd)
  have hF := (hm (T n)).prodMk
    (measurable_pi_lambda (fun p (v : Set.Icc (0 : ℝ) (T n)) ↦ gaussianGridPath T n p v)
      (fun v ↦ hm v))
  have hG : Measurable (gaussianGridFinalIncrement T n) :=
    ((measurable_pi_apply (Fin.last n)).comp measurable_fst).sub (hm (T n))
  have hpair : Measurable (fun f : Set.Icc (0 : ℝ) (T n) → ℝ ↦
      (f ⟨T n, hTn, le_rfl⟩, f)) :=
    (measurable_pi_apply _).prodMk measurable_id
  have hind := (gaussianGridFinalIncrement_indep_path T n hn hT hgap).comp hpair measurable_id
  change IndepFun (fun p ↦ (gaussianGridPath T n p (T n),
    fun v : Set.Icc (0 : ℝ) (T n) ↦ gaussianGridPath T n p v))
    (gaussianGridFinalIncrement T n) _ at hind
  have hh := hind.map_prod_eq_prod_map_map hF.aemeasurable hG.aemeasurable
  rw [gaussianGrid_endpoint_bridge_law_internal T n hn hT hgap,
    gaussianGridFinalIncrement_law T n hn hT hgap] at hh
  exact hh

end SRWTightness
