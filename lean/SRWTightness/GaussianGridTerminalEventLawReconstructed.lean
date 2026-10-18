import SRWTightness.GaussianGridTerminalEventLaw
import SRWTightness.GaussianGridTerminalJointLawReconstructed

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem gaussianGrid_terminal_event_probability_reconstructed
    (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) (l u At V q d γ : ℝ) :
    ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)).real
      (gaussianGridTerminalEvent T n l u At V q d γ) =
      (((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).prod
        (gaussianReal 0 (T (n + 1) - T n).toNNReal)).real
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
    gaussianGrid_terminal_joint_law_reconstructed T n hn hT hgap
  have hprod := Measure.map_prod_map η ν hG measurable_id
  simp only [Measure.map_id] at hprod
  rw [hprod] at hlaw
  have hp := congrArg (fun ρ ↦ ρ.real (terminalPathEvent (T n) l u At V q d γ)) hlaw
  rw [map_measureReal_apply hF (terminalPathEvent_measurable _ _ _ _ _ _ _ _),
    map_measureReal_apply (hG.prodMap measurable_id)
      (terminalPathEvent_measurable _ _ _ _ _ _ _ _)] at hp
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
  rw [he] at hp
  exact hp

end SRWTightness
