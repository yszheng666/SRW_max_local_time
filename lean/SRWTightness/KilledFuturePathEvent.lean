import SRWTightness.ScaledGaussianKilledProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A measurable future-survival test with a variable initial distance and terminal set. -/
def killedFuturePathEvent (T : ℝ) (hT : 0 ≤ T) (A : Set ℝ) :
    Set (ℝ × (Set.Icc (0 : ℝ) T → ℝ)) :=
  {p | p.1 - p.2 ⟨T, hT, le_rfl⟩ ∈ A ∧
    ∀ n j : ℕ, ∀ h : (j : ℝ) / 2 ^ n ≤ T,
      p.2 ⟨(j : ℝ) / 2 ^ n, by positivity, h⟩ ≤ p.1}

/-- The variable-initial-distance future survival event is measurable. -/
theorem killedFuturePathEvent_measurable (T : ℝ) (hT : 0 ≤ T)
    (A : Set ℝ) (hA : MeasurableSet A) : MeasurableSet (killedFuturePathEvent T hT A) := by
  unfold killedFuturePathEvent
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (hA.preimage (measurable_fst.sub
    ((measurable_pi_apply _).comp measurable_snd))).inter
    (MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun h ↦
        measurableSet_le ((measurable_pi_apply _).comp measurable_snd) measurable_fst)

/-- Every positive-distance section of the measurable future test is the exact killed kernel. -/
theorem killed_future_path_section (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) (A : Set ℝ) (hA : MeasurableSet A) :
    (gaussianCoefficientLaw.map (fun ω (t : Set.Icc (0 : ℝ) T) ↦
      Real.sqrt T * gaussianDyadicPath ω (t / T))).real
        (Prod.mk x ⁻¹' killedFuturePathEvent T hT.le A) =
      (killedBrownianDensityLaw T x).real A := by
  have hm : Measurable (fun ω (t : Set.Icc (0 : ℝ) T) ↦
      Real.sqrt T * gaussianDyadicPath ω (t / T)) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _))
  have hsec : MeasurableSet (Prod.mk x ⁻¹' killedFuturePathEvent T hT.le A) :=
    (killedFuturePathEvent_measurable T hT.le A hA).preimage
      (measurable_const.prodMk measurable_id)
  rw [map_measureReal_apply hm hsec,
    ← scaled_gaussian_killed_probability hReflection T x hT hx A hA]
  apply measureReal_congr
  filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
  apply propext
  apply and_congr_right
  intro hAω
  exact (continuous_flat_iff_dyadic _
    (continuous_const.mul (hω.comp (continuous_id.div_const T))) T x).symm

end SRWTightness
