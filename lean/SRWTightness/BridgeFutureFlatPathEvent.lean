import SRWTightness.DyadicFlatPathEvent

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A countable future-bridge barrier test with a variable intermediate endpoint. -/
def bridgeFutureFlatPathEvent (T b q : ℝ) : Set (ℝ × (Set.Icc (0 : ℝ) T → ℝ)) :=
  {p | ∀ n j : ℕ, ∀ h : (j : ℝ) / 2 ^ n ≤ T,
    p.2 ⟨(j : ℝ) / 2 ^ n, by positivity, h⟩ +
      (((j : ℝ) / 2 ^ n) / T) * (b - p.1) ≤ q - p.1}

/-- The variable-middle future bridge barrier test is measurable. -/
theorem bridgeFutureFlatPathEvent_measurable (T b q : ℝ) :
    MeasurableSet (bridgeFutureFlatPathEvent T b q) := by
  simp only [bridgeFutureFlatPathEvent, Set.setOf_forall]
  exact MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun j ↦
    MeasurableSet.iInter fun h ↦ measurableSet_le (by fun_prop) (by fun_prop)

/-- Each positive-distance section has the exact reflection survival probability. -/
theorem bridge_future_flat_path_section (hReflection : BridgeReflectionInput)
    (T b q a : ℝ) (hT : 0 < T) (haq : a < q) (hbq : b < q) :
    (gaussianCoefficientLaw.map (fun ω (t : Set.Icc (0 : ℝ) T) ↦ actualIntervalBridge T t ω)).real
      (Prod.mk a ⁻¹' bridgeFutureFlatPathEvent T b q) =
      1 - Real.exp (-(2 * (q - a) * (q - b) / T)) := by
  have hm : Measurable (fun ω (t : Set.Icc (0 : ℝ) T) ↦ actualIntervalBridge T t ω) :=
    measurable_pi_lambda _ (fun t ↦ actualIntervalBridge_measurable T t)
  have hsec : MeasurableSet (Prod.mk a ⁻¹' bridgeFutureFlatPathEvent T b q) :=
    (bridgeFutureFlatPathEvent_measurable T b q).preimage
      (measurable_const.prodMk measurable_id)
  rw [map_measureReal_apply hm hsec]
  have he : gaussianCoefficientLaw.real
      ((fun ω (t : Set.Icc (0 : ℝ) T) ↦ actualIntervalBridge T t ω) ⁻¹'
        (Prod.mk a ⁻¹' bridgeFutureFlatPathEvent T b q)) =
      gaussianCoefficientLaw.real (bridgeFlatEvent T (b - a) (q - a)) := by
    apply measureReal_congr
    filter_upwards [actualIntervalBridge_continuous T] with ω hω
    apply propext
    have hc := continuous_flat_iff_dyadic
      (fun t ↦ endpointBrownianBridge T (b - a) t ω)
      (hω.add ((continuous_id.div_const T).mul continuous_const)) T (q - a)
    change ((fun t : Set.Icc (0 : ℝ) T ↦ endpointBrownianBridge T (b - a) t ω) ∈
      dyadicFlatPathEvent T (q - a)) ↔
      ∀ t ∈ Set.Icc (0 : ℝ) T, endpointBrownianBridge T (b - a) t ω ≤ q - a
    exact hc.symm
  rw [he, hReflection T (b - a) (q - a) hT (sub_pos.mpr haq) (by linarith),
    show q - a - (b - a) = q - b by ring]

end SRWTightness
