import SRWTightness.EndpointBridgeConditionedKilledPrefix
import SRWTightness.ScaledGaussianBarrierBoundary
import SRWTightness.ExternalPositiveBridge

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Positive bridge prefixes are killed Brownian prefixes
weighted by the remaining killed kernel. -/
theorem positive_bridge_killed_prefix_probability (hReflection : BridgeReflectionInput)
    (T x y r : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y)
    (hr : 0 < r) (hrT : r < T) (B : Set (Set.Icc (0 : ℝ) r → ℝ)) (hB : MeasurableSet B) :
    (positiveBridgeCoefficientLaw T x y).real {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ positiveEndpointBridge T x y t ω) ∈ B} =
    ∫ ω in {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ x - Real.sqrt r * gaussianDyadicPath ω (t / r)) ∈ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) r, 0 < x - Real.sqrt r * gaussianDyadicPath ω (t / r)},
      killedBrownianDensity (T - r) (x - Real.sqrt r * gaussianDyadicPath ω (r / r)) y /
        killedBrownianDensity T x y ∂gaussianCoefficientLaw := by
  let H : (Set.Icc (0 : ℝ) r → ℝ) → (Set.Icc (0 : ℝ) r → ℝ) :=
    fun p t ↦ x - p t
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hxy : x - (x - y) = y := by ring
  have he := endpoint_bridge_conditioned_killed_prefix hReflection T (x - y) x r
    hT hx (by linarith) hr hrT (H ⁻¹' B) (hB.preimage hH)
  have he' : (positiveBridgeCoefficientLaw T x y).real {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ positiveEndpointBridge T x y t ω) ∈ B} =
      ∫ ω in {ω |
        (fun t : Set.Icc (0 : ℝ) r ↦ x - Real.sqrt r * gaussianDyadicPath ω (t / r)) ∈ B ∧
        (fun t : Set.Icc (0 : ℝ) r ↦ Real.sqrt r * gaussianDyadicPath ω (t / r)) ∈
          dyadicFlatPathEvent r x ∧ Real.sqrt r * gaussianDyadicPath ω (r / r) < x},
        killedBrownianDensity (T - r) (x - Real.sqrt r * gaussianDyadicPath ω (r / r)) y /
          killedBrownianDensity T x y ∂gaussianCoefficientLaw := by
    simpa only [positiveBridgeCoefficientLaw, positiveEndpointBridge, H, Set.mem_preimage,
      hxy] using he
  rw [he']
  apply setIntegral_congr_set
  filter_upwards [gaussianDyadicPath_ae_continuous,
    scaled_gaussian_barrier_boundary hReflection r x hr hx] with ω hcont hboundary
  have hc : Continuous (fun t ↦ Real.sqrt r * gaussianDyadicPath ω (t / r)) :=
    continuous_const.mul (hcont.comp (continuous_id.div_const r))
  have hd := continuous_flat_iff_dyadic _ hc r x
  apply propext
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro hBω
  simp only [sub_pos]
  constructor
  · intro h
    exact hboundary.mpr (hd.mpr h.1)
  · intro h
    exact ⟨hd.mp (hboundary.mp h), h r ⟨hr.le, le_rfl⟩⟩

end SRWTightness
