import SRWTightness.KilledBrownianDoobEventReal
import SRWTightness.ScaledGaussianSurvivalSplit
import SRWTightness.ScaledGaussianPastKilledIntegral
import SRWTightness.WeightedKilledEndpointEvent

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Doob past/endpoint events have the exact linearly weighted Bessel transition probability. -/
theorem killed_brownian_doob_past_endpoint (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 ≤ r) (hrT : r < T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (killedBrownianDoobCoefficientLaw T x).real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      x - Real.sqrt T * gaussianDyadicPath ω (T / T) ∈ B} =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈
        dyadicFlatPathEvent r x ∧ Real.sqrt T * gaussianDyadicPath ω (r / T) < x},
      ((x - Real.sqrt T * gaussianDyadicPath ω (r / T)) / x) *
        (besselDensityLaw (T - r) (x - Real.sqrt T * gaussianDyadicPath ω (r / T))).real B
          ∂gaussianCoefficientLaw := by
  classical
  let μ := gaussianCoefficientLaw
  let W := fun ω u ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ W ω u
  let R := fun ω ↦ x - W ω T
  let C : Set (Set.Icc (0 : ℝ) r → ℝ) :=
    {p | p ∈ A ∧ p ∈ dyadicFlatPathEvent r x ∧ p ⟨r, hr, le_rfl⟩ < x}
  let S := {ω | ∀ u ∈ Set.Icc (0 : ℝ) T, 0 < x - W ω u}
  let E := R ⁻¹' B
  let f := B.indicator (fun y ↦ y / x)
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hR : Measurable R :=
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _))
  have hE : MeasurableSet E := hB.preimage hR
  have hC : MeasurableSet C := hA.inter ((dyadicFlatPathEvent_measurable r x).inter
    (measurableSet_lt (measurable_pi_apply _) measurable_const))
  have hf : Measurable f := (measurable_id.div_const x).indicator hB
  have hval (ω) : f (R ω) = E.indicator (fun ω ↦ R ω / x) ω := by
    by_cases h : R ω ∈ B <;> simp [f, E, h]
  have hg := ((scaled_gaussian_path_process T hT).hasGaussianLaw_eval
    ⟨T, hT.le, le_rfl⟩).integrable
  have hbase : Integrable (fun ω ↦ R ω / x) μ :=
    ((integrable_const x).sub hg).div_const x
  have hi : Integrable (fun ω ↦ f (R ω)) μ :=
    (hbase.indicator hE).congr (ae_of_all _ (fun ω ↦ (hval ω).symm))
  have hleft : (∫ ω in S ∩ (P ⁻¹' A), f (R ω) ∂μ) =
      (killedBrownianDoobCoefficientLaw T x).real {ω | P ω ∈ A ∧ R ω ∈ B} := by
    have hAB : MeasurableSet {ω | P ω ∈ A ∧ R ω ∈ B} :=
      (hA.preimage hP).inter (hB.preimage hR)
    rw [killed_brownian_doob_event_real hReflection T x hT hx _ hAB]
    simp_rw [hval]
    rw [setIntegral_indicator hE]
    apply setIntegral_congr_set
    exact ae_of_all _ (fun ω ↦ by
      apply propext
      change ((ω ∈ S ∧ P ω ∈ A) ∧ R ω ∈ B) ↔
        (ω ∈ S ∧ P ω ∈ A ∧ R ω ∈ B)
      tauto)
  have hset : (S ∩ (P ⁻¹' A) : Set GaussianCoefficientSpace) =ᵐ[μ]
      {ω | P ω ∈ C ∧ ∀ u ∈ Set.Icc (0 : ℝ) (T - r), W ω (r + u) ≤ x} := by
    filter_upwards [scaled_gaussian_survival_split hReflection T x r hT hx hr hrT]
      with ω hω
    apply propext
    change ((∀ u ∈ Set.Icc (0 : ℝ) T, 0 < x - W ω u) ∧ P ω ∈ A) ↔
      ((P ω ∈ A ∧ P ω ∈ dyadicFlatPathEvent r x ∧ W ω r < x) ∧
        ∀ u ∈ Set.Icc (0 : ℝ) (T - r), W ω (r + u) ≤ x)
    have hs : (∀ u ∈ Set.Icc (0 : ℝ) T, 0 < x - W ω u) ↔
        (P ω ∈ dyadicFlatPathEvent r x ∧ W ω r < x ∧
          ∀ u ∈ Set.Icc (0 : ℝ) (T - r), W ω (r + u) ≤ x) := hω
    rw [hs]
    tauto
  have he := scaled_gaussian_past_killed_integral hReflection T r T x hT hr hrT le_rfl
    C hC (fun p hp ↦ hp.2.2) f hf hi
  have htrans :
      (∫ ω in {ω | P ω ∈ C ∧ ∀ u ∈ Set.Icc (0 : ℝ) (T - r), W ω (r + u) ≤ x},
        f (R ω) ∂μ) =
      ∫ ω in P ⁻¹' C, ∫ y, f y ∂killedBrownianDensityLaw (T - r) (x - W ω r) ∂μ := he
  change (killedBrownianDoobCoefficientLaw T x).real {ω | P ω ∈ A ∧ R ω ∈ B} =
    ∫ ω in P ⁻¹' C, ((x - W ω r) / x) * (besselDensityLaw (T - r) (x - W ω r)).real B ∂μ
  rw [← hleft, setIntegral_congr_set hset, htrans]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (hC.preimage hP)] with ω hω
  exact weighted_killed_endpoint_event (T - r) x (x - W ω r) (sub_pos.mpr hrT) hx
    (sub_pos.mpr hω.2.2) B hB

end SRWTightness
