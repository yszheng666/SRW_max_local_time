import SRWTightness.TailRecurrence

open MeasureTheory

namespace SRWTightness

/-- Total visits to a finite set before the actual domain exit. -/
noncomputable def setOccupation (D K : Finset Site) (x : Site) (ω : Sample) : ℕ :=
  ∑ y ∈ K, domainLocalTime D x y ω

 theorem measurable_setOccupation (D K : Finset Site) (x : Site) :
    Measurable (setOccupation D K x) :=
  Finset.measurable_sum K (fun y _ ↦ measurable_domainLocalTime D x y)

 theorem setOccupation_zero_of_not_mem (D K : Finset Site) (x : Site) (hx : x ∉ D)
    (ω : Sample) : setOccupation D K x ω = 0 := by
  simp [setOccupation, domainLocalTime_zero_of_not_mem D x _ hx]

 theorem setOccupation_first_step (D K : Finset Site) (x : Site) (hx : x ∈ D)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    setOccupation D K x ω = (if x ∈ K then 1 else 0) +
      setOccupation D K (x + step (ω 0)) (shift 1 ω) := by
  unfold setOccupation
  simp_rw [domainLocalTime_first_step D x _ hx ω hfin]
  rw [Finset.sum_add_distrib]
  congr 1
  simp [eq_comm]

noncomputable def setHitIndicator (D K : Finset Site) (x : Site) (ω : Sample) : ℝ :=
  if 1 ≤ setOccupation D K x ω then 1 else 0

 theorem measurable_setHitIndicator (D K : Finset Site) (x : Site) :
    Measurable (setHitIndicator D K x) :=
  (measurable_of_countable (fun n : ℕ ↦ if 1 ≤ n then (1 : ℝ) else 0)).comp
    (measurable_setOccupation D K x)

 theorem integrable_setHitIndicator (D K : Finset Site) (x : Site) :
    Integrable (setHitIndicator D K x) pathLaw := by
  refine ⟨(measurable_setHitIndicator D K x).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards [] with ω
  unfold setHitIndicator
  split_ifs <;> norm_num

noncomputable def setHitProbability (D K : Finset Site) (x : Site) : ℝ :=
  ∫ ω, setHitIndicator D K x ω ∂pathLaw

 theorem setHitProbability_eq_probability (D K : Finset Site) (x : Site) :
    setHitProbability D K x = pathLaw.real {ω | 1 ≤ setOccupation D K x ω} := by
  have hs : MeasurableSet {ω | 1 ≤ setOccupation D K x ω} :=
    (measurable_setOccupation D K x) measurableSet_Ici
  simpa [setHitProbability, setHitIndicator, Set.indicator] using
    (integral_indicator_one (μ := pathLaw) hs)

 theorem setHitProbability_zero_of_not_mem (D K : Finset Site) (x : Site) (hx : x ∉ D) :
    setHitProbability D K x = 0 := by
  simp [setHitProbability, setHitIndicator, setOccupation_zero_of_not_mem D K x hx]

 theorem setHitProbability_one (D K : Finset Site) (x : Site) (hx : x ∈ D) (hK : x ∈ K) :
    setHitProbability D K x = 1 := by
  have he : setHitIndicator D K x =ᵐ[pathLaw] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    have h := setOccupation_first_step D K x hx ω hω
    have hn : 1 ≤ setOccupation D K x ω := by
      rw [h, if_pos hK]
      omega
    simp [setHitIndicator, hn]
  unfold setHitProbability
  rw [integral_congr_ae he]
  simp

 theorem setHitProbability_harmonic (D K : Finset Site) (x : Site)
    (hx : x ∈ D) (hK : x ∉ K) :
    setHitProbability D K x = (1 / 4 : ℝ) *
      ∑ d : Direction, setHitProbability D K (x + step d) := by
  have he : setHitIndicator D K x =ᵐ[pathLaw]
      (fun ω ↦ setHitIndicator D K (x + step (ω 0)) (shift 1 ω)) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    have h := setOccupation_first_step D K x hx ω hω
    simp only [if_neg hK, zero_add] at h
    simp only [setHitIndicator, h]
  unfold setHitProbability
  rw [integral_congr_ae he]
  rw [integral_first_step_future (fun d ↦ setHitIndicator D K (x + step d))
    (fun d ↦ measurable_setHitIndicator D K _)
    (fun d ↦ integrable_setHitIndicator D K _)]
  exact integral_direction_average _

end SRWTightness
