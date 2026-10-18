import SRWTightness.RecordExitSlice
import SRWTightness.AnnulusEscapeIdentity

open MeasureTheory

namespace SRWTightness

/-- Actual entrance into K competing with exit from D, represented by exit from D minus K. -/
noncomputable def competingEntranceLaw (D K : Finset Site) (x : Site) : Measure Site :=
  (pathLaw.map (domainExitLocation (D \ K) x)).restrict (K : Set Site)

/-- The competing outer-exit mass; the inner-entrance and outer-exit masses sum to one. -/
noncomputable def competingExitMass (D K : Finset Site) (x : Site) : ℝ :=
  (pathLaw.map (domainExitLocation (D \ K) x)).real (K : Set Site)ᶜ

instance competingEntranceLaw_isFiniteMeasure (D K : Finset Site) (x : Site) :
    IsFiniteMeasure (competingEntranceLaw D K x) := by
  unfold competingEntranceLaw
  infer_instance

theorem competingEntranceLaw_supported (D K : Finset Site) (x : Site) :
    ∀ᵐ y ∂competingEntranceLaw D K x, y ∈ K :=
  ae_restrict_mem (Finset.measurableSet K)

/-- From an admissible initial point, every retained entrance is on the actual inner boundary. -/
theorem competingEntranceLaw_supported_boundary (D K : Finset Site) (x : Site)
    (hx : x ∈ D \ K) :
    ∀ᵐ y ∂competingEntranceLaw D K x, y ∈ domainExitBoundary (D \ K) ∩ (K : Set Site) := by
  have he : ∀ᵐ y ∂pathLaw.map (domainExitLocation (D \ K) x),
      y ∈ domainExitBoundary (D \ K) :=
    (ae_map_iff (measurable_domainExitLocation (D \ K) x).aemeasurable
      (Set.to_countable _ |>.measurableSet)).mpr
        (domainExitLocation_mem_boundary_ae (D \ K) x hx)
  exact (ae_restrict_of_ae he).and (ae_restrict_mem (Finset.measurableSet K))

/-- The actual competing masses are complementary, before any annulus approximation. -/
theorem competing_entrance_exit_mass (D K : Finset Site) (x : Site) :
    (competingEntranceLaw D K x).real Set.univ + competingExitMass D K x = 1 := by
  let μ := pathLaw.map (domainExitLocation (D \ K) x)
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_domainExitLocation (D \ K) x).aemeasurable
  change (μ.restrict (K : Set Site)).real Set.univ + μ.real (K : Set Site)ᶜ = 1
  rw [measureReal_restrict_apply_univ, measureReal_add_measureReal_compl (Finset.measurableSet K)]
  exact probReal_univ

/-- The entrance measure has exactly the existing SRW hitting probability as its mass. -/
theorem competingEntranceLaw_mass (D K : Finset Site) (hKD : K ⊆ D) (x : Site) :
    (competingEntranceLaw D K x).real Set.univ = setHitProbability D K x := by
  unfold competingEntranceLaw
  rw [measureReal_restrict_apply_univ,
    map_measureReal_apply (measurable_domainExitLocation (D \ K) x) (Finset.measurableSet K)]
  have hh : setHitProbability D K x = exitPayoff (D \ K) (setHitProbability D K) x := by
    apply harmonic_eq_exitPayoff
    intro y hy
    exact setHitProbability_harmonic D K y (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
  have he : exitPayoff (D \ K) (setHitProbability D K) x =
      exitPayoff (D \ K) (fun y ↦ if y ∈ K then 1 else 0) x := by
    apply exitPayoff_congr_on_compl
    intro y hy
    by_cases hyK : y ∈ K
    · simp [hyK, setHitProbability_one D K y (hKD hyK) hyK]
    · have hyD : y ∉ D := fun h ↦ hy (Finset.mem_sdiff.mpr ⟨h, hyK⟩)
      simp [hyK, setHitProbability_zero_of_not_mem D K y hyD]
  have hm : MeasurableSet {ω | domainExitLocation (D \ K) x ω ∈ K} :=
    (measurable_domainExitLocation (D \ K) x) (Finset.measurableSet K)
  have hi : exitPayoff (D \ K) (fun y ↦ if y ∈ K then 1 else 0) x =
      pathLaw.real {ω | domainExitLocation (D \ K) x ω ∈ K} := by
    simpa only [exitPayoff, Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
      (integral_indicator_one (μ := pathLaw) hm)
  exact (hh.trans (he.trans hi)).symm

/-- The actual outer-exit mass is the complementary escape probability. -/
theorem competingExitMass_eq_one_sub_hit (D K : Finset Site) (hKD : K ⊆ D) (x : Site) :
    competingExitMass D K x = 1 - setHitProbability D K x := by
  have hh := competing_entrance_exit_mass D K x
  rw [competingEntranceLaw_mass D K hKD x] at hh
  linarith

end SRWTightness
