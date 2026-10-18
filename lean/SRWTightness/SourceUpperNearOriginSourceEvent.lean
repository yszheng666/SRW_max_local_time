import SRWTightness.SourceUpperNearOriginLimit

open Filter MeasureTheory
open scoped Topology

namespace SRWTightness

/-- At source scales every site in the closed near-origin disk lies inside the killed domain. -/
theorem source_upper_near_origin_sites_iff (t : ℝ) (ht : 2 ≤ t) (x : Site) :
    x ∈ sourceUpperNearOriginSites t ↔ Real.sqrt (normSq x) ≤ Real.exp t / t := by
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hx⟩
    apply (mem_diskFinset _ _).mpr
    change normSq x < (Real.exp t) ^ 2
    have hh := hx.trans_lt (div_lt_self (Real.exp_pos t) (by linarith : 1 < t))
    nlinarith [Real.sq_sqrt (normSq_nonneg x), Real.sqrt_nonneg (normSq x), Real.exp_pos t]

/-- The formal event is exactly the source's closed near-origin local-time event. -/
theorem source_upper_near_origin_event_at_radius (R s : ℝ) (hR : 0 < R)
    (ht : 2 ≤ Real.log R) :
    sourceUpperNearOriginHighEvent (Real.log R) s =
      {ω | ∃ x : Site, Real.sqrt (normSq x) ≤ R / Real.log R ∧
        Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x} := by
  ext ω
  simp only [sourceUpperNearOriginHighEvent, Set.mem_setOf_eq,
    source_upper_near_origin_sites_iff (Real.log R) ht, sourceUpperVisitCutoff_at_radius,
    Real.exp_log hR, domainLocalTime_disk]

/-- Source (4.35): the actual closed near-origin high-point probability vanishes. -/
theorem source_upper_near_origin_source_vanishes (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun R : ℝ ↦ pathLaw.real
      {ω | ∃ x : Site, Real.sqrt (normSq x) ≤ R / Real.log R ∧
        Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x})
      atTop (𝓝 0) := by
  apply (source_upper_near_origin_radius_vanishes s hs).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 2)] with R hR ht
  rw [source_upper_near_origin_event_at_radius R s hR ht]

end SRWTightness
