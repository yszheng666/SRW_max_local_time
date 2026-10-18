import SRWTightness.FirstEntranceWordMark

open MeasureTheory
namespace SRWTightness

/-- Exact ordered-word mixture, including the empty atom, for every measurable mark event. -/
theorem firstEntranceWordMarkLaw_event (D K : Finset Site) (x : Site)
    (s : Set WordMark) (hs : MeasurableSet s) :
    firstEntranceWordMarkLaw D K x s =
      ENNReal.ofReal (competingExitMass D K x) * Measure.dirac none s +
        ∫⁻ y, killedWordMarkLaw D y s ∂competingEntranceLaw D K x := by
  classical
  let E := {ω | firstEntranceWordMark D K x ω ∈ s}
  let H := {ω | domainExitLocation (D \ K) x ω ∈ K}
  have hH : MeasurableSet H :=
    (measurable_domainExitLocation (D \ K) x) (Finset.measurableSet K)
  have hhit : pathLaw (E ∩ H) =
      ∫⁻ y, killedWordMarkLaw D y s ∂competingEntranceLaw D K x := by
    convert firstEntranceWordMark_hit_event D K x s hs using 1
    congr 1
    ext ω
    exact and_comm
  have hmiss : pathLaw Hᶜ = firstEntranceWordMarkLaw D K x {none} := by
    rw [firstEntranceWordMarkLaw,
      Measure.map_apply (measurable_firstEntranceWordMark D K x) (measurableSet_singleton _)]
    congr 1
    ext ω
    by_cases hh : domainExitLocation (D \ K) x ω ∈ K <;>
      simp [H, firstEntranceWordMark, killedWordMark, hh]
  have hmass : pathLaw Hᶜ = ENNReal.ofReal (competingExitMass D K x) := by
    rw [hmiss, ← firstEntranceWordMarkLaw_none D K x]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hdiff : E \ H = if none ∈ s then Hᶜ else ∅ := by
    ext ω
    by_cases hn : none ∈ s <;>
      by_cases hh : domainExitLocation (D \ K) x ω ∈ K <;>
        simp [E, H, firstEntranceWordMark, hn, hh]
  rw [firstEntranceWordMarkLaw,
    Measure.map_apply (measurable_firstEntranceWordMark D K x) hs]
  change pathLaw E = _
  rw [← measure_inter_add_sdiff E hH, hhit, hdiff]
  by_cases hn : none ∈ s <;>
    simp [hn, hmass, add_comm, Measure.dirac_apply' _ hs, Set.indicator]

end SRWTightness
