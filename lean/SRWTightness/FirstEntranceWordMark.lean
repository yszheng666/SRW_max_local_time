import SRWTightness.WordMark
import SRWTightness.CompetingEntranceFuture

open MeasureTheory
namespace SRWTightness

/-- Keep the complete ordered future word at first entrance into K, or the empty mark on a miss. -/
noncomputable def firstEntranceWordMark (D K : Finset Site) (x : Site) (ω : Sample) :
    WordMark :=
  if domainExitLocation (D \ K) x ω ∈ K then
    killedWordMark D (domainExitLocation (D \ K) x ω) (futureAt (domainExit (D \ K) x) ω)
  else none

/-- The entrance location and stopped future jointly define a measurable ordered mark. -/
theorem measurable_firstEntranceWordMark (D K : Finset Site) (x : Site) :
    Measurable (firstEntranceWordMark D K x) := by
  have hm : Measurable (fun p : Sample × Site ↦ killedWordMark D p.2 p.1) :=
    measurable_from_prod_countable_left (fun y ↦ measurable_killedWordMark D y)
  have hf := measurable_futureAt (domainExit (D \ K) x) (domainExit_isStoppingTime (D \ K) x)
  exact (hm.comp (hf.prodMk (measurable_domainExitLocation (D \ K) x))).ite
    ((measurable_domainExitLocation (D \ K) x) (Finset.measurableSet K)) measurable_const

/-- The actual law of the first-entry-trimmed word, including the failure-to-enter atom. -/
noncomputable def firstEntranceWordMarkLaw (D K : Finset Site) (x : Site) : Measure WordMark :=
  pathLaw.map (firstEntranceWordMark D K x)

instance firstEntranceWordMarkLaw_probability (D K : Finset Site) (x : Site) :
    IsProbabilityMeasure (firstEntranceWordMarkLaw D K x) :=
  Measure.isProbabilityMeasure_map (measurable_firstEntranceWordMark D K x).aemeasurable

/-- Every retained first-entry word has the exact entrance/future mixture law. -/
theorem firstEntranceWordMark_hit_event (D K : Finset Site) (x : Site)
    (s : Set WordMark) (hs : MeasurableSet s) :
    pathLaw {ω | domainExitLocation (D \ K) x ω ∈ K ∧ firstEntranceWordMark D K x ω ∈ s} =
      ∫⁻ y, killedWordMarkLaw D y s ∂competingEntranceLaw D K x := by
  have he : {ω | domainExitLocation (D \ K) x ω ∈ K ∧ firstEntranceWordMark D K x ω ∈ s} =
      {ω | domainExitLocation (D \ K) x ω ∈ K ∧
        futureAt (domainExit (D \ K) x) ω ∈ (killedWordMark D
          (domainExitLocation (D \ K) x ω)) ⁻¹' s} := by
    ext ω
    by_cases hh : domainExitLocation (D \ K) x ω ∈ K <;>
      simp [firstEntranceWordMark, hh]
  rw [he, competing_entrance_future_integral D K x
    (fun y ↦ (killedWordMark D y) ⁻¹' s) (fun y ↦ measurable_killedWordMark D y hs)]
  apply lintegral_congr
  intro y
  exact (Measure.map_apply (measurable_killedWordMark D y) hs).symm

/-- The empty ordered mark records exactly the competing outer-exit mass. -/
theorem firstEntranceWordMarkLaw_none (D K : Finset Site) (x : Site) :
    (firstEntranceWordMarkLaw D K x).real {none} = competingExitMass D K x := by
  rw [firstEntranceWordMarkLaw,
    map_measureReal_apply (measurable_firstEntranceWordMark D K x) (measurableSet_singleton _)]
  unfold competingExitMass
  rw [map_measureReal_apply (measurable_domainExitLocation (D \ K) x)
    (Finset.measurableSet K).compl]
  congr 1
  ext ω
  by_cases hh : domainExitLocation (D \ K) x ω ∈ K <;>
    simp [firstEntranceWordMark, killedWordMark, hh]

end SRWTightness
