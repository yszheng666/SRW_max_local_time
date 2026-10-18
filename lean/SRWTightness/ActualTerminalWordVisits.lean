import SRWTightness.NestedWordExtraction

open MeasureTheory

namespace SRWTightness

/-- Terminal finite path records extracted recursively from the actual killed SRW. -/
noncomputable def actualTerminalWordRecords (levels : List (Finset Site × Finset Site))
    (D : Finset Site) (x : Site) (ω : Sample) : List (Site × PathWord) :=
  terminalWordRecords levels x (killedPathWord D x ω)

theorem measurableSet_actualTerminalWordRecords_eq (levels : List (Finset Site × Finset Site))
    (D : Finset Site) (x : Site) (rs : List (Site × PathWord)) :
    MeasurableSet {ω | actualTerminalWordRecords levels D x ω = rs} := by
  exact (measurable_killedPathWord D x) (Set.to_countable
    {w : PathWord | terminalWordRecords levels x w = rs}).measurableSet

/-- Pathwise multilevel occupation identity for the actual extracted terminal records. -/
theorem actualTerminalWordRecords_visit_sum (levels : List (Finset Site × Finset Site))
    (D : Finset Site) (x y : Site) (hn : NestedWordDomains y D levels)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    domainLocalTime D x y ω =
      ((actualTerminalWordRecords levels D x ω).map (wordRecordVisits y)).sum := by
  have hout : x + position (wordPath (killedPathWord D x ω)) (killedPathWord D x ω).length ∉ D := by
    rw [killedPathWord_exitLocation]
    exact position_domain_exit_not_mem D x ω hfin
  have hh := terminalWordRecords_visit_sum levels D y hn x (killedPathWord D x ω) hout
  rw [killedPathWord_localTime] at hh
  exact hh.symm

theorem actualTerminalWordRecords_visit_sum_ae (levels : List (Finset Site × Finset Site))
    (D : Finset Site) (x y : Site) (hn : NestedWordDomains y D levels) :
    ∀ᵐ ω ∂pathLaw, domainLocalTime D x y ω =
      ((actualTerminalWordRecords levels D x ω).map (wordRecordVisits y)).sum := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hω
  exact actualTerminalWordRecords_visit_sum levels D x y hn ω hω

end SRWTightness
