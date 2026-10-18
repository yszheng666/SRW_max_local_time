import SRWTightness.ActualChildRecursion
import SRWTightness.ChildVisitCoverage
import SRWTightness.CompetingEntranceLaw
import SRWTightness.AnnulusEscapeEvent

open MeasureTheory

namespace SRWTightness

/-- There are no complete children exactly when the entrance set is never visited before exit. -/
theorem killedChildIntervals_eq_nil_iff (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    killedChildIntervals D K C x ω = [] ↔ setOccupation D K x ω = 0 := by
  constructor
  · intro hnil
    by_contra hn
    have hp : 0 < setOccupation D K x ω := by omega
    obtain ⟨j, hj, hvisit⟩ := (setOccupation_pos_iff D K x ω).mp hp
    obtain ⟨q, hq, _⟩ := killedChildIntervals_cover_visit D K C hKC hCD x ω hfin j hj hvisit
    simpa [hnil] using hq
  · intro hz
    rw [killedChildIntervals_eq_scan]
    have hs := scanChildIntervals_skip_prefix K C x ω
      (List.range (domainSteps D x ω + 1)) []
    suffices hh : ∀ i ∈ List.range (domainSteps D x ω + 1), x + position ω i ∉ K by
      simpa [scanChildIntervals] using hs hh
    intro i hi hK
    have hiN : i ≤ domainSteps D x ω := by simpa using List.mem_range.mp hi
    by_cases he : i = domainSteps D x ω
    · exact position_domain_exit_not_mem D x ω hfin (he ▸ hCD (hKC hK))
    · have hp := (setOccupation_pos_iff D K x ω).mpr ⟨i, by omega, hK⟩
      omega

/-- The zero child record is exactly strict parent escape before the next entrance. -/
theorem killedChildIntervals_nil_iff_escape (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    killedChildIntervals D K C x ω = [] ↔
      domainExit D x ω < setHittingTime K x 0 ω := by
  rw [killedChildIntervals_eq_nil_iff D K C hKC hCD x ω hfin]
  exact (exit_lt_setHittingTime_iff D K (fun y hy ↦ hCD (hKC hy)) x ω hfin).symm

/-- The actual zero child probability is the complementary entrance probability. -/
theorem killedChildIntervals_nil_probability (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) :
    pathLaw.real {ω | killedChildIntervals D K C x ω = []} =
      1 - setHitProbability D K x := by
  rw [← exit_before_hit_probability D K (fun y hy ↦ hCD (hKC hy)) x]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [domainExit_ne_top_ae D x] with ω hω
  exact propext (killedChildIntervals_nil_iff_escape D K C hKC hCD x ω hω)

/-- Base case of the actual ordered-child kernel: an empty record has outer-exit mass V. -/
theorem killedChildIntervals_nil_competing_mass (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) :
    pathLaw.real {ω | killedChildIntervals D K C x ω = []} = competingExitMass D K x := by
  rw [killedChildIntervals_nil_probability D K C hKC hCD x,
    competingExitMass_eq_one_sub_hit D K (fun y hy ↦ hCD (hKC hy)) x]

end SRWTightness
