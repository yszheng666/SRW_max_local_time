import SRWTightness.KilledPathWord
import SRWTightness.StoppedFuture

open MeasureTheory

namespace SRWTightness

/-- The observed finite direction word at a domain exit, using stoppedValue's convention at infinity. -/
noncomputable def stoppedPathWord (D : Finset Site) (x : Site) : Sample → PathWord :=
  stoppedValue (fun n ω ↦ (⟨n, fun k ↦ ω k⟩ : PathWord)) (domainExit D x)

/-- The whole finite path record belongs to the information available at the exit stopping time. -/
theorem measurable_stoppedPathWord (D : Finset Site) (x : Site) :
    Measurable[(domainExit_isStoppingTime D x).measurableSpace] (stoppedPathWord D x) := by
  letI : TopologicalSpace PathWord := ⊥
  letI : DiscreteTopology PathWord := ⟨rfl⟩
  have hs : StronglyAdapted history (fun n ω ↦ (⟨n, fun k ↦ ω k⟩ : PathWord)) := by
    intro n
    letI : MeasurableSpace Sample := history n
    have hm : Measurable (fun ω : Sample ↦ (⟨n, fun k ↦ ω k⟩ : PathWord)) :=
      (measurable_of_countable (fun v : Fin n → Direction ↦ (⟨n, v⟩ : PathWord))).comp
        (history_measurable_prefix n)
    exact hm.stronglyMeasurable
  exact measurable_stoppedValue hs.isStronglyProgressive_of_discrete (domainExit_isStoppingTime D x)

/-- At every finite exit the stopped record is the actual killed path word. -/
theorem stoppedPathWord_eq (D : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) : stoppedPathWord D x ω = killedPathWord D x ω := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
  unfold stoppedPathWord stoppedValue killedPathWord domainSteps
  apply congrArg (fun n : ℕ ↦ (⟨n, fun k ↦ ω k⟩ : PathWord))
  rw [← hn]
  rfl

/-- Strong Markov factorization retaining the entire actual killed word, hence all child marks. -/
theorem killed_word_future_factorization (D : Finset Site) (x : Site)
    (s : Set PathWord) (t : Set Sample) (ht : MeasurableSet t) :
    pathLaw ({ω | killedPathWord D x ω ∈ s} ∩ (futureAt (domainExit D x)) ⁻¹' t) =
      pathLaw {ω | killedPathWord D x ω ∈ s} * pathLaw t := by
  have hs : MeasurableSet[(domainExit_isStoppingTime D x).measurableSpace]
      {ω | stoppedPathWord D x ω ∈ s} :=
    (measurable_stoppedPathWord D x) (Set.to_countable s).measurableSet
  calc
    _ = pathLaw ({ω | stoppedPathWord D x ω ∈ s} ∩ (futureAt (domainExit D x)) ⁻¹' t) := by
      apply measure_congr
      filter_upwards [domainExit_ne_top_ae D x] with ω hω
      change (killedPathWord D x ω ∈ s ∧ futureAt (domainExit D x) ω ∈ t) =
        (stoppedPathWord D x ω ∈ s ∧ futureAt (domainExit D x) ω ∈ t)
      rw [stoppedPathWord_eq D x ω hω]
    _ = pathLaw {ω | stoppedPathWord D x ω ∈ s} * pathLaw t :=
      stopped_future_factorization (domainExit D x) (domainExit_isStoppingTime D x)
        (domainExit_ne_top_ae D x) _ t hs ht
    _ = _ := by
      congr 1
      apply measure_congr
      filter_upwards [domainExit_ne_top_ae D x] with ω hω
      change (stoppedPathWord D x ω ∈ s) = (killedPathWord D x ω ∈ s)
      rw [stoppedPathWord_eq D x ω hω]

end SRWTightness
