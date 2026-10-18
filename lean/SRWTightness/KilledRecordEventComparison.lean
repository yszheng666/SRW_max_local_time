import SRWTightness.CountableRecordEventComparison
import SRWTightness.KilledPathWord

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Event comparison for records extracted from the actual stopped SRW, preserving all joint tests. -/
theorem killed_record_event_exponential {R : Type*} [Countable R]
    (D : Finset Site) (x : Site) (F : PathWord → R) (q e : R → ℝ)
    (s : Set R) (E : ℝ) (hq : ∀ r, 0 ≤ q r) (he : ∀ r ∈ s, e r ≤ E)
    (h : ∀ r ∈ s,
      Real.exp (-e r) * q r ≤ pathLaw.real {ω | F (killedPathWord D x ω) = r} ∧
      pathLaw.real {ω | F (killedPathWord D x ω) = r} ≤ Real.exp (e r) * q r) :
    ENNReal.ofReal (Real.exp (-E)) * (∑' r : s, ENNReal.ofReal (q r)) ≤
      pathLaw {ω | F (killedPathWord D x ω) ∈ s} ∧
    pathLaw {ω | F (killedPathWord D x ω) ∈ s} ≤
      ENNReal.ofReal (Real.exp E) * (∑' r : s, ENNReal.ofReal (q r)) := by
  apply countable_record_event_exponential pathLaw (fun ω ↦ F (killedPathWord D x ω))
    q e s E hq _ he h
  intro r hr
  exact (measurable_killedPathWord D x)
    ((Set.to_countable {w : PathWord | F w = r}).measurableSet)

end SRWTightness
