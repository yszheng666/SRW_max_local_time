import SRWTightness.KilledRecordEventComparison
import SRWTightness.ActualFiniteRecordKernel

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Finite ordered trees with countably many leaf marks form a countable record space. -/
theorem finiteExcursionRecord_countable (M : Type*) [Countable M] (n : ℕ) :
    Countable (FiniteExcursionRecord M n) := by
  induction n with
  | zero => exact inferInstanceAs (Countable M)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Countable (List (FiniteExcursionRecord M n)))

/-- Actual finite-tree comparisons sum over joint restrictions on populations and leaf marks. -/
theorem actual_finite_record_event_comparison {M : Type*} [Countable M]
    (K C : ℕ → Finset Site) (F : Site → PathWord → M) (n : ℕ) (x : Site)
    (Q η : M → ℝ) (δ : ℕ → ℝ) (hQ : ∀ v, 0 ≤ Q v)
    (s : Set (FiniteExcursionRecord M n)) (E : ℝ)
    (he : ∀ r ∈ s, finiteRecordError δ η n r ≤ E)
    (h : ∀ r ∈ s,
      Real.exp (-finiteRecordError δ η n r) * finiteRecordReferenceWeight Q n r ≤
        pathLaw.real {ω | actualFiniteWordRecord K C F n x
          (killedPathWord (C n) x ω) = r} ∧
      pathLaw.real {ω | actualFiniteWordRecord K C F n x
          (killedPathWord (C n) x ω) = r} ≤
        Real.exp (finiteRecordError δ η n r) * finiteRecordReferenceWeight Q n r) :
    ENNReal.ofReal (Real.exp (-E)) *
        (∑' r : s, ENNReal.ofReal (finiteRecordReferenceWeight Q n r)) ≤
      pathLaw {ω | actualFiniteWordRecord K C F n x (killedPathWord (C n) x ω) ∈ s} ∧
    pathLaw {ω | actualFiniteWordRecord K C F n x (killedPathWord (C n) x ω) ∈ s} ≤
      ENNReal.ofReal (Real.exp E) *
        (∑' r : s, ENNReal.ofReal (finiteRecordReferenceWeight Q n r)) := by
  letI := finiteExcursionRecord_countable M n
  exact killed_record_event_exponential (C n) x (actualFiniteWordRecord K C F n x)
    (finiteRecordReferenceWeight Q n) (finiteRecordError δ η n) s E
    (finiteRecordReferenceWeight_nonneg Q hQ n) he h

end SRWTightness
