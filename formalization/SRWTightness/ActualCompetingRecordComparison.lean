import SRWTightness.CompetingMassComparison
import SRWTightness.SupportedRecordComparison

open MeasureTheory

namespace SRWTightness

/-- The supported record comparison specialized to the actual SRW competing entrance law. -/
theorem actual_competing_record_weight_comparison {R : Type*}
    (D K : Finset Site) (hKD : K ⊆ D) (S : Site → R → Measure Site) (A B : Set Site)
    (hSf : ∀ z r, IsFiniteMeasure (S z r))
    (hUs : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (hSs : ∀ z ∈ B, ∀ r, ∀ᵐ y ∂S z r, y ∈ A)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 4)
    (hp : ∀ x ∈ A, |setHitProbability D K x - 1 / 2| ≤ ε)
    (η Q : R → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hS : ∀ z ∈ B, ∀ r, Real.exp (-η r) * Q r ≤ (S z r).real Set.univ ∧
      (S z r).real Set.univ ≤ Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ A →
      Real.exp (-orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs ≤
        orderedRecordWeight (competingEntranceLaw D K) S (competingExitMass D K) rs x ∧
      orderedRecordWeight (competingEntranceLaw D K) S (competingExitMass D K) rs x ≤
        Real.exp (orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs := by
  apply supported_ordered_record_weight_comparison
    (competingEntranceLaw D K) S (competingExitMass D K) A B
    (fun x ↦ inferInstance) hSf hUs hSs (4 * ε) η Q hQ
  · intro x hx
    exact (competing_mass_exponential_bounds D K hKD x ε hε hsmall (hp x hx)).1
  · intro x hx
    exact (competing_mass_exponential_bounds D K hKD x ε hε hsmall (hp x hx)).2
  · exact hS

end SRWTightness
