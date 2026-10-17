import SRWTightness.GeometricRecordComparison
import SRWTightness.RelativeProbabilityExponential

open MeasureTheory
namespace SRWTightness

/-- Relative escape control gives matching exponential control of both complementary decisions. -/
theorem competing_geometric_mass_bounds (D K : Finset Site) (x : Site)
    (p ε : ℝ) (hp : 0 ≤ p) (hpHalf : p ≤ 1 / 2) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2)
    (hescape : |competingExitMass D K x - p| ≤ ε * p) :
    (Real.exp (-(2 * ε)) * (1 - p) ≤ (competingEntranceLaw D K x).real Set.univ ∧
      (competingEntranceLaw D K x).real Set.univ ≤ Real.exp (2 * ε) * (1 - p)) ∧
    (Real.exp (-(2 * ε)) * p ≤ competingExitMass D K x ∧
      competingExitMass D K x ≤ Real.exp (2 * ε) * p) := by
  have hmass := competing_entrance_exit_mass D K x
  have hreturn : |(competingEntranceLaw D K x).real Set.univ - (1 - p)| ≤ ε * (1 - p) := by
    rw [show (competingEntranceLaw D K x).real Set.univ - (1 - p) =
      -(competingExitMass D K x - p) by linarith, abs_neg]
    exact hescape.trans (mul_le_mul_of_nonneg_left (by linarith) hε)
  exact ⟨relative_probability_exponential _ (1 - p) ε (by linarith) hε hsmall hreturn,
    relative_probability_exponential _ p ε hp hε hsmall hescape⟩

/-- Actual competing kernels give a geometric ordered-record law without separating records from their exits. -/
theorem actual_geometric_record_weight_comparison {R : Type*}
    (D K : Finset Site) (S : Site → R → Measure Site) (A B : Set Site)
    (hSf : ∀ z r, IsFiniteMeasure (S z r))
    (hUs : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (hSs : ∀ z ∈ B, ∀ r, ∀ᵐ y ∂S z r, y ∈ A)
    (p ε : ℝ) (hp : 0 ≤ p) (hpHalf : p ≤ 1 / 2) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2)
    (hescape : ∀ x ∈ A, |competingExitMass D K x - p| ≤ ε * p)
    (η Q : R → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hS : ∀ z ∈ B, ∀ r, Real.exp (-η r) * Q r ≤ (S z r).real Set.univ ∧
      (S z r).real Set.univ ≤ Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ A →
      Real.exp (-orderedRecordError (2 * ε) η rs) * geometricOrderedReferenceWeight p Q rs ≤
        orderedRecordWeight (competingEntranceLaw D K) S (competingExitMass D K) rs x ∧
      orderedRecordWeight (competingEntranceLaw D K) S (competingExitMass D K) rs x ≤
        Real.exp (orderedRecordError (2 * ε) η rs) * geometricOrderedReferenceWeight p Q rs := by
  apply supported_geometric_record_weight_comparison
    (competingEntranceLaw D K) S (competingExitMass D K) A B
    (fun x ↦ inferInstance) hSf hUs hSs p hp (by linarith) (2 * ε) η Q hQ
  · intro x hx
    exact (competing_geometric_mass_bounds D K x p ε hp hpHalf hε hsmall (hescape x hx)).1
  · intro x hx
    exact (competing_geometric_mass_bounds D K x p ε hp hpHalf hε hsmall (hescape x hx)).2
  · exact hS

end SRWTightness
