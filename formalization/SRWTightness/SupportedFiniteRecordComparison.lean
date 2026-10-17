import SRWTightness.FiniteRecordComparison
import SRWTightness.SupportedRecordComparison

open MeasureTheory

namespace SRWTightness

/-- Finite-tree comparison on depth-dependent admissible boundary states. -/
theorem supported_finite_record_kernel_comparison {X M : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (U : ℕ → X → Measure X) (V : ℕ → X → ℝ)
    (S : ∀ n, X → FiniteExcursionRecord M n → Measure X) (A : ℕ → Set X)
    (hUf : ∀ n x, IsFiniteMeasure (U n x)) (hSf : ∀ n x r, IsFiniteMeasure (S n x r))
    (hUs : ∀ n x, x ∈ A (n + 1) → ∀ᵐ z ∂U n x, z ∈ A n)
    (hSs : ∀ n z, z ∈ A n → ∀ r, ∀ᵐ y ∂S n z r, y ∈ A (n + 1))
    (δ : ℕ → ℝ) (η Q : M → ℝ) (hQ : ∀ m, 0 ≤ Q m)
    (hU : ∀ n x, x ∈ A (n + 1) → Real.exp (-δ n) / 2 ≤ (U n x).real Set.univ ∧
      (U n x).real Set.univ ≤ Real.exp (δ n) / 2)
    (hV : ∀ n x, x ∈ A (n + 1) →
      Real.exp (-δ n) / 2 ≤ V n x ∧ V n x ≤ Real.exp (δ n) / 2)
    (hTerminal : ∀ x ∈ A 0, ∀ m, Real.exp (-η m) * Q m ≤ (S 0 x m).real Set.univ ∧
      (S 0 x m).real Set.univ ≤ Real.exp (η m) * Q m)
    (hStep : ∀ n x, x ∈ A (n + 1) → ∀ (rs : FiniteExcursionRecord M (n + 1)),
      (S (n + 1) x rs).real Set.univ = orderedRecordWeight (U n) (S n) (V n) rs x) :
    ∀ n x (r : FiniteExcursionRecord M n), x ∈ A n →
      Real.exp (-finiteRecordError δ η n r) * finiteRecordReferenceWeight Q n r ≤
        (S n x r).real Set.univ ∧
      (S n x r).real Set.univ ≤
        Real.exp (finiteRecordError δ η n r) * finiteRecordReferenceWeight Q n r := by
  intro n
  induction n with
  | zero => exact fun x r hx ↦ hTerminal x hx r
  | succ n ih =>
    intro x rs hx
    rw [hStep n x hx]
    exact supported_ordered_record_weight_comparison (U n) (S n) (V n) (A (n + 1)) (A n)
      (hUf n) (hSf n) (hUs n) (hSs n) (δ n) (finiteRecordError δ η n)
      (finiteRecordReferenceWeight Q n) (finiteRecordReferenceWeight_nonneg Q hQ n)
      (hU n) (hV n) (fun z hz r ↦ ih z r hz) rs x hx

end SRWTightness
