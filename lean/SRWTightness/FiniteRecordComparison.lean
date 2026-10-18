import SRWTightness.OrderedRecordComparison

open MeasureTheory

namespace SRWTightness

/-- A finite ordered tree record of a prescribed depth, with marks at its terminal generation. -/
def FiniteExcursionRecord (M : Type*) : ℕ → Type _
  | 0 => M
  | n + 1 => List (FiniteExcursionRecord M n)

/-- Exact reference mass, with geometric branching at each nonterminal vertex. -/
noncomputable def finiteRecordReferenceWeight {M : Type*} (Q : M → ℝ) :
    (n : ℕ) → FiniteExcursionRecord M n → ℝ
  | 0, m => Q m
  | n + 1, rs => orderedReferenceWeight (finiteRecordReferenceWeight Q n) rs

/-- Accumulated decision and terminal errors, with level zero next to the terminal marks. -/
def finiteRecordError {M : Type*} (δ : ℕ → ℝ) (η : M → ℝ) :
    (n : ℕ) → FiniteExcursionRecord M n → ℝ
  | 0, m => η m
  | n + 1, rs => orderedRecordError (δ n) (finiteRecordError δ η n) rs

theorem finiteRecordReferenceWeight_nonneg {M : Type*} (Q : M → ℝ) (hQ : ∀ m, 0 ≤ Q m) :
    ∀ n (r : FiniteExcursionRecord M n), 0 ≤ finiteRecordReferenceWeight Q n r := by
  intro n
  induction n with
  | zero => exact hQ
  | succ n ih => exact fun rs ↦ orderedReferenceWeight_nonneg _ ih rs

/-- Backward comparison on the entire finite tree, conditional on the actual kernel identities. -/
theorem finite_record_kernel_comparison {X M : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (U : ℕ → X → Measure X) (V : ℕ → X → ℝ)
    (S : ∀ n, X → FiniteExcursionRecord M n → Measure X)
    (hUf : ∀ n x, IsFiniteMeasure (U n x)) (hSf : ∀ n x r, IsFiniteMeasure (S n x r))
    (δ : ℕ → ℝ) (η Q : M → ℝ) (hQ : ∀ m, 0 ≤ Q m)
    (hU : ∀ n x, Real.exp (-δ n) / 2 ≤ (U n x).real Set.univ ∧
      (U n x).real Set.univ ≤ Real.exp (δ n) / 2)
    (hV : ∀ n x, Real.exp (-δ n) / 2 ≤ V n x ∧ V n x ≤ Real.exp (δ n) / 2)
    (hTerminal : ∀ x m, Real.exp (-η m) * Q m ≤ (S 0 x m).real Set.univ ∧
      (S 0 x m).real Set.univ ≤ Real.exp (η m) * Q m)
    (hStep : ∀ n x (rs : FiniteExcursionRecord M (n + 1)),
      (S (n + 1) x rs).real Set.univ = orderedRecordWeight (U n) (S n) (V n) rs x) :
    ∀ n x (r : FiniteExcursionRecord M n),
      Real.exp (-finiteRecordError δ η n r) * finiteRecordReferenceWeight Q n r ≤
        (S n x r).real Set.univ ∧
      (S n x r).real Set.univ ≤
        Real.exp (finiteRecordError δ η n r) * finiteRecordReferenceWeight Q n r := by
  intro n
  induction n with
  | zero => exact hTerminal
  | succ n ih =>
    intro x rs
    rw [hStep]
    exact ordered_record_weight_comparison (U n) (S n) (V n) (hUf n) (hSf n)
      (δ n) (finiteRecordError δ η n) (finiteRecordReferenceWeight Q n)
      (finiteRecordReferenceWeight_nonneg Q hQ n) (hU n) (hV n)
      (fun z r ↦ ih z r) rs x

end SRWTightness
