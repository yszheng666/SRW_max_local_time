import SRWTightness.ActualFiniteRecordKernel
import SRWTightness.ActualRecordProbabilityComparison

open MeasureTheory

namespace SRWTightness

/-- Multilevel comparison for trees extracted from the actual killed path, on entrance support. -/
theorem actual_finite_record_probability_comparison {M : Type*}
    (K C : ℕ → Finset Site) (hKC : ∀ n, K n ⊆ C n)
    (hCD : ∀ n, C n ⊆ C (n + 1)) (F : Site → PathWord → M)
    (A B : ℕ → Set Site) (hBK : ∀ n, B n ⊆ (K n : Set Site))
    (hBA : ∀ n, B n ⊆ A n) (hA : ∀ n, domainExitBoundary (C n) ⊆ A (n + 1))
    (hU : ∀ n x, x ∈ A (n + 1) →
      ∀ᵐ z ∂competingEntranceLaw (C (n + 1)) (K n) x, z ∈ B n)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hsmall : ∀ n, ε n ≤ 1 / 4)
    (hp : ∀ n x, x ∈ A (n + 1) →
      |setHitProbability (C (n + 1)) (K n) x - 1 / 2| ≤ ε n)
    (η Q : M → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hTerminal : ∀ x ∈ A 0, ∀ r,
      Real.exp (-η r) * Q r ≤ pathLaw.real {ω | F x (killedPathWord (C 0) x ω) = r} ∧
      pathLaw.real {ω | F x (killedPathWord (C 0) x ω) = r} ≤ Real.exp (η r) * Q r) :
    ∀ n x (r : FiniteExcursionRecord M n), x ∈ A n →
      Real.exp (-finiteRecordError (fun j ↦ 4 * ε j) η n r) *
          finiteRecordReferenceWeight Q n r ≤
        pathLaw.real {ω | actualFiniteWordRecord K C F n x (killedPathWord (C n) x ω) = r} ∧
      pathLaw.real {ω | actualFiniteWordRecord K C F n x (killedPathWord (C n) x ω) = r} ≤
        Real.exp (finiteRecordError (fun j ↦ 4 * ε j) η n r) *
          finiteRecordReferenceWeight Q n r := by
  intro n
  induction n with
  | zero => exact fun x r hx ↦ hTerminal x hx r
  | succ n ih =>
    intro x rs hx
    exact actual_supported_record_probability_comparison (C (n + 1)) (K n) (C n)
      (hKC n) (hCD n) (actualFiniteWordRecord K C F n) (A (n + 1)) (B n)
      (hBK n) (hA n) (hU n) (ε n) (hε n) (hsmall n) (hp n)
      (finiteRecordError (fun j ↦ 4 * ε j) η n) (finiteRecordReferenceWeight Q n)
      (finiteRecordReferenceWeight_nonneg Q hQ n)
      (fun z hz r ↦ ih z r (hBA n hz)) rs x hx

end SRWTightness
