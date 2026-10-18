import SRWTightness.ActualForestReferenceUpper
import SRWTightness.FiniteRecordReferenceMeasure

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Actual forest events compare directly to independent marked-GW reference trees. -/
theorem actual_marked_tree_forest_upper {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (hinput : MarkedGWTreeInput M)
    (μ : Measure M) (hμ : IsProbabilityMeasure μ) (n : ℕ)
    [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)]
    [MeasurableSpace (List (FiniteExcursionRecord M n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord M n))]
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → (FiniteExcursionRecord M n)) (A B : Set Site) (hBK : B ⊆ (K : Set Site))
    (hA : domainExitBoundary C ⊆ A)
    (hU : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (η : (FiniteExcursionRecord M n) → ℝ)
    (hp : ∀ x ∈ A, setHitProbability D K x ≤ ρ)
    (hF : ∀ z ∈ B, ∀ r, pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ Real.exp (η r) * finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r)
    (x : Site) (hUx : ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B) (j : ℕ) (hj : 1 ≤ j)
    (s : Set (List (FiniteExcursionRecord M n))) (E : ℝ) (hlen : ∀ rs ∈ s, rs.length = j)
    (herr : ∀ rs ∈ s, (rs.map η).sum ≤ E) :
    pathLaw {ω | killedChildRecords D K C x F ω ∈ s} ≤
      ENNReal.ofReal (ρ ^ (j - 1) * Real.exp E) *
        independentForestLaw (finiteRecordReferenceMeasure μ n) j s := by
  letI := finiteExcursionRecord_countable M n
  letI := finiteRecordReferenceMeasure_probability hinput μ hμ n
  apply actual_forest_reference_law_upper D K C hKC hCD F A B hBK hA hU
    ρ hρ η (finiteRecordReferenceMeasure μ n) hp _ x hUx j hj s E hlen herr
  intro z hz r
  rw [finiteRecordReferenceMeasure_real_singleton]
  exact hF z hz r

end SRWTightness
