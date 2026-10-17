import SRWTightness.IndependentForestLaw

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Joint actual forest events are bounded by the probability of independent reference roots. -/
theorem actual_forest_reference_law_upper {M : Type*} [Countable M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)]
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → M) (A B : Set Site) (hBK : B ⊆ (K : Set Site))
    (hA : domainExitBoundary C ⊆ A)
    (hU : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (η : M → ℝ) (μ : Measure M) [IsProbabilityMeasure μ]
    (hp : ∀ x ∈ A, setHitProbability D K x ≤ ρ)
    (hF : ∀ z ∈ B, ∀ r, pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ Real.exp (η r) * μ.real {r})
    (x : Site) (hUx : ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B) (j : ℕ) (hj : 1 ≤ j)
    (s : Set (List M)) (E : ℝ) (hlen : ∀ rs ∈ s, rs.length = j)
    (herr : ∀ rs ∈ s, (rs.map η).sum ≤ E) :
    pathLaw {ω | killedChildRecords D K C x F ω ∈ s} ≤
      ENNReal.ofReal (ρ ^ (j - 1) * Real.exp E) *
        independentForestLaw μ j s := by
  have hh := actual_forest_event_upper D K C hKC hCD F A B hBK hA hU ρ hρ
    η (fun r ↦ μ.real {r}) (fun _ ↦ measureReal_nonneg) hp hF x hUx j hj s E hlen herr
  rw [← independentForestLaw_event μ j s hlen] at hh
  exact hh

end SRWTightness
