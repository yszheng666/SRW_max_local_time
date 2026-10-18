import SRWTightness.ActualRecordKernel
import SRWTightness.ActualCompetingRecordComparison

open MeasureTheory

namespace SRWTightness

/-- Actual ordered-record probability bounds need child marginal control only on entrance support B. -/
theorem actual_supported_record_probability_comparison {M : Type*}
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → M) (A B : Set Site) (hBK : B ⊆ (K : Set Site))
    (hA : domainExitBoundary C ⊆ A)
    (hU : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 4)
    (hp : ∀ x ∈ A, |setHitProbability D K x - 1 / 2| ≤ ε)
    (η Q : M → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hF : ∀ z ∈ B, ∀ r,
      Real.exp (-η r) * Q r ≤ pathLaw.real {ω | F z (killedPathWord C z ω) = r} ∧
      pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ A →
      Real.exp (-orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs ≤
        pathLaw.real {ω | killedChildRecords D K C x F ω = rs} ∧
      pathLaw.real {ω | killedChildRecords D K C x F ω = rs} ≤
        Real.exp (orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs := by
  have hs : ∀ z ∈ B, ∀ r,
      ∀ᵐ y ∂recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r, y ∈ A := by
    intro z hz r
    filter_upwards [recordExitSlice_supported C z (hKC (hBK hz))
      (fun ω ↦ F z (killedPathWord C z ω)) r] with y hy
    exact hA hy
  have hm : ∀ z ∈ B, ∀ r,
      Real.exp (-η r) * Q r ≤
        (recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r).real Set.univ ∧
      (recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r).real Set.univ ≤
        Real.exp (η r) * Q r := by
    intro z hz r
    rw [recordExitSlice_mass]
    exact hF z hz r
  have hh := actual_competing_record_weight_comparison D K (fun z hz ↦ hCD (hKC hz))
    (fun z r ↦ recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r)
    A B (fun _ _ ↦ inferInstance) hU hs ε hε hsmall hp η Q hQ hm
  intro rs x hx
  simpa only [actual_ordered_record_kernel D K C hKC hCD F rs x] using hh rs x hx

/-- In an admissible parent region only the actual inner boundary entrance states need control. -/
theorem actual_boundary_record_probability_comparison {M : Type*}
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → M) (A : Set Site)
    (hAD : A ⊆ ((D \ K : Finset Site) : Set Site)) (hA : domainExitBoundary C ⊆ A)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 4)
    (hp : ∀ x ∈ A, |setHitProbability D K x - 1 / 2| ≤ ε)
    (η Q : M → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hF : ∀ z ∈ domainExitBoundary (D \ K) ∩ (K : Set Site), ∀ r,
      Real.exp (-η r) * Q r ≤ pathLaw.real {ω | F z (killedPathWord C z ω) = r} ∧
      pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ A →
      Real.exp (-orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs ≤
        pathLaw.real {ω | killedChildRecords D K C x F ω = rs} ∧
      pathLaw.real {ω | killedChildRecords D K C x F ω = rs} ≤
        Real.exp (orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs := by
  apply actual_supported_record_probability_comparison D K C hKC hCD F A
    (domainExitBoundary (D \ K) ∩ (K : Set Site)) (fun _ h ↦ h.2) hA
  · intro x hx
    exact competingEntranceLaw_supported_boundary D K x (hAD hx)
  · exact hε
  · exact hsmall
  · exact hp
  · exact hQ
  · exact hF

end SRWTightness
