import SRWTightness.ActualCompetingRecordComparison

open MeasureTheory

namespace SRWTightness

/-- Comparison for actual joint child-record and exit-position slices, retaining their dependence. -/
theorem actual_record_slice_weight_comparison {M : Type*}
    (D K C : Finset Site) (hKD : K ⊆ D) (hKC : K ⊆ C)
    (F : Site → Sample → M) (A : Set Site) (hA : domainExitBoundary C ⊆ A)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 4)
    (hp : ∀ x ∈ A, |setHitProbability D K x - 1 / 2| ≤ ε)
    (η Q : M → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hF : ∀ z ∈ K, ∀ r, Real.exp (-η r) * Q r ≤ pathLaw.real {ω | F z ω = r} ∧
      pathLaw.real {ω | F z ω = r} ≤ Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ A →
      Real.exp (-orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs ≤
        orderedRecordWeight (competingEntranceLaw D K)
          (fun z r ↦ recordExitSlice C z (F z) r) (competingExitMass D K) rs x ∧
      orderedRecordWeight (competingEntranceLaw D K)
          (fun z r ↦ recordExitSlice C z (F z) r) (competingExitMass D K) rs x ≤
        Real.exp (orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs := by
  apply actual_competing_record_weight_comparison D K hKD
    (fun z r ↦ recordExitSlice C z (F z) r) A (K : Set Site)
    (fun z r ↦ inferInstance)
  · intro x hx
    exact competingEntranceLaw_supported D K x
  · intro z hz r
    filter_upwards [recordExitSlice_supported C z (hKC hz) (F z) r] with y hy
    exact hA hy
  · exact hε
  · exact hsmall
  · exact hp
  · exact hQ
  · intro z hz r
    rw [recordExitSlice_mass]
    exact hF z hz r

end SRWTightness
