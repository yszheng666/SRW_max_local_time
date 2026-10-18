import SRWTightness.ActualRecordProbabilityComparison
import SRWTightness.SupportedRecordUpper

open MeasureTheory
namespace SRWTightness

/-- Actual ordered records inherit upper child bounds without lower child comparisons. -/
theorem actual_supported_record_probability_upper {M : Type*}
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → M) (A B : Set Site) (hBK : B ⊆ (K : Set Site))
    (hA : domainExitBoundary C ⊆ A)
    (hU : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 4)
    (hp : ∀ x ∈ A, |setHitProbability D K x - 1 / 2| ≤ ε)
    (η Q : M → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hF : ∀ z ∈ B, ∀ r,
      pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ A →
      pathLaw.real {ω | killedChildRecords D K C x F ω = rs} ≤
        Real.exp (orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs := by
  have hs : ∀ z ∈ B, ∀ r,
      ∀ᵐ y ∂recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r, y ∈ A := by
    intro z hz r
    filter_upwards [recordExitSlice_supported C z (hKC (hBK hz))
      (fun ω ↦ F z (killedPathWord C z ω)) r] with y hy
    exact hA hy
  have hm : ∀ z ∈ B, ∀ r,
      (recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r).real Set.univ ≤
        Real.exp (η r) * Q r := by
    intro z hz r
    rw [recordExitSlice_mass]
    exact hF z hz r
  have hh := supported_ordered_record_weight_upper
    (competingEntranceLaw D K)
    (fun z r ↦ recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r)
    (competingExitMass D K) A B (fun _ ↦ inferInstance) (fun _ _ ↦ inferInstance)
    hU hs (4 * ε) η Q hQ
    (fun x hx ↦ (competing_mass_exponential_bounds D K
      (fun z hz ↦ hCD (hKC hz)) x ε hε hsmall (hp x hx)).1.2)
    (fun x hx ↦ by
      have hv := (competing_mass_exponential_bounds D K
        (fun z hz ↦ hCD (hKC hz)) x ε hε hsmall (hp x hx)).2
      exact ⟨(by positivity : 0 ≤ Real.exp (-(4 * ε)) / 2).trans hv.1, hv.2⟩) hm
  intro rs x hx
  simpa only [actual_ordered_record_kernel D K C hKC hCD F rs x] using (hh rs x hx).2

end SRWTightness
