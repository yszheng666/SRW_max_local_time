import SRWTightness.SupportedInitialForestUpper
import SRWTightness.ActualRecordProbabilityComparison

open MeasureTheory

namespace SRWTightness

/-- Actual prescribed root records cost at most one initial entrance and rho per later return. -/
theorem actual_forest_probability_upper {M : Type*}
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → M) (A B : Set Site) (hBK : B ⊆ (K : Set Site))
    (hA : domainExitBoundary C ⊆ A)
    (hU : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (W : M → ℝ) (hW : ∀ r, 0 ≤ W r)
    (hp : ∀ x ∈ A, setHitProbability D K x ≤ ρ)
    (hF : ∀ z ∈ B, ∀ r, pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ W r)
    (x : Site) (hUx : ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B) (r : M) (rs : List M) :
    pathLaw.real {ω | (killedChildIntervals D K C x ω).length = (r :: rs).length ∧
      killedChildRecords D K C x F ω = r :: rs} ≤
        ρ ^ rs.length * ((r :: rs).map W).prod := by
  rw [actual_ordered_record_kernel_with_count D K C hKC hCD]
  apply (supported_initial_forest_upper (competingEntranceLaw D K)
    (fun z r ↦ recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r)
    (competingExitMass D K) A B (fun _ ↦ inferInstance) (fun _ _ ↦ inferInstance)
    hU _ ρ hρ W hW _ _ _ x _ hUx r rs).2
  · intro z hz r
    filter_upwards [recordExitSlice_supported C z (hKC (hBK hz))
      (fun ω ↦ F z (killedPathWord C z ω)) r] with y hy
    exact hA hy
  · intro y hy
    rw [competingEntranceLaw_mass D K (hKC.trans hCD)]
    exact hp y hy
  · intro y hy
    have hh := competing_entrance_exit_mass D K y
    have hnon : 0 ≤ competingExitMass D K y := measureReal_nonneg
    have hmass : 0 ≤ (competingEntranceLaw D K y).real Set.univ := measureReal_nonneg
    exact ⟨hnon, by linarith⟩
  · intro z hz r
    rw [recordExitSlice_mass]
    exact hF z hz r
  · have hh := competing_entrance_exit_mass D K x
    have hnon : 0 ≤ competingExitMass D K x := measureReal_nonneg
    linarith

end SRWTightness
