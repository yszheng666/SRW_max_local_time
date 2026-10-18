import SRWTightness.ActualSingleRootComparison
import SRWTightness.GeneralEntranceRadialSupport

open MeasureTheory
namespace SRWTightness

/-- One-root comparison on any radial entrance shell retains the exit-dependent nonreturn. -/
theorem radial_single_root_comparison {M : Type*}
    (D C : Finset Site) (b : Site) (a : ℝ) (ha : 1 ≤ a)
    (hAC : translateFinset b (diskFinset a) ⊆ C) (hCD : C ⊆ D)
    (x : Site) (hx : x ∈ D \ translateFinset b (diskFinset a))
    (F : Site → PathWord → M) (r : M) (c₁ c₂ η Q : ℝ)
    (hc₂ : 0 ≤ c₂) (hQ : 0 ≤ Q)
    (hI : c₁ ≤ setHitProbability D (translateFinset b (diskFinset a)) x)
    (hq : ∀ y ∈ domainExitBoundary C,
      c₂ ≤ competingExitMass D (translateFinset b (diskFinset a)) y)
    (hF : ∀ z : Site, a - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ a →
      Real.exp (-η) * Q ≤ pathLaw.real {ω | F z (killedPathWord C z ω) = r} ∧
      pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ Real.exp η * Q) :
    c₁ * c₂ * Real.exp (-η) * Q ≤
      pathLaw.real {ω | killedChildRecords D (translateFinset b (diskFinset a)) C x F ω = [r]} ∧
    pathLaw.real {ω | killedChildRecords D (translateFinset b (diskFinset a)) C x F ω = [r]} ≤
      Real.exp η * Q := by
  let A := translateFinset b (diskFinset a)
  let S : Set Site := {z | z ∈ A ∧ a - 1 ≤ Real.sqrt (normSq (z - b)) ∧
    Real.sqrt (normSq (z - b)) ≤ a}
  have hs : ∀ᵐ z ∂competingEntranceLaw D A x, z ∈ S := by
    filter_upwards [competingEntranceLaw_supported D A x,
      competingEntranceLaw_radial_support_domain D b a ha x hx] with z hz hr
    exact ⟨hz, hr⟩
  have h := actual_single_root_comparison D A C hAC hCD F S
    (fun z hz ↦ hz.1) x hs r c₁ c₂ η Q hc₂ hQ hI hq
    (fun z hz ↦ hF z hz.2.1 hz.2.2)
  have he : {ω | (killedChildIntervals D A C x ω).length = 1 ∧
      killedChildRecords D A C x F ω = [r]} =
      {ω | killedChildRecords D A C x F ω = [r]} := by
    ext ω
    constructor
    · exact fun hh ↦ hh.2
    · intro hh
      refine ⟨?_, hh⟩
      rw [← killedChildRecords_length D A C x F ω, hh, List.length_singleton]
  rw [he] at h
  exact h

end SRWTightness
