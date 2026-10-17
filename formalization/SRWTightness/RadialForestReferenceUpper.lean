import SRWTightness.GeneralEntranceRadialSupport
import SRWTightness.ActualForestReferenceUpper

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Radial root comparison in an arbitrary outer domain, with entrance supports discharged. -/
theorem radial_forest_reference_upper {M : Type*} [Countable M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)]
    (D : Finset Site) (b : Site) (a c : ℝ) (ha : 1 ≤ a) (hc : 0 ≤ c)
    (hKC : translateFinset b (diskFinset a) ⊆ translateFinset b (diskFinset c))
    (hCD : translateFinset b (diskFinset c) ⊆ D)
    (hboundary : domainExitBoundary (translateFinset b (diskFinset c)) ⊆ (D : Set Site))
    (F : Site → PathWord → M) (ρ : ℝ) (hρ : 0 ≤ ρ) (η : M → ℝ)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hp : ∀ y : Site, c ≤ Real.sqrt (normSq (y - b)) →
      Real.sqrt (normSq (y - b)) ≤ c + 1 →
      setHitProbability D (translateFinset b (diskFinset a)) y ≤ ρ)
    (hF : ∀ z : Site, a - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ a → ∀ r,
      pathLaw.real {ω | F z (killedPathWord (translateFinset b (diskFinset c)) z ω) = r} ≤
        Real.exp (η r) * μ.real {r})
    (x : Site) (hx : x ∈ D \ translateFinset b (diskFinset a)) (j : ℕ) (hj : 1 ≤ j)
    (s : Set (List M)) (E : ℝ) (hlen : ∀ rs ∈ s, rs.length = j)
    (herr : ∀ rs ∈ s, (rs.map η).sum ≤ E) :
    pathLaw {ω | killedChildRecords D (translateFinset b (diskFinset a))
      (translateFinset b (diskFinset c)) x F ω ∈ s} ≤
      ENNReal.ofReal (ρ ^ (j - 1) * Real.exp E) * independentForestLaw μ j s := by
  let K := translateFinset b (diskFinset a)
  let C := translateFinset b (diskFinset c)
  let B : Set Site := {z | z ∈ K ∧ a - 1 ≤ Real.sqrt (normSq (z - b)) ∧
    Real.sqrt (normSq (z - b)) ≤ a}
  have hentrance : ∀ y ∈ D \ K, ∀ᵐ z ∂competingEntranceLaw D K y, z ∈ B := by
    intro y hy
    filter_upwards [competingEntranceLaw_supported D K y,
      competingEntranceLaw_radial_support_domain D b a ha y hy] with z hz hr
    exact ⟨hz, hr⟩
  apply actual_forest_reference_law_upper D K C hKC hCD F (domainExitBoundary C) B
    (fun z hz ↦ hz.1) (fun _ h ↦ h) _ ρ hρ η μ _ _ x (hentrance x hx) j hj s E hlen herr
  · intro y hy
    apply hentrance y
    exact Finset.mem_sdiff.mpr ⟨hboundary hy, fun hyK ↦ hy.1 (hKC hyK)⟩
  · intro y hy
    have hr := translated_disk_boundary_radial b c hc y hy
    exact hp y hr.1 hr.2
  · intro z hz r
    exact hF z hz.2.1 hz.2.2 r

end SRWTightness
