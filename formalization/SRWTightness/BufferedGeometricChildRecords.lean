import SRWTightness.ActualGeometricChildRecords
import SRWTightness.BufferedLongRecordGeometry
import SRWTightness.AnnulusEscapeEvent

open MeasureTheory
namespace SRWTightness

/-- The actual long-segment root-list law uses only the fine-record estimates at inner entrance states. -/
theorem buffered_geometric_child_records {M : Type*}
    (ρ H J : ℝ) (hH : 1 ≤ H) (hρ : 8 * H ≤ ρ) (hJ : 1 ≤ J) (b : Site)
    (F : Site → PathWord → M) (p ε : ℝ) (hp : 0 ≤ p) (hpHalf : p ≤ 1 / 2)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2)
    (hescape : ∀ y ∈ domainExitBoundary (translateFinset b (diskFinset (Real.exp 1 * ρ + H))),
      |pathLaw.real {ω | domainExit (translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))) y ω <
        setHittingTime (translateFinset b (diskFinset (ρ - H))) y 0 ω} - p| ≤ ε * p)
    (η Q : M → ℝ) (hQ : ∀ u, 0 ≤ Q u)
    (hF : ∀ z : Site, ρ - H - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ ρ - H → ∀ u,
      Real.exp (-η u) * Q u ≤ pathLaw.real {ω |
        F z (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) z ω) = u} ∧
      pathLaw.real {ω |
        F z (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) z ω) = u} ≤
        Real.exp (η u) * Q u)
    (x : Site) (hx : x ∈ translateFinset b (diskFinset (ρ - H)))
    (hxlo : ρ - H - 1 ≤ Real.sqrt (normSq (x - b)))
    (hxhi : Real.sqrt (normSq (x - b)) ≤ ρ - H) (r : M) (rs : List M) :
    let E := 2 * ε * ((rs.length : ℝ) + 1) + ((r :: rs).map η).sum
    let W := p * (1 - p) ^ rs.length * ((r :: rs).map Q).prod
    let event := {ω | killedChildRecords
      (translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)))
      (translateFinset b (diskFinset (ρ - H)))
      (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) x F ω = r :: rs}
    Real.exp (-E) * W ≤ pathLaw.real event ∧ pathLaw.real event ≤ Real.exp E * W := by
  let D := translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))
  let K := translateFinset b (diskFinset (ρ - H))
  let C := translateFinset b (diskFinset (Real.exp 1 * ρ + H))
  let A := domainExitBoundary C
  let B : Set Site := {z | z ∈ K ∧ ρ - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
    Real.sqrt (normSq (z - b)) ≤ ρ - H}
  obtain ⟨hKC, hCD⟩ := buffered_long_domains_nested ρ H J hH hρ hJ b
  have hUs : ∀ y ∈ A, ∀ᵐ z ∂competingEntranceLaw D K y, z ∈ B := by
    intro y hy
    have hmem := buffered_long_boundary_mem_annulus ρ H J hH hρ hJ b y hy
    filter_upwards [competingEntranceLaw_supported D K y,
      competingEntranceLaw_radial_support b (ρ - H) (Real.exp (J + 1) * ρ + H)
        (by linarith) y hmem] with z hz hr
    exact ⟨hz, hr⟩
  have he : ∀ y ∈ A, |competingExitMass D K y - p| ≤ ε * p := by
    intro y hy
    rw [competingExitMass_eq_one_sub_hit D K (hKC.trans hCD),
      ← exit_before_hit_probability D K (hKC.trans hCD)]
    exact hescape y hy
  exact actual_geometric_child_records D K C hKC hCD F A B (fun _ hz ↦ hz.1)
    (fun _ hy ↦ hy) hUs p ε hp hpHalf hε hsmall he η Q hQ
    (fun z hz u ↦ hF z hz.2.1 hz.2.2 u) x ⟨hx, hxlo, hxhi⟩ r rs

end SRWTightness
