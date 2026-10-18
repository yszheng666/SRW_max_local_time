import SRWTightness.BufferedGeometricChildRecords
import SRWTightness.SourceLongEscapeProbability

namespace SRWTightness

/-- The unconditioned long-segment reference law and its k-dependent error follow from actual escape and fine-record bounds. -/
theorem buffered_long_record_estimate (hP : PotentialKernelAsymptoticInput) :
    ∃ C T : ℝ, 0 < C ∧ 2 ≤ T ∧ ∀ ρ H J : ℝ, 1 ≤ H → 8 * H ≤ ρ →
      T * (H + 1) ≤ ρ - H → 3 ≤ J →
      ∀ (M : Type*) (b : Site) (F : Site → PathWord → M) (η Q : M → ℝ),
      (∀ u, 0 ≤ Q u) →
      (∀ z : Site, ρ - H - 1 ≤ Real.sqrt (normSq (z - b)) →
        Real.sqrt (normSq (z - b)) ≤ ρ - H → ∀ u,
        Real.exp (-η u) * Q u ≤ pathLaw.real {ω |
          F z (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) z ω) = u} ∧
        pathLaw.real {ω |
          F z (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) z ω) = u} ≤
          Real.exp (η u) * Q u) →
      ∀ x : Site, x ∈ translateFinset b (diskFinset (ρ - H)) →
      ρ - H - 1 ≤ Real.sqrt (normSq (x - b)) → Real.sqrt (normSq (x - b)) ≤ ρ - H →
      ∀ (r : M) (rs : List M),
      let p := bufferedLongEscapeParameter ρ H J
      let E := C * (H + 1) / (ρ - H) * ((rs.length : ℝ) + 1) + ((r :: rs).map η).sum
      let W := p * (1 - p) ^ rs.length * ((r :: rs).map Q).prod
      let event := {ω | killedChildRecords
        (translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)))
        (translateFinset b (diskFinset (ρ - H)))
        (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) x F ω = r :: rs}
      Real.exp (-E) * W ≤ pathLaw.real event ∧ pathLaw.real event ≤ Real.exp E * W := by
  obtain ⟨C, a₀, hC, ha₀, hh⟩ := annulus_escape_relative hP
  let T := a₀ + 2 * C + 2
  have hT : 2 ≤ T := by dsimp [T]; linarith
  have hTC : 2 * C ≤ T := by dsimp [T]; linarith
  have hTa : a₀ ≤ T := by dsimp [T]; linarith
  refine ⟨2 * C, T, by positivity, hT, ?_⟩
  intro ρ H J hH hρ hlarge hJ M b F η Q hQ hF x hx hxlo hxhi r rs
  let p := bufferedLongEscapeParameter ρ H J
  let ε := C * (H + 1) / (ρ - H)
  have hH0 : 0 ≤ H := by linarith
  have hρ2 : 2 ≤ ρ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have ha0 : 0 < ρ - H := by linarith
  have hJ1 : 1 ≤ J := by linarith
  have hJpos : 0 < J + 1 := by linarith
  have hpBounds := buffered_long_escape_parameter_bounds ρ H J hρ0 hH0 (by linarith) hJ1
  have hp : 0 ≤ p := (show 0 ≤ (1 / 2 : ℝ) / (J + 1) by positivity).trans hpBounds.1
  have hpHalf : p ≤ 1 / 2 := hpBounds.2.trans ((div_le_iff₀ hJpos).mpr (by linarith))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hsmall : ε ≤ 1 / 2 := by
    dsimp only [ε]
    apply (div_le_iff₀ ha0).mpr
    have hm := (mul_le_mul_of_nonneg_right hTC (show 0 ≤ H + 1 by linarith)).trans hlarge
    nlinarith
  have ha : a₀ ≤ ρ - H := by
    have ht0 : 0 ≤ T := by linarith
    have hmult : T ≤ T * (H + 1) := by nlinarith [mul_nonneg ht0 hH0]
    exact hTa.trans (hmult.trans hlarge)
  have hescape : ∀ y ∈ domainExitBoundary (translateFinset b (diskFinset (Real.exp 1 * ρ + H))),
      |pathLaw.real {ω | domainExit (translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))) y ω <
        setHittingTime (translateFinset b (diskFinset (ρ - H))) y 0 ω} - p| ≤ ε * p := by
    intro y hy
    have hrad := translated_disk_boundary_radial b (Real.exp 1 * ρ + H) (by positivity) y hy
    have hab : 2 * (ρ - H) ≤ Real.exp 1 * ρ + H := by nlinarith [Real.exp_one_gt_two]
    obtain ⟨δ, hδ, he⟩ := hh (ρ - H) (Real.exp 1 * ρ + H) (Real.exp (J + 1) * ρ + H)
      ha hab (buffered_long_radius_gap ρ H J hρ2 hJ1) b y hrad.1 hrad.2
    have hδ' : |δ| ≤ ε := hδ.trans (div_le_div_of_nonneg_right
      (show C ≤ C * (H + 1) by nlinarith [mul_nonneg hC.le hH0]) ha0.le)
    change pathLaw.real {ω | domainExit (translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))) y ω <
      setHittingTime (translateFinset b (diskFinset (ρ - H))) y 0 ω} = p * (1 + δ) at he
    rw [he, show p * (1 + δ) - p = p * δ by ring, abs_mul, abs_of_nonneg hp]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hδ' hp
  have hb := buffered_geometric_child_records ρ H J hH hρ hJ1 b F p ε hp hpHalf hε hsmall
    hescape η Q hQ hF x hx hxlo hxhi r rs
  dsimp only at hb ⊢
  have hεid : 2 * ε = (2 * C) * (H + 1) / (ρ - H) := by dsimp [ε]; ring
  rw [hεid] at hb
  exact hb

end SRWTightness
