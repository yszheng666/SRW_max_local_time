import SRWTightness.SourceSuccessVisits
import SRWTightness.SourceSuccessCount

namespace SRWTightness

/-- A positive manuscript count supplies an actual successful site on the shared path. -/
theorem source_success_count_positive (R A γ : ℝ)
    (I : sourceCandidateAnnulus R → ℕ)
    (z : ∀ b : sourceCandidateAnnulus R,
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b)))
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace))
    (hp : 0 < sourceSuccessCount R A γ I z p) :
    ∃ b : sourceCandidateAnnulus R,
      p ∈ sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b) := by
  classical
  by_contra h
  have hn : ∀ b : sourceCandidateAnnulus R,
      p ∉ sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b) := by
    simpa only [not_exists] using h
  have hz : sourceSuccessCount R A γ I z p = 0 := by
    simp [sourceSuccessCount, hn]
  rw [hz] at hp
  exact (lt_irrefl 0) hp

/-- Manuscript (5.16): a successful site forces the integer disk maximum threshold. -/
theorem source_success_count_disk_max (R A γ : ℝ) (hR : 0 < R)
    (ht : sourceScaleThreshold 4 ≤ Real.log R)
    (I : sourceCandidateAnnulus R → ℕ)
    (z : ∀ b : sourceCandidateAnnulus R,
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b)))
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace))
    (hp : 0 < sourceSuccessCount R A γ I z p) :
    Nat.ceil (diskCenter R ^ 2) ≤ diskMax R p.1 := by
  obtain ⟨b, hb⟩ := source_success_count_positive R A γ I z p hp
  have hh := source_success_disk_max (Real.log R) A γ b (I b) (z b) ht
    (sourceSiteProjection b p) hb
  simpa only [sourceTerminalVisitCutoff_at_radius, Real.exp_log hR,
    sourceSiteProjection] using hh

/-- The second inclusion of (5.16) does not require a successful event. -/
theorem disk_cutoff_sqrt_max (R : ℝ) (ω : Sample)
    (hh : Nat.ceil (diskCenter R ^ 2) ≤ diskMax R ω) :
    diskCenter R ≤ Real.sqrt (diskMax R ω) := by
  have hcast : (Nat.ceil (diskCenter R ^ 2) : ℝ) ≤ (diskMax R ω : ℝ) := by
    exact_mod_cast hh
  calc
    diskCenter R ≤ |diskCenter R| := le_abs_self _
    _ = Real.sqrt (diskCenter R ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (diskMax R ω) := Real.sqrt_le_sqrt ((Nat.le_ceil _).trans hcast)

/-- The integer threshold implies the centered square-root maximum is nonnegative. -/
theorem source_success_count_sqrt_max (R A γ : ℝ) (hR : 0 < R)
    (ht : sourceScaleThreshold 4 ≤ Real.log R)
    (I : sourceCandidateAnnulus R → ℕ)
    (z : ∀ b : sourceCandidateAnnulus R,
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b)))
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace))
    (hp : 0 < sourceSuccessCount R A γ I z p) :
    diskCenter R ≤ Real.sqrt (diskMax R p.1) := by
  exact disk_cutoff_sqrt_max R p.1
    (source_success_count_disk_max R A γ hR ht I z p hp)

end SRWTightness
