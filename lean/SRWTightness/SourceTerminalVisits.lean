import SRWTightness.SourceExcursionDomains
import SRWTightness.DiskOnePoint

open MeasureTheory

namespace SRWTightness

/-- Actual terminal records for the source forest beginning at level k and ending at ℓ-1. -/
noncomputable def sourceTerminalRecords (m r : ℝ) (ℓ k : ℕ) (b : Site)
    (D : Finset Site) (x : Site) (ω : Sample) : List (Site × PathWord) :=
  actualTerminalWordRecords (sourceExcursionLevels m r ℓ b k (ℓ - k)) D x ω

/-- Source terminal entrance radius is exactly m-H0. -/
theorem source_terminal_entrance_domain (m r : ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b : Site) :
    sourceEntranceDomain m r ℓ b (ℓ - 1) =
      translateFinset b (diskFinset (m - sourceRecordBuffer r)) := by
  simp [sourceEntranceDomain, Nat.sub_add_cancel hℓ, sourceRecordRadius]

/-- Source terminal exit radius is exactly exp(1)m+H0. -/
theorem source_terminal_exit_domain (m r : ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b : Site) :
    sourceExitDomain m r ℓ b (ℓ - 1) =
      translateFinset b (diskFinset (Real.exp 1 * m + sourceRecordBuffer r)) := by
  have he : (ℓ : ℝ) - ((ℓ - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub hℓ]
    push_cast
    ring
  simp [sourceExitDomain, sourceRecordRadius, he, mul_comm]

/-- The source geometric levels assign every actual visit to a terminal finite path record. -/
theorem source_terminal_visit_identity (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (D K : Finset Site) (x : Site)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hK : K ⊆ translateFinset b (diskFinset (m - sourceRecordBuffer r - 2)))
    (hroot : sourceExitDomain m r ℓ b k ⊆ D)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (y : Site) (hy : y ∈ K) :
    domainLocalTime D x y ω =
      ((sourceTerminalRecords m r ℓ k b D x ω).map (wordRecordVisits y)).sum := by
  apply actualTerminalWordRecords_visit_sum
    (sourceExcursionLevels m r ℓ b k (ℓ - k)) D x y _ ω hfin
  exact sourceExcursionLevels_nested m r ℓ b y hr hm (hK hy) k (ℓ - k) D
    (by omega) hroot

/-- The same source identity for the original disk-killed walk and every observation coordinate. -/
theorem source_disk_terminal_visit_identity (R m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (K : Finset Site) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hK : K ⊆ translateFinset b (diskFinset (m - sourceRecordBuffer r - 2)))
    (hroot : sourceExitDomain m r ℓ b k ⊆ diskFinset R) :
    ∀ᵐ ω ∂pathLaw, ∀ y ∈ K, localTime ω (exitSteps R ω) y =
      ((sourceTerminalRecords m r ℓ k b (diskFinset R) 0 ω).map (wordRecordVisits y)).sum := by
  filter_upwards [domainExit_ne_top_ae (diskFinset R) 0] with ω hω
  intro y hy
  rw [← domainLocalTime_disk]
  exact source_terminal_visit_identity m r ℓ k hk b (diskFinset R) K 0 hr hm hK hroot
    ω hω y hy

end SRWTightness
