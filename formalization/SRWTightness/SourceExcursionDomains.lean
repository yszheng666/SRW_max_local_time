import SRWTightness.SourceRecordRadii
import SRWTightness.DiskCapacityLogBound
import SRWTightness.ActualTerminalWordVisits

namespace SRWTightness

/-- The source entrance ball A_(j+1) of a level-j excursion. -/
noncomputable def sourceEntranceDomain (m r : ℝ) (ℓ : ℕ) (b : Site) (j : ℕ) : Finset Site :=
  translateFinset b (diskFinset (sourceRecordRadius m ℓ (j + 1) - sourceRecordBuffer r))

/-- The source exit ball B_j of a level-j excursion. -/
noncomputable def sourceExitDomain (m r : ℝ) (ℓ : ℕ) (b : Site) (j : ℕ) : Finset Site :=
  translateFinset b (diskFinset (sourceRecordRadius m ℓ j + sourceRecordBuffer r))

/-- The actual source levels, starting at j and retaining n successive generations. -/
noncomputable def sourceExcursionLevels (m r : ℝ) (ℓ : ℕ) (b : Site) :
    ℕ → ℕ → List (Finset Site × Finset Site)
  | _, 0 => []
  | j, n + 1 => (sourceEntranceDomain m r ℓ b j, sourceExitDomain m r ℓ b j) ::
      sourceExcursionLevels m r ℓ b (j + 1) n

/-- Source radii decrease with the level index. -/
theorem sourceRecordRadius_antitone (m : ℝ) (hm : 0 ≤ m) (ℓ : ℕ) :
    Antitone (sourceRecordRadius m ℓ) := by
  intro i j hij
  have he : Real.exp ((ℓ : ℝ) - (j : ℝ)) ≤ Real.exp ((ℓ : ℝ) - (i : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hh : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  exact mul_le_mul_of_nonneg_left he hm

/-- The source entrance ball lies inside its exit ball. -/
theorem sourceEntranceDomain_subset_exit (m r : ℝ) (ℓ : ℕ) (b : Site) (j : ℕ)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) (hj : j + 1 ≤ ℓ) :
    sourceEntranceDomain m r ℓ b j ⊆ sourceExitDomain m r ℓ b j := by
  have hH : 0 ≤ sourceRecordBuffer r := by unfold sourceRecordBuffer; linarith
  have hm0 : 0 ≤ m := by linarith
  have hlo := sourceRecordRadius_ge_terminal m hm0 ℓ (j + 1) hj
  have hmono := sourceRecordRadius_antitone m hm0 ℓ (Nat.le_succ j)
  exact Finset.image_subset_image (diskFinset_mono _ _ (by linarith) (by linarith))

/-- Consecutive source exit balls are nested. -/
theorem sourceExitDomain_successor_subset (m r : ℝ) (ℓ : ℕ) (b : Site) (j : ℕ)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) :
    sourceExitDomain m r ℓ b (j + 1) ⊆ sourceExitDomain m r ℓ b j := by
  have hH : 0 ≤ sourceRecordBuffer r := by unfold sourceRecordBuffer; linarith
  have hm0 : 0 ≤ m := by linarith
  have hp : 0 ≤ sourceRecordRadius m ℓ (j + 1) :=
    mul_nonneg hm0 (Real.exp_pos _).le
  have hmono := sourceRecordRadius_antitone m hm0 ℓ (Nat.le_succ j)
  exact Finset.image_subset_image (diskFinset_mono _ _ (by linarith) (by linarith))

/-- The source observation ball is inside every entrance ball through the terminal level. -/
theorem sourceObservation_subset_entrance (m r : ℝ) (ℓ : ℕ) (b : Site) (j : ℕ)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) (hj : j + 1 ≤ ℓ) :
    translateFinset b (diskFinset (m - sourceRecordBuffer r - 2)) ⊆
      sourceEntranceDomain m r ℓ b j := by
  have hH : 0 ≤ sourceRecordBuffer r := by unfold sourceRecordBuffer; linarith
  have hm0 : 0 ≤ m := by linarith
  have hlo := sourceRecordRadius_ge_terminal m hm0 ℓ (j + 1) hj
  exact Finset.image_subset_image (diskFinset_mono _ _ (by linarith) (by linarith))

/-- The concrete source levels satisfy every nesting premise of terminal visit decomposition. -/
theorem sourceExcursionLevels_nested (m r : ℝ) (ℓ : ℕ) (b y : Site)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hy : y ∈ translateFinset b (diskFinset (m - sourceRecordBuffer r - 2)))
    (j n : ℕ) (D : Finset Site) (hn : j + n ≤ ℓ)
    (hD : sourceExitDomain m r ℓ b j ⊆ D) :
    NestedWordDomains y D (sourceExcursionLevels m r ℓ b j n) := by
  induction n generalizing j D with
  | zero => trivial
  | succ n ih =>
    have hj : j + 1 ≤ ℓ := by omega
    refine ⟨sourceObservation_subset_entrance m r ℓ b j hr hm hj hy,
      sourceEntranceDomain_subset_exit m r ℓ b j hr hm hj, hD, ?_⟩
    exact ih (j + 1) _ (by omega) (sourceExitDomain_successor_subset m r ℓ b j hr hm)

end SRWTightness
