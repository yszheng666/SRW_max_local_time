import SRWTightness.PositiveHarmonicChain
import SRWTightness.EntranceAtomGreen

open MeasureTheory
namespace SRWTightness

/-- Actual entrance atoms inherit harmonic-chain bounds even for arbitrarily small atoms. -/
theorem positive_entrance_chain (hinput : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 8 ≤ B → 2 * C ≤ B →
      ∀ (D K : Finset Site) (v : Site), v ∈ K → ∀ (x : ℕ → Site) (n : ℕ),
      (∀ i < n, normSq (x (i + 1) - x i) < 4) →
      (∀ i < n, translateFinset (x i) (diskFinset B) ⊆ D \ K) →
      Real.exp (-(2 * (C / B) * (n : ℝ))) *
          (competingEntranceLaw D K (x 0)).real {v} ≤
        (competingEntranceLaw D K (x n)).real {v} ∧
      (competingEntranceLaw D K (x n)).real {v} ≤
        Real.exp (2 * (C / B) * (n : ℝ)) *
          (competingEntranceLaw D K (x 0)).real {v} := by
  obtain ⟨C, hC, hh⟩ := positive_harmonic_chain hinput
  refine ⟨C, hC, ?_⟩
  intro B hB hCB D K v hv x n hstep hballs
  apply hh B hB hCB (fun y ↦ (competingEntranceLaw D K y).real {v})
    (fun _ ↦ measureReal_nonneg) x n hstep
  intro i hi y hy
  simp_rw [competingEntranceLaw_atom_payoff D K _ v hv]
  exact exitPayoff_first_step (D \ K) (fun z ↦ if z = v then 1 else 0) y
    (hballs i hi hy)

/-- A chain with bounded length-to-width ratio gives a scale-independent entrance comparison. -/
theorem positive_entrance_chain_uniform (hinput : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B L : ℝ), 8 ≤ B → 2 * C ≤ B →
      ∀ (D K : Finset Site) (v : Site), v ∈ K → ∀ (x : ℕ → Site) (n : ℕ),
      (n : ℝ) ≤ L * B →
      (∀ i < n, normSq (x (i + 1) - x i) < 4) →
      (∀ i < n, translateFinset (x i) (diskFinset B) ⊆ D \ K) →
      Real.exp (-(2 * C * L)) * (competingEntranceLaw D K (x 0)).real {v} ≤
        (competingEntranceLaw D K (x n)).real {v} ∧
      (competingEntranceLaw D K (x n)).real {v} ≤
        Real.exp (2 * C * L) * (competingEntranceLaw D K (x 0)).real {v} := by
  obtain ⟨C, hC, hh⟩ := positive_entrance_chain hinput
  refine ⟨C, hC, ?_⟩
  intro B L hB hCB D K v hv x n hn hstep hballs
  have hB0 : 0 < B := by linarith
  have hratio : (n : ℝ) / B ≤ L := (div_le_iff₀ hB0).mpr hn
  have he : 2 * (C / B) * (n : ℝ) ≤ 2 * C * L := by
    have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * C by positivity)
    calc
      _ = 2 * C * ((n : ℝ) / B) := by ring
      _ ≤ _ := h
  have hi := hh B hB hCB D K v hv x n hstep hballs
  constructor
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg he))
      measureReal_nonneg).trans hi.1
  · exact hi.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
      measureReal_nonneg)

end SRWTightness
