import SRWTightness.SourceEarlyPairNumericDecay
import SRWTightness.SourceDistancePairCount
import SRWTightness.SourceCenteredSuccessEvent

open MeasureTheory Filter
namespace SRWTightness

/-- The sum of actual centered pair-success probabilities at one distance index. -/
noncomputable def sourcePairShellMass (t A γ : ℝ) (I a : ℕ) : ℝ :=
  ∑ p ∈ sourceDistancePairs (sourceCandidateAnnulus (Real.exp t)) t a,
    sourceEnlargedLaw.real
      (sourceCenteredSuccessEvent t A γ p.1 I ∩ sourceCenteredSuccessEvent t A γ p.2 I)

/-- The actual shell sum inherits stretched decay from its uniform early endpoint bound. -/
theorem source_early_pair_shell_of_endpoint (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) (C : ℝ) (hC : 0 < C) (J₀ : ℕ) :
    ∃ a₀ : ℕ, 2 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (I a : ℕ), a₀ ≤ a →
      a < sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
      (∀ p ∈ sourceDistancePairs (sourceCandidateAnnulus (Real.exp t)) t a,
        sourceEnlargedLaw.real
          (sourceCenteredSuccessEvent t A (2 / 5) p.1 I ∩
            sourceCenteredSuccessEvent t A (2 / 5) p.2 I) ≤
        C * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 / (Real.exp t) ^ 4 *
          Real.exp (-4 * (ν : ℝ) - b ^ 2 / (2 * ((j : ℝ) + 1)) +
            4 * b + C * ((J : ℝ) + 1))) →
      sourcePairShellMass t A (2 / 5) I a ≤ Real.exp (-(a : ℝ) ^ (2 / 5 : ℝ) / 2) := by
  obtain ⟨B, hB, hc⟩ := source_distance_pairs_annulus_card hDisk hAnnulus
  obtain ⟨a₀, ha₀, hd⟩ := source_early_pair_numeric_decay (B * C) C (mul_pos hB hC) hC.le J₀
  refine ⟨a₀, ha₀, ?_⟩
  filter_upwards [hc, hd] with t hc hd
  intro A I a ha hrange
  dsimp only
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
  let e := -4 * (ν : ℝ) - b ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * b + C * ((J : ℝ) + 1)
  let v := C * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 / (Real.exp t) ^ 4 * Real.exp e
  intro hp
  have hs : sourcePairShellMass t A (2 / 5) I a ≤
      ((sourceDistancePairs (sourceCandidateAnnulus (Real.exp t)) t a).card : ℝ) * v := by
    unfold sourcePairShellMass
    calc
      _ ≤ ∑ _p ∈ sourceDistancePairs (sourceCandidateAnnulus (Real.exp t)) t a, v :=
        Finset.sum_le_sum hp
      _ = _ := by simp
  have hh := hs.trans (mul_le_mul_of_nonneg_right (hc a (by omega))
    (show 0 ≤ v by dsimp only [v]; positivity))
  have he : Real.exp (4 * t - 2 * (a : ℝ)) / (Real.exp t) ^ 4 =
      Real.exp (-2 * (a : ℝ)) := by
    rw [Real.exp_sub, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul,
      neg_mul, Real.exp_neg]
    field_simp
  have heq : B * Real.exp (4 * t - 2 * (a : ℝ)) * v =
      (B * C) * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 * Real.exp
        (-2 * (a : ℝ) - 4 * (ν : ℝ) - b ^ 2 / (2 * ((j : ℝ) + 1)) +
          4 * b + C * ((J : ℝ) + 1)) := by
    calc
      _ = (B * C) * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 *
          (Real.exp (4 * t - 2 * (a : ℝ)) / (Real.exp t) ^ 4) * Real.exp e := by
        dsimp only [v]
        ring
      _ = _ := by
        rw [he, mul_assoc, ← Real.exp_add]
        congr 2
        dsimp only [e]
        ring
  exact (hh.trans_eq heq).trans (hd a ha hrange)

end SRWTightness
