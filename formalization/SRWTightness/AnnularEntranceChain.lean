import SRWTightness.PositiveEntranceChain
import SRWTightness.LatticeBallCorridor

open MeasureTheory
namespace SRWTightness

/-- Short lattice chains in a fixed annular corridor give uniform actual entrance comparisons. -/
theorem annular_entrance_chain (hinput : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m a R : ℝ), 128 ≤ m → 32 * C ≤ m →
      0 ≤ a → a ≤ m / 2 → 2 * m ≤ R →
      ∀ (b : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      ∀ (v : Site), v ∈ K → ∀ (x : ℕ → Site) (n : ℕ), (n : ℝ) ≤ (5 / 2) * m →
      (∀ i < n, normSq (x (i + 1) - x i) ≤ 1) →
      (∀ i < n, (3 * m / 4) ^ 2 ≤ normSq (x i) ∧
        normSq (x i) ≤ 2 * (5 * m / 4) ^ 2) →
      Real.exp (-(80 * C)) *
          (competingEntranceLaw (translateFinset b (diskFinset R)) K (b + x 0)).real {v} ≤
        (competingEntranceLaw (translateFinset b (diskFinset R)) K (b + x n)).real {v} ∧
      (competingEntranceLaw (translateFinset b (diskFinset R)) K (b + x n)).real {v} ≤
        Real.exp (80 * C) *
          (competingEntranceLaw (translateFinset b (diskFinset R)) K (b + x 0)).real {v} := by
  obtain ⟨C, hC, hh⟩ := positive_entrance_chain_uniform hinput
  refine ⟨C, hC, ?_⟩
  intro m a R hm hCm ha ham hmR b K hK v hv x n hn hstep hrad
  have hm0 : 0 < m := by linarith
  have he : 2 * C * (40 : ℝ) = 80 * C := by ring
  have hp := hh (m / 16) 40 (by linarith) (by linarith)
    (translateFinset b (diskFinset R)) K v hv (fun i ↦ b + x i) n
    (by linarith : (n : ℝ) ≤ 40 * (m / 16)) ?_ ?_
  · simpa only [he] using hp
  · intro i hi
    have hs := hstep i hi
    simpa only [add_sub_add_left_eq_sub] using (lt_of_le_of_lt hs (by norm_num : (1 : ℝ) < 4))
  · intro i hi
    have hrad' := hrad i hi
    have hs := Real.sq_sqrt (normSq_nonneg (x i))
    have h0 := Real.sqrt_nonneg (normSq (x i))
    have hlo : 3 * m / 4 ≤ Real.sqrt (normSq (x i)) := by nlinarith
    have hhi : Real.sqrt (normSq (x i)) ≤ 15 * m / 8 := by nlinarith
    have hb := lattice_ball_inside_annulus b (b + x i) a (m / 16) R ha
      (by positivity) (by simpa only [add_sub_cancel_left] using
        (show a + m / 16 ≤ Real.sqrt (normSq (x i)) by linarith))
      (by simpa only [add_sub_cancel_left] using
        (show Real.sqrt (normSq (x i)) + m / 16 ≤ R by linarith))
    intro y hy
    have hy' := Finset.mem_sdiff.mp (hb hy)
    exact Finset.mem_sdiff.mpr ⟨hy'.1, fun hyK ↦ hy'.2 (hK hyK)⟩

end SRWTightness
