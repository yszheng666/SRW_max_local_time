import SRWTightness.CenteredBlockNeighbor
import SRWTightness.SourceUpperBlockCover

open Filter

namespace SRWTightness

/-- The source blocks eventually have at least four lattice sites on each side. -/
theorem source_upper_block_side_ge_four :
    ∀ᶠ t : ℝ in atTop, 4 ≤ sourceUpperBlockSide t := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with t ht
  have hlog : 1 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 1) ht
    rwa [Real.log_exp] at h
  have hpow : (8 : ℝ) ^ 4 ≤ (8 * Real.log t) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hu : 16 ≤ sourceUpperLogRadius t := by
    unfold sourceUpperLogRadius
    nlinarith [hpow]
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have he := Real.add_one_le_exp (sourceUpperLogRadius t / 4)
  linarith

/-- A closed half-disk block has a nearby open half-disk point controlling its traversals. -/
theorem source_upper_block_interior_witness (t : ℝ) (b x : Site)
    (ha : 4 ≤ sourceUpperBlockSide t) (hx : x ∈ sourceUpperBlock t b)
    (hclosed : Real.sqrt (normSq x) ≤ Real.exp t / 2) :
    ∃ y ∈ diskFinset (Real.exp t / 2),
      normSq (y - b) ≤ (sourceUpperBlockSide t : ℝ) ^ 2 := by
  by_cases hopen : x ∈ diskFinset (Real.exp t / 2)
  · exact ⟨x, hopen, centeredLatticeBlock_near _ _ _ hx⟩
  · have hx0 : x ≠ 0 := by
      intro he
      apply hopen
      rw [he, mem_diskFinset]
      simpa [disk, normSq] using
        (sq_pos_of_pos (show 0 < Real.exp t / 2 by positivity))
    obtain ⟨d, hd⟩ := exists_step_normSq_lt x hx0
    refine ⟨x + step d, ?_, centeredLatticeBlock_neighbor_near _ ha b x hx d⟩
    apply (mem_diskFinset _ _).mpr
    have hsq : normSq x ≤ (Real.exp t / 2) ^ 2 := by
      calc
        _ = Real.sqrt (normSq x) ^ 2 := (Real.sq_sqrt (normSq_nonneg x)).symm
        _ ≤ _ := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hclosed
    exact hd.trans_le hsq

end SRWTightness
