import SRWTightness.SourceUpperBlockFamilyCount

open Filter

namespace SRWTightness

/-- The total actual block family has at most a constant times the ambient disk area. -/
theorem source_upper_block_total_count :
    ∀ᶠ t : ℝ in atTop, ((sourceUpperBlockCenters t).card : ℝ) ≤
      25 * (Real.exp t) ^ 2 := by
  filter_upwards [source_upper_block_center_distance, source_upper_block_scale_conditions]
    with t hdist ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hz : (0 : Site) ∉ sourceUpperBlockCenters t := by
    intro hz
    have h := (hdist 0 hz).1
    have hp : 0 < Real.exp t / (2 * t) := by positivity
    norm_num [normSq] at h
    linarith
  have hZ : ∀ b ∈ sourceUpperBlockCenters t,
      b ∈ diskFinset (Real.exp t) ∧
        (sourceUpperBlockSide t : ℤ) ∣ b.1 ∧ (sourceUpperBlockSide t : ℤ) ∣ b.2 := by
    intro b hb
    obtain ⟨hb, hm⟩ := Finset.mem_filter.mp hb
    exact ⟨hb, hm.1, hm.2.1⟩
  have h := lattice_mesh_cardinality (Real.exp t) (by positivity)
    (sourceUpperBlockSide t) (sourceUpperBlockSide_pos t) (sourceUpperBlockCenters t) hz hZ
  have ha : (1 : ℝ) ≤ sourceUpperBlockSide t := by
    exact_mod_cast sourceUpperBlockSide_pos t
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity)
      (div_le_self (Real.exp_nonneg t) ha) 2) (by norm_num))

end SRWTightness
