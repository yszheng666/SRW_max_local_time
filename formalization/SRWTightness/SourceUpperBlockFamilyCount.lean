import SRWTightness.SourceUpperBlockRootGeometry
import SRWTightness.LatticeMeshCardinality

open Filter

namespace SRWTightness

/-- The actual upper blocks classified by their least admissible root level. -/
noncomputable def sourceUpperBlockRootFamily (t : ℝ) (k : ℕ) : Finset Site := by
  classical
  exact (sourceUpperBlockCenters t).filter (fun b ↦ sourceUpperBlockRoot t b = k)

/-- Equation (4.20): the actual root-level block family has the required spatial decay. -/
theorem source_upper_block_family_count :
    ∀ᶠ t : ℝ in atTop, ∀ k : ℕ,
      ((sourceUpperBlockRootFamily t k).card : ℝ) ≤
        25 * (Real.exp t) ^ 2 * Real.exp (-2 * (k : ℝ)) /
          (upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2 := by
  filter_upwards [source_upper_root_center_localization, source_upper_block_center_distance,
    source_upper_block_scale_conditions] with t hloc hdist ht
  intro k
  have ht0 : 0 < t := by linarith [ht.1]
  have hz : (0 : Site) ∉ sourceUpperBlockRootFamily t k := by
    intro hz
    have h := (hdist 0 (Finset.mem_filter.mp hz).1).1
    have hp : 0 < Real.exp t / (2 * t) := by positivity
    norm_num [normSq] at h
    linarith
  have hZ : ∀ b ∈ sourceUpperBlockRootFamily t k,
      b ∈ diskFinset (Real.exp t * Real.exp (-(k : ℝ))) ∧
        (sourceUpperBlockSide t : ℤ) ∣ b.1 ∧ (sourceUpperBlockSide t : ℤ) ∣ b.2 := by
    intro b hb
    obtain ⟨hb, hk⟩ := Finset.mem_filter.mp hb
    have h := hloc b hb
    rw [hk] at h
    have hm := (Finset.mem_filter.mp hb).2
    exact ⟨h, hm.1, hm.2.1⟩
  have h := lattice_mesh_cardinality (Real.exp t * Real.exp (-(k : ℝ))) (by positivity)
    (sourceUpperBlockSide t) (sourceUpperBlockSide_pos t) (sourceUpperBlockRootFamily t k)
    hz hZ
  calc
    _ ≤ 25 * ((Real.exp t * Real.exp (-(k : ℝ))) / (sourceUpperBlockSide t : ℝ)) ^ 2 := h
    _ = _ := by
      rw [sourceUpperBlockSide_cast, div_pow, mul_pow,
        show -2 * (k : ℝ) = -(k : ℝ) + -(k : ℝ) by ring, Real.exp_add]
      ring

end SRWTightness
