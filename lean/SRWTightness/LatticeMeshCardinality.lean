import SRWTightness.LatticeMeshSquareCover

namespace SRWTightness

/-- A disk mesh excluding the origin has a quadratic count even below one mesh spacing. -/
theorem lattice_mesh_cardinality (R : ℝ) (hR : 0 < R) (a : ℕ) (ha : 0 < a)
    (Z : Finset Site) (hzero : (0 : Site) ∉ Z)
    (hZ : ∀ z ∈ Z, z ∈ diskFinset R ∧ (a : ℤ) ∣ z.1 ∧ (a : ℤ) ∣ z.2) :
    (Z.card : ℝ) ≤ 25 * (R / (a : ℝ)) ^ 2 := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  by_cases hscale : (a : ℝ) ≤ R
  · have hcover := lattice_mesh_square_cover R hR a ha Z hZ
    have hc := (Finset.card_le_card hcover).trans (Finset.card_image_le)
    have hc' : (Z.card : ℝ) ≤ (2 * (⌈R / (a : ℝ)⌉₊ : ℝ) + 1) ^ 2 := by
      have hh : (Z.card : ℝ) ≤ ((centeredLatticeSquare ⌈R / (a : ℝ)⌉₊).card : ℝ) := by
        exact_mod_cast hc
      simpa only [centeredLatticeSquare_card] using hh
    have hX : 1 ≤ R / (a : ℝ) := (one_le_div ha').mpr hscale
    have hceil : (⌈R / (a : ℝ)⌉₊ : ℝ) ≤ R / (a : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hs : 2 * (⌈R / (a : ℝ)⌉₊ : ℝ) + 1 ≤ 5 * (R / (a : ℝ)) := by linarith
    have hp := pow_le_pow_left₀ (by positivity) hs 2
    nlinarith
  · have hRa : R < (a : ℝ) := lt_of_not_ge hscale
    have hempty : Z = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzR, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hZ z hz
      let w : Site := (u, v)
      have he : latticeScale a w = z := Prod.ext hu.symm hv.symm
      have hw : w ≠ 0 := by
        intro hw0
        have hz0 : z = 0 := by
          change z = (0, 0)
          simpa [hw0, latticeScale] using he.symm
        exact hzero (hz0 ▸ hz)
      have hn := mul_le_mul_of_nonneg_left (one_le_normSq_of_ne_zero w hw)
        (sq_nonneg (a : ℝ))
      rw [← normSq_latticeScale, he] at hn
      have hr := (mem_diskFinset R z).mp hzR
      change normSq z < R ^ 2 at hr
      nlinarith
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

end SRWTightness
