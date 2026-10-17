import SRWTightness.LatticeMeshSquareCover
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SRWTightness

/-- The logarithmic mesh weight sums quadratically, using exact square-shell counting. -/
theorem lattice_mesh_log_weight_sum (R b : ℝ) (hR : 0 < R) (a : ℕ) (ha : 0 < a)
    (hab : (a : ℝ) ≤ b) (haR : (a : ℝ) ≤ R) (Z : Finset Site)
    (hZ : ∀ z ∈ Z, z ∈ diskFinset R ∧ (a : ℤ) ∣ z.1 ∧ (a : ℤ) ∣ z.2) :
    (∑ z ∈ Z, (1 + Real.log (2 * R / max (Real.sqrt (normSq z)) b))) ≤
      34 * (R / (a : ℝ)) ^ 2 := by
  classical
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb : 0 < b := ha'.trans_le hab
  let g : Site → ℝ := fun z ↦ 2 * R / max (Real.sqrt (normSq z)) b
  let N := ⌈R / (a : ℝ)⌉₊
  have hg0 : ∀ z, 0 ≤ g z := by
    intro z
    exact div_nonneg (by positivity) (hb.le.trans (le_max_right _ _))
  have hlog : ∀ z, 1 + Real.log (2 * R / max (Real.sqrt (normSq z)) b) ≤ g z := by
    intro z
    have h := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : 0 < 2 * R) (hb.trans_le (le_max_right (Real.sqrt (normSq z)) b)))
    dsimp [g]
    linarith
  have hsum : (∑ z ∈ Z, (1 + Real.log (2 * R / max (Real.sqrt (normSq z)) b))) ≤
      ∑ z ∈ centeredLatticeSquare N, g (latticeScale a z) := by
    calc
      _ ≤ ∑ z ∈ Z, g z := Finset.sum_le_sum (fun z _ ↦ hlog z)
      _ ≤ ∑ z ∈ (centeredLatticeSquare N).image (latticeScale a), g z :=
        Finset.sum_le_sum_of_subset_of_nonneg (lattice_mesh_square_cover R hR a ha Z hZ)
          (fun z _ _ ↦ hg0 z)
      _ = _ := Finset.sum_image (fun x _ y _ he ↦ latticeScale_injective a ha he)
  have hzero : g (latticeScale a 0) ≤ 2 * R / (a : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * R) ha' hab
    simpa only [g, latticeScale, Prod.fst_zero, Prod.snd_zero, mul_zero, normSq,
      Int.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Real.sqrt_zero,
      max_eq_right hb.le] using hh
  have hshell : ∀ n : ℕ, ∀ z ∈ centeredLatticeSquare (n + 1) \ centeredLatticeSquare n,
      g (latticeScale a z) ≤ (2 * R / (a : ℝ)) / ((n : ℝ) + 1) := by
    intro n z hz
    have hs := normSq_lower_outside_centeredLatticeSquare n z (Finset.mem_sdiff.mp hz).2
    have hrad : (a : ℝ) * ((n : ℝ) + 1) ≤ Real.sqrt (normSq (latticeScale a z)) := by
      apply (Real.le_sqrt (by positivity) (normSq_nonneg _)).mpr
      rw [normSq_latticeScale]
      nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (a : ℝ))]
    have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * R)
      (show 0 < (a : ℝ) * ((n : ℝ) + 1) by positivity)
      (hrad.trans (le_max_left _ b))
    simpa only [g, div_div] using hh
  have hbox := centeredLatticeSquare_sum_bound (fun z ↦ g (latticeScale a z)) _ hzero hshell N
  have hX : 1 ≤ R / (a : ℝ) := (one_le_div ha').mpr haR
  have hceil : (N : ℝ) ≤ R / (a : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hmul := mul_le_mul_of_nonneg_left hceil
    (show 0 ≤ 16 * (R / (a : ℝ)) by positivity)
  have hquad := mul_nonneg (sub_nonneg.mpr hX) (show 0 ≤ R / (a : ℝ) by positivity)
  have hbase := hsum.trans hbox
  simp only [mul_div_assoc] at hbase ⊢
  nlinarith

end SRWTightness
