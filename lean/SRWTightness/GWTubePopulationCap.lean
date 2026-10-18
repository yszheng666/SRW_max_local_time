import SRWTightness.GWTubeLattice
import SRWTightness.ExternalMarkedGWTree

namespace SRWTightness

/-- The GW chronological population reads the finite tree at the complementary remaining depth. -/
theorem finite_record_gw_population {M : Type*} (n : ℕ) (r : FiniteExcursionRecord M n)
    (j : ℕ) (hj : j ≤ n) :
    geometricGWPopulation (finiteRecordPopulationList n r) j =
      finiteRecordLevelPopulation n r (n - j) := by
  unfold geometricGWPopulation finiteRecordPopulationList
  rw [List.getElem?_reverse (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn, Nat.add_sub_cancel, List.getElem?_ofFn,
    dif_pos (show n - j < n + 1 by omega), Option.getD_some]

/-- Every tube height is bounded by a common endpoint/root bound. -/
theorem gw_tube_height_cap (L : ℕ) (hL : 0 < L) (x y a b δ C Ctilde ε H : ℝ)
    (hC : 0 ≤ C) (ha : a ≤ H) (hb : b ≤ H) (hy : y + δ ≤ H)
    (r : GeometricGWRecord) (hr : r ∈ gwTubeEvent L x y a b δ C Ctilde ε)
    (hroot : geometricGWHeight r 0 ≤ H) (j : ℕ) (hj : j ≤ L) :
    geometricGWHeight r j ≤ H := by
  by_cases hj0 : j = 0
  · simpa only [hj0] using hroot
  by_cases hjL : j = L
  · simpa only [hjL] using hr.2.2.trans hy
  have hjpos : 0 < j := by omega
  have hjlt : j < L := by omega
  have hline := gw_barrier_line_mono L j hL hj a b H H ha hb
  have hcurv : 0 ≤ gwBarrierCurvature (1 / 2 - ε) j L := by
    apply Real.rpow_nonneg
    apply le_min (Nat.cast_nonneg j)
    exact sub_nonneg.mpr (by exact_mod_cast hj)
  have hh := (hr.1 j hjpos hjlt).2
  simp only [gwBarrierLine, sub_self, zero_mul, zero_div, add_zero] at hline
  dsimp only [gwBarrierLine] at hh
  nlinarith [mul_nonneg hC hcurv]

/-- A tube with heights at most 4t has every finite-tree generation at most 8t². -/
theorem finite_record_tube_population_cap {M : Type*} (n : ℕ) (hn : 0 < n)
    (t x y a b δ C Ctilde ε : ℝ) (ht : 2 ≤ t) (hC : 0 ≤ C)
    (ha : a ≤ 4 * t) (hb : b ≤ 4 * t) (hy : y + δ ≤ 4 * t)
    (r : FiniteExcursionRecord M n)
    (hr : finiteRecordPopulationList n r ∈ gwTubeEvent n x y a b δ C Ctilde ε)
    (i : ℕ) (hi : i ≤ n) :
    (finiteRecordLevelPopulation n r i : ℝ) ≤ 8 * t ^ 2 := by
  have hroot : geometricGWHeight (finiteRecordPopulationList n r) 0 ≤ 4 * t := by
    rw [geometricGWHeight, finite_record_gw_population n r 0 (Nat.zero_le _),
      Nat.sub_zero, finiteRecordLevelPopulation_root]
    have hs : Real.sqrt 2 ≤ 2 := by norm_num
    norm_num only [Nat.cast_one, mul_one]
    linarith
  have hh := gw_tube_height_cap n hn x y a b δ C Ctilde ε (4 * t) hC ha hb hy
    (finiteRecordPopulationList n r) hr hroot (n - i) (by omega)
  rw [geometricGWHeight, finite_record_gw_population n r (n - i) (by omega),
    Nat.sub_sub_self hi] at hh
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (finiteRecordLevelPopulation n r i : ℝ) by positivity)
  have hnon := Real.sqrt_nonneg (2 * (finiteRecordLevelPopulation n r i : ℝ))
  nlinarith

end SRWTightness
