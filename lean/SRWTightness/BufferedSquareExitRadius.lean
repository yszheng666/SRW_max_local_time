import SRWTightness.LatticeSquareExitGeometry
import SRWTightness.ExternalBufferedSquareGreen
import SRWTightness.CoordinateBounds

namespace SRWTightness

/-- A buffered observation has distance at least its buffer from every square exit. -/
theorem buffered_square_exit_radius_lower (δ : ℝ) (a x z : Site) (N : ℕ)
    (hb : squareProportionalBuffer δ a N x)
    (hz : z ∈ domainExitBoundary (latticeSquareInterior a N)) :
    δ * (N : ℝ) ≤ Real.sqrt (normSq (z - x)) := by
  have hf := abs_le.mp (abs_fst_le_normSq_bound (z - x) (Real.sqrt_nonneg _)
    (Real.sq_sqrt (normSq_nonneg _)).ge)
  have hs := abs_le.mp (abs_snd_le_normSq_bound (z - x) (Real.sqrt_nonneg _)
    (Real.sq_sqrt (normSq_nonneg _)).ge)
  simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub] at hf hs
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  rcases latticeSquareInterior_exit_side a z N hz with h | h | h | h
  all_goals
    have he := congrArg (fun t : ℤ ↦ (t : ℝ)) h
    try simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one] at he
    linarith [hf.1, hf.2, hs.1, hs.2]

/-- Square exits and interior points are at distance at most twice the side length. -/
theorem square_exit_radius_upper (a x z : Site) (N : ℕ)
    (hx : x ∈ latticeSquareInterior a N)
    (hz : z ∈ domainExitBoundary (latticeSquareInterior a N)) :
    Real.sqrt (normSq (z - x)) ≤ 2 * (N : ℝ) := by
  have hxb := latticeSquareInterior_subset a N hx
  have hzb := latticeSquareInterior_exit_mem_square a z N hz
  simp only [latticeSquare, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hxb hzb
  have hf : |(z.1 : ℝ) - x.1| ≤ (N : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast (show -(N : ℤ) ≤ z.1 - x.1 by omega)
    · exact_mod_cast (show z.1 - x.1 ≤ (N : ℤ) by omega)
  have hs : |(z.2 : ℝ) - x.2| ≤ (N : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast (show -(N : ℤ) ≤ z.2 - x.2 by omega)
    · exact_mod_cast (show z.2 - x.2 ≤ (N : ℤ) by omega)
  have hfs := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg N)).mpr hf
  have hss := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg N)).mpr hs
  simp only [sq_abs] at hfs hss
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  simp only [normSq, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  nlinarith [sq_nonneg (N : ℝ)]

end SRWTightness
