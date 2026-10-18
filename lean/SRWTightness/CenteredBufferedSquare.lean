import SRWTightness.ExternalBufferedInteriorDiskEmbedding
import SRWTightness.GeometryTriangle

namespace SRWTightness

/-- Lower corner of an even square centered at a lattice point. -/
def centeredSquareCorner (z : Site) (h : ℕ) : Site :=
  (z.1 - (h : ℤ), z.2 - (h : ℤ))

/-- A radius-r ball lies in the buffered interior of a centered square of half-side at least 4r. -/
theorem centered_square_ball_buffer (z x : Site) (h : ℕ) (r : ℝ)
    (hr : 1 ≤ r) (hh : 4 * r ≤ (h : ℝ)) (hx : normSq (x - z) ≤ r ^ 2) :
    x ∈ latticeSquareInterior (centeredSquareCorner z h) (2 * h) ∧
      squareProportionalBuffer (1 / 16) (centeredSquareCorner z h) (2 * h) x := by
  have hf := abs_le.mp (abs_fst_le_normSq_bound (x - z) (by linarith) hx)
  have hs := abs_le.mp (abs_snd_le_normSq_bound (x - z) (by linarith) hx)
  simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub] at hf hs
  constructor
  · rw [mem_latticeSquareInterior]
    simp only [centeredSquareCorner, Nat.cast_mul, Nat.cast_ofNat, Prod.fst, Prod.snd]
    constructor
    · constructor
      · exact_mod_cast (show (z.1 : ℝ) - h + 1 ≤ x.1 by linarith [hf.1])
      · exact_mod_cast (show (x.1 : ℝ) ≤ z.1 - h + 2 * h - 2 by linarith [hf.2])
    · constructor
      · exact_mod_cast (show (z.2 : ℝ) - h + 1 ≤ x.2 by linarith [hs.1])
      · exact_mod_cast (show (x.2 : ℝ) ≤ z.2 - h + 2 * h - 2 by linarith [hs.2])
  · unfold squareProportionalBuffer centeredSquareCorner
    simp only [Prod.fst, Prod.snd, Nat.cast_mul, Nat.cast_ofNat, Int.cast_sub, Int.cast_natCast]
    constructor
    · linarith [hf.1]
    constructor
    · linarith [hf.2]
    constructor
    · linarith [hs.1]
    · linarith [hs.2]

/-- Every interior point is within the full side length of the center in squared distance. -/
theorem centered_square_radius_bound (z x : Site) (h : ℕ)
    (hx : x ∈ latticeSquareInterior (centeredSquareCorner z h) (2 * h)) :
    normSq (x - z) ≤ (2 * (h : ℝ)) ^ 2 := by
  rw [mem_latticeSquareInterior] at hx
  simp only [centeredSquareCorner, Prod.fst, Prod.snd, Nat.cast_mul, Nat.cast_ofNat] at hx
  have hf : -(h : ℝ) ≤ (x.1 : ℝ) - z.1 ∧ (x.1 : ℝ) - z.1 ≤ h := by
    constructor
    · exact_mod_cast (show -(h : ℤ) ≤ x.1 - z.1 by omega)
    · exact_mod_cast (show x.1 - z.1 ≤ (h : ℤ) by omega)
  have hs : -(h : ℝ) ≤ (x.2 : ℝ) - z.2 ∧ (x.2 : ℝ) - z.2 ≤ h := by
    constructor
    · exact_mod_cast (show -(h : ℤ) ≤ x.2 - z.2 by omega)
    · exact_mod_cast (show x.2 - z.2 ≤ (h : ℤ) by omega)
  have hfs := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg h)).mpr (abs_le.mpr hf)
  have hss := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg h)).mpr (abs_le.mpr hs)
  simp only [sq_abs] at hfs hss
  simp only [normSq, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  nlinarith [sq_nonneg (h : ℝ)]

end SRWTightness
