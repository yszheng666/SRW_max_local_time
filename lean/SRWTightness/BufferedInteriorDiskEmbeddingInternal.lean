import SRWTightness.CenteredBufferedSquare
import SRWTightness.BufferedDyadicScale

namespace SRWTightness

/-- The original buffered dyadic enclosure input follows from explicit centered lattice squares. -/
theorem buffered_dyadic_interior_disk_embedding_input_internal :
    BufferedDyadicInteriorDiskEmbeddingInput := by
  intro δ R r A hδ hδ1 hr hscale hA hinside hdiam
  have hR : 0 < R := by
    by_contra h
    have hh := mul_nonpos_of_nonneg_of_nonpos hδ.le (le_of_not_gt h)
    linarith
  have hδR : δ * R < R := by nlinarith [mul_pos (sub_pos.mpr hδ1) hR]
  have hR1 : 1 ≤ R := by linarith
  have hrad : 0 ≤ (1 - δ) * R := mul_nonneg (sub_nonneg.mpr hδ1.le) hR.le
  obtain ⟨z, hz⟩ := hA
  obtain ⟨k, hk, hk'⟩ := exists_buffered_dyadic_half_side r hr
  obtain ⟨l, hl, hl'⟩ := exists_buffered_dyadic_half_side R hR1
  let a := centeredSquareCorner z (2 ^ (k + 1))
  let b := centeredSquareCorner 0 (2 ^ (l + 1))
  have hNk : (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by
    rw [show k + 2 = k + 1 + 1 by omega, pow_succ]
    omega
  have hNl : (2 : ℕ) ^ (l + 2) = 2 * 2 ^ (l + 1) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
    omega
  have hkr : (2 : ℝ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by
    rw [show k + 2 = k + 1 + 1 by omega, pow_succ]
    ring
  have hlr : (2 : ℝ) ^ (l + 2) = 2 * 2 ^ (l + 1) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
    ring
  have hAB (x : Site) (hx : x ∈ A) :
      x ∈ latticeSquareInterior a (2 ^ (k + 2)) ∧
        squareProportionalBuffer (1 / 16) a (2 ^ (k + 2)) x := by
    rw [hNk]
    apply centered_square_ball_buffer z x (2 ^ (k + 1)) r hr
    · exact_mod_cast hk
    · exact hdiam x hx z hz
  have houter (x : Site) (hx : normSq x ≤ R ^ 2) :
      x ∈ latticeSquareInterior b (2 ^ (l + 2)) ∧
        squareProportionalBuffer (1 / 16) b (2 ^ (l + 2)) x := by
    rw [hNl]
    apply centered_square_ball_buffer 0 x (2 ^ (l + 1)) R hR1
    · exact_mod_cast hl
    · simpa only [sub_zero] using hx
  refine ⟨a, b, l + 2, k + 2, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
    rw [hkr, hlr]
    linarith
  · intro x hx
    exact (hAB x hx).1
  · intro x hx
    have hxz := centered_square_radius_bound z x (2 ^ (k + 1)) (by rwa [hNk] at hx)
    have hadd := normSq_add_bound z (x - z) hrad
      (show 0 ≤ 2 * ((2 ^ (k + 1) : ℕ) : ℝ) by positivity) (hinside z hz) hxz
    have he : z + (x - z) = x := by abel
    rw [he] at hadd
    have hs : 0 ≤ (1 - δ) * R + 2 * (2 : ℝ) ^ (k + 1) := by positivity
    have hlt : (1 - δ) * R + 2 * (2 : ℝ) ^ (k + 1) < R := by nlinarith
    have hsq := sq_lt_sq₀ hs hR.le |>.mpr hlt
    rw [mem_diskFinset]
    change normSq x < R ^ 2
    have hadd' : normSq x ≤ ((1 - δ) * R + 2 * (2 : ℝ) ^ (k + 1)) ^ 2 := by
      exact_mod_cast hadd
    exact hadd'.trans_lt hsq
  · intro x hx
    exact (houter x (show normSq x ≤ R ^ 2 from (mem_diskFinset R x |>.mp hx).le)).1
  · rw [hkr]; linarith
  · rw [hkr]; linarith
  · rw [hlr]; linarith
  · rw [hlr]; linarith
  · intro x hx
    exact (hAB x hx).2
  · intro x hx
    apply (houter x ?_).2
    have hh := hinside x hx
    have hle : (1 - δ) * R ≤ R := by nlinarith [mul_nonneg hδ.le hR.le]
    exact hh.trans ((sq_le_sq₀ hrad hR.le).mpr hle)

end SRWTightness
