import SRWTightness.BufferedSquareGreenCenter
import SRWTightness.BufferedSquareLocalDisk
import SRWTightness.BiharmonicMixedDifference
import SRWTightness.GreenDifferenceSymmetry
import SRWTightness.LatticeNorm

namespace SRWTightness

/-- Nearby buffered targets have a quadratic Green-difference increment bound. -/
theorem buffered_square_green_near_increment (hH : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 < δ → ∀ (a b x y : Site) (N M : ℕ),
      0 < N → 0 < M → N ≤ M →
      latticeSquareInterior a N ⊆ latticeSquareInterior b M → x ≠ y →
      squareProportionalBuffer δ a N x → squareProportionalBuffer δ b M x →
      Real.sqrt (normSq (y - x)) ≤ δ * (N : ℝ) / 64 →
      let F := fun u v ↦ killedGreen (latticeSquareInterior b M) u v -
        killedGreen (latticeSquareInterior a N) u v
      |F x x + F y y - 2 * F x y| ≤ C * (2 * bufferedSquarePotentialError (δ / 2)) *
        (Real.sqrt (normSq (y - x)) / (δ * N / 8)) ^ 2 := by
  obtain ⟨C, hC, hbi⟩ := biharmonic_mixed_difference_bound hH
  refine ⟨C, hC, ?_⟩
  intro δ hδ a b x y N M hN hM hNM hED hxy hE hD hnear F
  let d := Real.sqrt (normSq (y - x))
  let B := δ * (N : ℝ) / 8
  let Ω := translateFinset x (diskFinset B)
  have hd : 1 ≤ d := Real.one_le_sqrt.mpr
    (one_le_normSq_of_ne_zero (y - x) (sub_ne_zero.mpr hxy.symm))
  have hdsq : d ^ 2 = normSq (y - x) := Real.sq_sqrt (normSq_nonneg _)
  have hlarge : 8 ≤ δ * (N : ℝ) := by dsimp [d] at hd; nlinarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hdB : 8 * d ≤ B := by dsimp [d, B]; linarith
  have hloc (z : Site) (hz : z ∈ Ω ∨ z ∈ domainExitBoundary Ω) :=
    buffered_square_local_disk δ hδ a b x N M hNM hlarge hE hD z hz
  have hxΩ : x ∈ Ω := by
    change x ∈ translateFinset x (diskFinset B)
    simp only [mem_translateFinset_iff, sub_self, mem_diskFinset, disk, Set.mem_setOf_eq]
    norm_num [normSq]
    exact sq_pos_of_pos hB
  have hyΩ : y ∈ Ω := by
    change y ∈ translateFinset x (diskFinset B)
    simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
    nlinarith
  have hysmall : y ∈ translateFinset x (diskFinset (2 * d)) := by
    simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
    nlinarith
  have hh := hbi x d B hd hdB F
    ((2 / Real.pi) * (Real.log (M : ℝ) - Real.log (N : ℝ)))
    (2 * bufferedSquarePotentialError (δ / 2))
    (by have := bufferedSquarePotentialError_pos (δ / 2); positivity)
    (fun t ht s hs ↦ green_difference_harmonic _ _ hED s t (hloc s (Or.inl hs)).1)
    (fun s hs t ht ↦ green_difference_harmonic_right _ _ hED s t (hloc t (Or.inl ht)).1)
    (fun s hs t ht ↦ buffered_square_green_difference_center (δ / 2) (by positivity)
      a b s t N M hN hM hED (hloc s hs).1 (hloc t ht).1
      (hloc t ht).2.1 (hloc t ht).2.2) hxΩ y hysmall hyΩ
  have hsym : F y x = F x y := by
    dsimp only [F]
    rw [killedGreen_symm_everywhere (latticeSquareInterior b M) y x,
      killedGreen_symm_everywhere (latticeSquareInterior a N) y x]
  have he : F y y - F x y - F y x + F x x = F x x + F y y - 2 * F x y := by
    rw [hsym]
    ring
  rw [he] at hh
  exact hh

end SRWTightness
