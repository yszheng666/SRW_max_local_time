import SRWTightness.BufferedSquareExitRadius
import SRWTightness.PotentialKernelComparableRadius
import SRWTightness.GreenPotentialFlatness

namespace SRWTightness

/-- A scale-independent potential error for a proportionally buffered square target. -/
noncomputable def bufferedSquarePotentialError (δ : ℝ) : ℝ :=
  potentialUpperConstant + potentialLowerConstant +
    (2 / Real.pi) * (|Real.log δ| + |Real.log 2|)

/-- This error constant is positive at every buffer value. -/
theorem bufferedSquarePotentialError_pos (δ : ℝ) : 0 < bufferedSquarePotentialError δ := by
  unfold bufferedSquarePotentialError
  have hU := potentialUpperConstant_pos
  have hL := potentialLowerConstant_pos
  positivity

/-- Square Green values plus the singular potential are uniformly centered at the side logarithm. -/
theorem buffered_square_green_potential_center (δ : ℝ) (hδ : 0 < δ)
    (a x y : Site) (N : ℕ) (hN : 0 < N)
    (hx : x ∈ latticeSquareInterior a N) (hy : y ∈ latticeSquareInterior a N)
    (hb : squareProportionalBuffer δ a N y) :
    |killedGreen (latticeSquareInterior a N) x y + potentialKernel (x - y) -
      (2 / Real.pi) * Real.log (N : ℝ)| ≤ bufferedSquarePotentialError δ := by
  have hh := green_flatness_from_potential_bounds (latticeSquareInterior a N) x y hx
    ((2 / Real.pi) * Real.log (N : ℝ)) (potentialKernel (x - y))
    (bufferedSquarePotentialError δ) 0
    (fun z hz ↦ potentialKernel_comparable_radius δ 2 N hδ (by norm_num)
      (by exact_mod_cast hN) (z - y)
      (buffered_square_exit_radius_lower δ a y z N hb hz)
      (square_exit_radius_upper a y z N hy hz)) (by simp)
  rw [add_zero] at hh
  convert hh using 1 <;> congr 1 <;> ring

/-- The logarithmic center of a nested-square Green difference has uniformly bounded error. -/
theorem buffered_square_green_difference_center (δ : ℝ) (hδ : 0 < δ)
    (a b x y : Site) (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hED : latticeSquareInterior a N ⊆ latticeSquareInterior b M)
    (hx : x ∈ latticeSquareInterior a N) (hy : y ∈ latticeSquareInterior a N)
    (hbE : squareProportionalBuffer δ a N y) (hbD : squareProportionalBuffer δ b M y) :
    |(killedGreen (latticeSquareInterior b M) x y -
        killedGreen (latticeSquareInterior a N) x y) -
      (2 / Real.pi) * (Real.log (M : ℝ) - Real.log (N : ℝ))| ≤
        2 * bufferedSquarePotentialError δ := by
  have hD := buffered_square_green_potential_center δ hδ b x y M hM (hED hx) (hED hy) hbD
  have hE := buffered_square_green_potential_center δ hδ a x y N hN hx hy hbE
  obtain ⟨hD1, hD2⟩ := abs_le.mp hD
  obtain ⟨hE1, hE2⟩ := abs_le.mp hE
  apply abs_le.mpr
  constructor <;> nlinarith

end SRWTightness
