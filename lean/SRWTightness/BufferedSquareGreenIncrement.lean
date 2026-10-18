import SRWTightness.BufferedSquareGreenNearIncrement
import SRWTightness.TwoScaleQuadraticBound

namespace SRWTightness

/-- Buffered nested-square Green increments satisfy the full uniform quadratic estimate. -/
theorem buffered_square_green_increment_bound (hH : PositiveHarmonicRelativeInput)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (a b x y : Site) (N M : ℕ),
      0 < N → 0 < M → N ≤ M →
      latticeSquareInterior a N ⊆ latticeSquareInterior b M →
      x ∈ latticeSquareInterior a N → y ∈ latticeSquareInterior a N →
      squareProportionalBuffer δ a N x → squareProportionalBuffer δ b M x →
      squareProportionalBuffer δ a N y → squareProportionalBuffer δ b M y →
      let F := fun u v ↦ killedGreen (latticeSquareInterior b M) u v -
        killedGreen (latticeSquareInterior a N) u v
      F x x + F y y - 2 * F x y ≤ L * normSq (x - y) / (N : ℝ) ^ 2 := by
  obtain ⟨C, hC, hnear⟩ := buffered_square_green_near_increment hH
  have hE := bufferedSquarePotentialError_pos δ
  have hEhalf := bufferedSquarePotentialError_pos (δ / 2)
  obtain ⟨L, hL, hcombine⟩ := exists_two_scale_quadratic_constant δ
    (C * (2 * bufferedSquarePotentialError (δ / 2)))
    (8 * bufferedSquarePotentialError δ) hδ (by positivity) (by positivity)
  refine ⟨L, hL, ?_⟩
  intro a b x y N M hN hM hNM hED hx hy hxE hxD hyE hyD F
  have hxx := buffered_square_green_difference_center δ hδ a b x x N M hN hM hED
    hx hx hxE hxD
  have hyy := buffered_square_green_difference_center δ hδ a b y y N M hN hM hED
    hy hy hyE hyD
  have hxy := buffered_square_green_difference_center δ hδ a b x y N M hN hM hED
    hx hy hyE hyD
  have hfar : F x x + F y y - 2 * F x y ≤ 8 * bufferedSquarePotentialError δ := by
    obtain ⟨hxx1, hxx2⟩ := abs_le.mp hxx
    obtain ⟨hyy1, hyy2⟩ := abs_le.mp hyy
    obtain ⟨hxy1, hxy2⟩ := abs_le.mp hxy
    dsimp only [F]
    nlinarith
  by_cases heq : x = y
  · subst y
    have h0 : F x x + F x x - 2 * F x x = 0 := by ring
    rw [h0]
    exact div_nonneg (mul_nonneg hL.le (normSq_nonneg _)) (sq_nonneg _)
  have hh := hcombine (N : ℝ) (Real.sqrt (normSq (y - x))) (F x x + F y y - 2 * F x y)
    (by exact_mod_cast hN) (Real.sqrt_nonneg _) hfar (fun hs ↦
      (le_abs_self _).trans (hnear δ hδ a b x y N M hN hM hNM hED heq hxE hxD hs))
  have hsym : normSq (y - x) = normSq (x - y) := by
    simp only [normSq, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    ring
  rwa [Real.sq_sqrt (normSq_nonneg _), hsym] at hh

end SRWTightness
