import SRWTightness.BufferedSquareGreenIncrement
import SRWTightness.HarmonicCovarianceNormalization

namespace SRWTightness

/-- The complete buffered-square Green input follows from the existing positive Harnack input. -/
theorem bufferedSquareGreenInput_of_positiveHarmonic
    (hH : PositiveHarmonicRelativeInput) : BufferedSquareGreenInput := by
  intro δ hδ hδhalf
  obtain ⟨L, hL, hinc⟩ := buffered_square_green_increment_bound hH δ hδ
  let q := Real.pi / 2
  let B := q * (2 * bufferedSquarePotentialError δ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hB : 0 ≤ B := by
    have := bufferedSquarePotentialError_pos δ
    dsimp [B]
    positivity
  refine ⟨2 * B, q * L, B, by positivity, mul_pos hq hL, hB, ?_⟩
  intro D E a b m n hD hE hn hnm hED x y hxE hyE hxD hyD
  subst D
  subst E
  have hN : 0 < (2 : ℕ) ^ n := by positivity
  have hM : 0 < (2 : ℕ) ^ m := by positivity
  have hNM : (2 : ℕ) ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hnm
  let c := Real.log ((2 : ℝ) ^ m) - Real.log ((2 : ℝ) ^ n)
  let F := fun u v ↦ killedGreen (latticeSquareInterior b (2 ^ m)) u v -
    killedGreen (latticeSquareInterior a (2 ^ n)) u v
  have hcenter (z : latticeSquareInterior a (2 ^ n))
      (hzE : squareProportionalBuffer δ a (2 ^ n) z)
      (hzD : squareProportionalBuffer δ b (2 ^ m) z) : |q * F z z - c| ≤ B := by
    have hh := buffered_square_green_difference_center δ hδ a b z z
      (2 ^ n) (2 ^ m) hN hM hED z.property z.property hzE hzD
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hh
    have he : q * (F z z - (2 / Real.pi) * c) = q * F z z - c := by
      dsimp [q]
      field_simp
      <;> ring
    have ht := mul_le_mul_of_nonneg_left hh hq.le
    change q * |F z z - (2 / Real.pi) * c| ≤ B at ht
    rw [← abs_of_pos hq, ← abs_mul, he] at ht
    exact ht
  have hcx := hcenter x hxE hxD
  have hcy := hcenter y hyE hyD
  dsimp only
  simp only [normalizedHarmonicCov_source_apply]
  change |q * F x x - q * F y y| ≤ 2 * B ∧
    q * F x x + q * F y y - 2 * (q * F x y) ≤
      q * L * normSq ((x : Site) - (y : Site)) / ((2 : ℝ) ^ n) ^ 2 ∧
    |q * F x x - c| ≤ B
  refine ⟨?_, ?_, hcx⟩
  · have hh := abs_sub_le (q * F x x) c (q * F y y)
    rw [abs_sub_comm c (q * F y y)] at hh
    linarith
  · have hh := hinc a b x y (2 ^ n) (2 ^ m) hN hM hNM hED x.property y.property
      hxE hxD hyE hyD
    have ht := mul_le_mul_of_nonneg_left hh hq.le
    simp only [Nat.cast_pow, Nat.cast_ofNat] at ht
    change q * (F x x + F y y - 2 * F x y) ≤
      q * (L * normSq ((x : Site) - (y : Site)) / ((2 : ℝ) ^ n) ^ 2) at ht
    convert ht using 1 <;> ring

end SRWTightness
