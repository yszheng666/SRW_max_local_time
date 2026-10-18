import SRWTightness.UpperGeometricRootSum

namespace SRWTightness

/-- Any finite collection of positive roots has geometric mass at most the return scale. -/
theorem upper_positive_root_geometric_sum (q : ℝ) (hq : 1 ≤ q) (I : Finset ℕ)
    (hI : ∀ J ∈ I, 1 ≤ J) :
    (∑ J ∈ I, (1 - 1 / q) ^ (J - 1)) ≤ q := by
  classical
  have hq0 : 0 < q := by linarith
  have hρ0 : 0 ≤ 1 - 1 / q := by
    have := (div_le_one hq0).mpr hq
    linarith
  have hρ1 : 1 - 1 / q < 1 := sub_lt_self _ (one_div_pos.mpr hq0)
  have hs := summable_geometric_of_lt_one hρ0 hρ1
  have heq : (∑ J ∈ I, (1 - 1 / q) ^ (J - 1)) =
      ∑ n ∈ I.image (fun J ↦ J - 1), (1 - 1 / q) ^ n := by
    symm
    apply Finset.sum_image
    intro a ha b hb hab
    dsimp only at hab
    have := hI a ha
    have := hI b hb
    omega
  rw [heq]
  calc
    _ ≤ ∑' n : ℕ, (1 - 1 / q) ^ n :=
      hs.sum_le_tsum _ (fun n _ ↦ pow_nonneg hρ0 n)
    _ = q := by rw [tsum_geometric_of_lt_one hρ0 hρ1]; field_simp; ring

/-- A constant nonnegative terminal error retains precisely the finite positive-root return scale. -/
theorem upper_positive_root_geometric_error (q E : ℝ) (hq : 1 ≤ q) (hE : 0 ≤ E)
    (I : Finset ℕ) (hI : ∀ J ∈ I, 1 ≤ J) :
    (∑ J ∈ I, ENNReal.ofReal ((1 - 1 / q) ^ (J - 1)) * ENNReal.ofReal E) ≤
      ENNReal.ofReal (q * E) := by
  have hq0 : 0 < q := by linarith
  have hρ0 : 0 ≤ 1 - 1 / q := by
    have := (div_le_one hq0).mpr hq
    linarith
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
    (fun J _ ↦ pow_nonneg hρ0 (J - 1)), ← ENNReal.ofReal_mul' hE]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (upper_positive_root_geometric_sum q hq I hI) hE)

end SRWTightness
