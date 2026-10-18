import SRWTightness.PlanarDyadicChain
import SRWTightness.DyadicChainingWeights

open scoped BigOperators

namespace SRWTightness

/-- A finite planar observation exceeding the total threshold crosses a dyadic edge threshold. -/
theorem planar_dyadic_chain_cover {ι : Type*} [Fintype ι]
    (J : Finset ι) (p : ι → ℝ × ℝ) (o : ι) (ho : o ∈ J) (R : ℝ) (hR : 0 < R)
    (φ : ι → ℝ) (h0 : φ o = 0)
    (heq : ∀ i ∈ J, ∀ j ∈ J, p i = p j → φ i = φ j)
    (a u : ℝ) (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hc : ∃ x ∈ J, a * (2 * u + 4) ≤ |φ x|) :
    ∃ n : ℕ, ∃ x ∈ J, a * (u + n + 1) / 2 ^ n ≤
      |φ (planarDyadicChain J p o R (n + 1) x) -
        φ (planarDyadicChain J p o R n x)| := by
  obtain ⟨N, hN⟩ := (planarDyadicRepresentative_eventually_exact J p o R hR).exists
  obtain ⟨x, hx, hcross⟩ := hc
  have hend : φ (planarDyadicChain J p o R (N + 1) x) = φ x := by
    exact heq _ (planarDyadicRepresentative_spec J p o R N x hx).1 x hx (hN x hx)
  have hsum : (∑ n ∈ Finset.range (N + 1), a * (u + n + 1) / (2 : ℝ) ^ n) ≤
      a * (2 * u + 4) := by
    simpa only [mul_div_assoc, Finset.mul_sum] using
      mul_le_mul_of_nonneg_left (dyadic_chaining_weight_sum_le u hu (N + 1)) ha
  obtain ⟨n, hn, ht⟩ := finite_chain_crossing_increment
    (fun n ↦ φ (planarDyadicChain J p o R n x))
    (fun n ↦ a * (u + n + 1) / (2 : ℝ) ^ n) N (a * (2 * u + 4)) h0
    (by simpa only [hend] using hcross) hsum
  exact ⟨n, x, hx, ht⟩

end SRWTightness
