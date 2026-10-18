import SRWTightness.ReferenceProductCgfTaylor
import SRWTightness.NormalizedMarkTilt

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Cubic cgf error for the actual centered normalized weighted occupation sum,
with the exact single-mark Green-energy quadratic term. -/
theorem normalizedWeightedSum_cgf_taylor (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |w z / (u * Real.sqrt (α * g))|) ≤ 1 / (8 * L)) (k : ℕ) :
    let β := fun z ↦ w z / (u * Real.sqrt (α * g))
    |cgf (normalizedWeightedSum K k α g u w) (markProductLaw D K α k) 1 -
      k * (2 * α * (∑ y : K, ∑ z : K, β y * killedGreen D y z * β z) -
        α * (∑ z, β z ^ 2) - (α * ∑ z, β z) ^ 2) / 2| ≤
          k * 23592976 * L ^ 3 * (∑ z, |β z|) ^ 3 / 6 := by
  let β := fun z ↦ w z / (u * Real.sqrt (α * g))
  have hf : normalizedWeightedSum K k α g u w =
      (fun Y : MarkSamples K k ↦ (∑ i, ∑ z, β z * (Y i z : ℝ)) -
        k * (α * ∑ z, β z)) := by
    funext Y
    rw [normalizedWeightedSum_tilt_algebra]
    dsimp [β]
    ring
  dsimp only
  rw [hf]
  exact referenceMark_product_cgf_green_taylor D K hKD α hα hcap β L hL hαL hG hsmall k

/-- With the source normalization k=u²/2, the exact normalized-sum cgf error has order 1/u. -/
theorem normalizedWeightedSum_cgf_taylor_scaled (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1) (w : K → ℝ) (L : ℝ) (hL : 0 < L)
    (hαL : α ≤ L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |w z|) ≤ (u * Real.sqrt (α * g)) / (8 * L))
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let β := fun z ↦ w z / (u * Real.sqrt (α * g))
    |cgf (normalizedWeightedSum K k α g u w) (markProductLaw D K α k) 1 -
      k * (2 * α * (∑ y : K, ∑ z : K, β y * killedGreen D y z * β z) -
        α * (∑ z, β z ^ 2) - (α * ∑ z, β z) ^ 2) / 2| ≤
          23592976 * L ^ 3 * (∑ z, |w z|) ^ 3 /
            (12 * u * (Real.sqrt (α * g)) ^ 3) := by
  have hsqrt : 0 < Real.sqrt (α * g) := Real.sqrt_pos.mpr (mul_pos hα hg)
  have hc : 0 < u * Real.sqrt (α * g) := mul_pos hu hsqrt
  have hphys : (∑ z, |w z / (u * Real.sqrt (α * g))|) =
      (∑ z, |w z|) / (u * Real.sqrt (α * g)) := by
    simp only [abs_div, abs_of_pos hc, ← Finset.sum_div]
  have hb : (∑ z, |w z / (u * Real.sqrt (α * g))|) ≤ 1 / (8 * L) := by
    rw [hphys]
    apply (div_le_iff₀ hc).mpr
    calc
      _ ≤ (u * Real.sqrt (α * g)) / (8 * L) := hsmall
      _ = _ := by ring
  have ht := normalizedWeightedSum_cgf_taylor D K hKD α g u hα.le hcap w
    L hL hαL hG hb k
  dsimp only at ht ⊢
  refine ht.trans_eq ?_
  rw [hphys, ← hk]
  field_simp
  <;> ring

end SRWTightness
