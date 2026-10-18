import SRWTightness.ReferenceProductTilt
import SRWTightness.NormalizedWeightedCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Constant centering does not change an exponential tilt of a probability measure. -/
theorem tilted_add_constant {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (c : ℝ) :
    μ.tilted (fun x ↦ f x + c) = μ.tilted f := by
  have hh := tilted_tilted (μ := μ) (f := fun _ ↦ c) (integrable_const (Real.exp c)) f
  rw [tilted_const] at hh
  have he : (fun _ : Ω ↦ c) + f = (fun x ↦ f x + c) := by
    funext x
    change c + f x = f x + c
    ring
  rw [he] at hh
  exact hh.symm

/-- The manuscript's centered, normalized sum differs from the sum of single-mark tilts
by one deterministic constant. -/
theorem normalizedWeightedSum_tilt_algebra (K : Finset Site) (k : ℕ) (α g u : ℝ)
    (w : K → ℝ) (Y : MarkSamples K k) :
    normalizedWeightedSum K k α g u w Y =
      (∑ i, ∑ z, (w z / (u * Real.sqrt (α * g))) * (Y i z : ℝ)) +
        (-α * k * ∑ z, w z / (u * Real.sqrt (α * g))) := by
  unfold normalizedWeightedSum normalizedMarkSum
  calc
    _ = ∑ z, ((∑ i, (w z / (u * Real.sqrt (α * g))) * (Y i z : ℝ)) -
        (w z / (u * Real.sqrt (α * g))) * (α * k)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_comm, ← Finset.sum_mul]
      ring

/-- The actual normalized weighted occupation tilt preserves independent single marks. -/
theorem normalizedWeightedSum_product_tilt (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |w z / (u * Real.sqrt (α * g))|) ≤ 1 / (4 * L)) (k : ℕ) :
    let f := fun Y : Mark K ↦ ∑ z, (w z / (u * Real.sqrt (α * g))) * (Y z : ℝ)
    let ν := (markProductLaw D K α k).tilted (normalizedWeightedSum K k α g u w)
    IsProbabilityMeasure ν ∧
    ν = Measure.pi (fun _ : Fin k ↦ (referenceMarkLaw D K α).tilted f) ∧
    iIndepFun (fun i (Y : MarkSamples K k) ↦ Y i) ν := by
  letI := markProductLaw_isProbabilityMeasure D K α hα hcap k
  have hfun : normalizedWeightedSum K k α g u w =
      (fun Y ↦ (∑ i, ∑ z, (w z / (u * Real.sqrt (α * g))) * (Y i z : ℝ)) +
        (-α * k * ∑ z, w z / (u * Real.sqrt (α * g)))) :=
    funext (normalizedWeightedSum_tilt_algebra K k α g u w)
  have heq : (markProductLaw D K α k).tilted (normalizedWeightedSum K k α g u w) =
      (markProductLaw D K α k).tilted
        (fun Y ↦ ∑ i, ∑ z, (w z / (u * Real.sqrt (α * g))) * (Y i z : ℝ)) := by
    rw [hfun, tilted_add_constant]
  dsimp only
  rw [heq]
  exact referenceMark_product_tilt D K hKD α hα hcap
    (fun z ↦ w z / (u * Real.sqrt (α * g))) L hL hG hsmall k

end SRWTightness
