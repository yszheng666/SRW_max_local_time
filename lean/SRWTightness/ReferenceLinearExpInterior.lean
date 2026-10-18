import SRWTightness.ReferenceLinearTilt
import Mathlib.Probability.Moments.IntegrableExpMul

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Every strictly small multiple of an arbitrary physical coefficient vector is interior
 to the exponential domain, including the zero vector. -/
theorem referenceMark_linear_exp_interior (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (4 * L)) :
    s ∈ interior (integrableExpSet (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
      (referenceMarkLaw D K α)) := by
  have hopen : IsOpen {v : ℝ | |v| * (∑ z, |β z|) < 1 / (4 * L)} :=
    isOpen_lt (by fun_prop) continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hopen.mem_nhds hs)
  intro v hv
  have hcoef : (∑ z, |v * β z|) = |v| * (∑ z, |β z|) := by
    simp only [abs_mul, Finset.mul_sum]
  have hh := (referenceMark_linear_exponential_bound D K hKD α hα hcap
    (fun z ↦ v * β z) L hL hG (by rw [hcoef]; exact hv.le)).1
  change Integrable (fun Y : Mark K ↦ Real.exp (v * ∑ z, β z * (Y z : ℝ))) _
  simpa only [Finset.mul_sum, mul_assoc] using hh

end SRWTightness
