import SRWTightness.ReferenceGenerating
import SRWTightness.IndependentMarks
import SRWTightness.MatrixRowContraction
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

def sumMarks (A : Finset Site) (k : ℕ) (Y : MarkSamples A k) : Mark A := fun z ↦ ∑ i, Y i z

 theorem markMonomial_sum (A : Finset Site) (k : ℕ) (v : A → ℝ) (Y : MarkSamples A k) :
    markMonomial v (sumMarks A k Y) = ∏ i : Fin k, markMonomial v (Y i) := by
  unfold markMonomial sumMarks
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_comm

 theorem integral_markMonomial_sum (D A : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (v : A → ℝ) :
    (∫ Y, markMonomial v (sumMarks A k Y) ∂markProductLaw D A α k) =
      (∫ Y, markMonomial v Y ∂referenceMarkLaw D A α) ^ k := by
  letI := referenceMarkLaw_isProbabilityMeasure D A α hα hcap
  simp_rw [markMonomial_sum]
  rw [markProductLaw, integral_fintype_prod_eq_prod]
  simp

 theorem markSum_generating_unit_cube (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (k : ℕ)
    (v : A → ℝ) (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    (∫ Y, markMonomial v (sumMarks A k Y) ∂markProductLaw D A α k) =
      (1 + α * ∑ z : A, (v z - 1) * ((observationResolventMatrix D A v)⁻¹.mulVec 1) z) ^ k := by
  rw [integral_markMonomial_sum D A α hα hcap k v,
    referenceMark_observation_generating D A hAD α hα hcap v hv0 hv1]

/-- An explicit positive-parameter range combines geometric integrability with row contraction. -/
theorem markSum_generating_controlled (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (k : ℕ)
    (v : A → ℝ) (b : ℝ) (hv0 : ∀ z, 0 ≤ v z) (hvb : ∀ z, v z ≤ b) (hb : 0 ≤ b)
    (hqb : ∀ z : A, (1 - 1 / killedGreen D z z) * b ^ Fintype.card A < 1)
    (hrow : ∀ y : A, ∑ z : A,
      |killedGreen D y z - (if y = z then 1 else 0)| * |v z - 1| < 1) :
    (∫ Y, markMonomial v (sumMarks A k Y) ∂markProductLaw D A α k) =
      (1 + α * ∑ z : A, (v z - 1) * ((observationResolventMatrix D A v)⁻¹.mulVec 1) z) ^ k := by
  rw [integral_markMonomial_sum D A α hα hcap k v]
  rw [referenceMark_observation_generating_integrable D A hAD α hα hcap v
    (integrable_killedMonomial D A v b hv0 hvb hb hqb)
    (observationResolvent_isUnit_of_row_sum D A v hrow)]

end SRWTightness
