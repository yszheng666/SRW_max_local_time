import SRWTightness.ReferenceTiltedCenteredMoment
import SRWTightness.ThirdProductMoment

open MeasureTheory

namespace SRWTightness

/-- The joint third centered moment bound is uniform in the observation family and permits
repeated coordinates. Its identification with derivatives is a separate analytic step. -/
theorem referenceMark_tilted_joint_centered_third {ι : Type*}
    (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (w : ι → K → ℝ)
    (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) :
    let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
    let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
    let C := fun i Y ↦ U i Y - ∫ V, U i V ∂ν
    ∀ i j k : ι,
      Integrable (fun Y ↦ C i Y * C j Y * C k Y) ν ∧
      |∫ Y, C i Y * C j Y * C k Y ∂ν| ≤ 17694732 * L ^ 3 := by
  let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
  let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
  let C := fun i Y ↦ U i Y - ∫ V, U i V ∂ν
  have hc (i : ι) := referenceMark_tilted_weighted_centered_third D K hKD α hα hcap
    (w i) (hw i) (hw1 i) β L hL hαL hG hsmall
  have hm (i : ι) : Measurable (C i) := by dsimp [C, U]; fun_prop
  dsimp only
  intro i j k
  have hh := third_product_moment_bound ν (C i) (C j) (C k) (hm i) (hm j) (hm k)
    (hc i).2.1 (hc j).2.1 (hc k).2.1
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hi := (hc i).2.2
  have hj := (hc j).2.2
  have hk := (hc k).2.2
  change (∫ Y, |C i Y| ^ 3 ∂ν) ≤ 5898244 * L ^ 3 at hi
  change (∫ Y, |C j Y| ^ 3 ∂ν) ≤ 5898244 * L ^ 3 at hj
  change (∫ Y, |C k Y| ^ 3 ∂ν) ≤ 5898244 * L ^ 3 at hk
  linarith

end SRWTightness
