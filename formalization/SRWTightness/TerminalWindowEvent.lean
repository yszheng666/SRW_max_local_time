import SRWTightness.SourceBoundedTilt
import Mathlib.Topology.ContinuousMap.Algebra

open MeasureTheory

namespace SRWTightness

/-- Site and final-average windows, together with an affine path barrier at every time. -/
def terminalWindowEvent {ι τ : Type*} [Fintype ι] [TopologicalSpace τ]
    (site last : ι) (siteLo siteHi lastLo lastHi : ℝ)
    (coeff : τ → ι → ℝ) (barrier : τ → ℝ) : Set ((ι → ℝ) × C(τ, ℝ)) :=
  {z | siteLo ≤ z.1 site ∧ z.1 site ≤ siteHi ∧
    lastLo ≤ z.1 last ∧ z.1 last ≤ lastHi ∧
    ∀ t, (∑ i, coeff t i * z.1 i) + z.2 t ≤ barrier t}

/-- Fixing the auxiliary continuous path leaves a convex event in the observation vector. -/
theorem terminalWindowEvent_section_convex {ι τ : Type*} [Fintype ι] [TopologicalSpace τ]
    (site last : ι) (siteLo siteHi lastLo lastHi : ℝ)
    (coeff : τ → ι → ℝ) (barrier : τ → ℝ) (path : C(τ, ℝ)) :
    Convex ℝ ((fun x ↦ (x, path)) ⁻¹'
      terminalWindowEvent site last siteLo siteHi lastLo lastHi coeff barrier) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hxl, hxu, hxl', hxu', hxp⟩ := hx
  obtain ⟨hyl, hyu, hyl', hyu', hyp⟩ := hy
  change siteLo ≤ a * x site + b * y site ∧ a * x site + b * y site ≤ siteHi ∧
    lastLo ≤ a * x last + b * y last ∧ a * x last + b * y last ≤ lastHi ∧ _
  have hz (r : ℝ) : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [hz siteLo, mul_nonneg ha (sub_nonneg.mpr hxl), mul_nonneg hb (sub_nonneg.mpr hyl)]
  · nlinarith [hz siteHi, mul_nonneg ha (sub_nonneg.mpr hxu), mul_nonneg hb (sub_nonneg.mpr hyu)]
  · nlinarith [hz lastLo, mul_nonneg ha (sub_nonneg.mpr hxl'), mul_nonneg hb (sub_nonneg.mpr hyl')]
  · nlinarith [hz lastHi, mul_nonneg ha (sub_nonneg.mpr hxu'), mul_nonneg hb (sub_nonneg.mpr hyu')]
  · intro t
    have he : (∑ i, coeff t i * (a * x i + b * y i)) =
        a * (∑ i, coeff t i * x i) + b * (∑ i, coeff t i * y i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    change (∑ i, coeff t i * (a * x i + b * y i)) + path t ≤ barrier t
    rw [he]
    have hx := mul_le_mul_of_nonneg_left (hxp t) ha
    have hy := mul_le_mul_of_nonneg_left (hyp t) hb
    nlinarith [hz (path t), hz (barrier t)]

/-- The full path event is closed, despite imposing the barrier at all times. -/
theorem terminalWindowEvent_isClosed {ι τ : Type*} [Fintype ι] [TopologicalSpace τ]
    (site last : ι) (siteLo siteHi lastLo lastHi : ℝ)
    (coeff : τ → ι → ℝ) (barrier : τ → ℝ) :
    IsClosed (terminalWindowEvent site last siteLo siteHi lastLo lastHi coeff barrier) := by
  have he : terminalWindowEvent site last siteLo siteHi lastLo lastHi coeff barrier =
      {z : (ι → ℝ) × C(τ, ℝ) | siteLo ≤ z.1 site} ∩
      ({z | z.1 site ≤ siteHi} ∩ ({z | lastLo ≤ z.1 last} ∩
      ({z | z.1 last ≤ lastHi} ∩
        ⋂ t, {z | (∑ i, coeff t i * z.1 i) + z.2 t ≤ barrier t}))) := by
    ext z
    simp [terminalWindowEvent]
  rw [he]
  refine (isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_le continuous_const (by fun_prop)).inter
        ((isClosed_le (by fun_prop) continuous_const).inter ?_)))
  apply isClosed_iInter
  intro t
  apply isClosed_le _ continuous_const
  exact (continuous_finset_sum _ (fun i _ ↦ continuous_const.mul
    ((continuous_apply i).comp continuous_fst))).add
      ((continuous_eval_const t).comp continuous_snd)

/-- The closed event is measurable for the Borel structure of the vector/path product. -/
theorem terminalWindowEvent_measurableSet {ι τ : Type*} [Fintype ι] [TopologicalSpace τ]
    [MeasurableSpace ((ι → ℝ) × C(τ, ℝ))] [BorelSpace ((ι → ℝ) × C(τ, ℝ))]
    (site last : ι) (siteLo siteHi lastLo lastHi : ℝ)
    (coeff : τ → ι → ℝ) (barrier : τ → ℝ) :
    MeasurableSet (terminalWindowEvent site last siteLo siteHi lastLo lastHi coeff barrier) :=
  (terminalWindowEvent_isClosed site last siteLo siteHi lastLo lastHi coeff barrier).measurableSet

end SRWTightness
