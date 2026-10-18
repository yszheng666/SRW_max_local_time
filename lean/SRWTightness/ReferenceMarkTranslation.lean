import SRWTightness.ExternalProjectedMarkTranslation
import SRWTightness.GreenTranslation

open MeasureTheory

namespace SRWTightness

/-- Read translated mark coordinates at the corresponding original sites. -/
def translatedMarkPullback (b : Site) (K : Finset Site)
    (Y : Mark (translateFinset b K)) : Mark K :=
  fun z ↦ Y ⟨b + z, (mem_translateFinset_add b K z).mpr z.property⟩

/-- Pulling back translated mark coordinates is measurable. -/
theorem measurable_translatedMarkPullback (b : Site) (K : Finset Site) :
    Measurable (translatedMarkPullback b K) :=
  measurable_pi_lambda _ (fun z ↦ measurable_pi_apply _)

/-- Spatial translation preserves the entire killed occupation mark law. -/
theorem killedMarkLaw_translate_pullback (b : Site) (D K : Finset Site) (x : Site) :
    (killedMarkLaw (translateFinset b D) (translateFinset b K) (b + x)).map
      (translatedMarkPullback b K) = killedMarkLaw D K x := by
  rw [killedMarkLaw, Measure.map_map (measurable_translatedMarkPullback b K)
    (measurable_killedMark _ _ _), killedMarkLaw]
  congr 1
  funext ω z
  exact domainLocalTime_translate b D x z ω

/-- The reference mark measure is finite even outside the probability parameter region. -/
theorem referenceMarkLaw_finite (D K : Finset Site) (α : ℝ) :
    IsFiniteMeasure (referenceMarkLaw D K α) := by
  constructor
  simp only [referenceMarkLaw, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
    ENNReal.sum_lt_top.mpr (fun x hx ↦ ENNReal.ofReal_lt_top)⟩

/-- Spatial translation preserves the full reference law, including its zero atom. -/
theorem referenceMarkLaw_translate_pullback (b : Site) (D K : Finset Site) (α : ℝ) :
    (referenceMarkLaw (translateFinset b D) (translateFinset b K) α).map
      (translatedMarkPullback b K) = referenceMarkLaw D K α := by
  classical
  have hf := measurable_translatedMarkPullback b K
  simp only [referenceMarkLaw, Measure.map_add _ _ hf, Measure.map_smul,
    Measure.map_finset_sum hf.aemeasurable, Measure.map_dirac' hf,
    show translatedMarkPullback b K 0 = 0 from rfl, capacity_translate]
  congr 1
  have hs (f : Site → Measure (Mark K)) :
      (∑ x ∈ translateFinset b K, f x) = ∑ x ∈ K, f (b + x) := by
    change (∑ x ∈ K.image (fun x ↦ b + x), f x) = _
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact add_left_cancel hxy
  rw [hs]
  apply Finset.sum_congr rfl
  intro x hx
  rw [equilibriumMeasure_translate, killedMarkLaw_translate_pullback]

end SRWTightness
