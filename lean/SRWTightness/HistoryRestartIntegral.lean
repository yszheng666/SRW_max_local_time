import SRWTightness.FutureIndependence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- A past restriction keeps the actual restart site jointly independent of future steps. -/
theorem history_restart_product_law (n : ℕ) (E : Set Sample) (hE : MeasurableSet[history n] E)
    (ξ : Sample → Site) (hξ : Measurable[history n] ξ) :
    (pathLaw.restrict E).map (fun ω ↦ (ξ ω, shift n ω)) =
      ((pathLaw.restrict E).map ξ).prod pathLaw := by
  have hglobal : Measurable ξ := hξ.mono (history.le n) le_rfl
  have hpair : Measurable (fun ω ↦ (ξ ω, shift n ω)) := hglobal.prodMk (measurable_shift n)
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply hpair (hs.prod ht), Measure.prod_prod, Measure.map_apply hglobal hs,
    Measure.restrict_apply (hpair (hs.prod ht)), Measure.restrict_apply (hglobal hs)]
  have hset : (fun ω ↦ (ξ ω, shift n ω)) ⁻¹' (s ×ˢ t) ∩ E =
      (ξ ⁻¹' s ∩ E) ∩ (shift n) ⁻¹' t := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    tauto
  rw [hset]
  exact measure_past_inter_future n _ t ((hξ hs).inter hE) ht

/-- Nonnegative restart functionals integrate exactly against their ordinary future means. -/
theorem lintegral_history_restart (n : ℕ) (E : Set Sample) (hE : MeasurableSet[history n] E)
    (ξ : Sample → Site) (hξ : Measurable[history n] ξ)
    (f : Site → Sample → ℝ≥0∞) (hf : ∀ z, Measurable (f z)) :
    (∫⁻ ω, f (ξ ω) (shift n ω) ∂pathLaw.restrict E) =
      ∫⁻ ω, (∫⁻ υ, f (ξ ω) υ ∂pathLaw) ∂pathLaw.restrict E := by
  have hglobal : Measurable ξ := hξ.mono (history.le n) le_rfl
  have hpair : Measurable (fun ω ↦ (ξ ω, shift n ω)) := hglobal.prodMk (measurable_shift n)
  have hmeas : Measurable (fun p : Site × Sample ↦ f p.1 p.2) :=
    measurable_from_prod_countable_right hf
  calc
    _ = ∫⁻ p : Site × Sample, f p.1 p.2
        ∂(pathLaw.restrict E).map (fun ω ↦ (ξ ω, shift n ω)) :=
      (lintegral_map hmeas hpair).symm
    _ = ∫⁻ p : Site × Sample, f p.1 p.2
        ∂((pathLaw.restrict E).map ξ).prod pathLaw := by
      rw [history_restart_product_law n E hE ξ hξ]
    _ = ∫⁻ z, ∫⁻ υ, f z υ ∂pathLaw ∂(pathLaw.restrict E).map ξ :=
      lintegral_prod _ hmeas.aemeasurable
    _ = _ := lintegral_map (measurable_of_countable _) hglobal

end SRWTightness
