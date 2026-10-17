import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Set
open scoped ENNReal

namespace SRWTightness

 theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp [Measure.pi_empty_univ]
  | succ n ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
          f 0 x.1 * ∏ i, f (Fin.succ i) (x.2 i)
          ∂(μ 0).prod (Measure.pi (fun i ↦ μ i.succ)) := by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
        rw [lintegral_prod_mul (g := fun x : (i : Fin n) → E i.succ ↦ ∏ i, f i.succ (x i))
          (μ := μ 0) (ν := Measure.pi (fun i ↦ μ i.succ))
          (hf 0).aemeasurable (by
            apply Measurable.aemeasurable
            apply Finset.measurable_prod
            intro i hi
            exact (hf i.succ).comp (measurable_pi_apply i)),
          ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)]
      _ = _ := by rw [Fin.prod_univ_succ]

 theorem lintegral_finite_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod _ (fun i ↦ hf (e i))

 theorem finite_product_withDensity {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : ι) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [lintegral_finite_prod _ hf]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i)]

end SRWTightness
