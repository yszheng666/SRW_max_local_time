import SRWTightness.ExteriorConditionalWordLaw
import Mathlib.Algebra.BigOperators.Ring.List

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- Coordinate records of chronologically ordered words preserve their fixed header order. -/
theorem list_zip_ofFn_map {α β R : Type*} (ss : List α)
    (f : Fin ss.length → β) (F : α → β → R) :
    (ss.zip (List.ofFn f)).map (fun p ↦ F p.1 p.2) =
      List.ofFn (fun i ↦ F (ss.get i) (f i)) := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    rw [List.ofFn_succ]
    simp only [List.zip_cons_cons, List.map_cons]
    rw [ih]
    change F s (f 0) :: List.ofFn (fun i : Fin ss.length ↦ F (ss.get i) (f i.succ)) =
      List.ofFn (fun i : Fin (ss.length + 1) ↦ F ((s :: ss).get i) (f i))
    rw [List.ofFn_succ]
    rfl

/-- Arbitrary per-slot record atoms under the independent bridge law have the product of the
actual prescribed-exit conditional record probabilities. No record/exit independence is used. -/
theorem exterior_record_product_law {R : Type*} (C₀ C₁ : Finset Site)
    (h : ExteriorPathRecord) (F : ExteriorSlot → PathWord → R) (r : Fin h.1.length → R) :
    (exteriorIndependentWordLaw C₀ C₁ h).real
      {us | (h.1.zip us).map (fun p ↦ F p.1 p.2) = List.ofFn r} =
      ∏ i, pathLaw.real {ω |
        F (h.1.get i) (killedPathWord (if (h.1.get i).2.1 then C₁ else C₀)
          (h.1.get i).2.2.1 ω) = r i ∧
        domainExitLocation (if (h.1.get i).2.1 then C₁ else C₀) (h.1.get i).2.2.1 ω =
          (h.1.get i).2.2.2} /
        traceExitProbability (if (h.1.get i).2.1 then C₁ else C₀)
          (h.1.get i).2.2.1 (h.1.get i).2.2.2 := by
  letI (i : Fin h.1.length) : IsFiniteMeasure (killedWordBridgeLaw
      (if (h.1.get i).2.1 then C₁ else C₀) (h.1.get i).2.2.1 (h.1.get i).2.2.2) := by
    unfold killedWordBridgeLaw
    infer_instance
  rw [exteriorIndependentWordLaw, map_measureReal_apply (measurable_of_countable List.ofFn)
    (Set.to_countable _).measurableSet]
  have hs : List.ofFn ⁻¹' {us | (h.1.zip us).map (fun p ↦ F p.1 p.2) = List.ofFn r} =
      Set.univ.pi (fun i ↦ {u | F (h.1.get i) u = r i}) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_setOf_eq, list_zip_ofFn_map, List.ofFn_inj,
      funext_iff, Set.mem_univ_pi]
  rw [hs]
  unfold Measure.real
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact killedWordBridgeLaw_record _ _ _ _ _

/-- Multiplicative local bounds accumulate their logarithmic errors by summation. -/
theorem finite_product_exponential_comparison {ι : Type*} [Fintype ι]
    (a q E : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (h : ∀ i, Real.exp (-E i) * q i ≤ a i ∧ a i ≤ Real.exp (E i) * q i) :
    Real.exp (-(∑ i, E i)) * (∏ i, q i) ≤ ∏ i, a i ∧
      (∏ i, a i) ≤ Real.exp (∑ i, E i) * ∏ i, q i := by
  have hq (i : ι) : 0 ≤ q i :=
    nonneg_of_mul_nonneg_right ((ha i).trans (h i).2) (Real.exp_pos _)
  constructor
  · calc
      _ = ∏ i, Real.exp (-E i) * q i := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
      _ ≤ _ := Finset.prod_le_prod (fun i _ ↦ mul_nonneg (Real.exp_pos _).le (hq i))
        (fun i _ ↦ (h i).1)
  · calc
      _ ≤ ∏ i, Real.exp (E i) * q i :=
        Finset.prod_le_prod (fun i _ ↦ ha i) (fun i _ ↦ (h i).2)
      _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum]

end SRWTightness
