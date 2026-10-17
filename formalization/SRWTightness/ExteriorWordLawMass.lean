import SRWTightness.ExteriorIndependentWordLaw
import Mathlib.Algebra.BigOperators.Ring.List

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- A chronological zip product is the corresponding finite indexed product. -/
theorem list_zip_ofFn_prod {α β : Type*} (ss : List α)
    (f : Fin ss.length → β) (g : α → β → ℝ) :
    ((ss.zip (List.ofFn f)).map (fun p ↦ g p.1 p.2)).prod =
      ∏ i, g (ss.get i) (f i) := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    rw [List.ofFn_succ]
    simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]
    rw [ih]
    change g s (f 0) * (∏ i : Fin ss.length, g (ss.get i) (f i.succ)) =
      ∏ i : Fin (ss.length + 1), g ((s :: ss).get i) (f i)
    rw [Fin.prod_univ_succ]
    rfl

/-- Every word list of the correct length has its labeled bridge product as singleton mass. -/
theorem exteriorIndependentWordLaw_singleton (C₀ C₁ : Finset Site)
    (h : ExteriorPathRecord) (us : List PathWord) (hlen : us.length = h.1.length) :
    (exteriorIndependentWordLaw C₀ C₁ h).real {us} = labeledExteriorBridgeWordProduct C₀ C₁ h us := by
  let f : Fin h.1.length → PathWord := fun i ↦ us[i.val]'(by omega)
  have hf : List.ofFn f = us := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp [f]
  rw [← hf, exteriorIndependentWordLaw_ofFn]
  exact (list_zip_ofFn_prod h.1 f (fun s u ↦ killedWordBridgeProbability
    (if s.2.1 then C₁ else C₀) s.2.2.1 s.2.2.2 u)).symm

/-- The independent word law is supported on exactly the recorded number of long slots. -/
theorem exteriorIndependentWordLaw_wrong_length (C₀ C₁ : Finset Site)
    (h : ExteriorPathRecord) (us : List PathWord) (hlen : us.length ≠ h.1.length) :
    (exteriorIndependentWordLaw C₀ C₁ h).real {us} = 0 := by
  rw [exteriorIndependentWordLaw, map_measureReal_apply (measurable_of_countable List.ofFn)
    (measurableSet_singleton _)]
  have hs : (List.ofFn : (Fin h.1.length → PathWord) → List PathWord) ⁻¹' {us} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have he : List.ofFn f = us := hf
    exact hlen (by rw [← he, List.length_ofFn])
  rw [hs, measureReal_empty]

end SRWTightness
