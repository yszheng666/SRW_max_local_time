import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Equal-length zipped products cancel the nonzero factors of their first list exactly. -/
theorem list_zip_div_product_cancel {α β : Type*} (ss : List α) (us : List β)
    (q : α → ℝ) (r : β → ℝ) (hlen : us.length = ss.length)
    (hq : ∀ s ∈ ss, q s ≠ 0) :
    (ss.map q).prod * ((ss.zip us).map (fun p ↦ r p.2 / q p.1)).prod =
      (us.map r).prod := by
  induction ss generalizing us with
  | nil =>
    have he : us = [] := List.length_eq_zero_iff.mp hlen
    subst us
    simp
  | cons s ss ih =>
    cases us with
    | nil => simp at hlen
    | cons u us =>
      have hs := hq s List.mem_cons_self
      have ht := ih us (by simpa using hlen) (fun t ht ↦ hq t (List.mem_cons_of_mem s ht))
      simp only [List.map_cons, List.prod_cons, List.zip_cons_cons]
      calc
        (q s * (ss.map q).prod) *
            ((r u / q s) * ((ss.zip us).map (fun p ↦ r p.2 / q p.1)).prod) =
            r u * ((ss.map q).prod * ((ss.zip us).map (fun p ↦ r p.2 / q p.1)).prod) := by
              field_simp [hs]
              <;> ring
        _ = _ := by rw [ht]

end SRWTightness
