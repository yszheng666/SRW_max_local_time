import SRWTightness.FilteredWordWeight

open scoped ENNReal

namespace SRWTightness

/-- The ordered product of first-return masses for the actual marked word. -/
noncomputable def filteredReturnWeight {α σ : Type*} (P : σ → σ → ℝ≥0∞)
    (f : α → σ) (p : α → Bool) : σ → List α → ℝ≥0∞
  | _, [] => 1
  | x, a :: as => filteredWordMass P f p x (f a) [] * filteredReturnWeight P f p (f a) as

/-- The same exact return product precedes every terminal destination mass. -/
theorem filteredWordMass_factorization {α σ : Type*} (P : σ → σ → ℝ≥0∞)
    (f : α → σ) (p : α → Bool) (x y : σ) (as : List α)
    (ha : ∀ a ∈ as, p a) :
    filteredWordMass P f p x y as = filteredReturnWeight P f p x as *
      filteredWordMass P f p (as.foldl (fun _ a ↦ f a) x) y [] := by
  induction as generalizing x with
  | nil => simp [filteredReturnWeight]
  | cons a as ih =>
      rw [filteredWordMass_cons P f p x y a as (ha a (by simp)),
        ih (f a) (fun b hb ↦ ha b (List.mem_cons_of_mem _ hb))]
      simp only [filteredReturnWeight, List.foldl_cons, mul_assoc]

/-- Summing over possible exits preserves that common return factor. -/
theorem filteredWordMass_exit_sum_factorization {α σ β : Type*}
    (P : σ → σ → ℝ≥0∞) (f : α → σ) (p : α → Bool) (x : σ)
    (e : β → σ) (as : List α) (ha : ∀ a ∈ as, p a) :
    (∑' j : β, filteredWordMass P f p x (e j) as) =
      filteredReturnWeight P f p x as *
        ∑' j : β, filteredWordMass P f p (as.foldl (fun _ a ↦ f a) x) (e j) [] := by
  simp only [filteredWordMass_factorization P f p x _ as ha, ENNReal.tsum_mul_left]

end SRWTightness
