import SRWTightness.FilteredWordFactorization

namespace SRWTightness

/-- The recursive terminal site is the last point of the complete nonempty trace. -/
theorem finiteChain_fold_last_site {α σ : Type*} (f : α → σ) (x : σ) (as : List α) :
    as.foldl (fun _ a ↦ f a) x = (x :: as.map f).getLastD x := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
      simpa only [List.foldl_cons, List.map_cons, List.getLastD_cons] using ih (f a)

end SRWTightness
