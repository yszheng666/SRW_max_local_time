import SRWTightness.FilteredWordDecomposition
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open scoped ENNReal

namespace SRWTightness

/-- The actual product of transition weights along a finite word with fixed endpoints. -/
noncomputable def chainWordWeight {α σ : Type*} (P : σ → σ → ℝ≥0∞) (f : α → σ) :
    σ → List α → σ → ℝ≥0∞
  | x, [], y => P x y
  | x, a :: as, y => P x (f a) * chainWordWeight P f (f a) as y

/-- Splitting a transition word at a marked site factors its exact weight. -/
theorem chainWordWeight_append_marker {α σ : Type*} (P : σ → σ → ℝ≥0∞) (f : α → σ)
    (x y : σ) (u v : List α) (a : α) :
    chainWordWeight P f x (u ++ a :: v) y =
      chainWordWeight P f x u (f a) * chainWordWeight P f (f a) v y := by
  induction u generalizing x with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, chainWordWeight, ih, mul_assoc]

/-- The mass of all finite transition words with the specified ordered marked trace. -/
noncomputable def filteredWordMass {α σ : Type*} (P : σ → σ → ℝ≥0∞) (f : α → σ)
    (p : α → Bool) (x y : σ) (as : List α) : ℝ≥0∞ :=
  ∑' w : FilteredWordFiber p as, chainWordWeight P f x w.val y

/-- Summing over actual words factors at the first marked return, with no assumed kernel law. -/
theorem filteredWordMass_cons {α σ : Type*} (P : σ → σ → ℝ≥0∞) (f : α → σ)
    (p : α → Bool) (x y : σ) (a : α) (as : List α) (ha : p a) :
    filteredWordMass P f p x y (a :: as) =
      filteredWordMass P f p x (f a) [] * filteredWordMass P f p (f a) y as := by
  unfold filteredWordMass
  rw [← (filteredWordConsEquiv p a as ha).tsum_eq]
  change (∑' q : FilteredWordFiber p [] × FilteredWordFiber p as,
    chainWordWeight P f x (q.1.val ++ a :: q.2.val) y) = _
  simp only [chainWordWeight_append_marker]
  dsimp only [FilteredWordFiber]
  rw [ENNReal.tsum_prod']
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

end SRWTightness
