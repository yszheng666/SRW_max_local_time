import SRWTightness.GaussianGridPath
import SRWTightness.GaussianGridFinalIncrement

namespace SRWTightness

/-- Every average coordinate is the actual Gaussian grid path at its observation time. -/
theorem gaussianGrid_coordinate_node (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1))
    (p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) (i : Fin n) :
    gaussianGridPath T n p (T (i.val + 1)) = p.1 i.castSucc := by
  unfold gaussianGridPath
  rw [bridgedGridPath_node T _ n (i.val + 1) hgap (by omega), observationMeshValue_succ]

/-- The grid path starts at zero when the first observation time is zero. -/
theorem gaussianGrid_coordinate_zero (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < n, T j < T (j + 1))
    (p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :
    gaussianGridPath T n p 0 = 0 := by
  have hh := bridgedGridPath_node T (fun j x ↦ observationMeshValue x j) n 0
    hgap (by omega) p
  simpa only [gaussianGridPath, hT, observationMeshValue_zero] using hh

/-- Differences of average coordinates are path increments at their exact observation times. -/
theorem gaussianGrid_coordinate_difference (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1))
    (p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) (i j : Fin n) :
    p.1 j.castSucc - p.1 i.castSucc =
      gaussianGridPath T n p (T (j.val + 1)) - gaussianGridPath T n p (T (i.val + 1)) := by
  rw [gaussianGrid_coordinate_node T n hgap p j, gaussianGrid_coordinate_node T n hgap p i]

/-- The last coordinate difference is exactly the independent final increment. -/
theorem gaussianGrid_coordinate_final_difference (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n + 1, T j < T (j + 1))
    (p : (Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :
    p.1 (Fin.last (n + 1)) - p.1 (Fin.last n).castSucc =
      gaussianGridFinalIncrement T (n + 1) p := by
  unfold gaussianGridFinalIncrement
  rw [← gaussianGrid_coordinate_node T (n + 1) hgap p (Fin.last n)]
  rfl

end SRWTightness
