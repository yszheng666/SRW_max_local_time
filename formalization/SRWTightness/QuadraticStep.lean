import SRWTightness.StepBound

namespace SRWTightness

/-- Exact quadratic increment, with the lattice step having Euclidean length one. -/
theorem normSq_add_step (x : Site) (d : Direction) :
    normSq (x + step d) = normSq x +
      2 * ((x.1 : ℝ) * (step d).1 + (x.2 : ℝ) * (step d).2) + 1 := by
  fin_cases d <;> simp [normSq, step] <;> ring

 theorem abs_fst_le_normSq_bound (x : Site) {a : ℝ} (ha : 0 ≤ a)
    (h : normSq x ≤ a ^ 2) : |(x.1 : ℝ)| ≤ a := by
  apply abs_le_of_sq_le_sq _ ha
  dsimp [normSq] at h
  nlinarith [sq_nonneg (x.2 : ℝ)]

 theorem abs_snd_le_normSq_bound (x : Site) {a : ℝ} (ha : 0 ≤ a)
    (h : normSq x ≤ a ^ 2) : |(x.2 : ℝ)| ≤ a := by
  apply abs_le_of_sq_le_sq _ ha
  dsimp [normSq] at h
  nlinarith [sq_nonneg (x.1 : ℝ)]

end SRWTightness
