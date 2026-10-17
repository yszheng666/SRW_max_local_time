import SRWTightness.BoundaryRelativeComparison
import SRWTightness.GreenFirstStep

namespace SRWTightness

/-- Boundary relative control propagates for the actual punctured Green column and escape weight. -/
theorem punctured_green_relative_error (D K A : Finset Site) (hA : A ⊆ D \ K)
    (z : Site) (hz : z ∉ A) (α δ : ℝ)
    (hb : ∀ y ∈ domainExitBoundary A,
      |killedGreen (D \ K) y z - α * (1 - setHitProbability D K y)| ≤
        δ * (1 - setHitProbability D K y))
    (x : Site) (hx : x ∈ A) :
    |killedGreen (D \ K) x z - α * (1 - setHitProbability D K x)| ≤
      δ * (1 - setHitProbability D K x) := by
  apply harmonic_relative_error_on_boundary A (fun y ↦ killedGreen (D \ K) y z)
    (fun y ↦ 1 - setHitProbability D K y) _ _ α δ hb x hx
  · intro y hy
    have hyz : y ≠ z := fun h ↦ hz (h ▸ hy)
    simpa only [if_neg hyz, zero_add] using
      killedGreen_first_step_sum (D \ K) y z (hA hy)
  · intro y hy
    have hh := setHitProbability_harmonic D K y (Finset.mem_sdiff.mp (hA hy)).1
      (Finset.mem_sdiff.mp (hA hy)).2
    rw [Finset.sum_sub_distrib, mul_sub]
    norm_num [Direction] at *
    linarith

end SRWTightness
