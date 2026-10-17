import SRWTightness.ShortRootExitSeparation

namespace SRWTightness

/-- A strict separation margin keeps all exits of one disk outside the other disk. -/
theorem disk_exit_outside_other (b w x : Site) (R : ℝ) (hR : 0 ≤ R)
    (hsep : 2 * R + 1 < Real.sqrt (normSq (w - b)))
    (hx : x ∈ domainExitBoundary (translateFinset b (diskFinset R))) :
    x ∉ translateFinset w (diskFinset R) := by
  intro hin
  have hh := disk_exit_other_inner_separation b w x x R R hR hR hx hin
  simp only [sub_self, (normSq_eq_zero_iff 0).2 rfl, Real.sqrt_zero] at hh
  linarith

end SRWTightness
