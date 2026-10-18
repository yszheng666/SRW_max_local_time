import SRWTightness.DiskGreenExplicitAsymptotic

namespace SRWTightness

/-- Source (2.7) uniformly over all lattice disk centers, with its literal constant. -/
theorem diskCenter_explicit_asymptotic (hinput : PotentialKernelAsymptoticInput) :
    ∃ B R₁ : ℝ, 0 ≤ B ∧ 2 ≤ R₁ ∧ ∀ R : ℝ, R₁ ≤ R → ∀ b : Site,
      |killedGreen (translateFinset b (diskFinset R)) b b -
        ((2 / Real.pi) * Real.log R + sourcePotentialConstant)| ≤ B / R := by
  obtain ⟨B, R₁, hB, hR₁, hb, hlim⟩ := diskGreen_explicit_asymptotic hinput
  refine ⟨B, R₁, hB, hR₁, ?_⟩
  intro R hR b
  have he := killedGreen_translate b (diskFinset R) 0 0
  simp only [add_zero] at he
  rw [he]
  exact hb R hR

end SRWTightness
