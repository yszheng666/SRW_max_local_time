import SRWTightness.AnnulusEscapeIdentity

namespace SRWTightness

/-- Enlarging the killing domain can only increase the probability of hitting a fixed target. -/
theorem setHitProbability_mono_domain (D E K : Finset Site) (hDE : D ⊆ E) (x : Site) :
    setHitProbability D K x ≤ setHitProbability E K x := by
  have hD : setHitProbability D K x = exitPayoff (D \ K) (setHitProbability D K) x := by
    apply harmonic_eq_exitPayoff
    intro y hy
    exact setHitProbability_harmonic D K y (Finset.mem_sdiff.mp hy).1
      (Finset.mem_sdiff.mp hy).2
  have hE : setHitProbability E K x = exitPayoff (D \ K) (setHitProbability E K) x := by
    apply harmonic_eq_exitPayoff
    intro y hy
    exact setHitProbability_harmonic E K y (hDE (Finset.mem_sdiff.mp hy).1)
      (Finset.mem_sdiff.mp hy).2
  rw [hD, hE]
  apply exitPayoff_mono_on_compl
  intro y hy
  by_cases hyD : y ∈ D
  · have hyK : y ∈ K := by
      by_contra hn
      exact hy (Finset.mem_sdiff.mpr ⟨hyD, hn⟩)
    rw [setHitProbability_one D K y hyD hyK,
      setHitProbability_one E K y (hDE hyD) hyK]
  · rw [setHitProbability_zero_of_not_mem D K y hyD, setHitProbability_eq_probability]
    exact MeasureTheory.measureReal_nonneg

end SRWTightness
