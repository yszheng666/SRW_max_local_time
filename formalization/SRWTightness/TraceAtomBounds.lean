import SRWTightness.ExternalKilledTraceFactorization

open MeasureTheory
namespace SRWTightness

/-- A relative conditional trace ratio controls joint atoms, including zero trace atoms. -/
theorem trace_atom_bounds (D K : Finset Site) (x e : Site) (ε : ℝ)
    (he : 0 < traceExitProbability D x e)
    (hratio : ∀ ξ : List Site,
      0 < pathLaw.real {ω | killedVisitTrace D K x ω = ξ} →
      |(pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
        traceExitProbability D x e) / pathLaw.real {ω | killedVisitTrace D K x ω = ξ} - 1| ≤ ε)
    (ξ : List Site) :
    ((1 - ε) * traceExitProbability D x e) *
        pathLaw.real {ω | killedVisitTrace D K x ω = ξ} ≤
      pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} ∧
    pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} ≤
      ((1 + ε) * traceExitProbability D x e) *
        pathLaw.real {ω | killedVisitTrace D K x ω = ξ} := by
  by_cases hp : 0 < pathLaw.real {ω | killedVisitTrace D K x ω = ξ}
  · have hh := abs_le.mp (hratio ξ hp)
    have hlo : (1 - ε) * pathLaw.real {ω | killedVisitTrace D K x ω = ξ} ≤
        pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
          traceExitProbability D x e := (le_div_iff₀ hp).mp (by linarith [hh.1])
    have hhi : pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
          traceExitProbability D x e ≤
        (1 + ε) * pathLaw.real {ω | killedVisitTrace D K x ω = ξ} :=
      (div_le_iff₀ hp).mp (by linarith [hh.2])
    constructor
    · nlinarith [(le_div_iff₀ he).mp hlo]
    · nlinarith [(div_le_iff₀ he).mp hhi]
  · have hz : pathLaw.real {ω | killedVisitTrace D K x ω = ξ} = 0 :=
      le_antisymm (le_of_not_gt hp) measureReal_nonneg
    have hj : pathLaw.real
        {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} = 0 := by
      apply le_antisymm _ measureReal_nonneg
      calc
        _ ≤ pathLaw.real {ω | killedVisitTrace D K x ω = ξ} :=
          measureReal_mono (fun _ h ↦ h.1)
        _ = 0 := hz
    simp only [hz, hj, mul_zero, le_refl, and_self]

end SRWTightness
