import SRWTightness.KilledPathWord
import SRWTightness.SetHitting

open MeasureTheory
namespace SRWTightness

/-- All visits to K before the final step of the finite killed word, retaining their order. -/
noncomputable def wordVisitTrace (K : Finset Site) (x : Site) (w : PathWord) : List Site := by
  classical
  exact (List.ofFn (fun i : Fin w.length ↦ x + position (wordPath w) i)).filter (· ∈ K)

/-- The complete actual trace before killing, with repeated visits retained. -/
noncomputable def killedVisitTrace (D K : Finset Site) (x : Site) (ω : Sample) : List Site :=
  wordVisitTrace K x (killedPathWord D x ω)

/-- The actual probability of leaving D before the first positive return to K. -/
noncomputable def traceStopProbability (D K : Finset Site) (x : Site) : ℝ :=
  pathLaw.real {ω | domainExit D x ω < setHittingTime K x 1 ω}

/-- The same terminal escape with a prescribed exit atom. -/
noncomputable def traceStopExitProbability (D K : Finset Site) (x e : Site) : ℝ :=
  pathLaw.real {ω | domainExit D x ω < setHittingTime K x 1 ω ∧ domainExitLocation D x ω = e}

/-- The exit-atom probability used to condition a killed segment. -/
noncomputable def traceExitProbability (D : Finset Site) (x e : Site) : ℝ :=
  pathLaw.real {ω | domainExitLocation D x ω = e}

/-- Standard finite killed-chain Markov factorization: the same return-kernel product precedes
both terminal escape factors. This is an explicit foundational input, not a disk comparison. -/
def KilledTraceFactorizationInput : Prop :=
  ∀ (D K : Finset Site) (x e : Site), K ⊆ D → x ∈ K → ∀ ξ : List Site,
    0 < pathLaw.real {ω | killedVisitTrace D K x ω = ξ} →
    ∃ w : ℝ, 0 ≤ w ∧
      pathLaw.real {ω | killedVisitTrace D K x ω = ξ} =
        w * traceStopProbability D K (ξ.getLastD x) ∧
      pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} =
        w * traceStopExitProbability D K (ξ.getLastD x) e

/-- Equation trace-rn on the actual killed SRW trace, conditional on standard Markov factorization. -/
theorem killed_trace_conditional_ratio (hTrace : KilledTraceFactorizationInput)
    (D K : Finset Site) (x e : Site) (hKD : K ⊆ D) (hx : x ∈ K) (ξ : List Site)
    (hξ : 0 < pathLaw.real {ω | killedVisitTrace D K x ω = ξ})
    (he : 0 < traceExitProbability D x e) :
    (pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
        traceExitProbability D x e) / pathLaw.real {ω | killedVisitTrace D K x ω = ξ} =
      traceStopExitProbability D K (ξ.getLastD x) e /
        (traceExitProbability D x e * traceStopProbability D K (ξ.getLastD x)) := by
  obtain ⟨w, hw, hp, hj⟩ := hTrace D K x e hKD hx ξ hξ
  have hprod : w * traceStopProbability D K (ξ.getLastD x) ≠ 0 := by
    rw [← hp]
    exact hξ.ne'
  have hw0 := (mul_ne_zero_iff.mp hprod).1
  have hq0 := (mul_ne_zero_iff.mp hprod).2
  rw [hp, hj]
  field_simp
  <;> ring

end SRWTightness
