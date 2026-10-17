import SRWTightness.BufferedLongChildExitComparison

open MeasureTheory
namespace SRWTightness

/-- The long-exit comparison applies to every exact ordered child-record list. -/
theorem buffered_long_child_exit_atoms (hR : TraceExcursionReconstructionInput)
    (hP : PotentialKernelAsymptoticInput) (hH : PositiveHarmonicRelativeInput)
    (hM : KilledExitDecompositionInput) (hT : KilledTraceFactorizationInput) :
    ∃ A J₀ : ℝ, 0 < A ∧ 1 ≤ J₀ ∧ ∀ ρ H J : ℝ,
      1 ≤ H → 8 * H ≤ ρ → J₀ ≤ J → ∀ b x e : Site,
      x ∈ translateFinset b (diskFinset (ρ - H)) →
      e ∉ translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)) →
      0 < traceExitProbability
        (translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))) x e →
      ∀ (M : Type*) (F : Site → PathWord → M) (rs : List M),
      let D := translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))
      let K := translateFinset b (diskFinset (ρ - H))
      let C := translateFinset b (diskFinset (Real.exp 1 * ρ + H))
      let δ := A * (J + 1) * Real.exp (-J)
      let event := {ω | killedChildRecords D K C x F ω = rs}
      let joint := pathLaw.real {ω | ω ∈ event ∧ domainExitLocation D x ω = e}
      Real.exp (-δ) * pathLaw.real event ≤ joint / traceExitProbability D x e ∧
        joint / traceExitProbability D x e ≤ Real.exp δ * pathLaw.real event := by
  obtain ⟨A, J₀, hA, hJ₀, hh⟩ := buffered_long_child_exit_comparison hR hP hH hM hT
  refine ⟨A, J₀, hA, hJ₀, ?_⟩
  intro ρ H J hH1 hρ hJ b x e hx he hep M F rs
  letI : MeasurableSpace (List M) := ⊤
  let ν : Measure Unit := Measure.dirac ()
  letI : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  let s : Set (List M × Unit) := {rs} ×ˢ Set.univ
  have hs : MeasurableSet s := (show MeasurableSet ({rs} : Set (List M)) from trivial).prod
    MeasurableSet.univ
  have hb := hh ρ H J hH1 hρ hJ b x e hx he hep M Unit F ν s hs
  let D := translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))
  let K := translateFinset b (diskFinset (ρ - H))
  let C := translateFinset b (diskFinset (Real.exp 1 * ρ + H))
  let event := {ω | killedChildRecords D K C x F ω = rs}
  have hset : {p : Sample × Unit | (killedChildRecords D K C x F p.1, p.2) ∈ s} =
      event ×ˢ Set.univ := by ext p; simp [s, event]
  have hprob (κ : Measure Sample) :
      (κ.prod ν).real {p : Sample × Unit | (killedChildRecords D K C x F p.1, p.2) ∈ s} =
      κ.real event := by rw [hset, measureReal_prod_prod, measureReal_univ_eq_one, mul_one]
  dsimp only at hb ⊢
  rw [hprob pathLaw, hprob (pathLaw.restrict {ω | domainExitLocation D x ω = e}),
    measureReal_restrict_apply (measurableSet_killedChildRecords_eq D K C x F rs)] at hb
  exact hb

end SRWTightness
