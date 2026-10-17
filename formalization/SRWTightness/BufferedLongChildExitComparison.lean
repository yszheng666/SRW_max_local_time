import SRWTightness.BufferedLongTraceRecords
import SRWTightness.BufferedLongTraceComparison

open MeasureTheory
namespace SRWTightness

/-- Complete child records and independent auxiliary tests inherit the uniform long-exit factor. -/
theorem buffered_long_child_exit_comparison (hR : TraceExcursionReconstructionInput)
    (hP : PotentialKernelAsymptoticInput) (hH : PositiveHarmonicRelativeInput)
    (hM : KilledExitDecompositionInput) (hT : KilledTraceFactorizationInput) :
    ∃ A J₀ : ℝ, 0 < A ∧ 1 ≤ J₀ ∧ ∀ ρ H J : ℝ,
      1 ≤ H → 8 * H ≤ ρ → J₀ ≤ J →
      ∀ (b x e : Site),
      x ∈ translateFinset b (diskFinset (ρ - H)) →
      e ∉ translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)) →
      0 < traceExitProbability
        (translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))) x e →
      ∀ (M Ξ : Type*) [MeasurableSpace (List M)] [MeasurableSpace Ξ]
        (F : Site → PathWord → M) (ν : Measure Ξ) [IsProbabilityMeasure ν]
        (s : Set (List M × Ξ)), MeasurableSet s →
      let D := translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))
      let K := translateFinset b (diskFinset (ρ - H))
      let C := translateFinset b (diskFinset (Real.exp 1 * ρ + H))
      let δ := A * (J + 1) * Real.exp (-J)
      let event := {p : Sample × Ξ | (killedChildRecords D K C x F p.1, p.2) ∈ s}
      let joint := ((pathLaw.restrict {ω | domainExitLocation D x ω = e}).prod ν).real event
      Real.exp (-δ) * (pathLaw.prod ν).real event ≤ joint / traceExitProbability D x e ∧
        joint / traceExitProbability D x e ≤ Real.exp δ * (pathLaw.prod ν).real event := by
  obtain ⟨A, J₀, hA, hJ₀, hh⟩ := buffered_long_trace_comparison hP hH hM hT
  refine ⟨A, J₀, hA, hJ₀, ?_⟩
  intro ρ H J hH1 hρ hJ b x e hx he hep M Ξ _ _ F ν _ s hs
  letI : MeasurableSpace (List Site) := ⊤
  letI : MeasurableSingletonClass (List Site) := ⟨fun _ ↦ trivial⟩
  let D := translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))
  let K := translateFinset b (diskFinset (ρ - H))
  let C := translateFinset b (diskFinset (Real.exp 1 * ρ + H))
  let E := translateFinset b (diskFinset (Real.exp 1 * ρ + H + 2))
  have hJ1 : 1 ≤ J := hJ₀.trans hJ
  obtain ⟨g, hg⟩ := buffered_long_child_trace_representation hR ρ H J hH1 hρ hJ1 b x F
  have hρ0 : 0 ≤ ρ := by linarith
  have hH0 : 0 ≤ H := by linarith
  have he1 := Real.exp_one_gt_two
  have hKE : K ⊆ E := Finset.image_subset_image
    (diskFinset_mono _ _ (by linarith) (by nlinarith))
  let test := {p : List Site × Ξ | (g p.1, p.2) ∈ s}
  have hm : Measurable (fun p : List Site × Ξ ↦ (g p.1, p.2)) :=
    ((measurable_of_countable g).comp measurable_fst).prodMk measurable_snd
  have htest : MeasurableSet test := hm hs
  have hcomp := hh ρ H J (by linarith) hH0 (by linarith) hJ b x e E
    (Finset.Subset.refl _) (hKE hx) he hep Ξ ν test htest
  have hprob (κ : Measure Sample)
      (hk : killedChildRecords D K C x F =ᵐ[κ] fun ω ↦ g (killedVisitTrace D E x ω)) :
      (κ.prod ν).real {p : Sample × Ξ | (killedChildRecords D K C x F p.1, p.2) ∈ s} =
      (κ.prod ν).real {p : Sample × Ξ | (killedVisitTrace D E x p.1, p.2) ∈ test} := by
    apply measureReal_congr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := κ) (ν := ν)).ae hk] with p hp
    change ((killedChildRecords D K C x F p.1, p.2) ∈ s) =
      ((g (killedVisitTrace D E x p.1), p.2) ∈ s)
    rw [hp]
  have hu := hprob pathLaw hg
  have hc := hprob (pathLaw.restrict {ω | domainExitLocation D x ω = e})
    (ae_restrict_of_ae hg)
  dsimp only at hcomp ⊢
  change Real.exp _ * _ ≤ _ / _ ∧ _ / _ ≤ Real.exp _ * _
  rw [hu, hc]
  exact hcomp

end SRWTightness
