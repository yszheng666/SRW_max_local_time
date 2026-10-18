import SRWTightness.SourceEarlyLongRootCount
import SRWTightness.SourceLongChildExitAtoms

open Filter
namespace SRWTightness

/-- The actual short-root count conditioned on a long exit has no fine-record error. -/
theorem source_conditioned_long_root_count (hR : TraceExcursionReconstructionInput)
    (hP : PotentialKernelAsymptoticInput) (hH : PositiveHarmonicRelativeInput)
    (hM : KilledExitDecompositionInput) (hT : KilledTraceFactorizationInput) :
    ∃ A C J₀ : ℝ, 0 < A ∧ 0 < C ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ ν J : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t → J₀ ≤ (J : ℝ) → J ≤ ν →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let ρ := sourceRecordRadius m ℓ (ν + 1)
      ∀ b x e : Site, x ∈ sourceEntranceDomain m 1 ℓ b ν →
      ρ - 14 - 1 ≤ Real.sqrt (normSq (x - b)) → Real.sqrt (normSq (x - b)) ≤ ρ - 14 →
      e ∉ sourceExitDomain m 1 ℓ b (ν - J) →
      0 < traceExitProbability (sourceExitDomain m 1 ℓ b (ν - J)) x e →
      ∀ k : ℕ,
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      let E := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) + C * 15 / (ρ - 14) * ((k : ℝ) + 1)
      let event := {ω | (killedChildIntervals (sourceExitDomain m 1 ℓ b (ν - J))
        (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν) x ω).length = k + 1}
      let conditional := pathLaw.real {ω | ω ∈ event ∧
        domainExitLocation (sourceExitDomain m 1 ℓ b (ν - J)) x ω = e} /
        traceExitProbability (sourceExitDomain m 1 ℓ b (ν - J)) x e
      Real.exp (-E) * (p * (1 - p) ^ k) ≤ conditional ∧
        conditional ≤ Real.exp E * (p * (1 - p) ^ k) := by
  obtain ⟨C, hC, hu⟩ := source_early_long_root_count hP
  obtain ⟨A, J₀, hA, hJ₀, hc⟩ := source_long_child_exit_atoms hR hP hH hM hT
  refine ⟨A, C, max 3 J₀, hA, hC, le_max_left _ _, ?_⟩
  filter_upwards [hu, hc] with t hut hct
  intro ν J hν hJ hJν
  dsimp only
  intro b x e hx hxlo hxhi he hep k
  have hJ3r : (3 : ℝ) ≤ J := (le_max_left _ _).trans hJ
  have hJ3 : 3 ≤ J := by exact_mod_cast hJ3r
  have hJbase : J₀ ≤ (J : ℝ) := (le_max_right _ _).trans hJ
  have hp := hut ν J hν hJ3 hJν b x hx hxlo hxhi k
  have hq := hct ν J hν hJbase hJν b x e hx he hep Unit
    (fun _ _ ↦ ()) (() :: List.replicate k ())
  dsimp only at hp hq ⊢
  rw [killed_child_records_unit_event] at hq
  have combine (E δ w q v : ℝ)
      (hu : Real.exp (-E) * w ≤ q ∧ q ≤ Real.exp E * w)
      (hc : Real.exp (-δ) * q ≤ v ∧ v ≤ Real.exp δ * q) :
      Real.exp (-(δ + E)) * w ≤ v ∧ v ≤ Real.exp (δ + E) * w := by
    constructor
    · calc
        _ = Real.exp (-δ) * (Real.exp (-E) * w) := by
          rw [neg_add, Real.exp_add]; ring
        _ ≤ Real.exp (-δ) * q := mul_le_mul_of_nonneg_left hu.1 (Real.exp_pos _).le
        _ ≤ v := hc.1
    · calc
        v ≤ Real.exp δ * q := hc.2
        _ ≤ Real.exp δ * (Real.exp E * w) := mul_le_mul_of_nonneg_left hu.2 (Real.exp_pos _).le
        _ = _ := by rw [Real.exp_add]; ring
  exact combine _ _ _ _ _ hp hq

end SRWTightness
