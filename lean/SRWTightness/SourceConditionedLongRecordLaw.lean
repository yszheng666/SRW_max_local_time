import SRWTightness.SourceLongRecordLaw
import SRWTightness.SourceLongChildExitAtoms

open Filter
namespace SRWTightness

/-- The source ordered fine-record law, conditional on any reachable prescribed long exit. -/
theorem source_conditioned_long_record_law (hR : TraceExcursionReconstructionInput)
    (hP : PotentialKernelAsymptoticInput) (hH : PositiveHarmonicRelativeInput)
    (hM : KilledExitDecompositionInput) (hT : KilledTraceFactorizationInput) :
    ∃ A C B W J₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b : Site) (a : ℝ) (K : Finset Site), 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) → ∀ ν J : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t → J₀ ≤ (J : ℝ) → J ≤ ν →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let ρ := sourceRecordRadius m ℓ (ν + 1)
      ∀ x e : Site, x ∈ sourceEntranceDomain m 1 ℓ b ν →
      ρ - 14 - 1 ≤ Real.sqrt (normSq (x - b)) → Real.sqrt (normSq (x - b)) ≤ ρ - 14 →
      e ∉ sourceExitDomain m 1 ℓ b (ν - J) →
      0 < traceExitProbability (sourceExitDomain m 1 ℓ b (ν - J)) x e →
      ∀ (r : FiniteExcursionRecord (Mark K) (ℓ - (ν + 1)))
        (rs : List (FiniteExcursionRecord (Mark K) (ℓ - (ν + 1)))),
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      let E := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
        (C * 15 / (ρ - 14) * ((rs.length : ℝ) + 1) +
        ((r :: rs).map (sourceLongFineError B W t a K ν)).sum)
      let weight := p * (1 - p) ^ rs.length * ((r :: rs).map (sourceLongFineReferenceMass t b K ν)).prod
      let event := {ω | killedChildRecords (sourceExitDomain m 1 ℓ b (ν - J))
        (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν) x
        (sourceLongFineRecord t b K ν) ω = r :: rs}
      let conditional := pathLaw.real {ω | ω ∈ event ∧
        domainExitLocation (sourceExitDomain m 1 ℓ b (ν - J)) x ω = e} /
        traceExitProbability (sourceExitDomain m 1 ℓ b (ν - J)) x e
      Real.exp (-E) * weight ≤ conditional ∧ conditional ≤ Real.exp E * weight := by
  obtain ⟨C, B, W, hC, hB, hW, hu⟩ := source_long_record_law hP
  obtain ⟨A, J₀, hA, hJ₀, hc⟩ := source_long_child_exit_atoms hR hP hH hM hT
  refine ⟨A, C, B, W, max 3 J₀, hA, hC, hB, hW, le_max_left _ _, ?_⟩
  filter_upwards [hu, hc] with t hut hct
  intro b a K ha hcut hK ν J hν hJ hJν
  dsimp only
  intro x e hx hxlo hxhi he hep r rs
  have hJ3r : (3 : ℝ) ≤ J := (le_max_left _ _).trans hJ
  have hJ3 : 3 ≤ J := by exact_mod_cast hJ3r
  have hJbase : J₀ ≤ (J : ℝ) := (le_max_right _ _).trans hJ
  have hp := hut b a K ha hcut hK ν J hν hJ3 hJν x hx hxlo hxhi r rs
  have hq := hct ν J hν hJbase hJν b x e hx he hep _
    (sourceLongFineRecord t b K ν) (r :: rs)
  dsimp only at hp hq ⊢
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
