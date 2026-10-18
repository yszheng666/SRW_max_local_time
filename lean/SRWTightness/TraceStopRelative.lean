import SRWTightness.ExternalKilledExitDecomposition
import SRWTightness.TraceExitRelativeRatio

namespace SRWTightness

/-- Averaging the propagated relative error gives the terminal escape-kernel error at K. -/
theorem trace_stop_relative_from_neighbors (hM : KilledExitDecompositionInput)
    (D K : Finset Site) (hKD : K ⊆ D) (x e : Site) (hx : x ∈ K) (he : e ∉ D)
    (s ε : ℝ)
    (hn : ∀ d : Direction,
      |traceExitProbability (D \ K) (x + step d) e -
        s * competingExitMass D K (x + step d)| ≤
      ε * s * competingExitMass D K (x + step d)) :
    |traceStopExitProbability D K x e - s * traceStopProbability D K x| ≤
      ε * s * traceStopProbability D K x := by
  rw [hM.2.1 D K hKD x hx, hM.2.2 D K hKD x hx e he]
  have hid : (1 / 4 : ℝ) * (∑ d : Direction, traceExitProbability (D \ K) (x + step d) e) -
      s * ((1 / 4 : ℝ) * ∑ d : Direction, competingExitMass D K (x + step d)) =
      (1 / 4 : ℝ) * ∑ d : Direction,
        (traceExitProbability (D \ K) (x + step d) e - s * competingExitMass D K (x + step d)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  calc
    _ ≤ (1 / 4 : ℝ) * ∑ d : Direction,
        |traceExitProbability (D \ K) (x + step d) e - s * competingExitMass D K (x + step d)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1 / 4 : ℝ) * ∑ d : Direction, ε * s * competingExitMass D K (x + step d) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ ↦ hn d)) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Actual positive trace atoms have a positive terminal escape factor in the standard factorization. -/
theorem trace_stop_positive_of_trace (hT : KilledTraceFactorizationInput)
    (D K : Finset Site) (hKD : K ⊆ D) (x e : Site) (hx : x ∈ K) (ξ : List Site)
    (hξ : 0 < pathLaw.real {ω | killedVisitTrace D K x ω = ξ}) :
    0 < traceStopProbability D K (ξ.getLastD x) := by
  obtain ⟨w, hw, hp, _⟩ := hT D K x e hKD hx ξ hξ
  rw [hp] at hξ
  by_contra h
  have hh := mul_nonpos_of_nonneg_of_nonpos hw (le_of_not_gt h)
  linarith

/-- Relative kernel and entrance errors control the actual conditioned-to-unconditioned trace ratio. -/
theorem killed_trace_relative_comparison (hT : KilledTraceFactorizationInput)
    (D K : Finset Site) (hKD : K ⊆ D) (x e : Site) (hx : x ∈ K) (ξ : List Site)
    (hξ : 0 < pathLaw.real {ω | killedVisitTrace D K x ω = ξ})
    (he : 0 < traceExitProbability D x e) (s ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hcond : |traceExitProbability D x e - s| ≤ δ * s)
    (hterm : |traceStopExitProbability D K (ξ.getLastD x) e -
      s * traceStopProbability D K (ξ.getLastD x)| ≤
      ε * s * traceStopProbability D K (ξ.getLastD x)) :
    |(pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
      traceExitProbability D x e) / pathLaw.real {ω | killedVisitTrace D K x ω = ξ} - 1| ≤
      2 * (ε + δ) := by
  rw [killed_trace_conditional_ratio hT D K x e hKD hx ξ hξ he]
  exact trace_exit_relative_ratio _ _ _ _ _ _ he
    (trace_stop_positive_of_trace hT D K hKD x e hx ξ hξ) hε hδ hδhalf hcond hterm

end SRWTightness
