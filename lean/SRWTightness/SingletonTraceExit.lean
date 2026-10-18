import SRWTightness.KilledTraceSupport
import SRWTightness.TraceStopRelative

open MeasureTheory
namespace SRWTightness

/-- For a singleton target, the terminal escape atom factors exactly by its exit probability. -/
theorem singleton_trace_stop_exit (hM : KilledExitDecompositionInput)
    (D : Finset Site) (b e : Site) (hb : b ∈ D) (he : e ∉ D) :
    traceStopExitProbability D {b} b e =
      traceExitProbability D b e * traceStopProbability D {b} b := by
  classical
  have hKD : ({b} : Finset Site) ⊆ D := by simpa using hb
  let s := traceExitProbability D b e
  have hU (y : Site) : traceExitProbability (D \ {b}) y e =
      traceExitProbability D y e - s * (1 - competingExitMass D {b} y) := by
    have hi : (∫ z, traceExitProbability D z e ∂competingEntranceLaw D {b} y) =
        s * (1 - competingExitMass D {b} y) := by
      have hc : (∫ z, traceExitProbability D z e ∂competingEntranceLaw D {b} y) =
          ∫ z, s ∂competingEntranceLaw D {b} y := by
        apply integral_congr_ae
        filter_upwards [competingEntranceLaw_supported D {b} y] with z hz
        have hz' : z = b := Finset.mem_singleton.mp hz
        subst z
        rfl
      rw [hc, integral_const, smul_eq_mul]
      have hm := competing_entrance_exit_mass D {b} y
      have hm' : (competingEntranceLaw D {b} y).real Set.univ =
          1 - competingExitMass D {b} y := by linarith
      rw [hm']
      ring
    have hh := hM.1 D {b} hKD y e he
    rw [hi] at hh
    linarith
  rw [hM.2.1 D {b} hKD b (by simp), hM.2.2 D {b} hKD b (by simp) e he]
  simp_rw [hU]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  norm_num only [Finset.sum_const, Finset.card_univ, Direction, Fintype.card_fin, nsmul_eq_mul]
  have hh := trace_exit_probability_harmonic D e b hb
  dsimp [s] at *
  nlinarith

/-- The full singleton trace is independent of the specified reachable exit atom. -/
theorem singleton_trace_conditional_ratio (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) (D : Finset Site) (b e : Site)
    (hb : b ∈ D) (he : e ∉ D) (hep : 0 < traceExitProbability D b e) (ξ : List Site)
    (hξ : 0 < pathLaw.real {ω | killedVisitTrace D {b} b ω = ξ}) :
    (pathLaw.real {ω | killedVisitTrace D {b} b ω = ξ ∧ domainExitLocation D b ω = e} /
      traceExitProbability D b e) / pathLaw.real {ω | killedVisitTrace D {b} b ω = ξ} = 1 := by
  classical
  have hKD : ({b} : Finset Site) ⊆ D := by simpa using hb
  have hlast : ξ.getLastD b = b := Finset.mem_singleton.mp
    (killed_trace_last_mem D {b} b (by simp) ξ hξ)
  have hq := trace_stop_positive_of_trace hT D {b} hKD b e (by simp) ξ hξ
  rw [hlast] at hq
  rw [killed_trace_conditional_ratio hT D {b} b e hKD (by simp) ξ hξ hep,
    hlast, singleton_trace_stop_exit hM D b e hb he]
  exact div_self (mul_pos hep hq).ne'

end SRWTightness
