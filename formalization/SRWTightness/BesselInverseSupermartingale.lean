import SRWTightness.BesselInversePastEvent
import SRWTightness.BesselPastFiltration
import Mathlib.Probability.Martingale.Basic

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual inverse Bessel radius is a supermartingale on every positive nondecreasing grid. -/
theorem bessel_inverse_supermartingale (T x : ℝ) (hT : 0 < T) (hx : 0 < x)
    (q : ℕ → ℝ) (hq : Monotone q) (hpos : ∀ n, 0 < q n) (hupper : ∀ n, q n ≤ T) :
    Supermartingale (fun n ω ↦ (actualBesselThree T x (q n) ω)⁻¹)
      (besselPastFiltration T q hq) (independentBridgeLaw (Fin 3)) := by
  apply supermartingale_of_setIntegral_succ_le
    (bessel_inverse_stronglyAdapted T x q hq (fun n ↦ (hpos n).le))
    (fun n ↦ (bessel_three_inverse_moment_input_internal.2 T x (q n)
      hT hx (hpos n) (hupper n)).1)
  intro n A hA
  rcases eq_or_lt_of_le (hq (Nat.le_succ n)) with he | ht
  · rw [← he]
  · change MeasurableSet[MeasurableSpace.comap (besselPast T (q n)) inferInstance] A at hA
    obtain ⟨B, hB, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
    rw [← hpre]
    exact bessel_inverse_past_event_le T x (q n) (q (n + 1)) hT hx (hpos n) ht
      (hupper (n + 1)) B hB

end SRWTightness
