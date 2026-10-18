import SRWTightness.StoppedFuture
import SRWTightness.DiskObservable

open MeasureTheory ProbabilityTheory

namespace SRWTightness

set_option maxHeartbeats 1000000 in
theorem measurable_futureAt (τ : Sample → WithTop ℕ) (hτ : IsStoppingTime history τ) :
    Measurable (futureAt τ) := by
  have hm : Measurable (fun p : Sample × ℕ ↦ shift p.2 p.1) :=
    measurable_from_prod_countable_left (fun n ↦ measurable_shift n)
  exact hm.comp (measurable_id.prodMk (hτ.measurable'.untopD 0))

 theorem stopped_future_law (τ : Sample → WithTop ℕ) (hτ : IsStoppingTime history τ)
    (hfin : ∀ᵐ ω ∂pathLaw, τ ω ≠ ⊤) : pathLaw.map (futureAt τ) = pathLaw := by
  apply Measure.ext
  intro t ht
  rw [Measure.map_apply (measurable_futureAt τ hτ) ht]
  have h := stopped_future_factorization τ hτ hfin Set.univ t MeasurableSet.univ ht
  simpa using h

/-- The translated path after a disk exit has precisely the original SRW law. -/
theorem disk_exit_future_law {R : ℝ} (hR : 0 ≤ R) :
    pathLaw.map (futureAt (exitTime R)) = pathLaw :=
  stopped_future_law _ (exitTime_isStoppingTime R) (exitTime_ne_top_ae hR)

end SRWTightness
