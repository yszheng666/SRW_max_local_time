import SRWTightness.RecordExitFuture
import SRWTightness.StoppedFutureLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open MeasureTheory

namespace SRWTightness

/-- Sum over actual exit positions while keeping each child record jointly coupled to its exit. -/
theorem killed_record_future_exit_sum {R : Type*} (D : Finset Site) (x : Site)
    (F : PathWord → R) (r : R) (t : Site → Set Sample) (ht : ∀ ξ, MeasurableSet (t ξ)) :
    pathLaw {ω | F (killedPathWord D x ω) = r ∧
      futureAt (domainExit D x) ω ∈ t (domainExitLocation D x ω)} =
      ∑' ξ, recordExitSlice D x (fun ω ↦ F (killedPathWord D x ω)) r {ξ} * pathLaw (t ξ) := by
  let E : Site → Set Sample := fun ξ ↦
    {ω | F (killedPathWord D x ω) = r ∧ domainExitLocation D x ω = ξ} ∩
      (futureAt (domainExit D x)) ⁻¹' t ξ
  have hF : MeasurableSet {ω | F (killedPathWord D x ω) = r} :=
    (measurable_killedPathWord D x) (Set.to_countable {w | F w = r}).measurableSet
  have hm : ∀ ξ, MeasurableSet (E ξ) := by
    intro ξ
    exact (hF.inter ((measurable_domainExitLocation D x) (measurableSet_singleton ξ))).inter
      ((measurable_futureAt (domainExit D x) (domainExit_isStoppingTime D x)) (ht ξ))
  have hd : Pairwise (fun ξ η ↦ Disjoint (E ξ) (E η)) := by
    intro ξ η hne
    apply Set.disjoint_left.mpr
    intro ω hξ hη
    exact hne (hξ.1.2.symm.trans hη.1.2)
  have he : (⋃ ξ, E ξ) = {ω | F (killedPathWord D x ω) = r ∧
      futureAt (domainExit D x) ω ∈ t (domainExitLocation D x ω)} := by
    ext ω
    constructor
    · intro h
      obtain ⟨ξ, hξ⟩ := Set.mem_iUnion.mp h
      refine ⟨hξ.1.1, ?_⟩
      rw [hξ.1.2]
      exact hξ.2
    · intro h
      exact Set.mem_iUnion.mpr ⟨domainExitLocation D x ω, ⟨h.1, rfl⟩, h.2⟩
  rw [← he, measure_iUnion hd hm]
  apply tsum_congr
  intro ξ
  exact killed_record_exit_future_factorization D x F r ξ (t ξ) (ht ξ)

/-- The child record/future probability is the integral against its actual joint exit slice S. -/
theorem killed_record_future_exit_integral {R : Type*} (D : Finset Site) (x : Site)
    (F : PathWord → R) (r : R) (t : Site → Set Sample) (ht : ∀ ξ, MeasurableSet (t ξ)) :
    pathLaw {ω | F (killedPathWord D x ω) = r ∧
      futureAt (domainExit D x) ω ∈ t (domainExitLocation D x ω)} =
      ∫⁻ ξ, pathLaw (t ξ) ∂recordExitSlice D x (fun ω ↦ F (killedPathWord D x ω)) r := by
  rw [killed_record_future_exit_sum D x F r t ht, lintegral_countable']
  apply tsum_congr
  intro ξ
  exact mul_comm _ _

end SRWTightness
