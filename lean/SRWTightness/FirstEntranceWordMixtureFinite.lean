import SRWTightness.FirstEntranceWordMixture

open MeasureTheory
namespace SRWTightness

/-- The entrance/future integral is the finite mixture over actual entrance atoms. -/
theorem firstEntranceWordMark_mixture_sum (D K : Finset Site) (x : Site) (s : Set WordMark) :
    (∫⁻ y, killedWordMarkLaw D y s ∂competingEntranceLaw D K x) =
      ∑ y ∈ K, competingEntranceLaw D K x {y} * killedWordMarkLaw D y s := by
  rw [competingEntranceLaw, lintegral_finset]
  apply Finset.sum_congr rfl
  intro y hy
  simp [Measure.restrict_apply, hy, mul_comm]

/-- The actual first-entry-trimmed law is exactly its empty atom plus killed ordered futures. -/
theorem firstEntranceWordMarkLaw_eq (D K : Finset Site) (x : Site) :
    firstEntranceWordMarkLaw D K x =
      ENNReal.ofReal (competingExitMass D K x) • Measure.dirac none +
        ∑ y ∈ K, competingEntranceLaw D K x {y} • killedWordMarkLaw D y := by
  apply Measure.ext
  intro s hs
  rw [firstEntranceWordMarkLaw_event D K x s hs, firstEntranceWordMark_mixture_sum]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]

end SRWTightness
