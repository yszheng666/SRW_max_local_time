import SRWTightness.ChainGeometry
import SRWTightness.StoppedMaximum

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Iterating strong Markov at successive exits gives the power bound for the whole prefix. -/
theorem prob_chain_max_lt_le_pow {R : ℝ} (hR : 0 ≤ R) (j k : ℕ) :
    pathLaw {ω | stoppedMax (exitChain R j) ω < k} ≤
      (pathLaw {ω | diskMax R ω < k}) ^ j := by
  induction j with
  | zero =>
    calc
      _ ≤ pathLaw Set.univ := measure_mono (Set.subset_univ _)
      _ = _ := by simp
  | succ j ih =>
    have hs : MeasurableSet[(exitChain_isStoppingTime R j).measurableSpace]
        {ω | stoppedMax (exitChain R j) ω < k} :=
      (measurable_stoppedMax _ (exitChain_isStoppingTime R j)) measurableSet_Iio
    have ht : MeasurableSet {ω | diskMax R ω < k} :=
      (measurable_diskMax R) measurableSet_Iio
    have hind := stopped_future_factorization _ (exitChain_isStoppingTime R j)
      (exitChain_ne_top_ae hR j) _ _ hs ht
    have hfin : ∀ᵐ ω ∂pathLaw, ∀ i, exitChain R i ω ≠ ⊤ :=
      ae_all_iff.mpr (exitChain_ne_top_ae hR)
    have hsub : {ω | stoppedMax (exitChain R (j + 1)) ω < k} ≤ᵐ[pathLaw]
        ({ω | stoppedMax (exitChain R j) ω < k} ∩
          (futureAt (exitChain R j)) ⁻¹' {ω | diskMax R ω < k} : Set Sample) := by
      filter_upwards [hfin] with ω hω
      intro hk
      change stoppedMax (exitChain R (j + 1)) ω < k at hk
      change stoppedMax (exitChain R j) ω < k ∧ diskMax R (futureAt (exitChain R j) ω) < k
      rw [stoppedMax_eq _ ω (hω (j + 1))] at hk
      change maxLocalTime ω (chainSteps R (j + 1) ω) < k at hk
      constructor
      · rw [stoppedMax_eq _ ω (hω j)]
        exact lt_of_le_of_lt (maxLocalTime_mono ω
          (chainSteps_mono R ω hω (Nat.le_succ j))) hk
      · have hb := shifted_max_le ω (chainSteps R j ω)
          (exitSteps R (shift (chainSteps R j ω) ω))
        rw [← chainSteps_succ R j ω (hω (j + 1))] at hb
        exact lt_of_le_of_lt hb hk
    calc
      _ ≤ _ := measure_mono_ae hsub
      _ = pathLaw {ω | stoppedMax (exitChain R j) ω < k} *
          pathLaw {ω | diskMax R ω < k} := hind
      _ ≤ (pathLaw {ω | diskMax R ω < k}) ^ j * pathLaw {ω | diskMax R ω < k} :=
        mul_le_mul_right' ih _
      _ = _ := (pow_succ _ _).symm

end SRWTightness
