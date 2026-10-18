import SRWTightness.FutureIndependence

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

noncomputable def futureAt (τ : Sample → WithTop ℕ) (ω : Sample) : Sample :=
  shift ((τ ω).untopD 0) ω

 theorem futureAt_eq (τ : Sample → WithTop ℕ) (ω : Sample) (n : ℕ)
    (h : τ ω = n) : futureAt τ ω = shift n ω := by
  unfold futureAt
  rw [h]
  rfl

/-- Strong Markov factorization for the entire future path, at any a.s. finite stopping time. -/
theorem stopped_future_factorization (τ : Sample → WithTop ℕ)
    (hτ : IsStoppingTime history τ) (hfin : ∀ᵐ ω ∂pathLaw, τ ω ≠ ⊤)
    (s t : Set Sample) (hs : MeasurableSet[hτ.measurableSpace] s) (ht : MeasurableSet t) :
    pathLaw (s ∩ (futureAt τ) ⁻¹' t) = pathLaw s * pathLaw t := by
  let u : ℕ → Set Sample := fun n ↦ s ∩ {ω | τ ω = n}
  have hu : ∀ n, MeasurableSet[history n] (u n) := fun n ↦
    (hτ.measurableSet_inter_eq_iff s n).mp (hs.inter (hτ.measurableSet_eq' n))
  have hum : ∀ n, MeasurableSet (u n) := fun n ↦ (history.le n) _ (hu n)
  have hud : Pairwise (fun i j ↦ Disjoint (u i) (u j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (WithTop.coe_inj.mp (hi.2.symm.trans hj.2))
  have hvd : Pairwise (fun i j ↦ Disjoint (u i ∩ (shift i) ⁻¹' t) (u j ∩ (shift j) ⁻¹' t)) := by
    intro i j hij
    exact (hud hij).mono Set.inter_subset_left Set.inter_subset_left
  have hvm : ∀ n, MeasurableSet (u n ∩ (shift n) ⁻¹' t) :=
    fun n ↦ (hum n).inter ((measurable_shift n) ht)
  have hus : (⋃ n, u n) =ᵐ[pathLaw] s := by
    filter_upwards [hfin] with ω hω
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hω
    apply propext
    constructor
    · intro h
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
      exact hn.1
    · intro h
      exact Set.mem_iUnion.mpr ⟨k, h, hk.symm⟩
  have hvs : (⋃ n, u n ∩ (shift n) ⁻¹' t) =ᵐ[pathLaw]
      (s ∩ (futureAt τ) ⁻¹' t : Set Sample) := by
    filter_upwards [hfin] with ω hω
    apply propext
    constructor
    · intro h
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
      refine ⟨hn.1.1, ?_⟩
      change futureAt τ ω ∈ t
      rw [futureAt_eq τ ω n hn.1.2]
      exact hn.2
    · intro h
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hω
      refine Set.mem_iUnion.mpr ⟨k, ⟨h.1, hk.symm⟩, ?_⟩
      change shift k ω ∈ t
      rw [← futureAt_eq τ ω k hk.symm]
      exact h.2
  rw [← measure_congr hvs, measure_iUnion hvd hvm]
  simp_rw [measure_past_inter_future _ _ t (hu _) ht]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hud hum, measure_congr hus]

end SRWTightness
