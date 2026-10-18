import SRWTightness.StoppedFuture
import SRWTightness.ShiftHistory

open MeasureTheory

namespace SRWTightness

noncomputable def concatenatedStop (τ η : Sample → WithTop ℕ) (ω : Sample) : WithTop ℕ :=
  τ ω + η (futureAt τ ω)

 theorem withTop_add_le_nat_iff (a b : WithTop ℕ) (n : ℕ) :
    a + b ≤ n ↔ ∃ k ≤ n, a = k ∧ b ≤ (n - k : ℕ) := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe i =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe j =>
      constructor
      · intro h
        have hnat : i + j ≤ n := WithTop.coe_le_coe.mp h
        refine ⟨i, by omega, rfl, ?_⟩
        exact WithTop.coe_le_coe.mpr (show j ≤ n - i by omega)
      · rintro ⟨k, hk, he, hle⟩
        have hik : i = k := WithTop.coe_inj.mp he
        have hj : j ≤ n - k := WithTop.coe_le_coe.mp hle
        exact WithTop.coe_le_coe.mpr (show i + j ≤ n by omega)

 theorem concatenatedStop_le_iff (τ η : Sample → WithTop ℕ) (ω : Sample) (n : ℕ) :
    concatenatedStop τ η ω ≤ n ↔
      ∃ k ≤ n, τ ω = k ∧ η (shift k ω) ≤ (n - k : ℕ) := by
  rw [concatenatedStop, withTop_add_le_nat_iff]
  constructor
  · rintro ⟨k, hk, hτ, hη⟩
    rw [futureAt_eq τ ω k hτ] at hη
    exact ⟨k, hk, hτ, hη⟩
  · rintro ⟨k, hk, hτ, hη⟩
    rw [← futureAt_eq τ ω k hτ] at hη
    exact ⟨k, hk, hτ, hη⟩

/-- A stopping rule can be restarted on the future path at a stopping time. -/
theorem concatenatedStop_isStoppingTime (τ η : Sample → WithTop ℕ)
    (hτ : IsStoppingTime history τ) (hη : IsStoppingTime history η) :
    IsStoppingTime history (concatenatedStop τ η) := by
  intro n
  letI : MeasurableSpace Sample := history n
  have he : {ω | concatenatedStop τ η ω ≤ n} =
      ⋃ k : {k : ℕ // k ≤ n}, {ω | τ ω = (k : ℕ)} ∩
        (shift k) ⁻¹' {ω | η ω ≤ (n - k : ℕ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    rw [concatenatedStop_le_iff]
    constructor
    · rintro ⟨k, hk, ht, he⟩
      exact ⟨⟨k, hk⟩, ht, he⟩
    · rintro ⟨k, ht, he⟩
      exact ⟨k, k.property, ht, he⟩
  have hm : MeasurableSet[history n] (⋃ k : {k : ℕ // k ≤ n},
      {ω | τ ω = (k : ℕ)} ∩ (shift k) ⁻¹' {ω | η ω ≤ (n - k : ℕ)}) := by
    apply MeasurableSet.iUnion
    intro k
    apply ((history.mono k.property) _ (hτ.measurableSet_eq k)).inter
    have hb := (measurable_shift_history k (n - k)) (hη (n - k))
    exact (history.mono (show (k : ℕ) + (n - k) ≤ n by omega)) _ hb
  exact he.symm ▸ hm

end SRWTightness
