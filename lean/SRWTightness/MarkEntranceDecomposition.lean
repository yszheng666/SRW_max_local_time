import SRWTightness.MarkTest
import SRWTightness.EntranceAtomGreen
import SRWTightness.MaximumPrinciple

open MeasureTheory

namespace SRWTightness

/-- A payoff vanishing outside the parent domain decomposes over actual entrance atoms. -/
theorem punctured_exit_payoff_entrance_sum (D K : Finset Site) (f : Site → ℝ)
    (hf : ∀ y, y ∉ D → f y = 0) (x : Site) :
    exitPayoff (D \ K) f x = ∑ v ∈ K, (competingEntranceLaw D K x).real {v} * f v := by
  classical
  let g : Site → ℝ := fun y ↦ ∑ v ∈ K, f v * (if y = v then 1 else 0)
  have hb (y : Site) (hy : y ∉ D \ K) : f y = g y := by
    by_cases hyK : y ∈ K
    · simp [g, mul_ite, hyK, eq_comm]
    · have hyD : y ∉ D := fun h ↦ hy (Finset.mem_sdiff.mpr ⟨h, hyK⟩)
      have hn (v : Site) (hv : v ∈ K) : y ≠ v := fun h ↦ hyK (h ▸ hv)
      rw [hf y hyD]
      dsimp [g]
      symm
      apply Finset.sum_eq_zero
      intro v hv
      simp [hn v hv]
  have he : exitPayoff (D \ K) f x = exitPayoff (D \ K) g x :=
    le_antisymm (exitPayoff_mono_on_compl _ f g (fun y hy ↦ (hb y hy).le) x)
      (exitPayoff_mono_on_compl _ g f (fun y hy ↦ (hb y hy).ge) x)
  rw [he]
  change (∫ ω, ∑ v ∈ K, f v * (if domainExitLocation (D \ K) x ω = v then 1 else 0) ∂pathLaw) = _
  rw [integral_finset_sum K (fun v _ ↦
    (integrable_domainExit_payoff (D \ K) x (fun y ↦ if y = v then 1 else 0)).const_mul (f v))]
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_const_mul, competingEntranceLaw_atom_payoff D K x v hv]
  exact mul_comm _ _

/-- The complete actual occupation mark decomposes after first entrance, with the zero mark centered. -/
theorem markTestExpectation_entrance_decomposition (D K : Finset Site) (F : Mark K → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ Y, ‖F Y‖ ≤ C) (x : Site) :
    markTestExpectation D K F x - F 0 =
      ∑ v ∈ K, (competingEntranceLaw D K x).real {v} * (markTestExpectation D K F v - F 0) := by
  rw [harmonic_eq_exitPayoff (D \ K) (fun y ↦ markTestExpectation D K F y - F 0)
    (fun y hy ↦ centered_markTest_harmonic D K F hF C hC y
      (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2) x]
  apply punctured_exit_payoff_entrance_sum
  intro y hy
  rw [markTestExpectation_eq_of_not_mem D K F y hy, sub_self]

end SRWTightness
