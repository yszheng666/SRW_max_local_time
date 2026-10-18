import SRWTightness.DomainFirstStep
import SRWTightness.KilledGreen

namespace SRWTightness

 theorem domainSteps_first_step (D : Finset Site) (x : Site) (hx : x ∈ D) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) :
    domainSteps D x ω = 1 + domainSteps D (x + step (ω 0)) (shift 1 ω) := by
  have he : domainExit D (x + step (ω 0)) (shift 1 ω) ≠ ⊤ := by
    rw [domainExit_first_step D x hx ω] at hfin
    exact (WithTop.add_ne_top.mp hfin).2
  suffices hh : (domainSteps D x ω : WithTop ℕ) =
      (1 : WithTop ℕ) + (domainSteps D (x + step (ω 0)) (shift 1 ω) : WithTop ℕ) by
    exact WithTop.coe_inj.mp hh
  rw [coe_domainSteps D x ω hfin, coe_domainSteps D _ _ he]
  exact domainExit_first_step D x hx ω

 theorem localTime_one_translate (ω : Sample) (x y : Site) :
    localTime ω 1 (y - x) = if x = y then 1 else 0 := by
  rw [show 1 = 0 + 1 from rfl, localTime_succ]
  simp only [localTime_zero, position_zero_as_zero, zero_add]
  simp [eq_comm, sub_eq_zero]

 theorem domainLocalTime_first_step (D : Finset Site) (x y : Site) (hx : x ∈ D) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) :
    domainLocalTime D x y ω = (if x = y then 1 else 0) +
      domainLocalTime D (x + step (ω 0)) y (shift 1 ω) := by
  unfold domainLocalTime
  rw [domainSteps_first_step D x hx ω hfin, localTime_add,
    localTime_one_translate, position_one_as_step]
  rw [sub_add_eq_sub_sub]

 theorem domainLocalTime_zero_of_not_mem (D : Finset Site) (x y : Site) (hx : x ∉ D)
    (ω : Sample) : domainLocalTime D x y ω = 0 := by
  unfold domainLocalTime domainSteps
  rw [domainExit_eq_zero_of_not_mem D x hx ω]
  exact localTime_zero ω (y - x)

end SRWTightness
