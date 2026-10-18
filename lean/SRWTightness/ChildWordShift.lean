import SRWTightness.ChildKilledWord

namespace SRWTightness

/-- Slicing after renewal agrees exactly with shifting the parent killed path first. -/
theorem slice_killedPathWord_shift (D : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (b a c : ℕ) (hb : b ≤ domainSteps D x ω)
    (hc : c ≤ domainSteps D x ω - b) :
    slicePathWord (killedPathWord D x ω) (b + a) (b + c) =
      slicePathWord (killedPathWord D (x + position ω b) (shift b ω)) a c := by
  simp only [slicePathWord, killedPathWord]
  congr 1
  · omega
  · apply (Fin.heq_fun_iff (show b + c - (b + a) = c - a by omega)).mpr
    intro k
    have hk := k.isLt
    have hleft : b + (a + (k : ℕ)) < domainSteps D x ω := by omega
    have hright : a + (k : ℕ) < domainSteps D (x + position ω b) (shift b ω) := by
      rw [domainSteps_shift_before_exit D x ω hfin b hb]
      omega
    simp [wordPath, extendWord, shift, hleft, hright, Nat.add_assoc]

end SRWTightness
