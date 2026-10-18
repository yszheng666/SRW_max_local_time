import SRWTightness.ActualChildBranching
import SRWTightness.PathWordSlice

namespace SRWTightness

/-- A child slice ending at its true exit is exactly the killed word of the shifted actual walk. -/
theorem slice_killedPathWord_eq_child (D C : Finset Site) (x : Site) (ω : Sample)
    (a b : ℕ) (hb : b ≤ domainSteps D x ω)
    (he : b = a + domainSteps C (x + position ω a) (shift a ω)) :
    slicePathWord (killedPathWord D x ω) a b =
      killedPathWord C (x + position ω a) (shift a ω) := by
  subst b
  simp only [slicePathWord, killedPathWord]
  congr 1 <;> try simp only [Nat.add_sub_cancel_left, heq_eq_eq]
  apply (Fin.heq_fun_iff (Nat.add_sub_cancel_left a _)).mpr
  intro k
  have hk := k.isLt
  have hk' : a + (k : ℕ) < domainSteps D x ω := by omega
  simp [wordPath, killedPathWord, extendWord, shift, hk']

/-- The actual first-child mark uses the child-domain killed word with no change of law. -/
theorem first_child_word_eq_killed (D K C : Finset Site) (hCD : C ⊆ D)
    (x : Site) (ω : Sample) (hparent : domainExit D x ω ≠ ⊤) :
    let a := domainSteps (D \ K) x ω
    let b := a + domainSteps C (x + position ω a) (shift a ω)
    slicePathWord (killedPathWord D x ω) a b =
      killedPathWord C (x + position ω a) (shift a ω) := by
  dsimp only
  apply slice_killedPathWord_eq_child
  · have ha := (subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hparent).2
    exact (shifted_subdomain_exit_bounds D C hCD x ω hparent _ ha).2
  · rfl

end SRWTightness
