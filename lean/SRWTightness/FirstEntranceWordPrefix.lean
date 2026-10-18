import SRWTightness.FirstEntranceWordMark
import SRWTightness.KilledWordPrefixCongruence
import SRWTightness.DomainStepsShift

namespace SRWTightness

/-- The first-entry ordered mark depends only on the increments before the finite parent exit. -/
theorem firstEntranceWordMark_eq_of_prefix (D K : Finset Site) (x : Site) (ω υ : Sample)
    (hfin : domainExit D x ω ≠ ⊤)
    (hω : ∀ i < domainSteps D x ω, ω i = υ i) :
    firstEntranceWordMark D K x ω = firstEntranceWordMark D K x υ := by
  let a := domainSteps (D \ K) x ω
  obtain ⟨hf, ha⟩ := subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hfin
  have hp (i : ℕ) (hi : i ≤ domainSteps D x ω) : position ω i = position υ i := by
    apply position_congr
    intro k hk
    exact hω k (hk.trans_le hi)
  have he := (domainSteps_eq_of_positions (D \ K) x ω υ hf
    (fun i hi ↦ hp i (hi.trans ha))).2
  have hl : domainExitLocation (D \ K) x ω = domainExitLocation (D \ K) x υ := by
    unfold domainExitLocation
    rw [← he, hp _ ha]
  have hfo : futureAt (domainExit (D \ K) x) ω = shift a ω := rfl
  have hfv : futureAt (domainExit (D \ K) x) υ = shift a υ := by
    change shift (domainSteps (D \ K) x υ) υ = shift a υ
    rw [← he]
  have hfuture := (shifted_subdomain_exit_bounds D D (Finset.Subset.refl D)
    x ω hfin a ha).1
  have hw : killedPathWord D (x + position ω a) (shift a ω) =
      killedPathWord D (x + position ω a) (shift a υ) := by
    apply killedPathWord_eq_of_prefix _ _ _ _ hfuture
    intro i hi
    rw [domainSteps_shift_before_exit D x ω hfin a ha] at hi
    exact hω (a + i) (by omega)
  have hmark : killedWordMark D (domainExitLocation (D \ K) x ω)
      (futureAt (domainExit (D \ K) x) ω) =
      killedWordMark D (domainExitLocation (D \ K) x υ)
        (futureAt (domainExit (D \ K) x) υ) := by
    rw [← hl, hfo, hfv]
    exact congrArg (fun w ↦ (some (x + position ω a, w) : WordMark)) hw
  by_cases hh : domainExitLocation (D \ K) x ω ∈ K
  · have hh' : domainExitLocation (D \ K) x υ ∈ K := hl ▸ hh
    simpa only [firstEntranceWordMark, if_pos hh, if_pos hh'] using hmark
  · have hh' : domainExitLocation (D \ K) x υ ∉ K := hl ▸ hh
    simp only [firstEntranceWordMark, if_neg hh, if_neg hh']

end SRWTightness
