import SRWTightness.ExitChain
import SRWTightness.ExitPathBound
import SRWTightness.GeometryTriangle

namespace SRWTightness

@[simp] theorem chainSteps_zero (R : ℝ) (ω : Sample) : chainSteps R 0 ω = 0 := rfl

 theorem chainSteps_succ (R : ℝ) (j : ℕ) (ω : Sample)
    (hnext : exitChain R (j + 1) ω ≠ ⊤) :
    chainSteps R (j + 1) ω = chainSteps R j ω +
      exitSteps R (shift (chainSteps R j ω) ω) := by
  have hi : exitChain R j ω ≠ ⊤ := (WithTop.add_ne_top.mp hnext).1
  have he : exitTime R (shift (chainSteps R j ω) ω) ≠ ⊤ := (WithTop.add_ne_top.mp hnext).2
  suffices hh : (chainSteps R (j + 1) ω : WithTop ℕ) =
      ((chainSteps R j ω + exitSteps R (shift (chainSteps R j ω) ω) : ℕ) : WithTop ℕ) by
    exact WithTop.coe_inj.mp hh
  change (chainSteps R (j + 1) ω : WithTop ℕ) =
    (chainSteps R j ω : WithTop ℕ) + (exitSteps R (shift (chainSteps R j ω) ω) : WithTop ℕ)
  rw [coe_chainSteps R (j + 1) ω hnext,
    coe_chainSteps R j ω hi, coe_exitSteps R _ he]
  rfl

 theorem chainSteps_mono (R : ℝ) (ω : Sample) (hfin : ∀ j, exitChain R j ω ≠ ⊤) :
    Monotone (fun j ↦ chainSteps R j ω) := by
  intro i j hij
  suffices hh : (chainSteps R i ω : WithTop ℕ) ≤ chainSteps R j ω by
    exact WithTop.coe_le_coe.mp hh
  rw [coe_chainSteps R i ω (hfin i), coe_chainSteps R j ω (hfin j)]
  exact exitChain_mono R ω hij

/-- Every point of the first j killed segments lies within radius j(R+1). -/
theorem normSq_up_to_chainSteps {R : ℝ} (hR : 0 ≤ R) (ω : Sample)
    (hfin : ∀ j, exitChain R j ω ≠ ⊤) (j : ℕ) :
    ∀ k ≤ chainSteps R j ω, normSq (position ω k) ≤ ((j : ℝ) * (R + 1)) ^ 2 := by
  induction j with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by simpa using hk
    simp [hk0, position, normSq]
  | succ j ih =>
    intro k hk
    have hp := ih (chainSteps R j ω) le_rfl
    by_cases hle : k ≤ chainSteps R j ω
    · have hb := ih k hle
      have hjb : 0 ≤ (j : ℝ) * (R + 1) :=
        mul_nonneg (Nat.cast_nonneg j) (by linarith)
      have hmono : (j : ℝ) * (R + 1) ≤ ((j + 1 : ℕ) : ℝ) * (R + 1) := by
        push_cast
        nlinarith
      exact hb.trans ((sq_le_sq₀ hjb (hjb.trans hmono)).mpr hmono)
    · have hstart : chainSteps R j ω ≤ k := Nat.le_of_lt (lt_of_not_ge hle)
      have he : exitTime R (shift (chainSteps R j ω) ω) ≠ ⊤ :=
        (WithTop.add_ne_top.mp (hfin (j + 1))).2
      have hk' : k - chainSteps R j ω ≤ exitSteps R (shift (chainSteps R j ω) ω) := by
        rw [chainSteps_succ R j ω (hfin (j + 1))] at hk
        omega
      have hb := normSq_up_to_exitSteps hR _ he _ hk'
      have ht := normSq_add_bound (position ω (chainSteps R j ω))
        (position (shift (chainSteps R j ω) ω) (k - chainSteps R j ω))
        (mul_nonneg (Nat.cast_nonneg j) (by linarith : 0 ≤ R + 1))
        (by linarith : 0 ≤ R + 1) hp hb
      rw [← position_add, Nat.add_sub_of_le hstart] at ht
      convert ht using 1 <;> push_cast <;> ring

end SRWTightness
