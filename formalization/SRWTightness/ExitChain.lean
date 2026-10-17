import SRWTightness.ConcatenatedStop
import SRWTightness.StoppedFutureLaw

open MeasureTheory

namespace SRWTightness

/-- Successive exits from disks centered at the current position, source (10.1). -/
noncomputable def exitChain (R : ℝ) : ℕ → Sample → WithTop ℕ
  | 0 => fun _ ↦ 0
  | j + 1 => concatenatedStop (exitChain R j) (exitTime R)

 theorem exitChain_isStoppingTime (R : ℝ) (j : ℕ) :
    IsStoppingTime history (exitChain R j) := by
  induction j with
  | zero => exact isStoppingTime_const history 0
  | succ j ih => exact concatenatedStop_isStoppingTime _ _ ih (exitTime_isStoppingTime R)

 theorem exitChain_ne_top_ae {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    ∀ᵐ ω ∂pathLaw, exitChain R j ω ≠ ⊤ := by
  induction j with
  | zero => exact Filter.Eventually.of_forall (fun _ ↦ WithTop.coe_ne_top)
  | succ j ih =>
    have hmap : ∀ᵐ ω ∂pathLaw.map (futureAt (exitChain R j)), exitTime R ω ≠ ⊤ := by
      rw [stopped_future_law _ (exitChain_isStoppingTime R j) ih]
      exact exitTime_ne_top_ae hR
    have hf := ae_of_ae_map (measurable_futureAt _ (exitChain_isStoppingTime R j)).aemeasurable hmap
    filter_upwards [ih, hf] with ω hi he
    exact WithTop.add_ne_top.mpr ⟨hi, he⟩

 theorem exitChain_future_law {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    pathLaw.map (futureAt (exitChain R j)) = pathLaw :=
  stopped_future_law _ (exitChain_isStoppingTime R j) (exitChain_ne_top_ae hR j)

 theorem exitChain_le_succ (R : ℝ) (j : ℕ) (ω : Sample) :
    exitChain R j ω ≤ exitChain R (j + 1) ω :=
  le_add_of_nonneg_right (show 0 ≤ exitTime R (futureAt (exitChain R j) ω) from bot_le)

 theorem exitChain_mono (R : ℝ) (ω : Sample) : Monotone (fun j ↦ exitChain R j ω) :=
  monotone_nat_of_le_succ (fun j ↦ exitChain_le_succ R j ω)

noncomputable def chainSteps (R : ℝ) (j : ℕ) (ω : Sample) : ℕ :=
  (exitChain R j ω).untopD 0

 theorem coe_chainSteps (R : ℝ) (j : ℕ) (ω : Sample) (h : exitChain R j ω ≠ ⊤) :
    (chainSteps R j ω : WithTop ℕ) = exitChain R j ω := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp h
  unfold chainSteps
  rw [← hk]
  rfl

end SRWTightness
