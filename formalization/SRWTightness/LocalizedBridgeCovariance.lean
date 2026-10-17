import SRWTightness.LocalizedIntervalBridge

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem localizedIntervalBridge_gaussian (a b : ℝ) (hab : a < b) :
    IsGaussianProcess (localizedIntervalBridge a b) gaussianCoefficientLaw := by
  let f : ℝ → Set.Icc (0 : ℝ) (b - a) := fun v ↦
    ⟨max 0 (min (b - a) (v - a)), le_max_left _ _,
      max_le (by linarith) (min_le_left _ _)⟩
  exact (actualIntervalBridge_gaussian (b - a) (by linarith)).comp_right f

theorem localizedIntervalBridge_memLp (a b v : ℝ) (hab : a < b) :
    MemLp (localizedIntervalBridge a b v) 2 gaussianCoefficientLaw :=
  ((localizedIntervalBridge_gaussian a b hab).hasGaussianLaw_eval v).memLp_two

theorem localizedIntervalBridge_covariance_inside (a b s t : ℝ) (hab : a < b)
    (hs : a ≤ s) (hs' : s ≤ b) (ht : a ≤ t) (ht' : t ≤ b) :
    cov[localizedIntervalBridge a b s, localizedIntervalBridge a b t; gaussianCoefficientLaw] =
      min (s - a) (t - a) - (s - a) * (t - a) / (b - a) := by
  have he v hv hv' : localizedIntervalBridge a b v = actualIntervalBridge (b - a) (v - a) :=
    funext (localizedIntervalBridge_inside a b v hv hv')
  rw [he s hs hs', he t ht ht']
  exact actualIntervalBridge_covariance _ _ _ (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

theorem timeGridBridge_inside (T : ℕ → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k < n)
    (v : ℝ) (hl : T k ≤ v) (hu : v ≤ T (k + 1)) (ω : ℕ → GaussianCoefficientSpace) :
    timeGridBridge T n ω v = localizedIntervalBridge (T k) (T (k + 1)) v (ω k) := by
  unfold timeGridBridge
  apply Finset.sum_eq_single k
  · intro j hj hjk
    have hj' : j < n := Finset.mem_range.mp hj
    rcases lt_or_gt_of_ne hjk with h | h
    · exact localizedIntervalBridge_right _ _ _ (hgap j hj')
        ((timeGridTime_mono T n hgap (Nat.succ_le_of_lt h) (Nat.le_of_lt hk)).trans hl) _
    · exact localizedIntervalBridge_left _ _ _
        (hu.trans (timeGridTime_mono T n hgap (Nat.succ_le_of_lt h) (Nat.le_of_lt hj'))) _
  · intro h
    exact (h (Finset.mem_range.mpr hk)).elim

theorem independentLocalizedBridge_memLp (a b v : ℝ) (hab : a < b) (j : ℕ) :
    MemLp (fun ω : ℕ → GaussianCoefficientSpace ↦ localizedIntervalBridge a b v (ω j))
      2 (independentBridgeLaw ℕ) :=
  (localizedIntervalBridge_memLp a b v hab).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ gaussianCoefficientLaw) j)

theorem independentLocalizedBridge_covariance_ne (a b c d s t : ℝ)
    (hab : a < b) (hcd : c < d) (i j : ℕ) (hij : i ≠ j) :
    cov[fun ω : ℕ → GaussianCoefficientSpace ↦ localizedIntervalBridge a b s (ω i),
      fun ω ↦ localizedIntervalBridge c d t (ω j); independentBridgeLaw ℕ] = 0 := by
  have hind : iIndepFun (fun (j : ℕ) (ω : ℕ → GaussianCoefficientSpace) ↦ ω j)
      (independentBridgeLaw ℕ) :=
    iIndepFun_infinitePi (fun _ ↦ measurable_id)
  exact ((hind.indepFun hij).comp (localizedIntervalBridge_measurable a b s)
    (localizedIntervalBridge_measurable c d t)).covariance_eq_zero
      (independentLocalizedBridge_memLp a b s hab i)
      (independentLocalizedBridge_memLp c d t hcd j)

theorem independentLocalizedBridge_covariance_same (a b s t : ℝ)
    (hab : a < b) (hs : a ≤ s) (hs' : s ≤ b) (ht : a ≤ t) (ht' : t ≤ b) (j : ℕ) :
    cov[fun ω : ℕ → GaussianCoefficientSpace ↦ localizedIntervalBridge a b s (ω j),
      fun ω ↦ localizedIntervalBridge a b t (ω j); independentBridgeLaw ℕ] =
      min (s - a) (t - a) - (s - a) * (t - a) / (b - a) := by
  have hm : (independentBridgeLaw ℕ).map (fun ω ↦ ω j) = gaussianCoefficientLaw :=
    Measure.infinitePi_map_eval _ j
  have hc := covariance_map_fun (μ := independentBridgeLaw ℕ)
    (Z := fun ω ↦ ω j)
    (localizedIntervalBridge_measurable a b s).aestronglyMeasurable
    (localizedIntervalBridge_measurable a b t).aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable
  rw [hm] at hc
  rw [← hc]
  exact localizedIntervalBridge_covariance_inside a b s t hab hs hs' ht ht'

theorem timeGridBridge_covariance_same (T : ℕ → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k < n) (s t : ℝ)
    (hs : T k ≤ s) (hs' : s ≤ T (k + 1)) (ht : T k ≤ t) (ht' : t ≤ T (k + 1)) :
    cov[fun ω ↦ timeGridBridge T n ω s, fun ω ↦ timeGridBridge T n ω t;
      independentBridgeLaw ℕ] =
      min (s - T k) (t - T k) - (s - T k) * (t - T k) / (T (k + 1) - T k) := by
  have he v hv hv' : (fun ω ↦ timeGridBridge T n ω v) =
      (fun ω ↦ localizedIntervalBridge (T k) (T (k + 1)) v (ω k)) :=
    funext (timeGridBridge_inside T n k hgap hk v hv hv')
  rw [he s hs hs', he t ht ht']
  exact independentLocalizedBridge_covariance_same _ _ _ _ (hgap k hk) hs hs' ht ht' k

theorem timeGridBridge_covariance_ne (T : ℕ → ℝ) (n i j : ℕ)
    (hgap : ∀ k < n, T k < T (k + 1)) (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (s t : ℝ) (hs : T i ≤ s) (hs' : s ≤ T (i + 1))
    (ht : T j ≤ t) (ht' : t ≤ T (j + 1)) :
    cov[fun ω ↦ timeGridBridge T n ω s, fun ω ↦ timeGridBridge T n ω t;
      independentBridgeLaw ℕ] = 0 := by
  have hsfun := funext (timeGridBridge_inside T n i hgap hi s hs hs')
  have htfun := funext (timeGridBridge_inside T n j hgap hj t ht ht')
  rw [hsfun, htfun]
  exact independentLocalizedBridge_covariance_ne _ _ _ _ s t (hgap i hi) (hgap j hj) i j hij

end SRWTightness
