import SRWTightness.GeometricGWLaw

open MeasureTheory

namespace SRWTightness

noncomputable def gwBarrierLine (a b : ℝ) (j L : ℕ) : ℝ :=
  a + (b - a) * (j : ℝ) / (L : ℝ)

noncomputable def gwBarrierCurvature (p : ℝ) (j L : ℕ) : ℝ :=
  (min (j : ℝ) ((L : ℝ) - j)) ^ p

/-- Upper barrier with a closed terminal window, as in Rosen Theorem 9.1(a). -/
def gwUpperBarrierEvent (L : ℕ) (a b y δ C ε : ℝ) : Set GeometricGWRecord :=
  {r | (∀ j : ℕ, 0 < j → j < L →
      geometricGWHeight r j ≤ gwBarrierLine a b j L + C * gwBarrierCurvature (1 / 2 - ε) j L) ∧
    geometricGWHeight r L ∈ Set.Icc y (y + δ)}

/-- Two-sided tube with the same closed terminal window. -/
def gwTubeEvent (L : ℕ) (x y a b δ C Ctilde ε : ℝ) : Set GeometricGWRecord :=
  {r | (∀ j : ℕ, 0 < j → j < L →
      geometricGWHeight r j ∈ Set.Icc
        (gwBarrierLine x y j L - Ctilde * gwBarrierCurvature (1 / 2 + ε) j L)
        (gwBarrierLine a b j L - C * gwBarrierCurvature (1 / 2 - ε) j L)) ∧
    geometricGWHeight r L ∈ Set.Icc y (y + δ)}

/-- Positive square-root population lattice intersects the given interval. -/
def gwPositiveLatticeIntersects (a b : ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Real.sqrt (2 * (n : ℝ)) ∈ Set.Icc a b

noncomputable def gwBarrierPrefactor (L : ℕ) (x y a b : ℝ) : ℝ :=
  ((1 + a - x) * (1 + b - y) / (L : ℝ)) *
    Real.exp (-((x - y) ^ 2 / (2 * (L : ℝ))))

/-- Explicit external input: Rosen, arXiv:2203.14394v1, Theorem 9.1(a). -/
def GWBarrierUpperInput : Prop :=
  ∀ δ C η ε : ℝ, 0 < δ → 0 ≤ C → 1 < η → 0 < ε → ε < 1 / 2 →
    ∃ K : ℝ, 0 < K ∧ ∀ (L k : ℕ) (a b y : ℝ), 0 < L → 0 < k →
      let x := Real.sqrt (2 * (k : ℝ))
      x ≤ η * L → Real.sqrt 2 ≤ y → y ≤ η * L → x ≤ a → y ≤ b →
      (geometricGWRecordLaw k L).real (gwUpperBarrierEvent L a b y δ C ε) ≤
        K * gwBarrierPrefactor L x y a b * Real.sqrt (x / (y * L))

/-- Explicit external input: Rosen Theorem 9.1(b), retaining both lattice conditions. -/
def GWBarrierLowerInput : Prop :=
  ∀ δ C Ctilde η ε : ℝ,
    0 < δ → 0 ≤ C → C < Ctilde → 1 < η → 0 < ε → ε < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧ ∀ (L k : ℕ) (a b y : ℝ), 0 < L → 0 < k →
      let x := Real.sqrt (2 * (k : ℝ))
      x ≤ η * L → Real.sqrt 2 ≤ y → y ≤ η * L → x ≤ a → y ≤ b →
      (1 + a - x) * (1 + b - y) ≤ η * L →
      (L : ℝ) / η ≤ max (x * y) |y - x| →
      gwPositiveLatticeIntersects y (y + δ) →
      (∀ j : ℕ, 0 < j → j < L → gwPositiveLatticeIntersects
        (gwBarrierLine x y j L - Ctilde * gwBarrierCurvature (1 / 2 + ε) j L)
        (gwBarrierLine a b j L - C * gwBarrierCurvature (1 / 2 - ε) j L)) →
      c * gwBarrierPrefactor L x y a b * min (Real.sqrt (x / (y * L))) 1 ≤
        (geometricGWRecordLaw k L).real (gwTubeEvent L x y a b δ C Ctilde ε)

theorem gwUpperBarrierEvent_measurable (L : ℕ) (a b y δ C ε : ℝ) :
    MeasurableSet (gwUpperBarrierEvent L a b y δ C ε) := Set.to_countable _ |>.measurableSet

theorem gwTubeEvent_measurable (L : ℕ) (x y a b δ C Ctilde ε : ℝ) :
    MeasurableSet (gwTubeEvent L x y a b δ C Ctilde ε) :=
  Set.to_countable _ |>.measurableSet

end SRWTightness
