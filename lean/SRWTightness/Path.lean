import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.SplitIfs

namespace SRWTightness

abbrev Site := ℤ × ℤ
abbrev Direction := Fin 4
abbrev Sample := ℕ → Direction

def step (d : Direction) : Site :=
  if d = 0 then (1, 0) else if d = 1 then (-1, 0)
  else if d = 2 then (0, 1) else (0, -1)

def position (ω : Sample) : ℕ → Site
  | 0 => (0, 0)
  | n + 1 => position ω n + step (ω n)

/-- Visits on the half-open interval [0,n), as in source equation (1.1). -/
def localTime (ω : Sample) (n : ℕ) (x : Site) : ℕ :=
  ∑ k ∈ Finset.range n, if position ω k = x then 1 else 0

/-- The finite range contains every site with positive local time. -/
def visited (ω : Sample) (n : ℕ) : Finset Site :=
  (Finset.range n).image (position ω)

/-- Maximum over all lattice sites, computed on the finite visited range. -/
def maxLocalTime (ω : Sample) (n : ℕ) : ℕ :=
  (visited ω n).sup (localTime ω n)

@[simp] theorem localTime_zero (ω : Sample) (x : Site) : localTime ω 0 x = 0 := by
  simp [localTime]

 theorem localTime_succ (ω : Sample) (n : ℕ) (x : Site) :
    localTime ω (n + 1) x = localTime ω n x +
      (if position ω n = x then 1 else 0) := by
  simp [localTime, Finset.sum_range_succ]

 theorem localTime_le_time (ω : Sample) (n : ℕ) (x : Site) :
    localTime ω n x ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [localTime_succ]
    split_ifs <;> omega

 theorem localTime_mono (ω : Sample) {n m : ℕ} (h : n ≤ m) (x : Site) :
    localTime ω n x ≤ localTime ω m x := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m h ih =>
    rw [localTime_succ]
    omega

 theorem localTime_eq_zero_of_not_mem (ω : Sample) (n : ℕ) (x : Site)
    (h : x ∉ visited ω n) : localTime ω n x = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hx : position ω k ≠ x := by
    intro he
    apply h
    exact Finset.mem_image.mpr ⟨k, hk, he⟩
  simp [hx]

 theorem localTime_le_max (ω : Sample) (n : ℕ) (x : Site) :
    localTime ω n x ≤ maxLocalTime ω n := by
  by_cases h : x ∈ visited ω n
  · exact Finset.le_sup h
  · rw [localTime_eq_zero_of_not_mem ω n x h]
    exact Nat.zero_le _

 theorem maxLocalTime_le_time (ω : Sample) (n : ℕ) : maxLocalTime ω n ≤ n := by
  apply Finset.sup_le
  intro x hx
  exact localTime_le_time ω n x

 theorem maxLocalTime_mono (ω : Sample) {n m : ℕ} (h : n ≤ m) :
    maxLocalTime ω n ≤ maxLocalTime ω m := by
  apply Finset.sup_le
  intro x hx
  exact (localTime_mono ω h x).trans (localTime_le_max ω m x)

/-- Adding the endpoint changes the unrestricted maximum by at most one. -/
theorem maxLocalTime_succ_le (ω : Sample) (n : ℕ) :
    maxLocalTime ω (n + 1) ≤ maxLocalTime ω n + 1 := by
  apply Finset.sup_le
  intro x hx
  have h := localTime_le_max ω n x
  rw [localTime_succ]
  split_ifs <;> omega

/-- The inclusive endpoint convention agrees exactly with the next half-open interval. -/
def inclusiveMaxLocalTime (ω : Sample) (n : ℕ) : ℕ :=
  (visited ω (n + 1)).sup
    (fun x ↦ ∑ k ∈ Finset.range (n + 1), if position ω k = x then 1 else 0)

theorem inclusiveMaxLocalTime_eq (ω : Sample) (n : ℕ) :
    inclusiveMaxLocalTime ω n = maxLocalTime ω (n + 1) := rfl

/-- Positions up to time n depend only on the first n directions. -/
theorem position_congr (ω ω' : Sample) (n : ℕ)
    (h : ∀ k < n, ω k = ω' k) : position ω n = position ω' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [position]
    rw [ih (fun k hk ↦ h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

 theorem localTime_congr (ω ω' : Sample) (n : ℕ)
    (h : ∀ k < n, ω k = ω' k) (x : Site) : localTime ω n x = localTime ω' n x := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [position_congr ω ω' k (fun j hj ↦ h j (hj.trans (Finset.mem_range.mp hk)))]

 theorem maxLocalTime_congr (ω ω' : Sample) (n : ℕ)
    (h : ∀ k < n, ω k = ω' k) : maxLocalTime ω n = maxLocalTime ω' n := by
  have hv : visited ω n = visited ω' n := by
    apply Finset.image_congr
    intro k hk
    exact position_congr ω ω' k (fun j hj ↦ h j (hj.trans (Finset.mem_range.mp hk)))
  unfold maxLocalTime
  rw [hv]
  congr 1
  funext x
  exact localTime_congr ω ω' n h x

theorem position_eq_sum (ω : Sample) (n : ℕ) :
    position ω n = ∑ k ∈ Finset.range n, step (ω k) := by
  induction n with
  | zero => simp [position]
  | succ n ih => simp [position, Finset.sum_range_succ, ih]

end SRWTightness
