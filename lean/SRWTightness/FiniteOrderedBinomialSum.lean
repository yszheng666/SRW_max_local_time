import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace SRWTightness

/-- Assigning a positive-size subset to its least time gives the exact ordered binomial sum. -/
theorem finset_sum_choose_greater_card (I : Finset ℕ) (p : ℕ) :
    (∑ n ∈ I, ((I.filter (fun k ↦ n < k)).card).choose p) = I.card.choose (p + 1) := by
  classical
  induction I using Finset.induction_on_min with
  | empty => simp
  | insert a s hmin ih =>
    have ha : a ∉ s := fun h ↦ (lt_irrefl a) (hmin a h)
    have hfirst : (insert a s).filter (fun k ↦ a < k) = s := by
      rw [Finset.filter_insert, if_neg (lt_irrefl a)]
      exact Finset.filter_eq_self.mpr hmin
    have hrest (n : ℕ) (hn : n ∈ s) :
        (insert a s).filter (fun k ↦ n < k) = s.filter (fun k ↦ n < k) := by
      rw [Finset.filter_insert, if_neg (not_lt_of_ge (hmin n hn).le)]
    calc
      _ = s.card.choose p + ∑ n ∈ s, ((s.filter (fun k ↦ n < k)).card).choose p := by
        rw [Finset.sum_insert ha, hfirst]
        congr 1
        exact Finset.sum_congr rfl (fun n hn ↦ by rw [hrest n hn])
      _ = s.card.choose p + s.card.choose (p + 1) := by rw [ih]
      _ = (s.card + 1).choose (p + 1) := (Nat.choose_succ_succ' s.card p).symm
      _ = _ := by rw [Finset.card_insert_of_notMem ha]

end SRWTightness
