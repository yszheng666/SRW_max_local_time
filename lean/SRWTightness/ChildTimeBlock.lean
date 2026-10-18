import SRWTightness.ChildRangeRenewal

namespace SRWTightness

/-- The inclusive entrance-to-exit observation block is exactly the translated local range. -/
theorem child_time_block (a b : ℕ) (hab : a < b) :
    (List.range (b - a + 1)).map (a + ·) =
      a :: (List.range' (a + 1) (b - a - 1) ++ [b]) := by
  rw [← List.range'_eq_map_range]
  have hn : a + (b - a + 1) = b + 1 := by omega
  have hr := List.range'_append_1 (s := 0) (m := a) (n := b - a + 1)
  simp only [Nat.zero_add, ← List.range_eq_range', hn] at hr
  have hs := child_time_range_split a b b hab le_rfl
  simp only [Nat.sub_self, List.range'_zero, List.append_nil] at hs
  exact List.append_cancel_left (hr.trans hs)

end SRWTightness
