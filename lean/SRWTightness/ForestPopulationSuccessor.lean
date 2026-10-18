import SRWTightness.ExternalMarkedGWForestJoint

set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.FiniteExcursionRecord SRWTightness.GeometricGWRecord

namespace SRWTightness

/-- The initial generation of an ordered forest counts each root exactly once. -/
theorem forest_level_population_roots {M : Type*} (n : ℕ)
    (rs : List (FiniteExcursionRecord M n)) : forestLevelPopulation n rs n = rs.length := by
  induction rs with
  | nil => simp [forestLevelPopulation]
  | cons r rs ih =>
    simp only [forestLevelPopulation, List.map_cons, List.sum_cons,
      finiteRecordLevelPopulation_root, List.length_cons] at ⊢ ih
    omega

/-- Every lower generation of a parent forest is the corresponding generation of its children. -/
theorem forest_level_population_successor {M : Type*} (n : ℕ)
    (rss : List (List (FiniteExcursionRecord M n))) (j : ℕ) (hj : j ≤ n) :
    forestLevelPopulation (n + 1) rss j = forestLevelPopulation n rss.flatten j := by
  have hne : j ≠ n + 1 := by omega
  simp only [forestLevelPopulation, finiteRecordLevelPopulation, if_neg hne,
    List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]

/-- Flattening one parent layer retains every population count and appends its root count. -/
theorem forest_population_list_successor {M : Type*} (n : ℕ)
    (rss : List (List (FiniteExcursionRecord M n))) :
    forestPopulationList (n + 1) rss = forestPopulationList n rss.flatten ++ [rss.length] := by
  unfold forestPopulationList
  rw [List.ofFn_succ']
  simp only [Fin.val_last, forest_level_population_roots, List.concat_eq_append]
  congr 1
  apply congrArg List.ofFn
  funext j
  exact forest_level_population_successor n rss j (by omega)

/-- Ordered terminal leaves commute with flattening the parent layer. -/
theorem forest_leaves_successor {M : Type*} (n : ℕ)
    (rss : List (List (FiniteExcursionRecord M n))) :
    rss.flatMap (finiteRecordLeaves (n + 1)) = rss.flatten.flatMap (finiteRecordLeaves n) := by
  simp only [finiteRecordLeaves]
  induction rss with
  | nil => rfl
  | cons rs rss ih => simp [ih]

end SRWTightness
