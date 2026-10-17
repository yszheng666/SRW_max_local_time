import SRWTightness.ExternalMarkedGWForestJoint

namespace SRWTightness

/-- The population record of a singleton forest is exactly its original single-tree record. -/
theorem forest_population_list_singleton {M : Type*} (n : ℕ)
    (r : FiniteExcursionRecord M n) :
    forestPopulationList n [r] = finiteRecordPopulationList n r := by
  simp [forestPopulationList, forestLevelPopulation, finiteRecordPopulationList]

end SRWTightness
