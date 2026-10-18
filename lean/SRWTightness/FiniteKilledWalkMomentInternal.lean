import SRWTightness.ExitDurationExponentialMoment

namespace SRWTightness

/-- The entire original finite killed-walk square-root moment input follows internally. -/
theorem finite_killed_walk_moment_input_internal : FiniteKilledWalkMomentInput :=
  integrable_exp_sqrt_domain_steps

end SRWTightness
