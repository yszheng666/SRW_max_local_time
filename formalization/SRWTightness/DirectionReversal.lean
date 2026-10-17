import SRWTightness.Path

namespace SRWTightness

def reverseDirection (d : Direction) : Direction :=
  if d = 0 then 1 else if d = 1 then 0 else if d = 2 then 3 else 2

 theorem reverseDirection_involutive : Function.Involutive reverseDirection := by
  unfold Function.Involutive
  decide

 theorem step_reverseDirection (d : Direction) : step (reverseDirection d) = -step d := by
  revert d
  decide

 theorem step_injective : Function.Injective step := by
  unfold Function.Injective
  decide

 def directionReversal : Direction ≃ Direction where
  toFun := reverseDirection
  invFun := reverseDirection
  left_inv := reverseDirection_involutive
  right_inv := reverseDirection_involutive

end SRWTightness
