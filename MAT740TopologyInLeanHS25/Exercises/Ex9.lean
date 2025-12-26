import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.Connectedness

open MyConnected

variable {X Y : Type*} [Topology X] [Topology Y]

theorem Disconnected_Prop : ¬(Connected Prop) := by
  rw [Connected]
  push_neg
  have cont_id : Cont (id : Prop → Prop) := Cont_id
  have non_const : ∀ b : Prop, ¬(Constant id b) := by
    sorry -- exercise
  use id

theorem Connected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
  : Connected X → Connected Y := by
    sorry -- exercise

theorem PathConnected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
  : PathConnected X → PathConnected Y := by
    sorry -- exercise
    /- Hints:
      - Use `Classical.choice` the get a witness of `Nonempty _`.
      - Use `constructor` to provide witness for `Nonempty _` -/
