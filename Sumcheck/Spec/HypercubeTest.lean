import Sumcheck.Spec.Hypercube
import Mathlib.Data.ZMod.Basic   -- ZMod
import Mathlib.Tactic            -- native_decide (удобно для вычислений в proofs)

open scoped BigOperators

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

#eval
  hypercubeSum
    (F := ZMod 17)
    (n := 2)
    (fun v => v 0 + v 1)
