namespace Lookup

universe u
variable {F : Type u} [Field F]

class MLPCS (n : ℕ) where
  Comm : Type
  commit : (func F n) → Comm
  openEval : (f : func F n) → (r : vec F n) → F → Prop
  -- later: soundness axioms for openEval, batching, etc.

end Lookup
