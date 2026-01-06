import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Sumcheck.Spec.Testing

-- import Testing

noncomputable section
open Classical

namespace SumcheckTests

open Sumcheck

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

abbrev F := ZMod 17

/-- A 3-variate "polynomial" as a function `Fin 3 → F → F`: p(X,Y,Z)=2X+YZ. -/
def p3 : Sumcheck.func F 3 :=
  fun x => (2 : F) * x 0 + x 1 * x 2

def p5 : Sumcheck.func F 5 :=
  fun x => (2 : F) * x 0 + x 1 * x 2 * x 3 + 3 * x 4

/-- Helper: build a vector of length 2 from two scalars. -/
def v2 (x y : F) : Sumcheck.vec F 2 :=
  fun i => if i = 0 then x else y

/-- Helper: build a vector of length 3 from three scalars. -/
def v3 (x y z : F) : Sumcheck.vec F 3 :=
  fun i => if i = 0 then x else if i = 1 then y else z

-- Sanity check: direct evaluation of p3
example (x y z : F) : p3 (v3 x y z) = (2 : F) * x + y * z := by
  simp [p3, v3]


#check vecAppendHead (F := F) (n := 2)
#check p3
#check (funcSubstituteHeadSingle (F := F) (n := 2) p3 4)  -- should be 2*4 + 5*6 = 8 + 30 = 38 = 4 mod 17
#check (fun (v : vec F 1) => (2 : F) * 3 + 4 * v 0)  -- should be 2*3 + 4*v0 = 6 + 4*v0



-- Test: substitute the head variable X := r in p(X,Y,Z)
-- Result should be (2r + YZ) as a function in 2 variables.
example (r : F) :
  funcSubstituteHeadSingle (F := F) p3 r
    = fun v => (2 : F) * r + v 0 * v 1 := by
  funext v
  simp [p3, funcSubstituteHeadSingle, vecAppendHead]



example (r : F) :
  funcSubstituteHeadSingle (F := F) p3 r
    = fun v => (2 : F) * r + v 0 * v 1 := by
  funext v
  unfold funcSubstituteHeadSingle
  unfold p3
  unfold vecAppendHead
  rfl


example (r : F) :
  funcSubstituteHeadSingle (F := F) p3 r
    = fun v => (2 : F) * r + v 0 * v 1 := by
  funext v
  unfold funcSubstituteHeadSingle
  unfold p3

  -- Reduce vecAppendHead applications one by one
  change
    (2 : F) * (vecAppendHead 2 r v 0)
      + (vecAppendHead 2 r v 1) * (vecAppendHead 2 r v 2)
      =
      (2 : F) * r + v 0 * v 1

  -- Now reduce each application by computation
  unfold vecAppendHead
  rfl

example (r0 r1 : F) :
  funcSubstituteHeadLong (F := F) (n := 1) (k := 2) p3 (v2 r0 r1)
    = (fun (v : vec F 1) => (2 : F) * r0 + r1 * v 0) := by
  funext v
  unfold funcSubstituteHeadLong
  unfold funcSubstituteHeadSingle
  unfold p3
  unfold vecAppendHead
  rfl

example (r0 r1 : F) :
  funcSubstituteHeadLong (F := F) (n := 1) (k := 2) p3 (v2 r0 r1)
    = (fun (v : vec F 1) => (2 : F) * r0 + r1 * v 0) := by
  funext v
  simp [funcSubstituteHeadLong, funcSubstituteHeadSingle, p3, vecAppendHead]
  rfl

example :
  funcSumTailSingle (F := F) (n := 2) p3
    = fun v => 4 * v 0 + v 1 := by
  funext v
  unfold funcSumTailSingle
  unfold p3
  unfold vecAppendTail
  simp
  ring

set_option trace.Meta.Tactic.simp true

example :
  funcSumTailLong (F := F) (n := 1) (k := 2) p3
    = fun v => (8 : F) * v 0 + (1 : F) := by
  funext v
  unfold funcSumTailLong
  unfold funcSumTailLong
  unfold funcSumTailLong
  unfold funcSumTailSingle
  unfold castFinVecAddZero
  unfold p3
  unfold vecAppendTail
  unfold castFinAddZero
  simp
  ring


example :
  funcSumTailLong (F := F) (n := 1) (k := 2) p3
    = fun v => (8 : F) * v 0 + (1 : F) := by
  funext v
  -- this should recursively reduce k=2 → k=1 → k=0 automatically
  simp [funcSumTailLong, funcSumTailSingle, p3, vecAppendTail, castFinVecAddZero, castFinAddZero]
  ring

example (r0 r1 : F) :
  funcSubstituteHeadLong (F := F) (n := 1) (k := 2)
  (funcSumTailLong (F := F) (n := 3) (k := 2) p5) (v2 r0 r1)
    = fun v => (8 : F) * r0 + (2 : F) * r1 * v 0 + 6 := by
  funext v
  -- this should recursively reduce k=2 → k=1 → k=0 automatically
  simp [
    funcSumTailLong,
    funcSumTailSingle,
    vecAppendTail,
    castFinVecAddZero,
    castFinAddZero,
    p5,
    funcSubstituteHeadLong,
    funcSubstituteHeadSingle,
    vecAppendHead,
    v2]
  ring

example (r0 r1 : F) :
  funcSumTailLong (F := F) (n := 1) (k := 2)
  (funcSubstituteHeadLong (F := F) (n := 3) (k := 2) p5 (v2 r0 r1))
    = fun v => (8 : F) * r0 + (2 : F) * r1 * v 0 + 6 := by
  funext v
  simp [
    funcSumTailLong,
    funcSumTailSingle,
    vecAppendTail,
    castFinVecAddZero,
    castFinAddZero,
    p5,
    funcSubstituteHeadLong,
    funcSubstituteHeadSingle,
    vecAppendHead,
    v2]
  ring

example (r0 r1 : F) :
  funcSumTailLong (F := F) (n := 1) (k := 2)
  (funcSubstituteHeadLong (F := F) (n := 3) (k := 2) p5 (v2 r0 r1))
    =
  funcSubstituteHeadLong (F := F) (n := 1) (k := 2)
  (funcSumTailLong (F := F) (n := 3) (k := 2) p5) (v2 r0 r1) := by
  funext v
  simp [
    funcSumTailLong,
    funcSumTailSingle,
    vecAppendTail,
    castFinVecAddZero,
    castFinAddZero,
    p5,
    funcSubstituteHeadLong,
    funcSubstituteHeadSingle,
    vecAppendHead,
    v2]

end SumcheckTests
