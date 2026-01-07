import SumCheck.Spec.evalAndSum

noncomputable section
open Classical
open SumCheck

namespace SumCheck

universe u
variable {F : Type u} [Field F]

/-- The unique vector of length 0. -/
def vecNil : vec F 0 := fun i => Fin.elim0 i

/-- “Sum over all variables ∈ {0,1}” as a scalar. This is `funcSumTailLong` down to arity 0. -/
def fullSum (n : ℕ) (p : func F n) : F :=
  (funcSumTailLong (F := F) (n := 0) (k := n) p) vecNil

/-- Honest prover’s *round polynomial* for the first variable:
    g(x) = Σ_{b∈{0,1}^n} p(x,b).  Written using your primitives. -/
def roundPoly (n : ℕ) (p : func F (1 + n)) : F → F :=
  fun x => fullSum (F := F) n (funcSubstituteHeadSingle (F := F) (n := n) x p)

/-- **One-round completeness check**:
    g(0)+g(1) = Σ_{b∈{0,1}^{1+n}} p(b).

    This is the exact verifier check in the first round of sum-check.
-/
theorem sumcheck_step_complete
  (n : ℕ) (p : func F (1 + n)) :
  roundPoly (F := F) n p 0 + roundPoly (F := F) n p 1 = fullSum (F := F) (1 + n) p := by
  -- expand definitions
  unfold roundPoly fullSum

  -- Now unfold `funcSumTailLong` at k = (1+n) and k = n as needed.
  -- The key is that summing all (1+n) vars is “sum last n after splitting off head”.
  --
  -- `funcSumTailLong` does the tail-sum by repeated `funcSumTailSingle`.
  -- For k = 1+n, the first unfold produces a `funcSumTailSingle` at arity (n+1).
  --
  -- After unfolding, everything reduces by simp + rfl.
  --
  -- This proof is intentionally “definitional”: it uses your recursion equations.
  cases n with
  | zero =>
      -- n = 0:  p : func F (1+0) = func F 1
      -- roundPoly 0 p x = fullSum 0 (substitute x) = (substitute x) vecNil
      -- fullSum 1 p = p(vecAppendTail vecNil 0)+p(vecAppendTail vecNil 1)
      funext -- not needed but harmless if simp generates lambdas
      simp [funcSumTailLong, funcSumTailSingle, funcSubstituteHeadSingle,
            vecAppendHead, vecAppendTail, vecNil]
  | succ n =>
      -- n = n'+1
      -- unfold `funcSumTailLong` once on the RHS and twice on the LHS (inside fullSum n+1 etc)
      -- and let simp drive the definitional equalities.
      simp [funcSumTailLong, fullSum, funcSumTailSingle, funcSubstituteHeadSingle,
            vecNil]

/-!
## “Global invariant” used in the multi-round completeness proof

In the real protocol, after fixing some prefix variables to the verifier’s challenges,
the prover must send the next polynomial computed from that partially-fixed function.

Your already-proved theorem `sumTailLong_substHeadLong_comm` is the algebraic statement
that makes the invariant stable under “fix prefix” and “sum tail”.
-/

/-- A convenient corollary naming: prefix substitution commutes with tail summation. -/
theorem sumcheck_completeness_core
  (m n k : ℕ) :
  (fun (r : vec F m) (p : func F (m + n + k)) =>
      funcSumTailLong (F := F) (n := n) (k := k)
        (funcSubstituteHeadLong (F := F) (n := n + k) (m := m) r (funcAssoc m n k p)))
  =
  (fun (r : vec F m) (p : func F (m + n + k)) =>
      funcSubstituteHeadLong (F := F) (n := n) (m := m) r
        (funcSumTailLong (F := F) (n := m + n) (k := k) p)) := by
  simpa using (sumTailLong_substHeadLong_comm (F := F) m n k)

end SumCheck
