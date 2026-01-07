import SumCheck.Spec.evalAndSum

noncomputable section
open Classical
open SumCheck

namespace SumCheck

universe u
variable {F : Type u} [Field F]

/-- The unique vector of length 0. -/
def vecNil : vec F 0 := fun i => Fin.elim0 i

/-- Sum of a boolean function over the full hypercube `{0,1}^n`.

This is defined purely in terms of your `funcSumTailLong` by summing all `n` variables,
reducing to arity `0`, and then evaluating at the unique `vec F 0`.
-/
def fullSum (n : ℕ) (p : func F n) : F :=
  (funcSumTailLong (F := F) (n := 0) (k := n) p) vecNil

/-- Partial evaluation (prefix assignment) followed by summation of the remaining tail.

`evalAndSum m k r p` means: fix the first `m` variables to `r`, then sum the last `k`
variables (where `p` has arity `m + k`).
-/
def evalAndSum (m k : ℕ) (r : vec F m) (p : func F (m + k)) : F :=
  fullSum (F := F) k (funcSubstituteHeadLong (F := F) (n := k) (m := m) r p)

/-!
# Soundness (algebraic consistency) lemmas

In a full interactive Sum-check protocol, *soundness* additionally relies on degree bounds.
This project (so far) models the core algebraic operators (substitution / summation) and
their commuting properties. The lemmas below capture the *algebraic consistency* part
that any sound verifier uses internally.
-/

/-- Unfolding lemma: `fullSum` is exactly tail-summing down to arity 0 and evaluating. -/
theorem fullSum_def (n : ℕ) (p : func F n) :
    fullSum (F := F) n p = (funcSumTailLong (F := F) (n := 0) (k := n) p) vecNil := by
  rfl

/-- Summing zero variables does nothing (as a scalar statement). -/
theorem fullSum_zero (p : func F 0) : fullSum (F := F) 0 p = p vecNil := by
  simp [fullSum, funcSumTailLong]

/-- One-step tail expansion at the scalar level:

`Σ_{b∈{0,1}^{n+1}} p(b) = Σ_{b∈{0,1}^n} p(b,0) + Σ_{b∈{0,1}^n} p(b,1)`.

This is the algebraic identity behind the verifier's `g(0)+g(1)` check.
-/
theorem fullSum_succ (n : ℕ) (p : func F (n + 1)) :
    fullSum (F := F) (n + 1) p =
      fullSum (F := F) n (fun xs => p (vecAppendTail n xs 0)) +
      fullSum (F := F) n (fun xs => p (vecAppendTail n xs 1)) := by
  -- unfold one step of `funcSumTailLong` at k = n+1, then unfold `funcSumTailSingle`
  -- and reduce by definitional equality.
  -- `Nat.add_succ` rewriting: n + Nat.succ k = (n + k) + 1 is built into your definition.
  -- Here we are at base `n := 0` for `fullSum`.
  induction n with
  | zero =>
      -- n = 0: p : func F (0+1)
      simp [fullSum, funcSumTailLong, funcSumTailSingle, vecNil, vecAppendTail]
  | succ n ih =>
      -- n = n+1
      -- simp can unfold the recursion one layer; the remaining structure follows by ih.
      simp [fullSum, funcSumTailLong, funcSumTailSingle, ih, Nat.add_assoc]

/-- **Core commutation / consistency lemma** used in soundness arguments:

Fixing a prefix (substitution) commutes with summing a suffix (tail-sum).

This is exactly your theorem `sumTailLong_substHeadLong_comm`, repackaged as a lemma.
-/
theorem sumTailLong_substHeadLong_comm_sound
  (m n k : ℕ) :
  (fun (r : vec F m) (p : func F (m + n + k)) =>
      funcSumTailLong (F := F) (n := n) (k := k)
        (funcSubstituteHeadLong (F := F) (n := n + k) (m := m) r (funcAssoc m n k p)))
  =
  (fun (r : vec F m) (p : func F (m + n + k)) =>
      funcSubstituteHeadLong (F := F) (n := n) (m := m) r
        (funcSumTailLong (F := F) (n := m + n) (k := k) p)) := by
  simpa using (sumTailLong_substHeadLong_comm (F := F) m n k)

/-- A convenient scalar corollary of the commutation lemma:

If you first fix the first `m` variables and then sum the last `k`, you get the same scalar
as if you first sum the last `k` and then fix the first `m`.

(Here everything is ultimately evaluated down to a scalar via `fullSum`.)
-/
theorem evalAndSum_comm
  (m k : ℕ) (r : vec F m) (p : func F (m + k)) :
    evalAndSum (F := F) m k r p
      =
    fullSum (F := F) 0
      (funcSubstituteHeadLong (F := F) (n := 0) (m := m) r
        (funcSumTailLong (F := F) (n := m) (k := k) p)) := by
  -- This is basically definitional: `evalAndSum` already reduces to a scalar
  -- by tail-summing to arity 0 and evaluating at `vecNil`.
  -- We rewrite using the commutation lemma with `n := 0`.
  unfold evalAndSum fullSum
  -- Turn `p : func F (m+k)` into `func F (m+0+k)` for the lemma.
  have h : m + 0 + k = m + k := by simp [Nat.add_assoc]
  -- Use commutation at n=0.
  have := congrArg (fun (t : (vec F m → func F (m + 0 + k) → func F 0)) => t r (cast (by simp [h]) p))
    (sumTailLong_substHeadLong_comm_sound (F := F) m 0 k)
  -- Now simplify the casts away.
  simpa [funcAssoc, h, Nat.add_assoc] using congrArg (fun q => q vecNil) this

end SumCheck
