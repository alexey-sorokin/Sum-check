import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

noncomputable section
open Classical

namespace Sumcheck

universe u
variable {F : Type u} [Field F]

/-!
  This file gives a *minimal* (degree-free) model of the **sum-check verifier**
  for an arbitrary function `f : (Fin n → F) → F`.

  We **explicitly** model the Boolean hypercube `{0,1}^n` as `Fin n → Bool` and
  provide an embedding into field points by mapping `false ↦ (0 : F)` and
  `true ↦ (1 : F)`.

  The verifier checks only the standard consistency equations

    `g_i(0) + g_i(1) = current_claim`, then updates `current_claim := g_i(r_i)`

  and finally checks `f r = current_claim`.

  There is **no degree check** on the messages `g_i`.
-/

/-! ### The Boolean hypercube `{0,1}^n` inside `F` -/

/-- A bit embedded into the field: `false ↦ 0`, `true ↦ 1`. -/
def bit (b : Bool) : F := if b then (1 : F) else (0 : F)

/-- The Boolean hypercube `{0,1}^n` as functions `Fin n → Bool`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Embed a Boolean cube point into a field point. -/
def cubePoint {n : ℕ} (x : Cube n) : (Fin n → F) := fun i => bit (x i)

/-- The sum of `f` over the Boolean hypercube `{0,1}^n`. -/
def cubeSum (n : ℕ) (f : (Fin n → F) → F) : F :=
  ∑ x : Cube n, f (cubePoint (F := F) x)

/--
The prover's transcript for degree-free sum-check:

* `claim0` is the initial claim (usually the claimed sum over `{0,1}^n`).
* `g i` is the i-th round message, modeled only as a function `F → F`.
  We do **not** check that it is a polynomial of any bounded degree.
-/
structure Transcript (n : ℕ) where
  claim0 : F
  g      : Fin n → (F → F)

/--
Degree-free sum-check verifier, deterministic given challenges `r : Fin n → F`.

Round `i`:
1) check `g_i(0) + g_i(1) = claim`
2) update `claim := g_i(r_i)`
After `n` rounds, check `f r = claim`.
-/
def verify (n : ℕ)
    (f  : (Fin n → F) → F)
    (tr : Transcript (F := F) n)
    (r  : Fin n → F) : Prop :=

  -- `go k i hi claim` means: there are `k` rounds left, the current index is `i`,
  -- and `hi : i + k = n` connects them to the global length `n`.
  let rec go : (k : ℕ) → (i : ℕ) → (hi : i + k = n) → (claim : F) → Prop
    | 0, i, hi, claim =>
        -- Base case: no rounds left.
        f r = claim
    | (k+1), i, hi, claim =>
        -- We need `i < n` to build `fi : Fin n`.
        have hlt : i < n := by
          have : i < i + (k+1) := Nat.lt_add_of_pos_right (Nat.succ_pos k)
          simpa [hi] using this
        let fi : Fin n := ⟨i, hlt⟩
        (tr.g fi 0 + tr.g fi 1 = claim) ∧
          -- Move to the next index: show `(i+1) + k = n` from `i + (k+1) = n`.
          have hi' : (i+1) + k = n := by
            have h1 : i + Nat.succ k = n := by
              simpa [Nat.succ_eq_add_one] using hi
            have hswap : Nat.succ i + k = i + Nat.succ k := by
              -- both sides are `Nat.succ (i + k)`
              simpa [Nat.succ_add, Nat.add_succ]
            have h2 : Nat.succ i + k = n := by
              simpa [hswap] using h1
            simpa [Nat.succ_eq_add_one] using h2
          go k (i+1) hi' (tr.g fi (r fi))

  go n 0 (by simp) tr.claim0

/-! ### A convenience wrapper mentioning `{0,1}^n` explicitly -/

/--
`verifyCube` is just `verify`, but with a *suggested* interpretation:
`tr.claim0` is intended to be the sum of `f` over `{0,1}^n`.

Note: the verifier does **not** recompute that sum; this definition merely
spells out what the initial claim usually means.
-/
def verifyCube (n : ℕ)
    (f  : (Fin n → F) → F)
    (tr : Transcript (F := F) n)
    (r  : Fin n → F) : Prop :=
  tr.claim0 = cubeSum (F := F) n f ∧ verify (F := F) n f tr r

end Sumcheck
