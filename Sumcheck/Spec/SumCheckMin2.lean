import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

noncomputable section
open Classical

namespace Sumcheck

universe u
variable {F : Type u} [Field F]

def castFinAddZero (n : ℕ) (i : Fin (n + 0)) : Fin n :=
  Fin.cast (by simp) i

def castFinAddZeroReverse (n : ℕ) (i : Fin n) : Fin (n + 0) :=
  Fin.cast (by simp) i

def vec (F : Type u) [Field F] (n : ℕ) : Type u :=
  Fin n → F

def func (F : Type u) [Field F] (n : ℕ) : Type u :=
  vec F n → F

def castFinVecAddZero (n : ℕ) (xs : vec F (n + 0)) : vec F n :=
  fun i => xs (castFinAddZero n i)

def castFinVecAddZeroReverse (n : ℕ) (xs : vec F n) : vec F (n + 0) :=
  fun i => xs (castFinAddZero n i)


/--
A transcript for the sum-check protocol *without degree checks*.

- `claim0` is the initial claim (usually the claimed total sum).
- `g i` is the prover message at round `i`, represented simply
  as a function `F → F` (no degree restriction is enforced).
-/
structure Transcript (n : ℕ) where
  claim0 : F
  g      : Fin n → (F → F)

/--
Verifier for the sum-check protocol without degree checks.

Inputs:
- `n` : number of variables
- `f` : the original function `(Fin n → F) → F`
- `tr`: transcript containing the initial claim and prover messages
- `r` : verifier randomness, one field element per round

Output:
- A proposition asserting that the transcript is accepted.
-/
def verify (n : ℕ)
    (f  : (Fin n → F) → F)
    (tr : Transcript (F := F) n)
    (r  : Fin n → F) : Prop :=

  -- Recursive verifier loop.
  -- `k` : number of remaining rounds
  -- `i` : current round index
  -- `hi`: proof that i + k = n
  -- `claim`: current claim value
  let rec go : (k : ℕ) → (i : ℕ) → (hi : i + k = n) → (claim : F) → Prop
    | 0, i, hi, claim =>
        -- Base case: no rounds left, check final equality
        f r = claim
    | (k+1), i, hi, claim =>
        -- From i + (k+1) = n we get i < n
        have hlt : i < n := by
          have : i < i + (k+1) := Nat.lt_add_of_pos_right (Nat.succ_pos k)
          simpa [hi] using this
        -- Convert the natural index i into Fin n
        let fi : Fin n := ⟨i, hlt⟩
        -- Check g_i(0) + g_i(1) = current claim,
        -- then recurse with updated claim g_i(r_i)
        (tr.g fi 0 + tr.g fi 1 = claim) ∧
          have hi' : (i+1) + k = n := by
            -- (i+1) + k = i + (k+1)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
          go k (i+1) hi' (tr.g fi (r fi))

  -- Start the verifier loop with all rounds remaining
  go n 0 (by simp) tr.claim0

def vecAppendTail {n : ℕ} (v : Fin n → F) (b : F) : Fin (n + 1) → F :=
  fun i =>
    if h : i.val < n then
      v ⟨i.val, h⟩
    else
      b




/- not used now-/
def vecCutTail {n : ℕ} (v : vec F (n + 1)) : vec F n :=
  fun i => v i.castSucc

def funcSubstituteHead {n : ℕ} (p : func F (n + 1)) (r : F) : func F n :=
  fun xs => p (fun i => Fin.cases r xs i)

def funcSumTailSingle {n : ℕ} (p : func F (n + 1)) : (func F n) :=
  fun xs => (p (vecAppendTail xs 0) + p (vecAppendTail xs 1))

def funcSumTailLong {n : ℕ} (p : func F (n + k)) (k : ℕ) (hk : k ≤ n) : func F n :=
if h : k = n then
    -- Only one variable to sum over (x_n)
    fun xs =>
      let extendedVec : Fin (n + 1) → F := vecAppendTail xs 0
      funcSumTailSingle (fun _ => p extendedVec) xs
  else
    have h_lt : k < n := by omega
    -- First sum over x_n, then recursively sum from k to n-1
    let p_without_last : (Fin n → F) → F := funcSumTailSingle p
    funcSumTailLong p_without_last k (by omega)

-- Самый простой вариант: рекурсия по k
def sum_last_k_vars {n : ℕ} (p : func F (n + k)) (k : ℕ) : func F n :=
  match k with
    | 0 =>
      fun xs => p (Fin.cast (by simp) (castFinVecAddZeroReverse n xs))
    | k' + 1 =>
      -- k = k' + 1
      -- Представляем p как многочлен от (n + k') + 1 переменных
      let p_as_plus_one : func F ((n + k') + 1) :=
        cast (by ring) p

      -- Суммируем по последней переменной
      let p_summed_last : func F (n + k') :=
        funcSumTailSingle p_as_plus_one

      -- Рекурсивно суммируем по оставшимся k' переменным
      sum_last_k_vars (k := k') p_summed_last
  | k' + 1 =>
      -- k = k' + 1
      -- Представляем p как многочлен от (m + k') + 1 переменных
      let p_as_plus_one : Poly ((m + k') + 1) :=
        cast (by ring) p

      -- Суммируем по последней переменной
      let p_summed_last : Poly (m + k') :=
        sum_last_axiom p_as_plus_one

      -- Рекурсивно суммируем по оставшимся k' переменным
      sum_last_k_vars (k := k') p_summed_last


end Sumcheck
