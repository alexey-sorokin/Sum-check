import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Sumcheck.Spec.fin
import Sumcheck.Spec.vec
import Sumcheck.Spec.func

noncomputable section
open Classical
open Sumcheck

namespace Sumcheck

universe u
variable {F : Type u} [Field F]


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecAppendHead (n : ℕ) : F → vec F n → vec F (1 + n)
| r_head, xs =>
  fun i =>
    match i with
    | ⟨0, _⟩ => r_head
    | ⟨k + 1, hk⟩ =>
        -- hk : k+1 < 1+n, turn it into k < n
        have hk' : k + 1 < n + 1 := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hk
        have hk'' : k < n := Nat.succ_lt_succ_iff.mp hk'
        xs ⟨k, hk''⟩


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecAppendTail (n : ℕ) : vec F n → F → vec F (n + 1)
| xs, r_head =>
  fun i =>
    match i with
    | ⟨k, _⟩ =>
        if h : k < n then
          xs ⟨k, h⟩
        else
          r_head

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAppendTail_vecAddZeroInv_is_vecAddZeroInv_vecAppendTail
  {F : Type} [Field F]
  (n : ℕ) (xs : vec F n) (r_head : F) :
  vecAppendTail (F := F) (n := n) (vecAddZeroInv (F := F) (n := n) xs) r_head
  =
  vecAddZeroInv (F := F) (n := n + 1) (vecAppendTail (F := F) (n := n) xs r_head) := by
  funext i
  cases' i with k hk
  have hkn : k < n + 1 := by
    -- k < n+1
    exact hk
  by_cases hkn' : k < n
  · -- case k < n
    -- both sides reduce to xs at coordinate k
    simp [vecAppendTail, vecAddZeroInv, hkn', finAddZeroInv]
  · -- case ¬ k < n  (so k = n)
    have hk_eq : k = n := Nat.eq_of_lt_succ_of_not_lt hkn hkn'
    subst k  -- <— important: eliminates k, keeps n

    -- both sides reduce to r_head at the last coordinate
    simp [vecAppendTail, vecAddZeroInv, finAddZeroInv]



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAppendHead_vecAppendTail_comm_pointwise
  {F : Type} [Field F]
  (n : ℕ) (r_head : F) (xs : vec F n) (r_tail : F) :
  vecAppendHead (F := F) (n := n + 1) r_head (vecAppendTail (F := F) (n := n) xs r_tail)
  =
  vecAppendTail (F := F) (n := 1 + n) (vecAppendHead (F := F) (n := n) r_head xs) r_tail := by
  funext i
  cases' i with k hk
  cases k with
  | zero =>
      -- i = 0
      simp [vecAppendHead, vecAppendTail]
  | succ k =>
      -- i = k+1
      by_cases hkn : k < n
      · -- case k < n  (so i is not the last coordinate)
        have hright : k.succ < 1 + n := by
          -- k+1 < n+1
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.succ_lt_succ hkn
        -- unfold both sides; vecAppendTail chooses xs, vecAppendHead chooses the tail part
        simp [vecAppendHead, vecAppendTail, hkn, hright]
      · -- case ¬ k < n  (so k = n, hence i is the last coordinate)
        have hk_lt : k < n + 1 := by
          -- from hk : k+1 < (n+1)+1 we get k < n+1
          -- (note: n+2 is definitional equal to (n+1)+1)
          exact Nat.succ_lt_succ_iff.mp (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk)
        have hk_eq : k = n := Nat.eq_of_lt_succ_of_not_lt hk_lt hkn
        subst k  -- <— important: eliminates k, keeps n

        have hright : ¬ (Nat.succ n < 1 + n) := by
          -- ¬(n+1 < n+1)
          simp [Nat.succ_eq_add_one, Nat.add_comm] --using (Nat.lt_irrefl (n + 1))

        -- both sides reduce to r_tail at the last coordinate
        simp [vecAppendHead, vecAppendTail, hright]
