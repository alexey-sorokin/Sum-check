import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Sumcheck.Spec.fin
import Sumcheck.Spec.vec
import Sumcheck.Spec.func
import Sumcheck.Spec.headTail

noncomputable section
open Classical
open Sumcheck

namespace Sumcheck

universe u
variable {F : Type u} [Field F]


def funcSubstituteHeadSingle (n : ℕ) : F → func F (1 + n) → func F n :=
  fun r p => (fun xs => p (vecAppendHead n r xs))

def funcSubstituteHeadLong {F : Type} [Field F] {n : ℕ} :
    (m : ℕ) → (r : vec F m) → func F (m + n) → func F n
| 0, r, p =>
    fun xs => p (vecZeroAddInv n xs)

| Nat.succ m, r, p =>
    -- We want to call funcSubstituteHeadSingle at arity (1 + (m + n)).
    -- But p is at arity (Nat.succ m + n) = (m+1)+n.

    -- Step A: turn p : func F ((m+1)+n) into func F (n+(m+1)) using commutativity
    let p_comm : func F (n + Nat.succ m) :=
      funcAddComm (F := F) (a := Nat.succ m) (b := n) p

    -- Step B: reassociate n + (m+1) to (n + m) + 1 so it matches funcSubstituteHeadSingle (n := n + m)
    have h_assoc : n + Nat.succ m = (n + m) + 1 := by
      -- n + (m+1) = (n+m)+1
      simp [Nat.succ_eq_add_one, Nat.add_assoc]

    let p_assoc : func F ((n + m) + 1) :=
      cast (by simp [h_assoc]) p_comm

    -- Step C: now substitute head at size (n+m)+1, producing a function of size (n+m)
    let q : func F (n + m) :=
      funcSubstituteHeadSingle (F := F) (n := n + m) (r 0) (funcAddComm (n + m) 1 p_assoc)

    -- Step D: recursive call expects func F (m + n), so commute q : func F (n+m) to func F (m+n)
    let q_comm : func F (m + n) :=
      funcAddComm (F := F) (a := n) (b := m) q

    -- Recurse on the tail vector r⟨1..⟩ and q_comm
    funcSubstituteHeadLong
      (n := n)
      (m := m)
      (fun i => r i.succ)
      q_comm

/-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Summation over the tail variables X_n+1,...,X_n+k ∈ {0,1}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-/

def funcSumTailSingle (n : ℕ) : func F (n + 1) → func F n :=
  fun p xs => (p (vecAppendTail n xs 0) + p (vecAppendTail n xs 1))

def funcSumTailLong (n : ℕ) : (k : ℕ) → func F (n + k) → func F n
| 0, p =>
    -- p: vec (n+0) -> F
    fun xs => p (vecAddZeroInv n xs)
      -- p : func F (n + 0)
      -- #check castFinVecAddZero n xs

| Nat.succ k, p =>
    have hk : n + Nat.succ k = (n + k) + 1 := by
      simpa using (Nat.add_succ n k)

    let p' : func F ((n + k) + 1) :=
      cast (congrArg (fun t => func F t) hk) p

    -- keep n fixed, recurse on k
    funcSumTailLong (n := n) k (funcSumTailSingle (F := F) (n := n + k) p')

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


/-- Substituting the head variable commutes with summing over the last variable.
    Written with `1 + n + 1` / `1 + (n+1)` instead of `n+2`. -/
theorem sumTailSingle_substHeadSingle_comm
  {F : Type} [Field F]
  (n : ℕ) :
  (fun (r0 : F) (p : func F (1 + n + 1)) =>
      funcSumTailSingle (F := F) (n := n)
        (funcSubstituteHeadSingle (F := F)
          (n := n + 1) r0 (funcAssoc 1 n 1 p)))
  =
  (fun (r0 : F) (p : func F (1 + n + 1)) =>
      funcSubstituteHeadSingle (F := F) (n := n) r0
        (funcSumTailSingle (F := F) (n := 1 + n) p)):=
by
  funext r0 p v
  simp [funcSumTailSingle,
        funcSubstituteHeadSingle,
        vecAppendHead_vecAppendTail_comm_pointwise]
  rfl

-- m, n, 1 case
theorem sumTailSingle_substHeadLong_comm
  {F : Type} [Field F]
  (m n : ℕ) :
  (fun (r : vec F (m + 1)) (p : func F (m + 1 + n + 1)) =>
      funcSumTailSingle (F := F) (n := n)
        (funcSubstituteHeadLong (F := F)
          (n := n + 1) (m := m + 1) r (funcAssoc (m + 1) n 1 p)))
  =
  (fun (r : vec F (m + 1)) (p : func F (m + 1 + n + 1)) =>
      funcSubstituteHeadLong (F := F) (n := n) (m := m + 1) r
        (funcSumTailSingle (F := F) (n := m + 1 + n) p)):=
by
  funext r p

  induction m with
  | zero =>
      unfold funcSumTailSingle
      simp [funcSubstituteHeadLong]
      unfold funcSubstituteHeadSingle
      funext xs
      simp [funcAddComm_involutive,
            ← vecAppendHead_vecAppendTail_comm_pointwise]

      unfold funcAddComm funcAssoc
      ring_nf
      simp [vecComm_vecZeroAddInv_is_vecAddZeroInv,
            vecAppendTail_vecAddZeroInv_is_vecAddZeroInv_vecAppendTail]
      unfold vecAssocInv
      rfl
  | succ m hm =>
      simp [funcSubstituteHeadLong]
      rw [funcSubstituteHeadLong] at hm
      simp [funcAddComm_involutive]
      simp [hm]





-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


theorem sumTailLong_substHeadLong_comm
  {F : Type} [Field F]
  (m n k : ℕ) :
  (fun (r : vec F m) (p : func F (m + n + k)) =>
      funcSumTailLong (F := F) (n := n) (k := k)
        (funcSubstituteHeadLong (F := F)
          (n := n + k) (m := m) r (funcAssoc m n k p)))
  =
  (fun (r : vec F m) (p : func F (m + n + k)) =>
      funcSubstituteHeadLong (F := F) (n := n) (m := m) r
        (funcSumTailLong (F := F) (n := m + n) (k := k) p)) := by
  -- extensionality on the two arguments
  funext r p

  -- main induction on k
  induction k with
  | zero =>
      simp [funcSumTailLong]
      induction m with
        | zero =>
            funext xs
            simp [funcSubstituteHeadLong]
            rfl
        | succ m h_mn0 =>
            funext xs
            simp [funcSubstituteHeadLong]
            rfl
  | succ k h_mnk =>
       induction m with
        | zero =>
            simp [funcSubstituteHeadLong] at h_mnk
            simp [funcSumTailLong, funcSubstituteHeadLong]
            funext xs
            let p' := funcSumTailSingle (0 + n + k) p
            let ap' := funcAssoc 0 n k p'
            let q := funcSumTailLong (0 + n) k p'
            let xs' := vecZeroAddInv n xs
            specialize h_mnk p'
            have h_mnk_xs :
              funcSumTailLong n k (fun v => ap' (vecZeroAddInv (n + k) v)) xs
                =
              q xs' := by
                simpa using congrArg (fun t => t xs) h_mnk

            simp [ap', xs', q, p'] at h_mnk_xs

            simp [← h_mnk_xs]
            have h1:
                (funcSumTailSingle (n + k)
                  fun w => funcAssoc 0 n (k + 1) p (vecZeroAddInv (n + (k + 1)) w))
                =
                (fun v => funcAssoc 0 n k
                            (funcSumTailSingle (0 + n + k) p)
                              (vecZeroAddInv (n + k) v)
                ) := by
                  funext u
                  simp [funcSumTailSingle, funcAssoc, vecAppendTail, vecAssocInv]
                  rfl
            rw [← h1]
            rfl

            --simp [funcSumTailSingle, castFinVecZeroAddReverse]

        | succ m ihm =>
            simp [funcSumTailLong]
            have ihm_rp:
              (fun (r : vec F m) (p : func F (m + 1 + n + k)) =>
                  funcSumTailLong (F := F) (n := n) (k := k)
                    (funcSubstituteHeadLong (F := F) (n := n + k) (m := m) r
                      (funcAssoc (m + 1) n k p)))
              =
              (fun (r : vec F m) (p : func F (m + 1 + n + k)) =>
                  funcSubstituteHeadLong (F := F) (n := n) (m := m) r
                    (funcSumTailLong (F := F) (n := m + 1 + n) (k := k) p)) := by
                specialize ihm
                funext r p
                simpa using congrArg (fun t => t r p) ihm

            let p' := (funcSumTailSingle (m + 1 + n + k) p)

            have h_assoc_mn_k :
              m + 1 + n + k = (m + 1 + n) + k := by
                rw [Nat.add_assoc, Nat.add_assoc]

            let r' : vec F m := fun i => r i.succ

            subst r'


            let p' : func F ((m + 1) + n + k) := funcAssoc (m + 1) n k p

            let p_single : func F (((m + 1) + n) + 1) :=
              cast (by simp [Nat.add_assoc]) p

            let q_single : func F ((m + n) + 1) :=
              funcSubstituteHeadSingle (F := F) (n := m + n) (r 0) p_single

            let q : func F (m + n) :=
              funcAddComm (F := F) (a := n) (b := m) q_single

            have ih_apply :
              funcSumTailLong (F := F) (n := n) (k := k)
                (funcSubstituteHeadLong (F := F) (n := n + k) (m := m)
                  (fun i => r i.succ)
                  (funcAssoc m n k q))
              =
              funcSubstituteHeadLong (F := F) (n := n) (m := m)
                (fun i => r i.succ)
                (funcSumTailLong (F := F) (n := m + n) (k := k) q)
              := by
                specialize ihm q
                simpa using congrArg (fun t => t r') ihm

            simp [ih_apply]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem sumTailSingle_substHeadLong_comm_old (n m : ℕ) :
  (fun (r : vec F m) (p : func F (n + m + 1)) =>
    funcSumTailSingle (F := F) (n := n)
      (funcSubstituteHeadLong (F := F) (n := n + 1) (m := m) r
        (funcRightComm n m 1 p)
      )
  )
  =
  (fun (r : vec F m) (p : func F (n + m + 1)) =>
    funcSubstituteHeadLong (F := F) (n := n) (m := m) r
      (funcSumTailSingle p)) := by
  funext r p
    --simp[]

  #check p -- n + m + 1
  #check funcSumTailSingle (F := F) (n := n + m) p -- n + m
  #check funcSubstituteHeadLong (F := F) (n := n) (m := m) r (funcSumTailSingle p) -- n
  -- #check

  #check p -- n + l + 1
  #check funcRightComm n m 1 p -- n + 1 + m
  #check funcSubstituteHeadLong (F := F) (n := n + 1) m r (funcRightComm n m 1 p) -- n + 1
  #check funcSumTailSingle (F := F) (n := n) (funcSubstituteHeadLong (F := F) (n := n + 1) m r (funcRightComm n m 1 p)) -- n


  #check funcSubstituteHeadLong (F := F) (n := n + 1) (m := m) r p

  #check funcSubstituteHeadSingle (F := F) (n := n + l)

  induction l with
  | zero =>
      -- l = 0: r is an empty vector
      simp [funcSubstituteHeadLong, funcSumTailSingle]

      -- We need to show the casts commute
      -- funext xs
      simp [castFinVecAddZero, castFinAddZero, vecAppendTail]
      rfl

  | succ l ih =>

    let r' : vec F l := (fun i => r i.succ)

    simp [funcSubstituteHeadLong]

    -- LHS
    #check p
    #check funcRightComm n (l + 1) 1 p
    #check funcSubstituteHeadSingle (n := n + 1 + l) (r 0) (funcRightComm n (l + 1) 1 p)
    #check funcSubstituteHeadLong l r' (funcSubstituteHeadSingle (r 0) (funcRightComm n (l + 1) 1 p))
    #check funcSumTailSingle (funcSubstituteHeadLong l r' (funcSubstituteHeadSingle (r 0) (funcRightComm n (l + 1) 1 p)))

    -- RHS
    #check p
    #check funcSumTailSingle p
    #check funcSubstituteHeadSingle (r 0) (funcSumTailSingle p)
    #check funcSubstituteHeadLong l r' (funcSubstituteHeadSingle (r 0) (funcSumTailSingle p))



    have h :
        funcSubstituteHeadSingle (F := F) (n := n + l) (r 0) (funcSumTailSingle p)
        =
        funcSumTailSingle (F := F) (n := n + l) (funcSubstituteHeadSingle (r 0) p)
        := by
          rw [sumTailSingle_substHeadSingle_comm_pointwise (F := F) (n := n + l) (r0 := r 0) p]

    simp [h]

    have hr:
    funcSubstituteHeadSingle (r 0) (funcRightComm n (l + 1) 1 p)
    =
    funcRightComm n l 1 (funcSubstituteHeadSingle (r 0) p) := by
      funext xs
      unfold funcSubstituteHeadSingle
      simp [funcRightComm]
      apply congrArg p


      -- LHS
      #check vecRightComm n 1 (l + 1) (vecAppendHead (n + 1 + l) (r 0) xs) -- n + (l + 1) + 1

      -- RHS
      #check vecAppendHead (n + l + 1) (r 0) (vecRightComm n 1 l xs) -- n + l + 1 + 1


      --simp [funcSubstituteHeadSingle]


    -- LHS
    #check p -- n + (l + 1) + 1
    #check funcRightComm n (l + 1) 1 p -- n + 1 + (l + 1)
    #check funcSubstituteHeadSingle (r 0) (funcRightComm n (l + 1) 1 p) -- (n + 1).add l

    -- RHS
    #check p -- n + (l + 1) + 1
    #check funcSubstituteHeadSingle (r 0) p -- n + (l + 1
    #check funcRightComm n l 1 (funcSubstituteHeadSingle (r 0) p)
    -- n + 1 + l
