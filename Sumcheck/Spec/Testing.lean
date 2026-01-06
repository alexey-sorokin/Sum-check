import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

noncomputable section
open Classical

namespace Sumcheck

universe u
variable {F : Type u} [Field F]

def vec (F : Type u) [Field F] (n : ℕ) : Type u :=
  Fin n → F

def func (F : Type u) [Field F] (n : ℕ) : Type u :=
  vec F n → F

def castFinAddZero (n : ℕ) (i : Fin (n + 0)) : Fin n :=
  Fin.cast (by simp) i

def castFinAddZeroReverse (n : ℕ) (i : Fin n) : Fin (n + 0) :=
  Fin.cast (by simp) i

def castFinVecAddZero (n : ℕ) (xs : vec F (n + 0)) : vec F n :=
  fun i => xs (castFinAddZero n i)

def castFinVecAddZeroReverse (n : ℕ) (xs : vec F n) : vec F (n + 0) :=
  fun i => xs (castFinAddZeroReverse n i)

def vecAssoc (n k l : ℕ) : vec F (n + k + l) → vec F (n + (k + l)) :=
  fun v i => v (Fin.cast (by rw [Nat.add_assoc]) i)

def vecAssocReverse (n k l : ℕ) : vec F (n + (k + l)) → vec F (n + k + l) :=
  fun v i => v (Fin.cast (by rw [← Nat.add_assoc]) i)

def vecRightComm (n k l : ℕ) : vec F (n + k + l) → vec F (n + l + k) :=
  fun v i => v (Fin.cast (by rw [Nat.add_right_comm]) i)

def funcAssoc (n k l : ℕ) : func F (n + k + l) → func F (n + (k + l)) :=
  fun p v => p (vecAssocReverse  n k l v)

def funcAssocReverse (n k l : ℕ) : func F (n + (k + l)) → func F (n + k + l) :=
  fun p v => p (vecAssoc n k l v)

def funcRightComm (n k l : ℕ) : func F (n + k + l) → func F (n + l + k) :=
  fun p v => p (vecRightComm  n l k v)












def sameWhenZero (n k : ℕ) (f : func F (n + k)) (hk : k = 0) : func F (n) := by
  cases hk
  -- теперь k = 0, цель: func F n, а f : func F (n + 0)
  simpa using f

def vecAppendHead (n : ℕ) : F → vec F n → vec F (n + 1)
| b, xs =>
  fun i =>
    match i with
    | ⟨0, _⟩        => b
    | ⟨k + 1, hk⟩   => xs ⟨k, (Nat.succ_lt_succ_iff.mp hk)⟩

def vecAppendTail (n : ℕ) : vec F n → F → vec F (n + 1)
| xs, r =>
  fun i =>
    match i with
    | ⟨k, _⟩ =>
        if h : k < n then
          xs ⟨k, h⟩
        else
          r

theorem vecAppendHead_vecAppendTail_comm_pointwise
  (n : ℕ) (r_head : F) (xs : vec F n) (r_tail : F) :
  vecAppendHead (n := n + 1) r_head (vecAppendTail (n := n) xs r_tail)
  =
  vecAppendTail (n := n + 1) (vecAppendHead (n := n) r_head xs) r_tail := by
  funext i
  rcases i with ⟨k, hk⟩
  cases k with
  | zero =>
      simp [vecAppendHead, vecAppendTail]
  | succ j =>
      by_cases hjn : j < n
      ·
        have hsucc : j.succ < n + 1 := Nat.succ_lt_succ hjn
        simp [vecAppendHead, vecAppendTail, hjn, hsucc]
      ·
        have hsucc : ¬ j.succ < n + 1 := by
          simpa [Nat.succ_lt_succ_iff] using hjn
        simp [vecAppendHead, vecAppendTail, hjn, hsucc]



/- not used now-/
def vecCutTail {n : ℕ} (v : vec F (n + 1)) : vec F n :=
  fun i => v i.castSucc



/-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Substitution the head variables r_1,...,r_k ∈ F
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-/

def funcSubstituteHeadSingle {n : ℕ} : F → func F (n + 1) → func F n :=
  fun r p => (fun xs => p (vecAppendHead n r xs))

def funcSubstituteHeadLong {n : ℕ} :
    (l : ℕ) → (r : vec F l) → func F (n + l) → func F n
| 0, r, p =>
    fun xs =>
      by
        simpa using p (castFinVecAddZero n xs)
| Nat.succ l, r, p =>
    -- have hl : n + Nat.succ l = n + (l + 1) := by
    --  rw [Nat.succ_eq_add_one]
    funcSubstituteHeadLong
      (n := n)
      (l := l)
      (fun i => r i.succ)
      (funcSubstituteHeadSingle (n := n + l) (r 0) p)






    -- head first, then recurse on the remaining tail:




/-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Summation over the tail variables X_n+1,...,X_n+k ∈ {0,1}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-/

def funcSumTailSingle {n : ℕ} : func F (n + 1) → func F n :=
  fun p xs => (p (vecAppendTail n xs 0) + p (vecAppendTail n xs 1))

/-
def funcSumTailSingle {n : ℕ} (p : func F (n + 1)) : (func F n) :=
  fun xs => (p (vecAppendTail n xs 0) + p (vecAppendTail n xs 1))
-/

def funcSumTailLong {n : ℕ} : (k : ℕ) → func F (n + k) → func F n
| 0, p =>
    fun xs => by
      -- здесь p : func F (n + 0)
      simpa using p (castFinVecAddZero n xs)
| (Nat.succ k), p =>
    have hk : n + Nat.succ k = (n + k) + 1 := by
      simpa using (Nat.add_succ n k)

    let p' : func F ((n + k) + 1) :=
      cast (congrArg (fun t => func F t) hk) p

    funcSumTailLong k (funcSumTailSingle (n := n + k) p')



theorem funcSumTailLong_substituteHeadLong_comm
    {n k l : ℕ} (r : vec F k) (p : func F (n + k + l)) :
    funcSumTailLong (F := F) (n := n) (k := l)
      (funcSubstituteHeadLong (F := F) (n := n + l) (k := k) r
        (cast
          (by
            -- n + k + l = (n + l) + k
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          )
          p))
    =
    funcSubstituteHeadLong (F := F) (n := n) (k := k) r
      (funcSumTailLong (F := F) (n := n + k) (k := l)
        (cast
          (by
            -- n + k + l = (n + k) + l
            simpa [Nat.add_assoc]
          )
          p)) := by
    sorry


theorem sumTail_substHead_comm_comp
  (n k l : ℕ) (r : vec F l) :
  (funcSumTailLong (F := F) (n := n) k) ∘
    (funcSubstituteHeadLong (F := F) (n := n + k) l r) ∘
    (fun p : func F (n + l + k) =>
      cast
        (by simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])
        p)
  =
  (funcSubstituteHeadLong (F := F) (n := n) l r) ∘
    (funcSumTailLong (F := F) (n := n + l) k) ∘
    (fun p : func F (n + l + k) =>
      cast
        (by simp [Nat.add_assoc])
        p) := by
  sorry

theorem sumTailSingle_substHeadSingle_comm_pointwise
  (n : ℕ) (r0 : F) (p : func F (n + 2)) :
  funcSumTailSingle (F := F) (n := n)
      (funcSubstituteHeadSingle (F := F) (n := n + 1) r0 p)
  =
  funcSubstituteHeadSingle (F := F) (n := n) r0
      (funcSumTailSingle (F := F) (n := n + 1) p) := by
  funext xs
  simp [funcSumTailSingle, funcSubstituteHeadSingle, vecAppendHead_vecAppendTail_comm_pointwise]


-- Function.curry

theorem sumTailSingle_substHeadSingle_comm (n : ℕ) :
  (fun (r0 : F) (p : func F (n + 1 + 1)) =>
      funcSumTailSingle (F := F) (n := n)
        (funcSubstituteHeadSingle (F := F) (n := n + 1) r0 p))
  =
  (fun (r0 : F) (p : func F (n + 1 + 1)) =>
      funcSubstituteHeadSingle (F := F) (n := n) r0
        (funcSumTailSingle (F := F) (n := n + 1) p)) := by
  funext r0 p xs

  -- #check (fun (r0 : F) (p : func F (n + 1 + 1)) => funcSumTailSingle (F := F) (n := n) (funcSubstituteHeadSingle (F := F) (n := n + 1) r0 p))

  simp [funcSumTailSingle, funcSubstituteHeadSingle,
        vecAppendHead_vecAppendTail_comm_pointwise]


theorem sumTailSingle_substHeadLong_comm (n l : ℕ) :
  (fun (r : vec F l) (p : func F (n + l + 1)) =>
    funcSumTailSingle (F := F) (n := n)
      (funcSubstituteHeadLong (F := F) (n := n + 1) l r
        (funcRightComm n l 1 p)
      )
  )
  =
  (fun (r : vec F l) (p : func F (n + l + 1)) =>
    funcSubstituteHeadLong (F := F) (n := n) (l := l) r
      (funcSumTailSingle p)) := by
  funext r p
    --simp[]

  #check p
  #check funcSumTailSingle (F := F) (n := n + l) p
  #check funcSubstituteHeadLong (F := F) (n := n) (l := l) r (funcSumTailSingle p)
  -- #check

  #check p
  #check funcRightComm n l 1 p
  #check funcSubstituteHeadLong (F := F) (n := n + 1) l r (funcRightComm n l 1 p)
  #check funcSumTailSingle (F := F) (n := n) (funcSubstituteHeadLong (F := F) (n := n + 1) l r (funcRightComm n l 1 p))

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
      -- funext xs
      -- Just expand everything completely and hope it reduces
      -- rw [funcSubstituteHeadLong]

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

    /- -
    have ht:
      funcSumTailSingle (funcSubstituteHeadLong l r' (funcRightComm n l 1 (funcSubstituteHeadSingle (r 0) p)))
      =
      funcSubstituteHeadLong l r' (funcSumTailSingle (funcSubstituteHeadSingle (r 0) p)) := ih r' (funcSubstituteHeadSingle (r 0) p)
    -/


    --simp [ht]


          -- rw [← sumTailSingle_substHeadSingle_comm]
      -- simp [funcSubstituteHeadLong, sumTailSingle_substHeadSingle_comm, ih]
        -- funcSumTailSingle,
        -- funcSubstituteHeadLong,
        -- funcSubstituteHeadSingle,
        -- vecAppendHead,
        -- vecAppendTail,
        -- Nat.add_assoc,
        -- Nat.add_left_comm,
        -- Nat.add_comm
      -- ]

      -- Apply the induction hypothesis
      -- apply congrArg
      -- exact ih (n := n + 1) (r := fun i => r i.succ) (p := p)



theorem sumTail_substHead_comm_pointwise
  (n k l : ℕ) (r : vec F l) (p : func F (n + l + k)) :
  funcSumTailLong (F := F) (n := n) k
    (funcSubstituteHeadLong (F := F) (n := n + k) l r
      (cast
        (by
          -- n + l + k = (n + k) + l
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])
        p))
  =
  funcSubstituteHeadLong (F := F) (n := n) l r
    (funcSumTailLong (F := F) (n := n + l) k
      (cast
        (by
          -- n + l + k = (n + l) + k
          simp [Nat.add_assoc])
        p)) := by
  induction k generalizing n with
  | zero =>
      funext xs
      simp [
        funcSumTailLong]
      sorry
  | succ k ih =>
      sorry




end Sumcheck
