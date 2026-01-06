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



def finAddZero (n : ℕ) : Fin (n + 0) → Fin n :=
  fun i => Fin.cast (by simp) i

def finAddZeroInv (n : ℕ) :  Fin n → Fin (n + 0) :=
  fun i => Fin.cast (by simp) i

def finZeroAdd (n : ℕ) : Fin (0 + n) → Fin n :=
  fun i => Fin.cast (by simp) i

def finZeroAddInv (n : ℕ) :  Fin n → Fin (0 + n) :=
  fun i => Fin.cast (by simp) i

def finAssoc (n k l : ℕ) : Fin (n + k + l) → Fin (n + (k + l)) :=
  fun i => Fin.cast (by rw [Nat.add_assoc]) i

def finAssocInv (n k l : ℕ) : Fin (n + (k + l)) → Fin (n + k + l) :=
  fun i => Fin.cast (by rw [← Nat.add_assoc]) i

def finComm (a b : ℕ) : Fin (a + b) → Fin (b + a) :=
  fun i => Fin.cast (by simp [Nat.add_comm]) i

theorem finComm_finZeroAddInv_is_finAddZeroInv (n : ℕ) (i : Fin n) :
  finComm 0 n (finZeroAddInv n i) = finAddZeroInv n i := by
  simp [finComm, finZeroAddInv, finAddZeroInv, Fin.cast]

theorem finComm_involutive (a b : ℕ) (i : Fin (a + b)) :
  finComm b a (finComm a b i) = i := by
  simp [finComm, Fin.cast]



def vecAddZero (n : ℕ) : vec F (n + 0) → vec F n :=
  fun xs i => xs (finAddZero n i)

def vecAddZeroInv (n : ℕ) : vec F n → vec F (n + 0) :=
  fun xs i => xs (finAddZeroInv n i)

def vecZeroAdd (n : ℕ) : vec F (0 + n) → vec F n :=
  fun xs i => xs (finZeroAddInv n i)

def vecZeroAddInv (n : ℕ) : vec F n → vec F (0 + n) :=
  fun xs i => xs (finZeroAdd n i)




def vecAssoc (n k l : ℕ) : vec F (n + k + l) → vec F (n + (k + l)) :=
  fun v i => v (finAssocInv n k l i)

def vecAssocInv (n k l : ℕ) : vec F (n + (k + l)) → vec F (n + k + l) :=
  fun v i => v (finAssoc n k l i)

def vecAddComm (a b : ℕ) : vec F (a + b) → vec F (b + a) :=
  fun v i => v (finComm b a i)

theorem vecAddComm_involutive (a b : ℕ) (v : vec F (a + b)) :
  vecAddComm b a (vecAddComm a b v) = v := by
  unfold vecAddComm
  simp [finComm_involutive]


def funcAssoc (n k l : ℕ) : func F (n + k + l) → func F (n + (k + l)) :=
  fun p v => p (vecAssocInv  n k l v)

def funcAssocInv (n k l : ℕ) : func F (n + (k + l)) → func F (n + k + l) :=
  fun p v => p (vecAssoc n k l v)

def funcAddComm (a b : ℕ) : func F (a + b) → func F (b + a) :=
  fun p v => p (vecAddComm b a v)

theorem funcAddComm_involutive (a b : ℕ) (p : func F (a + b)) :
  funcAddComm b a (funcAddComm a b p) = p
  := by
    unfold funcAddComm
    simp [vecAddComm_involutive]

def vecRightComm (n k l : ℕ) : vec F (n + k + l) → vec F (n + l + k) :=
  fun v i => v (Fin.cast (by rw [Nat.add_right_comm]) i)

def funcRightComm (n k l : ℕ) : func F (n + k + l) → func F (n + l + k) :=
  fun p v => p (vecRightComm  n l k v)

theorem vecComm_vecZeroAddInv_is_vecAddZeroInv (n : ℕ) (v : vec F n) :
  vecAddComm 0 n (vecZeroAddInv n v) = vecAddZeroInv n v := by
  funext i
  unfold vecZeroAddInv vecAddZeroInv vecAddComm
  simp [finZeroAdd, finAddZeroInv]
  simp [Fin.cast]
  rfl

/-

theorem vecZeroAddInv_is_vecAddZeroInv (n : ℕ) (v : vec F n) :
  vecZeroAddInv n v = vecAddZeroInv n v := by
  funext i
  simp [vecZeroAddInv, vecAddZeroInv]
  simp [finZeroAdd, finAddZeroInv]
  simp [Fin.cast]
  rfl



theorem vecAddComm_vecZeroAddInv_is_vecAddZeroInv (n : ℕ) (v : vec F n) :
  vecAddComm 0 n (vecZeroAddInv n v) = vecAddZeroInv n v := by
  funext i
  simp [vecAddComm]
  unfold vecZeroAddInv vecAddZeroInv
  simp [finZeroAdd, finAddZeroInv]
  simp [Fin.cast]
  rfl


-/
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

/-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Substitution the head variables r_1,...,r_k ∈ F
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-/

/-

def funcSubstituteHeadLong_old {n : ℕ} :
    (m : ℕ) → (r : vec F m) → func F (n + m) → func F n
| 0, r, p =>
    fun xs =>
      by
        simpa using p (castFinVecAddZero n xs)
| Nat.succ m, r, p =>
    -- have hl : n + Nat.succ m = n + (m + 1) := by
    --  rw [Nat.succ_eq_add_one]
    funcSubstituteHeadLong_old
      (n := n)
      (m := m)
      (fun i => r i.succ)
      (funcSubstituteHeadSingle (n := n + m) (r 0) p)

-/

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

/-
theorem sumTailSingle_substHeadSingle_comm_pointwise
  (n : ℕ) (r0 : F) (p : func F (n + 2)) :
  funcSumTailSingle (F := F) (n := n)
      (funcSubstituteHeadSingle (F := F) (n := n + 1) r0 p)
  =
  funcSubstituteHeadSingle (F := F) (n := n) r0
      (funcSumTailSingle (F := F) (n := n + 1) p) := by
  funext xs
  simp [
    funcSumTailSingle,
    funcSubstituteHeadSingle,
    vecAppendHead_vecAppendTail_comm_pointwise]
-/

-- Function.curry &&&&
/-
theorem sumTailSingle_substHeadSingle_comm (n : ℕ) :
  (fun (r0 : F) (p : func F (1 + n + 1)) =>
      funcSumTailSingle (F := F) (n := n)
        (funcSubstituteHeadSingle (F := F) (n := 1 + n) r0 p))
  =
  (fun (r0 : F) (p : func F (1 + n + 1)) =>
      funcSubstituteHeadSingle (F := F) (n := n) r0
        (funcSumTailSingle (F := F) (n := 1 + n) p)) := by
  funext r0 p xs

  simp [
    funcSumTailSingle,
    funcSubstituteHeadSingle,
    vecAppendHead_vecAppendTail_comm_pointwise]
-/

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
            -- want to show:
            -- LHS: funcSumTailLong (n := n) (k := k+1)
            --        (funcSubstituteHeadLong (n := n + (k+1)) (m := m+1) r
            --          (funcAssoc (m+1) n (k+1) p))
            --
            -- RHS: funcSubstituteHeadLong (n := n) (m := m+1) r
            --        (funcSumTailLong (n := m+1 + n) (k := k+1) p)

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

            /-
            have h_assoc_mn_k1 :
              (m + 1) + n + (k + 1) = ((m + 1) + n) + 1 + k := by
                rw [Nat.add_assoc, Nat.add_assoc]
            -/

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

/-
      have hm :
        (fun (r : vec F m) (q : func F (m + (n + k) + 1)) =>
            funcSumTailSingle (F := F) (n := n + k)
              (funcSubstituteHeadLong (F := F) (n := (n + k) + 1) (m := m) r q))
        =
        (fun (r : vec F m) (q : func F (m + (n + k) + 1)) =>
            funcSubstituteHeadLong (F := F) (n := n + k) (m := m) r
              (funcSumTailSingle (F := F) (n := m + (n + k)) q)) := by
        -- induction on m for the single-step commutation
        funext r q

            -- step m = m+1: unfold funcSubstituteHeadLong at succ,
            -- use ihm on the tail r', and the known single-variable comm lemma
            -- (details later)


      -- now use:
      -- 1) unfold funcSumTailLong at succ on both sides
      -- 2) rewrite using hm (commute single-step with subst-long)
      -- 3) apply ih to the remaining k-part (the recursive call)
      -- (details later)

-/





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

    /- -
    have ht:
      funcSumTailSingle (funcSubstituteHeadLong l r' (funcRightComm n l 1 (funcSubstituteHeadSingle (r 0) p)))
      =
      funcSubstituteHeadLong l r' (funcSumTailSingle (funcSubstituteHeadSingle (r 0) p)) := ih r' (funcSubstituteHeadSingle (r 0) p)
    -/


    --simp [ht]
