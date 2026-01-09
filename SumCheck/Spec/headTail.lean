import SumCheck.Spec.func

noncomputable section
open Classical
open SumCheck

namespace SumCheck

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

theorem vecAppendTail_vecAddZero_Inv_is_vecAddZero_Inv_vecAppendTail
  {F : Type} [Field F]
  (n : ℕ) (r_tail : F) :
  (vecAppendTail (F := F) (n := n + 0) · r_tail) ∘ (vecAddZero_Inv (F := F) (n := n))
  =
  (vecRightComm n 1 0) ∘
    ((vecAddZero_Inv (F := F) (n := n + 1)) ∘ (vecAppendTail (F := F) (n := n) · r_tail))
  := by
    unfold vecAppendTail
    unfold vecRightComm vecAddZero_Inv
    unfold finRightComm finAddZero
    rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAppendTail_vecZeroAdd_Inv_is_vecAssoc_Inv_vecZeroAdd_Inv_vecAppendTail
  {F : Type} [Field F]
  (n : ℕ) (r_tail : F) :
  (vecAppendTail (0 + n) · r_tail) ∘ (vecZeroAdd_Inv n)
  =
  (vecAssoc_Inv 0 n 1) ∘ ((vecZeroAdd_Inv (n + 1)) ∘ (vecAppendTail n · r_tail))
  := by
    unfold vecAppendTail
    unfold vecZeroAdd_Inv vecAssoc_Inv
    unfold finZeroAdd finAssoc
    ring_nf
    rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAddZero_Inv_vecAppendHead_is_vecAssoc_Inv_vecAppendHead_vecAddZero_Inv
  {F : Type} [Field F]
  (n : ℕ) (r_head : F) :
  (vecAddZero_Inv (1 + n)) ∘ (vecAppendHead n r_head)
  =
  (vecAssoc_Inv 1 n 0) ∘ (((vecAppendHead (n + 0) r_head)) ∘ (vecAddZero_Inv n))
  := by
  unfold vecAppendHead
  unfold vecAssoc_Inv vecAddZero_Inv
  unfold finAssoc finAddZero
  rfl


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAppendHead_vecZeroAdd_Inv_is_vecLeftComm_vecZeroAdd_Inv_vecAppendHead
  {F : Type} [Field F]
  (n : ℕ) (r_head : F) :
  (vecAppendHead (0 + n) r_head) ∘ (vecZeroAdd_Inv n)
  =
  (vecLeftComm 0 1 n) ∘ ((vecZeroAdd_Inv (1 + n)) ∘ (vecAppendHead n r_head))
  := by
  unfold vecAppendHead
  unfold vecZeroAdd_Inv vecLeftComm
  unfold finZeroAdd finLeftComm
  funext xs i
  cases' i with k hk
  cases k with
  | zero =>
      simp [Function.comp]
      rfl
  | succ k =>
      simp [Function.comp]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/-

theorem vecAppendTail_vecZeroAddInv_is_vecZeroAddInv_vecAppendTail_old
  {F : Type} [Field F]
  (n : ℕ) (xs : vec F n) (r_head : F) :
    vecAppendTail (0 + n) (vecZeroAdd_Inv (F := F) (n := n) xs) r_head
      =
    vecAssoc_Inv 0 n 1
      (vecZeroAdd_Inv (F := F) (n := n + 1) (vecAppendTail (F := F) (n := n) xs r_head)) := by
  funext i
  cases' i with k hk
  -- we will split into k < n (inside xs) vs k = n (last coordinate)
  have hk' : k < n + 1 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk

  by_cases hkn : k < n
  · -- k < n
    -- both sides reduce to xs ⟨k, hkn⟩ after casts are simplified
    simp [vecAppendTail, vecZeroAdd_Inv, vecAssoc_Inv, finZeroAdd, finAssoc, hkn]
  · -- ¬ k < n  ==> since k < n+1, we must have k = n
    have hk_eq : k = n := Nat.eq_of_lt_succ_of_not_lt hk' hkn
    subst hk_eq
    -- last coordinate: both sides reduce to r_head
    simp [vecAppendTail, vecZeroAdd_Inv, vecAssoc_Inv, finZeroAdd, finAssoc]

-/

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAppendTail_vecAppendHead_is_vecAssoc_Inv_vecAppendHead_vecAppendTail
  {F : Type} [Field F]
  (n : ℕ) (r_head r_tail : F) :
  (vecAppendTail (1 + n) · r_tail) ∘ (vecAppendHead n r_head)
  =
  (vecAssoc_Inv 1 n 1) ∘ ((vecAppendHead (n + 1) r_head) ∘ (vecAppendTail n · r_tail))
  := by
    unfold vecAppendTail vecAppendHead
    unfold vecAssoc_Inv
    unfold finAssoc
    ring_nf
    funext xs i
    cases' i with k hk
    cases k with
    | zero =>
      simp [Function.comp]
      rfl
    | succ k =>
      simp [Function.comp]
      ring_nf
      simp

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/-

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

-/

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAssoc_X_Id_Inv_vecAppentTail_is_vecAppendTail_vecAssoc_Inv
  (a b c : ℕ) (r_tail : F) :
  (vecAssoc_X_Id_Inv a b c 1)
      ∘ (vecAppendTail (a + (b + c)) · r_tail)
  =
  (vecAppendTail ((a + b) + c) · r_tail)
      ∘ (vecAssoc_Inv a b c) := by
  funext v
  unfold vecAppendTail vecAssoc_Inv vecAssoc_X_Id_Inv
  --unfold finAssoc_X_Id finAssoc
  ring_nf
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecComm_X_Id_X_Id_vecAppendTail_is_vecAppendTail_vecComm_X_Id
  (a b c : ℕ) (r_tail : F) :
  (vecComm_X_Id_X_Id a b c 1) ∘ (vecAppendTail (a + b + c) · r_tail)
  =
  (vecAppendTail (b + a + c) · r_tail) ∘ (vecComm_X_Id a b c)
  := by
  funext v
  unfold vecAppendTail vecComm_X_Id vecComm_X_Id_X_Id
  --unfold finComm_X_Id finComm_X_Id_X_Id
  ring_nf
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecId_X_Assoc_Inv_vecAppendHead_is_vecAppendHead_vecAssoc_Inv_poinwise
  (a b c : ℕ) (r_head : F) (v : vec F (a + (b + c))) :
  vecId_X_Assoc_Inv 1 a b c (vecAppendHead (a + (b + c)) r_head v)
  =
  vecAppendHead (a + b + c) r_head (vecAssoc_Inv a b c v)
  := by
    unfold vecAppendHead vecId_X_Assoc_Inv vecAssoc_Inv
    --unfold finId_X_Assoc finAssoc
    funext i
    cases' i with k hk
    cases k with
    | zero =>
      rfl
    | succ k =>
      rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecId_X_Assoc_Inv_vecAppendHead_is_vecAppendHead_vecAssoc_Inv
  (a b c : ℕ) (r_head : F) :
  (vecId_X_Assoc_Inv 1 a b c) ∘ (vecAppendHead (a + (b + c)) r_head)
    =
  (vecAppendHead (a + b + c) r_head) ∘ (vecAssoc_Inv a b c) := by
  funext v
  unfold Function.comp
  unfold vecAppendHead vecId_X_Assoc_Inv vecAssoc_Inv
  --unfold finId_X_Assoc finAssoc
  funext i
  cases' i with k hk
  cases k with
  | zero =>
      rfl
  | succ k =>
      rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecId_X_Id_X_Assoc_Inv_vecAppendHead_is_vecAppendHead_vecId_X_Assoc_Inv
  (a b c d : ℕ) (r_head : F) :
  (vecId_X_Id_X_Assoc_Inv 1 a b c d) ∘
    (vecAppendHead (a + (b + (c + d))) r_head)
  =
  (vecAppendHead (a + ((b + c) + d)) r_head) ∘
    (vecId_X_Assoc_Inv a b c d)
  := by
  funext v
  unfold Function.comp
  unfold vecAppendHead vecId_X_Assoc_Inv vecId_X_Id_X_Assoc_Inv
  --unfold finId_X_Assoc finId_X_Id_X_Assoc
  funext i
  cases' i with k hk
  cases k with
  | zero =>
      rfl
  | succ k =>
      rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


end SumCheck
