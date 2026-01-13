import SumCheck.Spec.func

noncomputable section
open Classical
open SumCheck

namespace SumCheck

universe u
variable {F : Type u} [Field F]


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecAppHeadSingle (n : ℕ) : F → vec F n → vec F (1 + n)
| r_head, xs =>
  fun i =>
    -- cast i : Fin (1+n) to Fin (n+1), then split 0 / succ
    Fin.cases r_head (fun j : Fin n => xs j) (finComm 1 n i)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecAppHead (n : ℕ) : (m : ℕ) → vec F m → vec F n → vec F (m + n)
| 0, r, xs =>
    -- 0 + n = n
    fun i => xs (finZeroAdd n i)
| Nat.succ m', r, xs =>
    -- head element of r (index 0 : Fin (m'+1))
    let r0 : F := r ⟨0, Nat.succ_pos m'⟩

    -- tail of r as a vector of length m'
    let rTail : vec F m' :=
      fun i =>
        r ⟨i.1 + 1, by
          -- i.2 : i.1 < m'
          -- need: i.1 + 1 < m' + 1
          simp
        ⟩

    vecComm_X_Id 1 m' n
      (vecAssoc_Inv 1 m' n
        (vecAppHeadSingle (F := F) (n := m' + n) r0
          (vecAppHead n m' rTail xs)))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecAppTailSingle (n : ℕ) : vec F n → F → vec F (n + 1)
| xs, r_tail =>
  fun i =>
    match i with
    | ⟨k, _⟩ =>
        if h : k < n then
          xs ⟨k, h⟩
        else
          r_tail

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecAppTail : (n k : ℕ) → vec F n → vec F k → vec F (n + k)
| n, 0, xs, r =>
    -- n + 0 = n
    fun i => xs (finAddZero n i)
| n, Nat.succ k, xs, r =>
    let r0 : F := r ⟨0, Nat.succ_pos k⟩
    let rTail : vec F k :=
      fun i =>
        r ⟨i.1 + 1, by
          -- i.2 : i.1 < k
          -- need: i.1+1 < k+1
          simp
        ⟩
    -- first append r0, then append the rest
    vecAssoc_Inv n k 1
      (vecAppTailSingle (n + k) (vecAppTail n k xs rTail) r0)


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecCutTailSingle (n : ℕ) : vec F (n + 1) → vec F n
| xs =>
  fun i => xs (finAddOne n i)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecCutTail (n : ℕ) : (k : ℕ) → vec F (n + k) → vec F n
| 0, xs =>
    -- xs : vec F (n + 0)
    vecAddZero (F := F) n xs
| k + 1, xs =>
    -- xs : vec F (n + (k+1))
    vecCutTail n k
      (vecCutTailSingle (F := F) (n := n + k)
        (vecAssoc_Inv (F := F) n k 1 xs))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecCutHeadSingle (n : ℕ) : vec F (1 + n) → vec F n
| xs =>
  fun i => xs (finOneAdd n i)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def vecCutHead (n : ℕ) : (m : ℕ) → vec F (m + n) → vec F n
| 0, xs => vecZeroAdd n xs
| m + 1, xs =>
    vecCutHead n m
      (vecCutHeadSingle (F := F) (n := m + n)
        (vecAssoc 1 m n
          (vecComm_X_Id m 1 n xs)))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/-- Take the first `m` coordinates of a length-`n` vector (given `m ≤ n`). -/
def vecTakeHead {n m : ℕ} (hm : m ≤ n) : vec F n → vec F m :=
  (vecCutTail (F := F) m (n - m)) ∘ (vecAddSubLE (F := F) m n hm)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecCutHeadSingle_vecAppHeadSingle_is_id
  {F : Type u} [Field F]
  (n : ℕ) (r_head : F) :
  (vecCutHeadSingle (F := F) n) ∘ (vecAppHeadSingle (F := F) n r_head) = id
  := by
  funext xs
  simp [vecCutHeadSingle, vecAppHeadSingle, Function.comp]
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecCutTailSingle_vecAppTailSingle_is_id
  {F : Type u} [Field F]
  (n : ℕ) (r_tail : F) :
  (vecCutTailSingle (F := F) n) ∘ (fun xs => vecAppTailSingle (F := F) n xs r_tail) = id := by
  funext xs
  unfold vecCutTailSingle
  unfold vecAppTailSingle
  unfold Function.comp
  unfold finAddOne
  simp

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAppendTail_vecAddZero_Inv_is_vecAddZero_Inv_vecAppendTail
  {F : Type u} [Field F]
  (n : ℕ) (r_tail : F) :
  (vecAppTailSingle (F := F) (n := n + 0) · r_tail) ∘ (vecAddZero_Inv (F := F) (n := n))
  =
  (vecRightComm n 1 0) ∘
    ((vecAddZero_Inv (F := F) (n := n + 1)) ∘ (vecAppTailSingle (F := F) (n := n) · r_tail))
  := by
    unfold vecAppTailSingle
    unfold vecRightComm vecAddZero_Inv
    unfold finRightComm finAddZero
    rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAppendTail_vecZeroAdd_Inv_is_vecAssoc_Inv_vecZeroAdd_Inv_vecAppendTail
  {F : Type u} [Field F]
  (n : ℕ) (r_tail : F) :
  (vecAppTailSingle (0 + n) · r_tail) ∘ (vecZeroAdd_Inv n)
  =
  (vecAssoc_Inv 0 n 1) ∘ ((vecZeroAdd_Inv (n + 1)) ∘ (vecAppTailSingle n · r_tail))
  := by
    unfold vecAppTailSingle
    unfold vecZeroAdd_Inv vecAssoc_Inv
    unfold finZeroAdd finAssoc
    ring_nf
    rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAddZero_Inv_vecAppendHead_is_vecAssoc_Inv_vecAppendHead_vecAddZero_Inv
  {F : Type u} [Field F]
  (n : ℕ) (r_head : F) :
  (vecAddZero_Inv (1 + n)) ∘ (vecAppHeadSingle n r_head)
  =
  (vecAssoc_Inv 1 n 0) ∘ (((vecAppHeadSingle (n + 0) r_head)) ∘ (vecAddZero_Inv n))
  := by
  unfold vecAppHeadSingle
  unfold vecAssoc_Inv vecAddZero_Inv
  unfold finAssoc finAddZero
  rfl


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAppendHead_vecZeroAdd_Inv_is_vecLeftComm_vecZeroAdd_Inv_vecAppendHead
  {F : Type u} [Field F]
  (n : ℕ) (r_head : F) :
  (vecAppHeadSingle (0 + n) r_head) ∘ (vecZeroAdd_Inv n)
  =
  (vecLeftComm 0 1 n) ∘ ((vecZeroAdd_Inv (1 + n)) ∘ (vecAppHeadSingle n r_head))
  := by
  unfold vecAppHeadSingle
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
      unfold finComm
      rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAppendTail_vecAppendHead_is_vecAssoc_Inv_vecAppendHead_vecAppendTail
  {F : Type u} [Field F]
  (n : ℕ) (r_head r_tail : F) :
  (vecAppTailSingle (1 + n) · r_tail) ∘ (vecAppHeadSingle n r_head)
  =
  (vecAssoc_Inv 1 n 1) ∘ ((vecAppHeadSingle (n + 1) r_head) ∘ (vecAppTailSingle n · r_tail))
  := by
    unfold vecAppTailSingle vecAppHeadSingle
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
      unfold finComm
      unfold Function.comp
      simp [Nat.add_comm]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecAssoc_X_Id_Inv_vecAppentTail_is_vecAppendTail_vecAssoc_Inv
  (a b c : ℕ) (r_tail : F) :
  (vecAssoc_X_Id_Inv a b c 1)
      ∘ (vecAppTailSingle (a + (b + c)) · r_tail)
  =
  (vecAppTailSingle ((a + b) + c) · r_tail)
      ∘ (vecAssoc_Inv a b c) := by
  funext v
  unfold vecAppTailSingle vecAssoc_Inv vecAssoc_X_Id_Inv
  --unfold finAssoc_X_Id finAssoc
  ring_nf
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecComm_X_Id_X_Id_vecAppendTail_is_vecAppendTail_vecComm_X_Id
  (a b c : ℕ) (r_tail : F) :
  (vecComm_X_Id_X_Id a b c 1) ∘ (vecAppTailSingle (a + b + c) · r_tail)
  =
  (vecAppTailSingle (b + a + c) · r_tail) ∘ (vecComm_X_Id a b c)
  := by
  funext v
  unfold vecAppTailSingle vecComm_X_Id vecComm_X_Id_X_Id
  --unfold finComm_X_Id finComm_X_Id_X_Id
  ring_nf
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecId_X_Assoc_Inv_vecAppendHead_is_vecAppendHead_vecAssoc_Inv_poinwise
  (a b c : ℕ) (r_head : F) (v : vec F (a + (b + c))) :
  vecId_X_Assoc_Inv 1 a b c (vecAppHeadSingle (a + (b + c)) r_head v)
  =
  vecAppHeadSingle (a + b + c) r_head (vecAssoc_Inv a b c v)
  := by
    unfold vecAppHeadSingle vecId_X_Assoc_Inv vecAssoc_Inv
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
  (vecId_X_Assoc_Inv 1 a b c) ∘ (vecAppHeadSingle (a + (b + c)) r_head)
    =
  (vecAppHeadSingle (a + b + c) r_head) ∘ (vecAssoc_Inv a b c) := by
  funext v
  unfold Function.comp
  unfold vecAppHeadSingle vecId_X_Assoc_Inv vecAssoc_Inv
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
    (vecAppHeadSingle (a + (b + (c + d))) r_head)
  =
  (vecAppHeadSingle (a + ((b + c) + d)) r_head) ∘
    (vecId_X_Assoc_Inv a b c d)
  := by
  funext v
  unfold Function.comp
  unfold vecAppHeadSingle vecId_X_Assoc_Inv vecId_X_Id_X_Assoc_Inv
  --unfold finId_X_Assoc finId_X_Id_X_Assoc
  funext i
  cases' i with k hk
  cases k with
  | zero =>
      rfl
  | succ k =>
      rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theorem vecId_X_Comm_XX_Id_vecAppTailSingle_is_vecAppTailSingle_vecId_X_Comm
  (a b c : ℕ) (r_tail : F) :
  (vecId_X_Comm_XX_Id a c b 1) ∘ (vecAppTailSingle (a + (c + b)) · r_tail)
  =
  (vecAppTailSingle (a + (b + c)) · r_tail) ∘ (vecId_X_Comm a c b)
  := by
    funext v
    unfold Function.comp
    unfold vecId_X_Comm_XX_Id vecId_X_Comm
    unfold vecAppTailSingle
    unfold finId_X_Comm_XX_Id finId_X_Comm
    simp [Nat.add_comm]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end SumCheck
