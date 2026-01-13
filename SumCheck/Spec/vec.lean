import SumCheck.Spec.fin

noncomputable section
open Classical
open SumCheck

namespace SumCheck

universe u
variable {F : Type u} [Field F]

def vec (F : Type u) [Field F] (n : ℕ) : Type u :=
  Fin n → F

/-- Empty vector. -/
def vecZero : vec F 0 := fun i => Fin.elim0 i

def vecOne : vec F 1 → F :=
  fun v => v ⟨0, by simp⟩

def vecOne_Inv : F → vec F 1 :=
  fun x => fun _i => x

def vecAddZero (n : ℕ) : vec F (n + 0) → vec F n :=
  fun xs i => xs (finAddZero_Inv n i)

def vecAddZero_Inv (n : ℕ) : vec F n → vec F (n + 0) :=
  fun xs i => xs (finAddZero n i)

def vecZeroAdd (n : ℕ) : vec F (0 + n) → vec F n :=
  fun xs i => xs (finZeroAdd_Inv n i)

def vecZeroAdd_Inv (n : ℕ) : vec F n → vec F (0 + n) :=
  fun xs i => xs (finZeroAdd n i)

def vecZeroAdd_X_Id (a b : ℕ) : vec F (0 + a + b) → vec F (a + b) :=
  fun xs i => xs (finZeroAdd_X_Id_Inv a b i)

def vecZeroAdd_X_Id_Inv (a b : ℕ) : vec F (a + b) → vec F (0 + a + b) :=
  fun xs i => xs (finZeroAdd_X_Id a b i)

def vecAddZero_X_Id (a b : ℕ) : vec F (a + 0 + b) → vec F (a + b) :=
  fun xs i => xs (finAddZero_X_Id_Inv a b i)

def vecAddZero_X_Id_Inv (a b : ℕ) : vec F (a + b) → vec F (a + 0 + b) :=
  fun xs i => xs (finAddZero_X_Id a b i)

def vecAssoc (n k l : ℕ) : vec F (n + k + l) → vec F (n + (k + l)) :=
  fun v i => v (finAssoc_Inv n k l i)

def vecAssoc_Inv (n k l : ℕ) : vec F (n + (k + l)) → vec F (n + k + l) :=
  fun v i => v (finAssoc n k l i)

def vecAssoc_X_Id (a b c d : ℕ) : vec F (a + b + c + d) → vec F (a + (b + c) + d) :=
  fun v i => v (finAssoc_X_Id_Inv a b c d i)

def vecAssoc_X_Id_Inv (a b c d : ℕ) : vec F (a + (b + c) + d) → vec F (a + b + c + d) :=
  fun v i => v (finAssoc_X_Id a b c d i)

def vecId_X_Assoc (a b c d : ℕ) : vec F (a + (b + c + d)) → vec F (a + (b + (c + d))) :=
  fun v i => v (finId_X_Assoc_Inv a b c d i)

def vecId_X_Assoc_Inv (a b c d : ℕ) : vec F (a + (b + (c + d))) → vec F (a + (b + c + d)) :=
  fun v i => v (finId_X_Assoc a b c d i)

def vecId_X_Id_X_Assoc (a b c d e : ℕ) :
    vec F (a + (b + (c + d + e))) → vec F (a + (b + (c + (d + e)))) :=
  fun v i => v (finId_X_Id_X_Assoc_Inv a b c d e i)

def vecId_X_Id_X_Assoc_Inv (a b c d e : ℕ) :
    vec F (a + (b + (c + (d + e)))) → vec F (a + (b + (c + d + e))) :=
  fun v i => v (finId_X_Id_X_Assoc a b c d e i)

def vecComm (a b : ℕ) : vec F (a + b) → vec F (b + a) :=
  fun v i => v (finComm b a i)

def vecComm_X_Id (a b c : ℕ) : vec F (a + b + c) → vec F (b + a + c) :=
  fun v i => v (finComm_X_Id b a c i)

def vecId_X_Comm (a b c : ℕ) : vec F (a + (b + c)) → vec F (a + (c + b)) :=
  fun v i => v (finId_X_Comm a c b i)

def vecComm_X_Id_X_Id (a b c d : ℕ) : vec F (a + b + c + d) → vec F (b + a + c + d) :=
  fun v i => v (finComm_X_Id_X_Id b a c d i)

def vecId_X_Comm_XX_Id (a b c d : ℕ) :
    vec F (a + (b + c) + d) → vec F (a + (c + b) + d) :=
  fun v i => v (finId_X_Comm_XX_Id a c b d i)

def vecRightComm (a b c : ℕ) : vec F (a + b + c) → vec F (a + c + b) :=
  fun v i => v (finRightComm a c b i)

def vecLeftComm (a b c : ℕ) : vec F (a + (b + c)) → vec F (b + (a + c)) :=
  fun v i => v (finLeftComm b a c i)

/-- `vec F b → vec F (a + (b-a))` via reindexing. -/
def vecAddSubLE (a b : ℕ) (h : a ≤ b) : vec F b → vec F (a + (b - a)) :=
  fun v => fun i => v (finAddSubLE_Inv a b h i)

/-- `vec F (a + (b-a)) → vec F b` via reindexing. -/
def vecAddSubLE_Inv (a b : ℕ) (h : a ≤ b) : vec F (a + (b - a)) → vec F b :=
  fun v => fun i => v (finAddSubLE a b h i)

@[simp]
theorem vecOne_comp_vecOneInv :
  (vecOne (F := F)) ∘ (vecOne_Inv (F := F)) = id := by
  funext x
  rfl

@[simp]
theorem vecOneInv_comp_vecOne :
  (vecOne_Inv (F := F)) ∘ (vecOne (F := F)) = id := by
  funext v
  -- both sides are the same value, since vecOneInv produces a constant function
  funext i
  simp [vecOne, vecOne_Inv, Function.comp]
  have hi : i = (0 : Fin 1) := by
    simpa using (Fin.eq_zero i)
  -- now rewrite
  simp [hi]

@[simp]
theorem vecComm_involutive (a b : ℕ) (v : vec F (a + b)) :
  vecComm b a (vecComm a b v) = v := by
  unfold vecComm
  simp [finComm_involutive]

@[simp]
theorem vecComm_vecZeroAddInv_is_vecAddZeroInv (n : ℕ) (v : vec F n) :
  vecComm 0 n (vecZeroAdd_Inv n v) = vecAddZero_Inv n v := by
  funext i
  unfold vecZeroAdd_Inv vecAddZero_Inv vecComm
  simp [finZeroAdd]
  simp [Fin.cast]
  rfl

@[simp]
theorem vecComm_X_Id_involutive (a b c : ℕ) (v : vec F (a + b + c)) :
  vecComm_X_Id b a c (vecComm_X_Id a b c v) = v := by
  unfold vecComm_X_Id
  simp [finComm_X_Id]

@[simp]
theorem vecId_X_Comm_involutive (a b c : ℕ) (v : vec F (a + (b + c))) :
  vecId_X_Comm a c b (vecId_X_Comm a b c v  ) = v := by
  unfold vecId_X_Comm
  simp [finId_X_Comm]

@[simp]
theorem vecId_X_Comm_XX_Id_involutive (a b c d : ℕ) (v : vec F (a + (b + c) + d)) :
  vecId_X_Comm_XX_Id a c b d (vecId_X_Comm_XX_Id a b c d v) = v := by
  unfold vecId_X_Comm_XX_Id
  simp [finId_X_Comm_XX_Id]

@[simp]
theorem vecComm_X_Id_finAssocInv_is_finAssocInv_finComm_X_Id_Id
  (a b c d : ℕ) (v : vec F ((a + b) + (c + d))) :
  vecAssoc_Inv (b + a) c d (vecComm_X_Id a b (c + d) v)
  =
  vecComm_X_Id_X_Id a b c d (vecAssoc_Inv (a + b) c d v)
  := by
  funext i
  unfold vecAssoc_Inv vecComm_X_Id vecComm_X_Id_X_Id
  simp [finComm_X_Id_finAssoc_is_finAssoc_finComm_X_Id_Id]


theorem vecPentagonIdentity (a b c d : ℕ) (v : vec F (a + (b + (c + d)))) :
  vecAssoc_X_Id_Inv a b c d (vecAssoc_Inv a (b + c) d (vecId_X_Assoc_Inv a b c d v))
  =
  vecAssoc_Inv (a + b) c d (vecAssoc_Inv a b (c + d) v)
  := by
  unfold vecAssoc_Inv vecId_X_Assoc_Inv vecAssoc_X_Id_Inv
  simp [finPentagonIdentity]

-- -----------------------
-- n + 0  (AddZero)
-- -----------------------

@[simp]
theorem vecAddZero_comp_vecAddZero_Inv_is_id
  (n : ℕ) :
    (vecAddZero (F := F) n) ∘ (vecAddZero_Inv (F := F) n) = id := by
  funext xs i
  unfold vecAddZero vecAddZero_Inv
  rfl

@[simp]
theorem vecAddZero_Inv_comp_vecAddZero_is_id
  (n : ℕ) :
    (vecAddZero_Inv (F := F) n) ∘ (vecAddZero (F := F) n) = id := by
  funext xs i
  unfold vecAddZero vecAddZero_Inv
  rfl

-- -----------------------
-- 0 + n  (ZeroAdd)
-- -----------------------

@[simp]
theorem vecZeroAdd_comp_vecZeroAdd_Inv_is_id
  (n : ℕ) :
    (vecZeroAdd (F := F) n) ∘ (vecZeroAdd_Inv (F := F) n) = id := by
  funext xs i
  unfold vecZeroAdd vecZeroAdd_Inv
  rfl

@[simp]
theorem vecZeroAdd_Inv_comp_vecZeroAdd_is_id
  (n : ℕ) :
    (vecZeroAdd_Inv (F := F) n) ∘ (vecZeroAdd (F := F) n) = id := by
  funext xs i
  unfold vecZeroAdd vecZeroAdd_Inv
  rfl

-- -----------------------
-- Assoc (n + k + l) ↔ (n + (k + l))
-- -----------------------

@[simp]
theorem vecAssoc_comp_vecAssoc_Inv_is_id
  (n k l : ℕ) :
    (vecAssoc (F := F) n k l) ∘ (vecAssoc_Inv (F := F) n k l) = id := by
  funext v i
  unfold vecAssoc vecAssoc_Inv
  rfl

@[simp]
theorem vecAssoc_Inv_comp_vecAssoc_is_id
  (n k l : ℕ) :
    (vecAssoc_Inv (F := F) n k l) ∘ (vecAssoc (F := F) n k l) = id := by
  funext v i
  unfold vecAssoc vecAssoc_Inv
  rfl

-- -----------------------
-- Assoc_X_Id (a+b+c+d) ↔ (a + (b+c) + d)
-- -----------------------

@[simp]
theorem vecAssoc_X_Id_comp_vecAssoc_X_Id_Inv_is_id
  (a b c d : ℕ) :
    (vecAssoc_X_Id (F := F) a b c d) ∘ (vecAssoc_X_Id_Inv (F := F) a b c d) = id := by
  funext v i
  unfold vecAssoc_X_Id vecAssoc_X_Id_Inv
  rfl

@[simp]
theorem vecAssoc_X_Id_Inv_comp_vecAssoc_X_Id_is_id
  (a b c d : ℕ) :
    (vecAssoc_X_Id_Inv (F := F) a b c d) ∘ (vecAssoc_X_Id (F := F) a b c d) = id := by
  funext v i
  unfold vecAssoc_X_Id vecAssoc_X_Id_Inv
  rfl

-- -----------------------
-- Id_X_Assoc  (a + (b + c + d)) ↔ (a + (b + (c + d)))
-- -----------------------

@[simp]
theorem vecId_X_Assoc_comp_vecId_X_Assoc_Inv_is_id
  (a b c d : ℕ) :
    (vecId_X_Assoc (F := F) a b c d) ∘ (vecId_X_Assoc_Inv (F := F) a b c d) = id := by
  funext v i
  unfold vecId_X_Assoc vecId_X_Assoc_Inv
  rfl

@[simp]
theorem vecId_X_Assoc_Inv_comp_vecId_X_Assoc_is_id
  (a b c d : ℕ) :
    (vecId_X_Assoc_Inv (F := F) a b c d) ∘ (vecId_X_Assoc (F := F) a b c d) = id := by
  funext v i
  unfold vecId_X_Assoc vecId_X_Assoc_Inv
  rfl

@[simp]
theorem vecId_X_Id_X_Assoc_comp_vecId_X_Id_X_Assoc_Inv_is_id
  (a b c d e : ℕ) :
    (vecId_X_Id_X_Assoc (F := F) a b c d e) ∘
      (vecId_X_Id_X_Assoc_Inv (F := F) a b c d e) = id := by
  funext v i
  unfold vecId_X_Id_X_Assoc vecId_X_Id_X_Assoc_Inv
  simp [Function.comp]
  rfl

@[simp]
theorem vecId_X_Id_X_Assoc_Inv_comp_vecId_X_Id_X_Assoc_is_id
  (a b c d e : ℕ) :
    (vecId_X_Id_X_Assoc_Inv (F := F) a b c d e) ∘
      (vecId_X_Id_X_Assoc (F := F) a b c d e) = id := by
  funext v i
  unfold vecId_X_Id_X_Assoc vecId_X_Id_X_Assoc_Inv
  simp [Function.comp]
  rfl

@[simp]
theorem vecZeroAdd_X_Id_comp_vecZeroAdd_X_Id_Inv_is_id
  (a b : ℕ) :
    (vecZeroAdd_X_Id (F := F) a b) ∘ (vecZeroAdd_X_Id_Inv (F := F) a b) = id := by
  funext xs i
  unfold vecZeroAdd_X_Id vecZeroAdd_X_Id_Inv
  rfl

@[simp]
theorem vecZeroAdd_X_Id_Inv_comp_vecZeroAdd_X_Id_is_id
  (a b : ℕ) :
    (vecZeroAdd_X_Id_Inv (F := F) a b) ∘ (vecZeroAdd_X_Id (F := F) a b) = id := by
  funext xs i
  unfold vecZeroAdd_X_Id vecZeroAdd_X_Id_Inv
  rfl

@[simp]
theorem vecAddZero_X_Id_comp_vecAddZero_X_Id_Inv_is_id
  (a b : ℕ) :
    (vecAddZero_X_Id (F := F) a b) ∘ (vecAddZero_X_Id_Inv (F := F) a b) = id := by
  funext xs i
  unfold vecAddZero_X_Id vecAddZero_X_Id_Inv
  rfl

@[simp]
theorem vecAddZero_X_Id_Inv_comp_vecAddZero_X_Id_is_id
  (a b : ℕ) :
    (vecAddZero_X_Id_Inv (F := F) a b) ∘ (vecAddZero_X_Id (F := F) a b) = id := by
  funext xs i
  unfold vecAddZero_X_Id vecAddZero_X_Id_Inv
  rfl

@[simp]
theorem vecAddSubLE_Inv_comp (a b : ℕ) (h : a ≤ b) :
  (vecAddSubLE_Inv (F := F) a b h) ∘ (vecAddSubLE (F := F) a b h) = id := by
  funext v
  funext i
  simp [Function.comp, vecAddSubLE, vecAddSubLE_Inv]
  rfl

@[simp]
theorem vecAddSubLE_comp_Inv (a b : ℕ) (h : a ≤ b) :
  (vecAddSubLE (F := F) a b h) ∘ (vecAddSubLE_Inv (F := F) a b h) = id := by
  funext v
  funext i
  simp [Function.comp, vecAddSubLE, vecAddSubLE_Inv]
  rfl

end SumCheck
