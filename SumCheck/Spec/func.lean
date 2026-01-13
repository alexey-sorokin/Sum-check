import SumCheck.Spec.vec

noncomputable section
open Classical
open SumCheck

namespace SumCheck

universe u
variable {F : Type u} [Field F]

def func (F : Type u) [Field F] (n : ℕ) : Type u :=
  vec F n → F

/-- Evaluate a function on the unique vector of length 0. -/
def funcZero : func F 0 → F :=
  fun p => p vecZero

/-- Turn a value into the constant function on vectors of length 0. -/
def funcZero_Inv : F → func F 0 :=
  fun x => fun _ => x

def funcAddZero (n : ℕ) : func F (n + 0) → func F n :=
  fun p v => p (vecAddZero n v)

def funcAddZero_Inv (n : ℕ) : func F n → func F (n + 0) :=
  fun p v => p (vecAddZero_Inv n v)

def funcZeroAdd (n : ℕ) : func F (0 + n) → func F n :=
  fun p v => p (vecZeroAdd_Inv n v)

def funcZeroAdd_Inv (n : ℕ) : func F n → func F (0 + n) :=
  fun p v => p (vecZeroAdd n v)

def funcZeroAdd_X_Id (a b : ℕ) : func F (0 + a + b) → func F (a + b) :=
  fun p v => p (vecZeroAdd_X_Id_Inv (F := F) a b v)

def funcZeroAdd_X_Id_Inv (a b : ℕ) : func F (a + b) → func F (0 + a + b) :=
  fun p v => p (vecZeroAdd_X_Id (F := F) a b v)

def funcAddZero_X_Id (a b : ℕ) : func F (a + 0 + b) → func F (a + b) :=
  fun p v => p (vecAddZero_X_Id_Inv (F := F) a b v)

def funcAddZero_X_Id_Inv (a b : ℕ) : func F (a + b) → func F (a + 0 + b) :=
  fun p v => p (vecAddZero_X_Id (F := F) a b v)

def funcAssoc (a b c : ℕ) : func F (a + b + c) → func F (a + (b + c)) :=
  fun p v => p (vecAssoc_Inv a b c v)

def funcAssoc_Inv (a b c : ℕ) : func F (a + (b + c)) → func F (a + b + c) :=
  fun p v => p (vecAssoc a b c v)

def funcAssoc_X_Id (a b c d : ℕ) : func F (a + b + c + d) → func F (a + (b + c) + d) :=
  fun p v => p (vecAssoc_X_Id_Inv a b c d v)

def funcAssoc_X_Id_Inv (a b c d : ℕ) : func F (a + (b + c) + d) → func F (a + b + c + d) :=
  fun p v => p (vecAssoc_X_Id a b c d v)

def funcId_X_Assoc (a b c d : ℕ) : func F (a + (b + c + d)) → func F (a + (b + (c + d))) :=
  fun p v => p (vecId_X_Assoc_Inv a b c d v)

def funcId_X_Assoc_Inv (a b c d : ℕ) : func F (a + (b + (c + d))) → func F (a + (b + c + d)) :=
  fun p v => p (vecId_X_Assoc a b c d v)

def funcId_X_Id_X_Assoc (a b c d e : ℕ) :
    func F (a + (b + (c + d + e))) → func F (a + (b + (c + (d + e)))) :=
  fun p v => p (vecId_X_Id_X_Assoc_Inv (F := F) a b c d e v)

def funcId_X_Id_X_Assoc_Inv (a b c d e : ℕ) :
    func F (a + (b + (c + (d + e)))) → func F (a + (b + (c + d + e))) :=
  fun p v => p (vecId_X_Id_X_Assoc (F := F) a b c d e v)

def funcComm (a b : ℕ) : func F (a + b) → func F (b + a) :=
  fun p v => p (vecComm b a v)

def funcComm_X_Id (a b c : ℕ) : func F (a + b + c) → func F (b + a + c) :=
  fun p v => p (vecComm_X_Id b a c v)

def funcId_X_Comm (a b c : ℕ) : func F (a + (b + c)) → func F (a + (c + b)) :=
  fun p v => p (vecId_X_Comm a c b v)

def funcComm_X_Id_X_Id (a b c d : ℕ) : func F (a + b + c + d) → func F (b + a + c + d) :=
  fun p v => p (vecComm_X_Id_X_Id b a c d v)

def funcId_X_Comm_XX_Id (a b c d : ℕ) : func F (a + (b + c) + d) → func F (a + (c + b) + d) :=
  fun p v => p (vecId_X_Comm_XX_Id a c b d v)

/-- `func F (a + (b-a)) → func F b` by precomposing with `vecAddSubLE`. -/
def funcAddSubLE_Inv (a b : ℕ) (h : a ≤ b) : func F (a + (b - a)) → func F b :=
  fun p v => p (vecAddSubLE (F := F) a b h v)

/-- `func F b → func F (a + (b-a))` by precomposing with `vecAddSubLE_Inv`. -/
def funcAddSubLE (a b : ℕ) (h : a ≤ b) : func F b → func F (a + (b - a)) :=
  fun p v => p (vecAddSubLE_Inv (F := F) a b h v)

@[simp]
theorem funcZero_funcZeroInv_is_id :
  (funcZero (F := F)) ∘ (funcZero_Inv (F := F)) = id := by
  funext x
  rfl

@[simp]
theorem funcZeroInv_funcZero_is_id :
  (funcZero_Inv (F := F)) ∘ (funcZero (F := F)) = id := by
  funext p
  -- goal: funcZeroInv (funcZero p) = p
  funext v
  -- v : vec F 0, but vec F 0 has only one element, so v = vecZero
  have hv : v = vecZero (F := F) := by
    funext i
    exact Fin.elim0 i
  -- now everything is definitional
  simp [funcZero, funcZero_Inv, hv]

@[simp]
theorem funcId_X_Comm_XX_Id_involutive (a b c d : ℕ) (p : func F (a + (b + c) + d)) :
  funcId_X_Comm_XX_Id a c b d (funcId_X_Comm_XX_Id a b c d p) = p
  := by
    unfold funcId_X_Comm_XX_Id
    simp

@[simp]
theorem funcComm_involutive (a b : ℕ) (p : func F (a + b)) :
  funcComm b a (funcComm a b p) = p
  := by
    unfold funcComm
    simp [vecComm_involutive]

theorem funcComm_X_Id_funcAssoc_is_funcAssoc_funcComm_X_Id_Id
  (a b c d : ℕ) (p : func F (a + b + c + d)) :
  funcComm_X_Id a b (c + d) (funcAssoc (a + b) c d p)
  =
  funcAssoc (b + a) c d (funcComm_X_Id_X_Id a b c d p)
  := by
    unfold funcComm_X_Id funcComm_X_Id_X_Id funcAssoc
    simp [vecComm_X_Id_finAssocInv_is_finAssocInv_finComm_X_Id_Id]

theorem funcPentagonIdentity (a b c d : ℕ) (p : func F (a + b + c + d)) :
  funcId_X_Assoc a b c d (funcAssoc a (b + c) d (funcAssoc_X_Id a b c d p))
  =
  funcAssoc a b (c + d) (funcAssoc (a + b) c d p)
  := by
    unfold funcId_X_Assoc funcAssoc funcAssoc_X_Id
    simp [vecPentagonIdentity]

-- -----------------------
-- n + 0  (AddZero)
-- -----------------------

@[simp]
theorem funcAddZero_funcAddZero_Inv_is_id
  (n : ℕ) :
    (funcAddZero (F := F) n) ∘ (funcAddZero_Inv (F := F) n) = id := by
  funext p v
  unfold funcAddZero funcAddZero_Inv
  rfl
  -- reduces to vecAddZero ∘ vecAddZero_Inv = id

@[simp]
theorem funcAddZero_Inv_funcAddZero_is_id
  (n : ℕ) :
    (funcAddZero_Inv (F := F) n) ∘ (funcAddZero (F := F) n) = id := by
  funext p v
  unfold funcAddZero funcAddZero_Inv
  rfl
-- -----------------------
-- 0 + n  (ZeroAdd)
-- -----------------------

@[simp]
theorem funcZeroAdd_funcZeroAdd_Inv_is_id
  (n : ℕ) :
    (funcZeroAdd (F := F) n) ∘ (funcZeroAdd_Inv (F := F) n) = id := by
  funext p v
  unfold funcZeroAdd funcZeroAdd_Inv
  rfl

@[simp]
theorem funcZeroAdd_Inv_funcZeroAdd_is_id
  (n : ℕ) :
    (funcZeroAdd_Inv (F := F) n) ∘ (funcZeroAdd (F := F) n) = id := by
  funext p v
  unfold funcZeroAdd funcZeroAdd_Inv
  rfl

-- -----------------------
-- Assoc (a + b + c) ↔ (a + (b + c))
-- -----------------------

@[simp]
theorem funcAssoc_funcAssoc_Inv_is_id
  (a b c : ℕ) :
    (funcAssoc (F := F) a b c) ∘ (funcAssoc_Inv (F := F) a b c) = id := by
  funext p v
  unfold funcAssoc funcAssoc_Inv
  rfl

@[simp]
theorem funcAssoc_Inv_funcAssoc_is_id
  (a b c : ℕ) :
    (funcAssoc_Inv (F := F) a b c) ∘ (funcAssoc (F := F) a b c) = id := by
  funext p v
  unfold funcAssoc funcAssoc_Inv
  rfl

-- -----------------------
-- Assoc_X_Id  (a+b+c+d) ↔ (a + (b+c) + d)
-- -----------------------

@[simp]
theorem funcAssoc_X_Id_funcAssoc_X_Id_Inv_is_id
  (a b c d : ℕ) :
    (funcAssoc_X_Id (F := F) a b c d) ∘ (funcAssoc_X_Id_Inv (F := F) a b c d) = id := by
  funext p v
  unfold funcAssoc_X_Id funcAssoc_X_Id_Inv
  rfl

@[simp]
theorem funcAssoc_X_Id_Inv_funcAssoc_X_Id_is_id
  (a b c d : ℕ) :
    (funcAssoc_X_Id_Inv (F := F) a b c d) ∘ (funcAssoc_X_Id (F := F) a b c d) = id := by
  funext p v
  unfold funcAssoc_X_Id funcAssoc_X_Id_Inv
  rfl

-- -----------------------
-- Id_X_Assoc  (a + (b + c + d)) ↔ (a + (b + (c + d)))
-- -----------------------

@[simp]
theorem funcId_X_Assoc_funcId_X_Assoc_Inv_is_id
  (a b c d : ℕ) :
    (funcId_X_Assoc (F := F) a b c d) ∘ (funcId_X_Assoc_Inv (F := F) a b c d) = id := by
  funext p v
  unfold funcId_X_Assoc funcId_X_Assoc_Inv
  rfl

@[simp]
theorem funcId_X_Assoc_Inv_funcId_X_Assoc_is_id
  (a b c d : ℕ) :
    (funcId_X_Assoc_Inv (F := F) a b c d) ∘ (funcId_X_Assoc (F := F) a b c d) = id := by
  funext p v
  unfold funcId_X_Assoc funcId_X_Assoc_Inv
  rfl

@[simp]
theorem funcId_X_Id_X_Assoc_funcId_X_Id_X_Assoc_Inv_is_id
  (a b c d e : ℕ) :
    (funcId_X_Id_X_Assoc (F := F) a b c d e) ∘
      (funcId_X_Id_X_Assoc_Inv (F := F) a b c d e) = id := by
  funext p v
  unfold funcId_X_Id_X_Assoc funcId_X_Id_X_Assoc_Inv
  simp [Function.comp]
  rfl

@[simp]
theorem funcId_X_Id_X_Assoc_Inv_funcId_X_Id_X_Assoc_is_id
  (a b c d e : ℕ) :
    (funcId_X_Id_X_Assoc_Inv (F := F) a b c d e) ∘
      (funcId_X_Id_X_Assoc (F := F) a b c d e) = id := by
  funext p v
  unfold funcId_X_Id_X_Assoc funcId_X_Id_X_Assoc_Inv
  simp [Function.comp]
  rfl

@[simp]
theorem funcZeroAdd_X_Id_funcZeroAdd_X_Id_Inv_is_id
  (a b : ℕ) :
    (funcZeroAdd_X_Id (F := F) a b) ∘ (funcZeroAdd_X_Id_Inv (F := F) a b) = id := by
  funext p v
  unfold funcZeroAdd_X_Id funcZeroAdd_X_Id_Inv
  rfl

@[simp]
theorem funcZeroAdd_X_Id_Inv_funcZeroAdd_X_Id_is_id
  (a b : ℕ) :
    (funcZeroAdd_X_Id_Inv (F := F) a b) ∘ (funcZeroAdd_X_Id (F := F) a b) = id := by
  funext p v
  unfold funcZeroAdd_X_Id funcZeroAdd_X_Id_Inv
  rfl

@[simp]
theorem funcAddZero_X_Id_funcAddZero_X_Id_Inv_is_id
  (a b : ℕ) :
    (funcAddZero_X_Id (F := F) a b) ∘ (funcAddZero_X_Id_Inv (F := F) a b) = id := by
  funext p v
  unfold funcAddZero_X_Id funcAddZero_X_Id_Inv
  rfl

@[simp]
theorem funcAddZero_X_Id_Inv_funcAddZero_X_Id_is_id
  (a b : ℕ) :
    (funcAddZero_X_Id_Inv (F := F) a b) ∘ (funcAddZero_X_Id (F := F) a b) = id := by
  funext p v
  unfold funcAddZero_X_Id funcAddZero_X_Id_Inv
  rfl

@[simp]
theorem funcAddSubLE_Inv_funcAddSubLE_is_id (a b : ℕ) (h : a ≤ b) :
  (funcAddSubLE_Inv (F := F) a b h) ∘ (funcAddSubLE (F := F) a b h) = id := by
  funext p
  funext v
  -- p : vec F (a + (b-a)) → F,  v : vec F (a + (b-a))
  simp [Function.comp, funcAddSubLE, funcAddSubLE_Inv]
  rfl

@[simp]
theorem funcAddSubLE_funcAddSubLE_Inv_is_id (a b : ℕ) (h : a ≤ b) :
  (funcAddSubLE (F := F) a b h) ∘ (funcAddSubLE_Inv (F := F) a b h) = id := by
  funext p
  funext v
  -- p : vec F b → F,  v : vec F b
  simp [Function.comp, funcAddSubLE, funcAddSubLE_Inv]
  rfl

end SumCheck
