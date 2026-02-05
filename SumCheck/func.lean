import SumCheck.vec

noncomputable section
open Classical
open NEO
open scoped BigOperators

namespace NEO

universe u
variable {F : Type u} [Field F]

def func (F : Type u) [Field F] (n : ℕ) : Type u :=
  vec F n → F

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- TRIVIAL DEFS

/-- Evaluate a function on the unique vector of length 0. -/
def funcZero : func F 0 → F :=
  fun p => p vecZero

/-- Turn a value into the constant function on vectors of length 0. -/
def funcZero_Inv : F → func F 0 :=
  fun x => fun _ => x

def funcCast (n1 n2 : ℕ) (h : n1 = n2) : func F n1 → func F n2 :=
  (· ∘ vecCast n2 n1 h.symm)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- LAMBDA DEFS

def funcZeroAdd (n : ℕ) : func F (0 + n) → func F n :=
  fun p v => p (vecZeroAdd_Inv n v)

def funcZeroAdd_Inv (n : ℕ) : func F n → func F (0 + n) :=
  fun p v => p (vecZeroAdd n v)

def funcZeroAdd_X_Id (a b : ℕ) : func F (0 + a + b) → func F (a + b) :=
  fun p v => p (vecZeroAdd_X_Id_Inv (F := F) a b v)

def funcZeroAdd_X_Id_Inv (a b : ℕ) : func F (a + b) → func F (0 + a + b) :=
  fun p v => p (vecZeroAdd_X_Id (F := F) a b v)

def funcId_X_ZeroAdd (a b : ℕ) :
    func F (a + (0 + b)) → func F (a + b) :=
  fun p v => p (vecId_X_ZeroAdd_Inv (F := F) a b v)

def funcId_X_ZeroAdd_Inv (a b : ℕ) :
    func F (a + b) → func F (a + (0 + b)) :=
  fun p v => p (vecId_X_ZeroAdd (F := F) a b v)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- RHO DEFS

def funcAddZero (n : ℕ) : func F (n + 0) → func F n :=
  fun p v => p (vecAddZero n v)

def funcAddZero_Inv (n : ℕ) : func F n → func F (n + 0) :=
  fun p v => p (vecAddZero_Inv n v)

def funcAddZero_X_Id (a b : ℕ) : func F (a + 0 + b) → func F (a + b) :=
  fun p v => p (vecAddZero_X_Id_Inv (F := F) a b v)

def funcAddZero_X_Id_Inv (a b : ℕ) : func F (a + b) → func F (a + 0 + b) :=
  fun p v => p (vecAddZero_X_Id (F := F) a b v)

def funcAddZero_X_Id_X_Id (a b c : ℕ) :
    func F (a + b + c) → func F (a + 0 + b + c) :=
  fun p v => p (vecAddZero_X_Id_X_Id (F := F) a b c v)

def funcAddZero_X_Id_X_Id_Inv (a b c : ℕ) :
    func F (a + 0 + b + c) → func F (a + b + c) :=
  fun p v => p (vecAddZero_X_Id_X_Id_Inv (F := F) a b c v)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ASSOCITIVITY DEFS

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

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- COMMUTATIVITY DEFS

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

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- Splitting DEFS

def funcSplit_Inv (n a b : ℕ) (h : n = a + b) :
    func F (a + b) → func F n :=
  (· ∘ vecDesum (F := F) (n := n) (a := a) (b := b) h)

def funcSplit (n a b : ℕ) (h : n = a + b) :
    func F n → func F (a + b) :=
  (· ∘ vecDesum_Inv (F := F) (n := n) (a := a) (b := b) h)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- OTHER DEFS

def funcCastToPrefixOneSuffix (n : ℕ) (i : Fin n) :
    func F n → func F ((i.1 + 1) + (n - (i.1 + 1))) :=
  (· ∘ vecCastToPrefixOneSuffix n i)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^(b + a - a) → F  ─── funcRightCancell ───▶  F^b → F
-/
def funcRightCancell (a b : ℕ) :
    func F (b + a - a) → func F b :=
  (· ∘ vecRightCancell_Inv a b)


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^(a + (b + a - a)) → F  ─── funcId_X_RightCancell ───▶  F^(a + b) → F
-/
def funcId_X_RightCancell (a b : ℕ) :
    func F (a + (b + a - a)) → func F (a + b) :=
  (· ∘ vecId_X_RightCancell_Inv a b)

-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================





-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- TRIVIAL THEOREMS



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- LAMBDA THEOREMS

@[simp]
theorem funcZero_funcZeroInv_is_id :
  (funcZero (F := F)) ∘ (funcZero_Inv (F := F)) = id
  := by
  rfl

@[simp]
theorem funcZeroInv_funcZero_is_id :
  (funcZero_Inv (F := F)) ∘ (funcZero (F := F)) = id
  := by
  funext p
  funext v
  simp [funcZero, funcZero_Inv]

@[simp]
theorem funcZeroAdd_funcZeroAdd_Inv_is_id
  (n : ℕ) :
    (funcZeroAdd (F := F) n) ∘ (funcZeroAdd_Inv (F := F) n) = id
  := by
  rfl

@[simp]
theorem funcZeroAdd_Inv_funcZeroAdd_is_id
  (n : ℕ) :
    (funcZeroAdd_Inv (F := F) n) ∘ (funcZeroAdd (F := F) n) = id
  := by
  rfl

@[simp]
theorem funcZeroAdd_X_Id_funcZeroAdd_X_Id_Inv_is_id
  (a b : ℕ) :
    (funcZeroAdd_X_Id (F := F) a b) ∘ (funcZeroAdd_X_Id_Inv (F := F) a b) = id
  := by
  rfl

@[simp]
theorem funcZeroAdd_X_Id_Inv_funcZeroAdd_X_Id_is_id
  (a b : ℕ) :
    (funcZeroAdd_X_Id_Inv (F := F) a b) ∘ (funcZeroAdd_X_Id (F := F) a b) = id
  := by
  rfl

@[simp]
theorem funcId_X_ZeroAdd_funcId_X_ZeroAdd_Inv_is_id
  (a b : ℕ) :
    (funcId_X_ZeroAdd (F := F) a b) ∘
      (funcId_X_ZeroAdd_Inv (F := F) a b)
    = id
  := by
  rfl

@[simp]
theorem funcId_X_ZeroAdd_Inv_funcId_X_ZeroAdd_is_id
  (a b : ℕ) :
    (funcId_X_ZeroAdd_Inv (F := F) a b) ∘
      (funcId_X_ZeroAdd (F := F) a b)
    = id
  := by
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- RHO THEOREMS

@[simp]
theorem funcAddZero_funcAddZero_Inv_is_id
  (n : ℕ) :
    (funcAddZero (F := F) n) ∘ (funcAddZero_Inv (F := F) n) = id
  := by
  rfl

@[simp]
theorem funcAddZero_Inv_funcAddZero_is_id
  (n : ℕ) :
    (funcAddZero_Inv (F := F) n) ∘ (funcAddZero (F := F) n) = id
  := by
  rfl


@[simp]
theorem funcAddZero_X_Id_funcAddZero_X_Id_Inv_is_id
  (a b : ℕ) :
    (funcAddZero_X_Id (F := F) a b) ∘ (funcAddZero_X_Id_Inv (F := F) a b) = id
  := by
  rfl

@[simp]
theorem funcAddZero_X_Id_Inv_funcAddZero_X_Id_is_id
  (a b : ℕ) :
    (funcAddZero_X_Id_Inv (F := F) a b) ∘ (funcAddZero_X_Id (F := F) a b) = id
  := by
  rfl

@[simp]
theorem funcAddZero_X_Id_X_Id_funcAddZero_X_Id_X_Id_Inv_is_id
  (a b c : ℕ) :
  (funcAddZero_X_Id_X_Id (F := F) a b c) ∘
      (funcAddZero_X_Id_X_Id_Inv (F := F) a b c)
    =
  id
  := by
  rfl

@[simp]
theorem funcAddZero_X_Id_X_Id_Inv_funcAddZero_X_Id_X_Id_is_id
  (a b c : ℕ) :
  (funcAddZero_X_Id_X_Id_Inv (F := F) a b c) ∘
      (funcAddZero_X_Id_X_Id (F := F) a b c)
    =
  id
  := by
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ASSOCIATIVITY THEOREMS

@[simp]
theorem funcAssoc_funcAssoc_Inv_is_id
  (a b c : ℕ) :
    (funcAssoc (F := F) a b c) ∘ (funcAssoc_Inv (F := F) a b c) = id
  := by
  rfl

@[simp]
theorem funcAssoc_Inv_funcAssoc_is_id
  (a b c : ℕ) :
    (funcAssoc_Inv (F := F) a b c) ∘ (funcAssoc (F := F) a b c) = id
  := by
  rfl

@[simp]
theorem funcAssoc_X_Id_funcAssoc_X_Id_Inv_is_id
  (a b c d : ℕ) :
    (funcAssoc_X_Id (F := F) a b c d) ∘ (funcAssoc_X_Id_Inv (F := F) a b c d) = id
  := by
  rfl

@[simp]
theorem funcAssoc_X_Id_Inv_funcAssoc_X_Id_is_id
  (a b c d : ℕ) :
    (funcAssoc_X_Id_Inv (F := F) a b c d) ∘ (funcAssoc_X_Id (F := F) a b c d) = id
  := by
  rfl

@[simp]
theorem funcId_X_Assoc_funcId_X_Assoc_Inv_is_id
  (a b c d : ℕ) :
    (funcId_X_Assoc (F := F) a b c d) ∘ (funcId_X_Assoc_Inv (F := F) a b c d) = id
  := by
  rfl

@[simp]
theorem funcId_X_Assoc_Inv_funcId_X_Assoc_is_id
  (a b c d : ℕ) :
    (funcId_X_Assoc_Inv (F := F) a b c d) ∘ (funcId_X_Assoc (F := F) a b c d) = id
  := by
  rfl

@[simp]
theorem funcId_X_Id_X_Assoc_funcId_X_Id_X_Assoc_Inv_is_id
  (a b c d e : ℕ) :
    (funcId_X_Id_X_Assoc (F := F) a b c d e) ∘
      (funcId_X_Id_X_Assoc_Inv (F := F) a b c d e) = id
  := by
  rfl

@[simp]
theorem funcId_X_Id_X_Assoc_Inv_funcId_X_Id_X_Assoc_is_id
  (a b c d e : ℕ) :
    (funcId_X_Id_X_Assoc_Inv (F := F) a b c d e) ∘
      (funcId_X_Id_X_Assoc (F := F) a b c d e) = id
  := by
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- COMMUTATIVE THEOREMS

@[simp]
theorem funcId_X_Comm_XX_Id_involutive (a b c d : ℕ) :
  (funcId_X_Comm_XX_Id a c b d) ∘ (funcId_X_Comm_XX_Id (F := F) a b c d) = id
  := by
 rfl

@[simp]
theorem funcComm_involutive (a b : ℕ) :
  (funcComm b a) ∘ (funcComm (F := F) a b) = id
  := by
  rfl

theorem funcComm_X_Id_funcAssoc_is_funcAssoc_funcComm_X_Id_Id
  (a b c d : ℕ) :
  (funcComm_X_Id a b (c + d)) ∘ (funcAssoc (a + b) c d)
  =
  (funcAssoc (b + a) c d) ∘ (funcComm_X_Id_X_Id (F := F) a b c d)
  := by
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- MIXED THEOREMS

theorem funcPentagonIdentity (a b c d : ℕ) :
  (funcId_X_Assoc a b c d) ∘ (funcAssoc a (b + c) d) ∘ (funcAssoc_X_Id a b c d)
  =
  (funcAssoc a b (c + d)) ∘ (funcAssoc (a + b) (F := F) c d)
  := by
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- OTHER THEOREMS

@[simp]
theorem funcSplit_Inv_funcSplit_is_id (n a b : ℕ) (h : n = a + b) :
    (funcSplit_Inv (F := F) (n := n) (a := a) (b := b) h) ∘
      (funcSplit (F := F) (n := n) (a := a) (b := b) h)
    = id := by
  funext p v
  simp [funcSplit, funcSplit_Inv, Function.comp]
  rfl

@[simp]
theorem funcSplit_funcSplit_Inv_is_id (n a b : ℕ) (h : n = a + b) :
    (funcSplit (F := F) (n := n) (a := a) (b := b) h) ∘
      (funcSplit_Inv (F := F) (n := n) (a := a) (b := b) h)
    = id := by
  funext p v
  simp [funcSplit, funcSplit_Inv, Function.comp]
  rfl

end NEO
