import SumCheck.Spec.common

noncomputable section
open Classical

namespace SumCheck

universe u
variable {F : Type u} [Field F]


def finAddZero (n : ℕ) : Fin (n + 0) → Fin n :=
  fun i => Fin.cast (by simp) i

def finAddZero_Inv (n : ℕ) :  Fin n → Fin (n + 0) :=
  fun i => Fin.cast (by simp) i

def finZeroAdd (n : ℕ) : Fin (0 + n) → Fin n :=
  fun i => Fin.cast (by simp) i

def finZeroAdd_Inv (n : ℕ) : Fin n → Fin (0 + n) :=
  fun i => Fin.cast (by simp) i

def finZeroAdd_X_Id (a b : ℕ) : Fin (0 + a + b) → Fin (a + b) :=
  fun i => Fin.cast (by simp) i

def finZeroAdd_X_Id_Inv (a b : ℕ) : Fin (a + b) → Fin (0 + a + b) :=
  fun i => Fin.cast (by simp) i

def finAddZero_X_Id (a b : ℕ) : Fin (a + 0 + b) → Fin (a + b) :=
  fun i => Fin.cast (by simp) i

def finAddZero_X_Id_Inv (a b : ℕ) : Fin (a + b) → Fin (a + 0 + b) :=
  fun i => Fin.cast (by simp) i

def finAssoc (n k l : ℕ) : Fin (n + k + l) → Fin (n + (k + l)) :=
  fun i => Fin.cast (by rw [Nat.add_assoc]) i

def finAssoc_Inv (n k l : ℕ) : Fin (n + (k + l)) → Fin (n + k + l) :=
  fun i => Fin.cast (by rw [← Nat.add_assoc]) i

def finAssoc_X_Id (a b c d : ℕ) : Fin (a + b + c + d) → Fin (a + (b + c) + d) :=
  fun i => Fin.cast (by simp [Nat.add_comm, Nat.add_left_comm]) i

def finAssoc_X_Id_Inv (a b c d : ℕ) : Fin (a + (b + c) + d) → Fin (a + b + c + d) :=
  fun i => Fin.cast (by simp [Nat.add_comm, Nat.add_left_comm]) i

def finId_X_Assoc (a b c d : ℕ) : Fin (a + (b + c + d)) → Fin (a + (b + (c + d))) :=
  fun i => Fin.cast (by simp [Nat.add_comm, Nat.add_left_comm]) i

def finId_X_Assoc_Inv (a b c d : ℕ) : Fin (a + (b + (c + d))) → Fin (a + (b + c + d)) :=
  fun i => Fin.cast (by simp [Nat.add_comm, Nat.add_left_comm]) i

def finId_X_Id_X_Assoc (x a b c d : ℕ) :
    Fin (x + (a + (b + c + d))) → Fin (x + (a + (b + (c + d)))) :=
  fun i => Fin.cast (by simp [Nat.add_comm, Nat.add_left_comm]) i

def finId_X_Id_X_Assoc_Inv (x a b c d : ℕ) :
    Fin (x + (a + (b + (c + d)))) → Fin (x + (a + (b + c + d))) :=
  fun i => Fin.cast (by simp [Nat.add_comm, Nat.add_left_comm]) i

def finComm (a b : ℕ) : Fin (a + b) → Fin (b + a) :=
  fun i => Fin.cast (by simp [Nat.add_comm]) i

def finLeftComm (a b c : ℕ) : Fin (a + (b + c)) → Fin (b + (a + c)) :=
  fun i => Fin.cast (by rw [Nat.add_left_comm]) i

def finRightComm (a b c : ℕ) : Fin (a + b + c) → Fin (a + c + b) :=
  fun i => Fin.cast (by rw [Nat.add_right_comm]) i

def finComm_X_Id (a b c : ℕ) : Fin (a + b + c) → Fin (b + a + c) :=
  fun i => Fin.cast (by simp [Nat.add_comm, Nat.add_left_comm]) i

def finId_X_Comm (a b c : ℕ) : Fin (a + (b + c)) → Fin (a + (c + b)) :=
  fun i => Fin.cast (by simp [Nat.add_comm]) i

def finComm_X_Id_X_Id (a b c d : ℕ) : Fin (a + b + c + d) → Fin (b + a + c + d) :=
  fun i => Fin.cast (by simp [Nat.add_comm, Nat.add_left_comm]) i

theorem finComm_finZeroAddInv_is_finAddZeroInv (n : ℕ) (i : Fin n) :
  finComm 0 n (finZeroAdd_Inv n i) = finAddZero_Inv n i := by
  simp [finComm, finZeroAdd_Inv, finAddZero_Inv, Fin.cast]

theorem finComm_involutive (a b : ℕ) (i : Fin (a + b)) :
  finComm b a (finComm a b i) = i := by
  simp [finComm, Fin.cast]

theorem finComm_X_Id_involutive (a b c : ℕ) (i : Fin (a + b + c)) :
  finComm_X_Id b a c (finComm_X_Id a b c i) = i := by
  simp [finComm_X_Id, Fin.cast]

theorem finId_X_Comm_involutive (a b c : ℕ) (i : Fin (a + (b + c))) :
  finId_X_Comm a c b (finId_X_Comm a b c i) = i := by
  simp [finId_X_Comm, Fin.cast]

theorem finComm_X_Id_finAssoc_is_finAssoc_finComm_X_Id_Id
  (a b c d : ℕ) (i : Fin (a + b + c + d)) :
  finComm_X_Id a b (c + d) (finAssoc (a + b) c d i)
  =
  finAssoc (b + a) c d (finComm_X_Id_X_Id a b c d i)
  := by
    simp [finAssoc, finComm_X_Id, finComm_X_Id_X_Id, Fin.cast]

theorem finPentagonIdentity
  (a b c d : ℕ) (i : Fin (a + b + c + d)) :
  finId_X_Assoc a b c d (finAssoc a (b + c) d (finAssoc_X_Id a b c d i))
  =
  finAssoc a b (c + d) (finAssoc (a + b) c d i)
  := by
    simp [finAssoc, finAssoc_X_Id, finId_X_Assoc, Fin.cast]

@[simp]
theorem finZeroAdd_X_Id_comp_finZeroAdd_X_Id_Inv_is_id
  (a b : ℕ) :
    (finZeroAdd_X_Id a b) ∘ (finZeroAdd_X_Id_Inv a b) = id := by
  funext i
  simp [finZeroAdd_X_Id, finZeroAdd_X_Id_Inv, Function.comp]

@[simp]
theorem finZeroAdd_X_Id_Inv_comp_finZeroAdd_X_Id_is_id
  (a b : ℕ) :
    (finZeroAdd_X_Id_Inv a b) ∘ (finZeroAdd_X_Id a b) = id := by
  funext i
  simp [finZeroAdd_X_Id, finZeroAdd_X_Id_Inv, Function.comp]

@[simp]
theorem finAddZero_X_Id_comp_finAddZero_X_Id_Inv_is_id
  (a b : ℕ) :
    (finAddZero_X_Id a b) ∘ (finAddZero_X_Id_Inv a b) = id := by
  funext i
  simp [finAddZero_X_Id, finAddZero_X_Id_Inv, Function.comp]

@[simp]
theorem finAddZero_X_Id_Inv_comp_finAddZero_X_Id_is_id
  (a b : ℕ) :
    (finAddZero_X_Id_Inv a b) ∘ (finAddZero_X_Id a b) = id := by
  funext i
  simp [finAddZero_X_Id, finAddZero_X_Id_Inv, Function.comp]


@[simp]
theorem finAssoc_X_Id_comp_finAssoc_X_Id_Inv_is_id
  (a b c d : ℕ) :
    (finAssoc_X_Id a b c d) ∘ (finAssoc_X_Id_Inv a b c d) = id := by
  funext i
  simp [finAssoc_X_Id, finAssoc_X_Id_Inv, Function.comp]

@[simp]
theorem finAssoc_X_Id_Inv_comp_finAssoc_X_Id_is_id
  (a b c d : ℕ) :
    (finAssoc_X_Id_Inv a b c d) ∘ (finAssoc_X_Id a b c d) = id := by
  funext i
  simp [finAssoc_X_Id, finAssoc_X_Id_Inv, Function.comp]

@[simp]
theorem finAssoc_comp_finAssoc_Inv_is_id
  (n k l : ℕ) :
    (finAssoc n k l) ∘ (finAssoc_Inv n k l) = id := by
  funext i
  simp [finAssoc, finAssoc_Inv, Function.comp]

@[simp]
theorem finAssoc_Inv_comp_finAssoc_is_id
  (n k l : ℕ) :
    (finAssoc_Inv n k l) ∘ (finAssoc n k l) = id := by
  funext i
  simp [finAssoc, finAssoc_Inv, Function.comp]

@[simp]
theorem finId_X_Assoc_comp_finId_X_Assoc_Inv_is_id
  (a b c d : ℕ) :
    (finId_X_Assoc a b c d) ∘ (finId_X_Assoc_Inv a b c d) = id := by
  funext i
  simp [finId_X_Assoc, finId_X_Assoc_Inv, Function.comp]

@[simp]
theorem finId_X_Assoc_Inv_comp_finId_X_Assoc_is_id
  (a b c d : ℕ) :
    (finId_X_Assoc_Inv a b c d) ∘ (finId_X_Assoc a b c d) = id := by
  funext i
  simp [finId_X_Assoc, finId_X_Assoc_Inv, Function.comp]

@[simp]
theorem finId_X_Id_X_Assoc_Inv_comp_finId_X_Id_X_Assoc_is_id
  (a b c d e : ℕ) :
    (finId_X_Id_X_Assoc_Inv a b c d e) ∘ (finId_X_Id_X_Assoc a b c d e) = id := by
  funext i
  simp [finId_X_Id_X_Assoc, finId_X_Id_X_Assoc_Inv, Function.comp]

@[simp]
theorem finId_X_Id_X_Assoc_comp_finId_X_Id_X_Assoc_Inv_is_id
  (a b c d e : ℕ) :
    (finId_X_Id_X_Assoc a b c d e) ∘ (finId_X_Id_X_Assoc_Inv a b c d e) = id := by
  funext i
  simp [finId_X_Id_X_Assoc, finId_X_Id_X_Assoc_Inv, Function.comp]

@[simp]
theorem finAddZero_comp_finAddZero_Inv_is_id
  (n : ℕ) :
    (finAddZero n) ∘ (finAddZero_Inv n) = id := by
  funext i
  simp [finAddZero, finAddZero_Inv, Function.comp]

@[simp]
theorem finAddZero_Inv_comp_finAddZero_is_id
  (n : ℕ) :
    (finAddZero_Inv n) ∘ (finAddZero n) = id := by
  funext i
  simp [finAddZero, finAddZero_Inv, Function.comp]

@[simp]
theorem finZeroAdd_comp_finZeroAdd_Inv_is_id
  (n : ℕ) :
    (finZeroAdd n) ∘ (finZeroAdd_Inv n) = id := by
  funext i
  simp [finZeroAdd, finZeroAdd_Inv, Function.comp]

@[simp]
theorem finZeroAdd_Inv_comp_finZeroAdd_is_id
  (n : ℕ) :
    (finZeroAdd_Inv n) ∘ (finZeroAdd n) = id := by
  funext i
  simp [finZeroAdd, finZeroAdd_Inv, Function.comp]

end SumCheck
