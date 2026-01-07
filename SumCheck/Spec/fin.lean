import SumCheck.Spec.common

noncomputable section
open Classical

namespace SumCheck

universe u
variable {F : Type u} [Field F]


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

def finRightComm (n k l : ℕ) : Fin (n + k + l) → Fin (n + l + k) :=
  fun i => Fin.cast (by rw [Nat.add_right_comm]) i

theorem finComm_finZeroAddInv_is_finAddZeroInv (n : ℕ) (i : Fin n) :
  finComm 0 n (finZeroAddInv n i) = finAddZeroInv n i := by
  simp [finComm, finZeroAddInv, finAddZeroInv, Fin.cast]

theorem finComm_involutive (a b : ℕ) (i : Fin (a + b)) :
  finComm b a (finComm a b i) = i := by
  simp [finComm, Fin.cast]

end SumCheck
