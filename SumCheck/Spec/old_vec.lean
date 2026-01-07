import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import SumСheck.Spec.fin

noncomputable section
open Classical
open Sumcheck

namespace Sumcheck

universe u
variable {F : Type u} [Field F]

def vec (F : Type u) [Field F] (n : ℕ) : Type u :=
  Fin n → F




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

def vecRightComm (n k l : ℕ) : vec F (n + k + l) → vec F (n + l + k) :=
  fun v i => v (finRightComm n l k i)

theorem vecAddComm_involutive (a b : ℕ) (v : vec F (a + b)) :
  vecAddComm b a (vecAddComm a b v) = v := by
  unfold vecAddComm
  simp [finComm_involutive]


theorem vecComm_vecZeroAddInv_is_vecAddZeroInv (n : ℕ) (v : vec F n) :
  vecAddComm 0 n (vecZeroAddInv n v) = vecAddZeroInv n v := by
  funext i
  unfold vecZeroAddInv vecAddZeroInv vecAddComm
  simp [finZeroAdd, finAddZeroInv]
  simp [Fin.cast]
  rfl


end Sumcheck
