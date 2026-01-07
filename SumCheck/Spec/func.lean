import SumCheck.Spec.vec

noncomputable section
open Classical
open SumCheck

namespace SumCheck

universe u
variable {F : Type u} [Field F]

def func (F : Type u) [Field F] (n : ℕ) : Type u :=
  vec F n → F



def funcAssoc (n k l : ℕ) : func F (n + k + l) → func F (n + (k + l)) :=
  fun p v => p (vecAssocInv  n k l v)

def funcAssocInv (n k l : ℕ) : func F (n + (k + l)) → func F (n + k + l) :=
  fun p v => p (vecAssoc n k l v)

def funcAddComm (a b : ℕ) : func F (a + b) → func F (b + a) :=
  fun p v => p (vecAddComm b a v)

def funcRightComm (n k l : ℕ) : func F (n + k + l) → func F (n + l + k) :=
  fun p v => p (vecRightComm n l k v)


theorem funcAddComm_involutive (a b : ℕ) (p : func F (a + b)) :
  funcAddComm b a (funcAddComm a b p) = p
  := by
    unfold funcAddComm
    simp [vecAddComm_involutive]


end SumCheck
