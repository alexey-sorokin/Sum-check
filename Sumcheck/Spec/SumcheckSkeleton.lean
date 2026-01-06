import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators

namespace Sumcheck

universe u
variable {F : Type u} [Field F]

noncomputable section

/- Basic objects -/

abbrev Point (n : ℕ) : Type u := Fin n → F
abbrev BoolPoint (n : ℕ) : Type := Fin n → Fin 2

/-- Поднять булеву точку в `F^n`. -/
def liftBool {n : ℕ} (b : BoolPoint n) : Point (F := F) n :=
  fun i => ((b i).val : F)

/-- Все булевы точки `{0,1}^n` как finset. -/
def hypercube (n : ℕ) : Finset (BoolPoint n) :=
  Finset.univ

/-- Сумма по булеву гиперкубу. -/
def hypercubeSum {n : ℕ} (g : Point (F := F) n → F) : F :=
  ∑ b ∈ hypercube n, g (liftBool (F := F) b)

/- Partial assignment / extension (for “fix first k coords, sum over rest”) -/

abbrev Partial (k : ℕ) : Type u := Fin k → F

/-- Хвост: координаты `1..n` (сдвиг). -/
def tail {n : ℕ} (x : Point (F := F) (n + 1)) : Point (F := F) n :=
  fun i => x i.succ

/-- Приклеить значение первой координаты `b` к хвосту `xs`. -/
def cons {n : ℕ} (b : F) (xs : Point (F := F) n) : Point (F := F) (n + 1) :=
  fun i => Fin.cases b xs i

/-- Раунд 0/1: сумма по хвосту после фиксации первой координаты. -/
def round1Sum {n : ℕ} (g : Point (F := F) (n + 1) → F) (b : F) : F :=
  ∑ xs : BoolPoint n, g (cons (F := F) b (liftBool (F := F) xs))

/- Transcript / messages (skeleton) -/

/-- Сообщение prover’а в раунде (пока просто значение в `F`, скелет). -/
abbrev Msg : Type u := F

/-- Транскрипт: вызовы verifier’а `r_k` и ответы prover’а `p_k` (скелет). -/
structure Transcript (n : ℕ) where
  r : Fin n → F
  p : Fin n → Msg

/-- “Полином раунда”, который prover *заявляет* в раунде k (скелет). -/
def roundPoly {n : ℕ} (k : Fin n) (g : Point (F := F) n → F) (tr : Transcript (F := F) n) : Msg :=
  0

/-- Проверка согласованности транскрипта (скелет). -/
def consistent {n : ℕ} (g : Point (F := F) n → F) (tr : Transcript (F := F) n) : Prop :=
  ∀ k : Fin n, tr.p k = roundPoly (F := F) (n := n) k g tr

/-- Verifier accepts (скелет): просто проверяет `consistent`. -/
def verifierAccepts {n : ℕ} (g : Point (F := F) n → F) (tr : Transcript (F := F) n) : Prop :=
  consistent (F := F) (n := n) g tr

/-- Completeness skeleton (пока без содержательного утверждения). -/
theorem completeness_skeleton {n : ℕ} (g : Point (F := F) n → F) : True :=
  trivial

end Sumcheck
