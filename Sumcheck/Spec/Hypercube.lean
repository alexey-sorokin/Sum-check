import Mathlib.Algebra.Polynomial.BigOperators

open scoped BigOperators

variable {F : Type*} [Field F]
variable {n : ℕ}

/-- Все булевы точки {0,1}ⁿ -/
def hypercube : Finset (Fin n → Fin 2) :=
  Finset.univ

/-- Склеить: голова `a0` и хвост `v : Fin n → α` в вектор длины `n+1`. -/
def vecCons {α : Type*} (a0 : α) (v : Fin n → α) : Fin (n+1) → α :=
  Fin.cases a0 (fun i => v i)

/-- Сумма функции по гиперкубу -/
def hypercubeSum (g : (Fin n → F) → F) : F :=
  ∑ x ∈ hypercube, g (fun i => (x i : F))

/--
Первые “две суммы” sum-check для фиксированного первого бита `b ∈ {0,1}`:
S(b) = ∑_{x ∈ {0,1}^n} g( (b, x) ) .
Здесь `(b, x)` — это вектор длины `n+1`.
-/
def round1Sum (g : (Fin (n+1) → F) → F) (b : Fin 2) : F :=
  hypercubeSum (F := F) (n := n) (fun x =>
    g (vecCons (b : F) (fun i => (x i : F)))
  )

/-- Часто удобно иметь отдельно b=0 и b=1. -/
def round1Sum0 (g : (Fin (n+1) → F) → F) : F := round1Sum (n := n) g 0
def round1Sum1 (g : (Fin (n+1) → F) → F) : F := round1Sum (n := n) g 1

/-- "Приставить голову": из `a : α` и хвоста `x : Fin n → α`
    получаем вектор длины `n+1`. -/
def finCons {α : Type*} {n : ℕ} (a : α) (x : Fin n → α) : Fin (n+1) → α :=
  fun i => Fin.cases a (fun j => x j) i

/-- Голова вектора длины `n+1` -/
def finHead {α : Type*} {n : ℕ} (v : Fin (n+1) → α) : α :=
  v 0

/-- Хвост вектора длины `n+1` -/
def finTail {α : Type*} {n : ℕ} (v : Fin (n+1) → α) : Fin n → α :=
  fun j => v j.succ

@[simp] lemma finCons_head {α : Type*} {n : ℕ} (a : α) (x : Fin n → α) :
    finHead (finCons a x) = a := by
  rfl

@[simp] lemma finCons_tail {α : Type*} {n : ℕ} (a : α) (x : Fin n → α) :
    finTail (finCons a x) = x := by
  rfl

@[simp] lemma finCons_zero {α : Type*} {n : ℕ} (a : α) (x : Fin n → α) :
    finCons a x 0 = a := by
  rfl

@[simp] lemma finCons_succ {α : Type*} {n : ℕ} (a : α) (x : Fin n → α) (j : Fin n) :
    finCons a x j.succ = x j := by
  rfl
