import Mathlib.Algebra.Polynomial.BigOperators

open scoped BigOperators

variable {n : ℕ}

/-- "Приписать голову": (b, xs) ↦ вектор длины n+1, где в нуле стоит b, дальше xs. -/
def consBool (b : Fin 2) (xs : Fin n → Fin 2) : Fin (n + 1) → Fin 2 :=
  fun i => Fin.cases b xs i

/-- "Хвост": взять координаты 1..n (через succ). -/
def tailBool (x : Fin (n + 1) → Fin 2) : Fin n → Fin 2 :=
  fun i => x i.succ

/-- Хвост после cons возвращает исходный xs. -/
theorem tail_consBool (b : Fin 2) (xs : Fin n → Fin 2) :
    tailBool (consBool b xs) = xs := by
  -- здесь funext УМЕСТЕН: цель = равенство функций Fin n → Fin 2
  funext i
  simp [tailBool, consBool]

/-- Разрезаем вектор длины n+1 на (голова, хвост). -/
def splitBool (x : Fin (n + 1) → Fin 2) : Fin 2 × (Fin n → Fin 2) :=
  (x 0, tailBool x)

/-- Склеиваем (голова, хвост) обратно в вектор длины n+1. -/
def unsplitBool (p : Fin 2 × (Fin n → Fin 2)) : Fin (n + 1) → Fin 2 :=
  consBool p.1 p.2

/-- split ∘ unsplit = id -/
theorem split_unsplit (p : Fin 2 × (Fin n → Fin 2)) :
    splitBool (unsplitBool (n := n) p) = p := by
  cases p with
  | mk b xs =>
    -- цель: ( (cons b xs) 0 , tail(cons b xs) ) = (b, xs)
    ext
    · simp [splitBool, unsplitBool, consBool]
    · simp [splitBool, unsplitBool, tail_consBool]

/-- unsplit ∘ split = id -/
theorem unsplit_split (x : Fin (n + 1) → Fin 2) :
    unsplitBool (n := n) (splitBool (n := n) x) = x := by
  -- цель: равенство функций Fin (n+1) → Fin 2
  funext i
  -- разбиваем i на 0 и succ i
  cases i using Fin.cases with
  | zero =>
      simp [unsplitBool, splitBool, consBool]
  | succ i =>
      simp [unsplitBool, splitBool, consBool, tailBool]
