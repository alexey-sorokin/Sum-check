import Mathlib.Algebra.Polynomial.BigOperators
import Sumcheck.Spec.Hypercube
import Sumcheck.Spec.HypercubeSplit

open scoped BigOperators

variable {F : Type*} [Field F]
variable {n : ℕ}

/--
Раунд 1 sum-check (спецификация “суммирования по хвосту”):

Для b ∈ {0,1} определяем
  round1Sum g b = ∑_{xs ∈ {0,1}^n} g( (b :: xs) )
где (b :: xs) — булев вектор длины n+1, затем 0/1 приводим к F по координатам.
-/
def round1Sum (g : (Fin (n + 1) → F) → F) (b : Fin 2) : F :=
  ∑ xs ∈ (hypercube (n := n)),
    g (fun i => (consBool (n := n) b xs i : F))

/-- Удобная лемма для случая b = 0. -/
theorem round1Sum_at0 (g : (Fin (n + 1) → F) → F) :
    round1Sum (F := F) (n := n) g (0 : Fin 2)
      =
    ∑ xs ∈ (hypercube (n := n)),
      g (fun i => (consBool (n := n) (0 : Fin 2) xs i : F)) := by
  simp [round1Sum]

/-- Удобная лемма для случая b = 1. -/
theorem round1Sum_at1 (g : (Fin (n + 1) → F) → F) :
    round1Sum (F := F) (n := n) g (1 : Fin 2)
      =
    ∑ xs ∈ (hypercube (n := n)),
      g (fun i => (consBool (n := n) (1 : Fin 2) xs i : F)) := by
  simp [round1Sum]
