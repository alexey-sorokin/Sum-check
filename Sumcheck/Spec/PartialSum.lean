import Sumcheck.Spec.Hypercube

open scoped BigOperators

variable {F : Type*} [Field F]
variable {n : ℕ}

/--
Частичная сумма по хвосту:
фиксируем первую координату в `t`,
а по остальным n координатам суммируем по {0,1}ⁿ.

h(t) = ∑_{x∈{0,1}ⁿ} g(t, x)
-/
def partialSum
  (g : (Fin (n + 1) → F) → F) :
  F → F :=
fun t =>
  ∑ x ∈ hypercube (n := n),
    g (Fin.cons t (fun i => (x i : F)))
