import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

def compLeft {β γ δ : Type} (k : γ → δ) {f1 f2 : β → γ} :
    f1 = f2 → (k ∘ f1 = k ∘ f2) :=
  congrArg (k ∘ ·)

def compRight {α β γ : Type} (g : α → β) {f1 f2 : β → γ} :
    f1 = f2 → (f1 ∘ g = f2 ∘ g) :=
  congrArg (· ∘ g)
