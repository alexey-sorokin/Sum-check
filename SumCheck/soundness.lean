import SumCheck.completeness
import Mathlib.Data.Finset.Card
-- import Mathlib.Algebra.BigOperators.Basic

noncomputable section
open Classical
open scoped BigOperators
open NEO

namespace NEO

universe u
variable {F : Type u} [Field F]

/-!
# Soundness building blocks for Sum-Check (degree-1 / multilinear case)

We model probabilities over a finite set `S : Finset F` via cardinalities.
The key “probabilistic” step in sum-check soundness is:

If a cheating univariate message `g` (degree ≤ 1) differs from the honest univariate
polynomial `h` (degree ≤ 1), then the verifier’s random challenge `r ∈ S` makes them
match with probability ≤ 1 / |S|, because two distinct affine functions can coincide
on at most one point.
-/

/-- Constant vector of length `1`. -/
def vecConst1 (x : F) : vec F 1 := fun _ => x

/-- Evaluate `func F 1` as a usual function `F → F`. -/
def eval1 (g : func F 1) (x : F) : F := g (vecConst1 (F := F) x)

/-- Affine (degree ≤ 1) predicate for `func F 1`. -/
def IsAffine1 (g : func F 1) : Prop :=
  ∃ a b : F, ∀ x : F, eval1 (F := F) g x = a * x + b

/-- Extensionality for `vec F 1`: determined by value at `0`. -/
lemma vec1_ext (v w : vec F 1)
  (h : v ⟨0, Nat.succ_pos 0⟩ = w ⟨0, Nat.succ_pos 0⟩) : v = w := by
  funext i
  apply Fin.ext
  have : i.1 = 0 := Nat.eq_of_lt_succ i.2
  simpa [this] using congrArg (fun t => (t : F)) h

/-- If two `func F 1` agree on all scalars, then they are equal. -/
lemma func1_ext {g h : func F 1}
  (he : ∀ x : F, eval1 (F := F) g x = eval1 (F := F) h x) : g = h := by
  funext v
  -- rewrite `v` to the constant vector with the same value
  have hv : v = vecConst1 (F := F) (v ⟨0, Nat.succ_pos 0⟩) := by
    apply vec1_ext
    simp [vecConst1]
  simpa [eval1, hv] using he (v ⟨0, Nat.succ_pos 0⟩)

/-- A nonzero affine function has at most one root in a finite set `S`. -/
lemma affine_roots_card_le_one (S : Finset F) {a b : F}
  (hne : (a, b) ≠ (0, 0)) :
  ((S.filter fun x => a * x + b = 0).card) ≤ 1 := by
  classical
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      apply hne
      simp [ha, hb]
    have : S.filter (fun x => a * x + b = 0) = ∅ := by
      ext x
      simp [ha, hb]
    simp [this]
  · -- `a ≠ 0`: unique solution `x0 = -b/a`
    let x0 : F := (-b) / a
    have huniq : ∀ x, a * x + b = 0 → x = x0 := by
      intro x hx
      have : a * x = -b := by linarith
      -- multiply both sides by `a⁻¹`
      have := congrArg (fun t => t * a⁻¹) this
      -- (a*x)*a⁻¹ = x and (-b)*a⁻¹ = (-b)/a
      simpa [mul_assoc, ha, x0, div_eq_mul_inv] using this
    have hsub :
      (S.filter fun x => a * x + b = 0) ⊆ ({x0} : Finset F) := by
      intro x hx
      have hx' : a * x + b = 0 := (Finset.mem_filter.mp hx).2
      have : x = x0 := huniq x hx'
      simpa [this]
    exact le_trans (Finset.card_le_of_subset hsub) (by simp)

/-- If two affine `func F 1` differ, they coincide on ≤ 1 point of `S`. -/
lemma affine_eq_points_card_le_one (S : Finset F) {g h : func F 1}
  (hg : IsAffine1 (F := F) g) (hh : IsAffine1 (F := F) h) (hneq : g ≠ h) :
  ((S.filter fun x => eval1 (F := F) g x = eval1 (F := F) h x).card) ≤ 1 := by
  classical
  rcases hg with ⟨ag, bg, hg⟩
  rcases hh with ⟨ah, bh, hh⟩
  have hpair : ((ag - ah), (bg - bh)) ≠ (0, 0) := by
    intro hpair
    have hag : ag = ah := by
      have : ag - ah = 0 := by simpa using congrArg Prod.fst hpair
      linarith
    have hbg : bg = bh := by
      have : bg - bh = 0 := by simpa using congrArg Prod.snd hpair
      linarith
    apply hneq
    apply func1_ext (F := F)
    intro x
    simp [eval1, hg, hh, hag, hbg]
  -- reduce to roots of affine difference
  have :
      (S.filter fun x => eval1 (F := F) g x = eval1 (F := F) h x)
        =
      (S.filter fun x => (ag - ah) * x + (bg - bh) = 0) := by
    ext x
    -- expand hg/hh and move to one side
    simp [hg, hh]
    -- (ag*x+bg = ah*x+bh) ↔ ((ag-ah)*x + (bg-bh) = 0)
    ring
  simpa [this] using
    affine_roots_card_le_one (F := F) S (a := ag - ah) (b := bg - bh) hpair

/-!
## “Probability” as cardinality ratio

For a finite `S`, a uniform random challenge `r ∈ S` makes an event `E : F → Prop`
hold with probability `card {x∈S | E x} / card S`.

The lemma below is the exact step used each round in sum-check soundness:
if the prover’s affine message differs from the honest affine message, it fools
the verifier in that round with probability ≤ 1/|S|.
-/

/-- One-round bound: two distinct affine messages match on ≤ 1 challenge in `S`. -/
theorem one_round_soundness
  (S : Finset F) (hS : 1 < S.card)
  {g h : func F 1}
  (hg : IsAffine1 (F := F) g) (hh : IsAffine1 (F := F) h) (hneq : g ≠ h) :
  ((S.filter fun x => eval1 (F := F) g x = eval1 (F := F) h x).card) * 1
    ≤ S.card := by
  have hle : (S.filter fun x => eval1 (F := F) g x = eval1 (F := F) h x).card ≤ 1 :=
    affine_eq_points_card_le_one (F := F) S hg hh hneq
  -- multiply both sides by 1, and use `1 ≤ S.card` from `hS`
  have hS1 : 1 ≤ S.card := Nat.succ_le_iff.mp (lt_of_lt_of_le (Nat.lt_succ_self 0) (le_of_lt hS))
  simpa using le_trans (Nat.mul_le_mul_right 1 hle) (by simpa using hS1)

/-!
## How to finish full sum-check soundness in *your* project

You already have:
* `verifierCheck : (n : ℕ) → func F n → proverTranscript n → Prop`
* honest messages `proverComp` (in completeness)

To prove full soundness for multilinear polynomials, you do:

Induction on `n`:
- Define the *honest* round-0 univariate polynomial `H0(r)` (a `func F 1`)
  as the true partial sum over the remaining hypercube.
- Compare it to the prover’s claimed round-0 message `G0(r)` from the transcript.
- If `G0 = H0` (as functions) then reduce to the tail instance.
- If `G0 ≠ H0`, apply `one_round_soundness` to show the bad challenges at this
  round are ≤ `|S|^n` (i.e. probability ≤ 1/|S|), then union-bound across rounds.

Because your `verifierCheck` chooses the challenge via
`randomChallengeInitial := vecTakeHead 1 n (vecComm n 1 randomChallenge)`,
your induction should follow that same “head extraction” and the exact `p`-update
already in `verifierCheck` (copy-paste its `p ↦ ...` transition into the proof).

The ONLY genuinely “probabilistic” lemma you need per round is `one_round_soundness`.
Everything else is algebra + counting + your recursion structure.
-/

end NEO
