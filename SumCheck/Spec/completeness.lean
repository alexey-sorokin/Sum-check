
import SumCheck.Spec.evalAndSum

noncomputable section
open Classical
open SumCheck

namespace SumCheck

universe u
variable {F : Type u} [Field F]

/-!
# Sum-check protocol (function-only skeleton)

This file defines:
* `hypercubeSum n p` = `∑_{x∈{0,1}^n} p x`
* `expectedG p r i : F → F` the honest prover's round message (partial sum)
* `Transcript` and a verifier predicate `VerifierAccepts`
* `honestTranscript` and a completeness lemma for the honest transcript

Soundness against cheating provers requires degree / polynomial constraints and is **not**
formalized here (only a trivial "soundness for the honest prover").
-/

def cutHeadProverComp (n : ℕ) : (Fin (n + 1) → func F 1) → (Fin n → func F 1)
| xs => fun i => xs ⟨i.1.succ, Nat.succ_lt_succ i.2⟩

/-- Honest round-`i` message as a univariate function.
`g_i(t) = Σ_{b∈{0,1}^{n-(i+1)}} p(r₀,…,r_{i-1}, t, b)`.
Here `i : Fin n` is 0-indexed.
-/
/-
def proverComputations_old (n : ℕ) (p : func F n) (r : vec F n) : Fin n → func F 1 :=
  fun i t =>
    -- let m : ℕ := i.1
    have hm1 : i.1 + 1 ≤ n := Nat.succ_le_of_lt i.2

    -- Substitute first `m` vars by `r's`, then substitute the next var by `t`, then sum the remaining `n - (m + 1)`
    funcSumTotal (F := F) (n - (i.1 + 1))
      (funcSubsHeadSingle (F := F) (n := n - (i.1 + 1)) (vecOne t)
        (funcSubsHead (F := F) (n := 1 + (n - (i.1 + 1))) (m := i.1)
          (vecTakeHead (F := F) (n := n) (m := i.1) (Nat.le_of_lt i.2) r)
          (funcAssoc (F := F) i.1 1 (n - (i.1 + 1))
            (funcAddSubLE (F := F) (a := i.1 + 1) (b := n) hm1 p))))
-/

def proverComputations (n : ℕ) (p : func F n) (r : vec F n) : Fin n → func F 1 :=
  fun i =>
    have hm1 : i.1 + 1 ≤ n := Nat.succ_le_of_lt i.2
    -- k = number of variables to be summed out (after the free one)
    -- let k : ℕ := n - (i.1 + 1)
    funcSubsHead (F := F) (n := 1) (m := i.1)
      (vecTakeHead (F := F) (n := n) (m := i.1) (Nat.le_of_lt i.2) r)
      (funcSumTail (F := F) (n := i.1 + 1) (k := (n - (i.1 + 1)))
          (funcAddSubLE (F := F) (a := i.1 + 1) (b := n) hm1 p))


/-
    funcSumTail (F := F) (n := 1) (k := n - (i.1 + 1))
      (funcSubsHead (F := F) (n := 1 + (n - (i.1 + 1))) (m := i.1)
        (vecTakeHead (F := F) (n := n) (m := i.1) (Nat.le_of_lt i.2) r)
        (funcAssoc (F := F) i.1 1 (n - (i.1 + 1))
          (funcAddSubLE (F := F) (a := i.1 + 1) (b := n) hm1 p)))
-/


/-- Transcript for `n` rounds (one univariate message per round). -/
structure Transcript (n : ℕ) where
  claimedSum : F
  randomChallenge : vec F n
  proverComputations : Fin n → func F 1


private theorem Transcript.ext'
  {n : ℕ} {t₁ t₂ : Transcript (F := F) n}
  (h₁ : t₁.claimedSum = t₂.claimedSum)
  (h₂ : t₁.randomChallenge = t₂.randomChallenge)
  (h₃ : t₁.proverComputations = t₂.proverComputations) :
  t₁ = t₂ := by
  cases t₁
  cases t₂
  cases h₁
  cases h₂
  cases h₃
  rfl

/-- Honest Prover transcript: claim is the true hypercube sum, messages are true partial sums. -/
def honestProverTranscript (n : ℕ) (p : func F n) (r : vec F n) : Transcript (F := F) n :=
  { claimedSum := funcSumTotal n p
    randomChallenge := r
    proverComputations := proverComputations (F := F) n p r}

/-- Verifier checks (sum-check consistency equations). -/
def verifierChecks : (n : ℕ) → func F n → Transcript (F := F) n → Prop
| 0, p, transcript =>
    -- no rounds: the "sum" is just evaluation at the empty point
    transcript.claimedSum = funcZero p
| Nat.succ n, p, transcript =>
    -- round 0 consistency + recursive checks on the tail instance
    let proverInitialComputation := transcript.proverComputations ⟨0, Nat.succ_pos _⟩

    (funcSumTotal 1 proverInitialComputation = transcript.claimedSum)
    ∧
    verifierChecks n
      (fun xs =>
        (funcComm n 1 p)
          (vecAppHeadSingle (F := F) n
            (transcript.randomChallenge ⟨0, Nat.succ_pos _⟩) xs
          )
      )
      {
        claimedSum :=
          proverInitialComputation
            (vecOne_Inv (transcript.randomChallenge ⟨0, Nat.succ_pos _⟩))
        randomChallenge :=
          vecCutHeadSingle (F := F) n (vecComm n 1 transcript.randomChallenge)
        proverComputations :=
          cutHeadProverComp (F := F) n (transcript.proverComputations)
      }

/-!
## Completeness (honest prover)

The proof is by induction on `n`. The induction step is essentially the defining
equation of `funcSumTailSingle` / `funcSumTail` plus unfolding `proverComputations`.
-/

/-- Base case: `proverComputations` for `n = 0` is vacuous (not used). -/

/- Completeness: the verifier accepts the honest prover transcript for any `p` and random challenges `r`. -/
theorem funcSumCheckcompleteness {n : ℕ} (p : func F n) (r : vec F n) :
    verifierChecks (F := F) n p (honestProverTranscript n p r) := by
  classical
  induction n with
  | zero =>
      -- n = 0
      simp [verifierChecks, honestProverTranscript, funcSumTotal]
      rfl
  | succ n ih =>
      -- unfold verifier, honest transcript, and the first-round message
      -- We reduce the n+1 case to the n case using the definition of `funcSumTotal`.
      constructor
      ·
        unfold honestProverTranscript
        simp
        unfold proverComputations
        unfold funcSumTotal
        have h1 (g : func F (0 + (n + 1))) :
          funcSumTail (F := F) 0 (n + 1) g
          =
          funcSumTailSingle (F := F) 0
            (funcSumTail (0 + 1) n
              (funcAssoc_Inv 0 1 n
                (funcId_X_Comm (F := F) 0 n 1 g)))
          := by
          exact (congrArg (fun f => f g)
            (funcSumTail_is_funcSumTailSingle_funcSumTail_funcAssoc_Inv_funcId_X_Comm 0 n))
        rw [h1]
        simp [funcSubsHead]
        have hl (g : func F 1) :
          funcZeroAdd_Inv 1
            (funcZeroAdd 1 g)
          =
          g
          := by
            simp
            rfl

        rw [hl]

        have h2 (g : func F (0 + 1)) :
            funcSumTail (F := F) 0 1 g = funcSumTailSingle (F := F) 0 g := by
          -- turn the goal into a reflexive one
          simpa using congrArg (fun (f : func F (0 + 1) → _) => f g)
            (funcSumTail_1_is_funcSumTailSingle (F := F) 0)

        rw [h2]
        rfl
      ·

        /-
        simp [verifierChecks]
        unfold verifierChecks
        unfold honestProverTranscript
        simp
        unfold honestProverTranscript at ih
        -/

        -- SECOND CONJUNCT: use ih

        let p' : func F n :=
          fun xs =>
            (funcComm n 1 p)
              (vecAppHeadSingle (F := F) n (r ⟨0, Nat.succ_pos _⟩) xs)

        let r' : vec F n :=
          vecCutHeadSingle (F := F) n (vecComm n 1 r)

        have ht :
            { claimedSum :=
              (proverComputations (F := F) (n + 1) p r ⟨0, Nat.succ_pos _⟩)
                (vecOne_Inv (r ⟨0, Nat.succ_pos _⟩)),
              randomChallenge := r',
              proverComputations :=
              cutHeadProverComp (F := F) n
                (proverComputations (F := F) (n + 1) p r) }
            =
            honestProverTranscript (F := F) (n := n) (p := p') r'
            := by
            apply Transcript.ext'
            · -- claimedSum field
              simp [honestProverTranscript, p', r']
              -- here you’ll get a real math goal: show your claimedSum equals `funcSumTotal n p'`
              unfold proverComputations
              unfold funcSumTotal
              unfold funcZero
              have h3 (g : func F ((0 + 1) + ((n + 1) - (0 + 1)))) :
                funcSubsHead (F := F) 1 0
                  (vecTakeHead (F := F) (n := n + 1) (m := 0) (Nat.zero_le (n + 1)) r)
                  (funcSumTail (0 + 1) ((n + 1) - (0 + 1)) g)
                =
                funcSumTail 1 ((n + 1) - (0 + 1))
                  (funcSubsHead (F := F) (1 + ((n + 1) - (0 + 1))) 0
                    (vecTakeHead (F := F) (n := n + 1) (m := 0) (Nat.zero_le (n + 1)) r)
                    (funcAssoc 0 1 ((n + 1) - (0 + 1)) g))
                := by
                exact
                  (congrArg (fun f => f g)
                    (sumTailLong_substHeadLong_comm 0 1 ((n + 1) - (0 + 1))
                      (vecTakeHead (F := F) (n := n + 1) (m := 0) (Nat.zero_le (n + 1)) r))
                  )
              simp at h3
              simp
              rw [h3]
              unfold funcSubsHead
              unfold funcAssoc funcZeroAdd_Inv funcZeroAdd funcAddSubLE funcComm
              unfold vecAssoc_Inv vecZeroAdd vecZeroAdd_Inv vecAddSubLE_Inv vecComm
              unfold vecAppHeadSingle
              unfold finAssoc finZeroAdd_Inv finZeroAdd finAddSubLE finComm
              unfold vecZero vecOne_Inv
              ring_nf
              simp





            · -- randomChallenge field
              simp [honestProverTranscript, r']
            · -- proverComputations field
              funext i
              simp [honestProverTranscript, cutHeadProverComp]

          -- rewrite to the honest transcript, then finish by ih
        simpa [ht] using (ih (p := p') (r := r'))



end SumCheck
