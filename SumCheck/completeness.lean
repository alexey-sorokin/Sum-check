import SumCheck.evalAndSum

noncomputable section

open Classical
open NEO
open scoped BigOperators

namespace NEO

universe u
variable {F : Type u} [Field F]

def proverCompCutHead (n : ℕ) : (Fin (1 + n) → func F 1) → (Fin n → func F 1) :=
  (· ∘ finEmbedTailFull n)

def proverComp (n : ℕ) (p : func F n) (r : vec F n) : Fin n → func F 1 :=
  fun i =>
    funcSubsHead (F := F) i.1 1
      (vecTakeHeadConditional
        n
        i.1
        (n - i.1)
        (by exact (Nat.add_sub_of_le (Nat.le_of_lt i.2)).symm) r)
        (funcSumTail (F := F) (i.1 + 1) (n - (i.1 + 1))
          (funcCastToPrefixOneSuffix n i p))

/-- Transcript for `n` rounds (one univariate message per round). -/
structure proverTranscript (n : ℕ) where
  claimedSum : F
  randomChallenge : vec F n
  proverComp : Fin n → func F 1

private theorem proverTranscriptEq
  {n : ℕ} {t₁ t₂ : proverTranscript (F := F) n}
  (h₁ : t₁.claimedSum = t₂.claimedSum)
  (h₂ : t₁.randomChallenge = t₂.randomChallenge)
  (h₃ : t₁.proverComp = t₂.proverComp) :
  t₁ = t₂ := by
  cases t₁
  cases t₂
  cases h₁
  cases h₂
  cases h₃
  rfl

/-- Honest Prover transcript: claim is the true hypercube sum, messages are true partial sums. -/
def proverTranscriptHonest (n : ℕ) (p : func F n) (r : vec F n) : proverTranscript (F := F) n :=
  { claimedSum := funcSumTotal n p
    randomChallenge := r
    proverComp := proverComp (F := F) n p r}

/-- Verifier checks (sum-check consistency equations). -/
def verifierCheck : (n : ℕ) → func F n → proverTranscript (F := F) n → Prop
| 0, p, ⟨claimedSum, _, _⟩ =>
    -- no rounds: the "sum" is just evaluation at the empty point
    claimedSum = funcZero p
| n + 1, p, ⟨claimedSum, randomChallenge, proverComp⟩ =>
    -- round 0 consistency + recursive checks on the tail instance
    let proverCompInitial := proverComp ⟨0, Nat.succ_pos _⟩
    let randomChallengeInitial := vecTakeHead 1 n (vecComm n 1 randomChallenge)

    (funcSumTotal 1 proverCompInitial = claimedSum)
    ∧
    verifierCheck n
      ((funcComm n 1 p)
        ∘ (vecSplit_Inv (F := F) 1 n)
        ∘ (Prod.mk randomChallengeInitial))
      {
        claimedSum := proverCompInitial randomChallengeInitial
        randomChallenge := vecTakeTail (F := F) 1 n (vecComm n 1 randomChallenge)
        proverComp := proverCompCutHead (F := F) n (proverComp ∘ (finComm 1 n))
      }

theorem funcSumCheckCompleteness {n : ℕ} (p : func F n) (r : vec F n) :
    verifierCheck (F := F) n p (proverTranscriptHonest n p r) := by
  classical
  induction n with
  | zero =>
      -- n = 0
      simp [verifierCheck, proverTranscriptHonest, funcSumTotal]
      have h0 : funcSumTail 0 0 (funcZeroAdd_Inv 0 p) = p
        := by
        exact congrArg (fun f => f p) funcSumTail00_funcZeroAdd_Inv0_is_id
      rw [h0]
  | succ n h_inductive =>
      -- unfold verifier, honest transcript, and the first-round message
      -- We reduce the n+1 case to the n case using the definition of `funcSumTotal`.
      constructor
      ·
        unfold funcSumTotal
        unfold proverComp

        let funcIntroZero :
          func F ((0 + 1) + (n + 1 - (0 + 1))) → func F ((0 + 1) + (n + (0 + 1) - (0 + 1))) :=
          funcCast
            (F := F)
            ((0 + 1) + (n + 1 - (0 + 1)))
            ((0 + 1) + (n + (0 + 1) - (0 + 1)))
            (by simp)

        have h1 (g : func F ((0 + 1) + (n + 1 - (0 + 1)))) :
          funcSumTail (F := F) (0 + 1) (n + 1 - (0 + 1)) g
          =
          funcSumTail
            (F := F)
            (0 + 1)
            (n + (0 + 1) - (0 + 1))
            (funcIntroZero g)
          := by
          unfold funcSumTail
          unfold funcIntroZero
          funext va
          simp
          rfl
        rw [h1]
        rw [funcSumTail_is_funcSumTail_funcId_X_RightCancell (F := F) (0 + 1) n]
        rw [funcSumTail_is_funcSumTail_funcId_X_Comm]

        rw [funcSubsHead01_is_funcZeroAdd1]
        unfold Function.comp

        have h2_1 (g : func F (0 + 1)) :
          funcZeroAdd_Inv 1 (funcZeroAdd 1 g) = g
          := by
          rfl

        rw [h2_1]
        have h3 (g : func F (0 + 1 + n)) :
          funcSumTail (F := F) 0 1 (funcSumTail (F := F) (0 + 1) n g)
          =
          funcSumTail (F := F) 0 (1 + n) (funcAssoc (F := F) 0 1 n g)
          := by
          exact congrArg (fun f => f g)
            (funcSumTail_funcSumTail_is_funcSumTail_funcAssoc (F := F) 0 1 n)
        rw [h3]
        rfl
      ·
          -- define the reduced instance
        let p' : func F n :=
          (funcComm n 1 p)
          ∘ (vecSplit_Inv (F := F) 1 n)
          ∘ (Prod.mk (vecTakeHead 1 n (vecComm n 1 r)))

        let r' : vec F n :=
          vecTakeTail 1 n (vecComm n 1 r)

        have ht :
          { claimedSum :=
              proverComp (F := F) (n + 1) p r ⟨0, Nat.succ_pos _⟩
                (vecTakeHead (F := F) 1 n (vecComm (F := F) n 1 r)),
            randomChallenge :=
              vecTakeTail (F := F) 1 n (vecComm (F := F) n 1 r),
            proverComp :=
              proverCompCutHead (F := F) n (proverComp (F := F) (n + 1) p r ∘ finComm 1 n) }
          =
          proverTranscriptHonest (F := F) (n := n) (p := p') r'
          := by
          apply proverTranscriptEq
          · -- claimedSum field
            unfold proverTranscriptHonest
            unfold proverComp
            unfold funcSumTotal
            unfold Function.comp
            unfold p' r'
            have h_claimedSum :
              funcSubsHead 0 1
                (vecTakeHeadConditional (n + 1) 0 (n + 1 - 0) (by simp) r)
                (funcSumTail
                  (0 + 1)
                  (n + 1 - (0 + 1))
                  (funcCastToPrefixOneSuffix (n + 1) 0 p))
              (vecTakeHead 1 n (vecComm n 1 r))
              =
              funcZero
                (funcSumTail 0 n
                  (funcZeroAdd_Inv n
                    (funcComm n 1 p
                      ∘ vecSplit_Inv 1 n
                      ∘ Prod.mk
                        (vecTakeHead 1 n (vecComm n 1 r)))))
              := by
              rw [vecTakeHeadConditional0_is_vecZero]
              rw [funcSubsHead01_is_funcZeroAdd1]
              unfold funcCastToPrefixOneSuffix
              unfold funcZeroAdd
              unfold funcComm
              unfold funcZero
              unfold funcZeroAdd_Inv
              unfold funcSumTail
              unfold vecSplit_Inv
              unfold vecToVecSum_Inv
              unfold vecSumSplit_Inv
              unfold vecComm
              unfold vecTakeHead
              unfold vecCastToPrefixOneSuffix
              simp
              unfold vecCast
              unfold Function.comp
              have h_claimedSum_arg (xn : HyperCube n) (i_n1 : Fin (n + 1)) :
                Sum.elim
                  (fun x1 => r (finComm 1 n (finEmbedHead 1 n x1)))
                  (hypercubeVec n xn)
                  (finAddToFinSum 1 n
                    (finCastToPrefixOneSuffix (n + 1) 0 i_n1))
                =
                Sum.elim
                  (fun x1 => r (finComm 1 n (finEmbedHead 1 n x1)))
                  (fun j_n => Sum.elim
                    Fin.elim0
                    (hypercubeVec n xn)
                    (finAddToFinSum 0 n
                      (finCast n (0 + n) (by simp) j_n))
                  )
                  (finAddToFinSum 1 n (finComm n 1 i_n1))
                := by
                classical

                have hs :
                  finAddToFinSum 1 n (finCastToPrefixOneSuffix (n+1) 0 i_n1)
                    =
                  finAddToFinSum 1 n (finComm n 1 i_n1)
                  := by
                  simp [finAddToFinSum, finCastToPrefixOneSuffix, finComm]
                  rfl

                rw [hs]

                -- split on the sum value appearing on the RHS
                cases h : finAddToFinSum 1 n (finComm n 1 i_n1) with
                | inl x1 =>
                    simp [finAddToFinSum]
                | inr j =>
                    have h0 :
                      (Sum.elim Fin.elim0 (hypercubeVec n xn)
                          (finAddToFinSum 0 n (finCast n (0 + n) (by simp) j)))
                        =
                      hypercubeVec (F := F) n xn j
                      := by
                      simp [finAddToFinSum, finCast, Sum.elim, hypercubeVec, Fin.addCases]
                    simp [h0]

              simp [h_claimedSum_arg]

            rw [← h_claimedSum]
            rfl
          · -- randomChallenge field
            simp [p', r', proverTranscriptHonest]
          · -- proverComp field
            unfold proverTranscriptHonest
            unfold proverComp
            unfold proverCompCutHead
            unfold p' r'
            unfold Function.comp

            have h_proverComp:
              (fun x : Fin n =>
              (fun i : Fin (n + 1) =>
                  funcSubsHead i 1
                    (vecTakeHeadConditional (n + 1) i (n + 1 - i) (by simp) r)
                    (funcSumTail (i + 1) (n + 1 - (i + 1))
                      (funcCastToPrefixOneSuffix (n + 1) i p)))
              (finComm 1 n (finEmbedTailFull n x)))
              =
              (fun i : Fin n =>
              funcSubsHead i 1
                (vecTakeHeadConditional n i (n - ↑i) (by simp)
                  (vecTakeTail 1 n (vecComm n 1 r)))
                (funcSumTail (i + 1) (n - (i + 1))
                  (funcCastToPrefixOneSuffix n i fun x =>
                    funcComm n 1 p
                      (vecSplit_Inv 1 n (vecTakeHead 1 n (vecComm n 1 r), x)))))
              := by

              funext x

              have hcomm : finComm 1 n (finEmbedTail 1 n x) = Fin.succ x
                := by
                simp [finComm, finEmbedTail]

              unfold finEmbedTailFull
              rw [hcomm]

              funext v
              unfold funcSubsHead
              unfold funcSumTail
              unfold funcCastToPrefixOneSuffix
              unfold funcComm

              -- reindex the tail hypercube (a := n, b := ↑x + 1, c := 1)
              rw [← hypercubeSumRightSubtrReindex
                (F := F) (a := n) (b := (↑x + 1)) (c := 1)
                (g := fun y => _)]

              classical
              refine Finset.sum_congr rfl ?_
              intro y hy
              refine congrArg p ?_
              funext j
              simp

              have h1 (w : vec F 1 × vec F (x + 1 + (n - (x + 1)))) :
                vecSplit_Inv (F := F) 1 n (vecId_P_CastToPrefixOneSuffix (F := F) 1 n x w)
                =
                vecId_X_CastToPrefixOneSuffix (F := F) 1 n x
                  (vecSplit_Inv (F := F) 1 ((x + 1) + (n - (x + 1))) w)
                := by
                exact congrArg (fun f => f w)
                  (vecSplit_Inv_vecId_P_CastToPrefixOneSuffix_is_vecId_X_CastToPrefixOneSuffix_vecSplit_Inv
                    (F := F) (a := 1) (b := n) (i := x))

              unfold vecId_P_CastToPrefixOneSuffix vecId_X_CastToPrefixOneSuffix at h1
              simp at h1

              rw [h1]

              have h2 (w : vec F (1 + (x + 1 + (n - (x + 1))))) :
                vecComm 1 n (vecId_X_CastToPrefixOneSuffix 1 n x w)
                =
                vecCastToPrefixOneSuffix (n + 1) (x.succ)
                  (vecId_X_RightSubtr_Inv (x + 1 + 1) n (x + 1) 1
                    (vecComm_X_Id 1 (x + 1) (n - (x + 1))
                      (vecAssoc_Inv 1 (x + 1) (n - (x + 1)) w)))
                := by
                unfold vecId_X_CastToPrefixOneSuffix
                unfold vecCastToPrefixOneSuffix
                unfold vecId_X_RightSubtr_Inv
                unfold vecAssoc_Inv vecComm vecComm_X_Id
                rfl

              unfold vecId_X_CastToPrefixOneSuffix at h2
              rw [h2]

              have h3 (w : vec F 1 × (vec F (x + 1) × vec F (n - (x + 1)))) :
                vecAssoc_Inv (F := F) 1 (x + 1) (n - (x + 1))
                  (vecSplit_Inv (F := F) 1 (x + 1 + (n - (x + 1)))
                  (vecId_X_App (F := F) 1 (x + 1) (n - (x + 1)) w))
                =
                vecSplit_Inv (F := F) (1 + (x + 1)) (n - (x + 1))
                  (vecApp_X_Id (F := F) 1 (x + 1) (n - (x + 1))
                  (vecProdAssoc_Inv (F := F) 1 (x + 1) (n - (x + 1)) w))
                := by
                exact congrArg (fun f => f w) (vecAppHeadTail_commutation 1 (x + 1) (n - (x + 1)))

              unfold vecId_X_App vecApp_X_Id at h3
              unfold vecId_X_ToVecSum_Inv vecToVecSum_Inv_X_Id at h3
              unfold vecId_X_vecSumSplit_Inv vecSumSplit_Inv_X_Id at h3
              simp at h3

              have h3_1 (a_1 : vec F (↑x + 1)) (b : vec F (n - (↑x + 1))) :
                vecToVecSum_Inv (↑x + 1) (n - (↑x + 1))
                  (vecSumSplit_Inv (↑x + 1) (n - (↑x + 1)) (a_1, b))
                =
                vecSplit_Inv (↑x + 1) (n - (↑x + 1)) (a_1, b)
                := by
                unfold vecSplit_Inv
                rfl

              simp [h3_1] at h3

              have h3_2  (w : (vec F 1 × vec F (↑x + 1)) × vec F (n - (↑x + 1))) :
                (Prod.map (vecToVecSum_Inv 1 (↑x + 1)) id
                  (Prod.map (vecSumSplit_Inv 1 (↑x + 1)) id
                    w))
                =
                ⟨vecSplit_Inv 1 (↑x + 1) w.1, w.2⟩
                := by
                unfold vecSplit_Inv
                rfl

              simp [h3_2] at h3

              rw [h3]

              have h4 (w : vec F 1 × ((vec F x × vec F 1) × vec F (n - (x + 1)))) :
                vecProdAssoc_Inv 1 (↑x + 1) (n - (↑x + 1)) (Prod.map id (Prod.map (vecSplit_Inv (↑x)   1) id) w)
                =
                (Prod.map (Prod.map id (vecSplit_Inv (F := F) (↑x) 1)) id) (vecProdAssoc4_Inv 1 (↑x) 1 (n - ((↑x) + 1)) w)
                := by
                exact congrArg (fun f => f w)
                  (vecProdAssoc_Inv_vecSplit_Inv_comm 1 x 1 (n - (x + 1)))

              simp at h4

              rw [h4]

              have h5 (w : vec F (1 + (x + 1)) × vec F (n - (x + 1))) :
                vecSplit_Inv (F := F) (x + 1 + 1) (n - (x + 1)) (vecComm_P_Id (F := F) 1 (x + 1) (n - (x + 1)) w)
                =
                vecComm_X_Id (F := F) 1 (x + 1) (n - (x + 1)) (vecSplit_Inv (F := F) (1 + (x + 1)) (n - (x + 1)) w)
                := by
                exact congrArg (fun f => f w)
                  (vecSplit_Inv_vecComm_P_Id_is_vecComm_X_Id_vecSplit_Inv 1 (x + 1) (n - (x + 1)))

              rw [← h5]

              have h6 (w : vec F (x + 1 + 1) × vec F (n - (x + 1))) :
                  vecSplit_Inv (F := F) (x + 1 + 1) (n - (x + 1)) w
                    =
                  vecAssoc_Inv (F := F) (x + 1) 1 (n - (x + 1))
                    (vecSplit_Inv (F := F) (x + 1) (1 + (n - (x + 1)))
                      (vecId_X_App (F := F) (x + 1) 1 (n - (x + 1))
                        (vecProdAssoc (F := F) (x + 1) 1 (n - (x + 1))
                          (vecApp_X_Id_Inv (F := F) (x + 1) 1 (n - (x + 1)) w)))) := by

                have h0 (w : vec F (↑x + 1) × (vec F 1 × vec F (n - (↑x + 1)))) :
                  vecAssoc_Inv (F := F) (↑x + 1) 1 (n - (↑x + 1))
                    (vecSplit_Inv (F := F) (↑x + 1) (1 + (n - (↑x + 1)))
                      (vecId_X_App (F := F) (↑x + 1) 1 (n - (↑x + 1)) w))
                  =
                  vecSplit_Inv (F := F) (↑x + 1 + 1) (n - (↑x + 1))
                    (vecApp_X_Id (F := F) (↑x + 1) 1 (n - (↑x + 1))
                      (vecProdAssoc_Inv (F := F) (↑x + 1) 1 (n - (↑x + 1)) w))
                  := by
                  exact congrArg (fun f => f w)
                    (vecAppHeadTail_commutation (F := F) (x + 1) 1 (n - (x + 1)))

                rw [h0]

                have h0_1 (u : (vec F (↑x + 1) × vec F 1) × vec F (n - (↑x + 1))) :
                  vecProdAssoc_Inv (↑x + 1) 1 (n - (↑x + 1))
                    (vecProdAssoc (↑x + 1) 1 (n - (↑x + 1)) u) = u
                  := by
                  exact congrArg (fun f => f u)
                    (vecProdAssoc_Inv_vecProdAssoc_is_id (↑x + 1) 1 (n - (↑x + 1)))

                have h0_2 (u : vec F (↑x + 1 + 1) × vec F (n - (↑x + 1))) :
                  vecApp_X_Id (↑x + 1) 1 (n - (↑x + 1))
                    (vecApp_X_Id_Inv (↑x + 1) 1 (n - (↑x + 1)) u) = u
                  := by
                  exact congrArg (fun f => f u)
                    (vecApp_X_Id_vecApp_X_Id_Inv_is_id (↑x + 1) 1 (n - (↑x + 1)))

                rw [h0_1, h0_2]

              rw [h6]

              have h7 (w : vec F (↑x + 1 + (1 + (n - (↑x + 1))))) :
                vecId_X_RightSubtr_Inv (F := F) ((↑x + 1) + 1) n (↑x + 1) 1
                  (vecAssoc_Inv (F := F) (↑x + 1) 1 (n - (↑x + 1)) w)
                =
                vecAssoc_Inv (F := F) (↑x + 1) 1 ((n + 1) - ((↑x + 1) + 1))
                  (vecId_XX_Id_RightSubtr_Inv (F := F) (↑x + 1) 1 n (↑x + 1) 1 w)
                := by
                exact congrArg (fun f => f w)
                  (vecId_X_RightSubtr_Inv_vecAssoc_Inv_is_vecAssoc_Inv_vecId_XX_Id_RightSubtr_Inv (F := F) (↑x + 1) 1 n (↑x + 1) 1)

              rw [h7]

              have h8 (w : vec F (↑x + 1) × vec F (1 + (n - (↑x + 1)))) :
                vecId_XX_Id_RightSubtr_Inv (F := F) (↑x + 1) 1 n (↑x + 1) 1
                  (vecSplit_Inv (F := F) (↑x + 1) (1 + (n - (↑x + 1))) w)
                =
                vecSplit_Inv (F := F) (↑x + 1) (1 + ((n + 1) - ((↑x + 1) + 1)))
                  (Prod.map id (vecId_X_RightSubtr_Inv (F := F) 1 n (↑x + 1) 1) w)
                := by
                exact congrArg (fun f => f w)
                  (vecSplit_Inv_Id_XX_Id_RightSubtr_Inv_commute (F := F) (↑x + 1) 1 n (↑x + 1) 1).symm

              rw [h8]

              have h9 (w : vec F 1 × vec F (n - (↑x + 1))) :
                vecSplit_Inv (F := F) 1 ((n + 1) - ((↑x + 1) + 1))
                ((Prod.map id (vecRightSubtr_Inv (F := F) n (↑x + 1) 1)) w)
                =
                vecId_X_RightSubtr_Inv (F := F) 1 n (↑x + 1) 1
                  (vecSplit_Inv (F := F) 1 (n - (↑x + 1)) w)
                := by
                exact congrArg (fun f => f w)
                  (vecSplit_Inv_vecRightSubtr_Inv_commute 1 n (↑x + 1) 1)

              have h10 (w : vec F (↑x + 1) × (vec F 1 × vec F (n - (↑x + 1)))) :
                (Prod.map id (vecId_X_RightSubtr_Inv 1 n (↑x + 1) 1))
                  (vecId_X_App (↑x + 1) 1 (n - (↑x + 1)) w)
                =
                vecId_X_App (↑x + 1) 1 (n + 1 - (↑x + 1 + 1))
                  ((Prod.map id (Prod.map id (vecRightSubtr_Inv n (↑x + 1) 1))) w)
                := by
                unfold vecId_X_App
                unfold vecId_X_ToVecSum_Inv vecId_X_vecSumSplit_Inv
                simp [Prod.map]
                have h0 (u : vec F 1 × vec F (n - (↑x + 1))) :
                  vecToVecSum_Inv 1 (n - (↑x + 1)) (vecSumSplit_Inv 1 (n - (↑x + 1)) u)
                  =
                  vecSplit_Inv 1 (n - (↑x + 1)) u
                  := by
                  unfold vecSplit_Inv
                  rfl
                rw [h0, ← h9]
                rfl

              rw [h10]

              have h11 (w : vec F (↑x + 1) × (vec F 1 × vec F (n + 1 - (↑x + 1 + 1)))) :
                vecAssoc_Inv (↑x + 1) 1 (n + 1 - (↑x + 1 + 1))
                  (vecSplit_Inv (↑x + 1) (1 + (n + 1 - (↑x + 1 + 1)))
                    (vecId_X_App (↑x + 1) 1 (n + 1 - (↑x + 1 + 1)) w))
                =
                vecSplit_Inv (F := F) ((↑x + 1) + 1) (n + 1 - (↑x + 1 + 1))
                  (vecApp_X_Id (F := F) (↑x + 1) 1 (n + 1 - (↑x + 1 + 1))
                    (vecProdAssoc_Inv (F := F) (↑x + 1) 1 (n + 1 - (↑x + 1 + 1)) w))
                := by
                exact congrArg (fun f => f w)
                  (vecAppHeadTail_commutation (↑x + 1) 1 (n + 1 - (↑x + 1 + 1)))

              rw [h11]

              rw [vecApp_X_Id_is_vecSplit_Inv_P_id_pointwise]

              have h12 (w : (vec F (x + 1) × vec F 1) × vec F (n - (x + 1))) :
                vecProdAssoc_Inv (F := F) (↑x + 1) 1 (n + 1 - (↑x + 1 + 1))
                  (Prod.map id (Prod.map id (vecRightSubtr_Inv (F := F) n (↑x + 1) 1))
                    (vecProdAssoc (F := F) (↑x + 1) 1 (n - (↑x + 1)) w))
                =
                (Prod.map id (vecRightSubtr_Inv (F := F) n (↑x + 1) 1)) w
                := by
                unfold vecProdAssoc_Inv vecProdAssoc
                simp [Prod.map]

              rw [h12]

              have h_arith1 : n + 1 = ↑x + 1 + (n + 1 - (↑x + 1))
                := by
                have hx : x.1 ≤ n := Nat.le_of_lt_succ (Nat.lt_succ_of_lt x.2)
                have hx' : x.1 + 1 ≤ n + 1 := Nat.succ_le_succ hx
                simpa using (Nat.add_sub_of_le hx').symm

              have h_arith2 : n = ↑x + (n - ↑x)
                := by
                have hx : x.1 ≤ n := Nat.le_of_lt_succ (Nat.lt_succ_of_lt x.2)
                simp [Nat.add_sub_of_le hx]

              let r0 := vecTakeHead 1 n (vecComm n 1 r)
              let vy := vecTakeHeadConditional n (↑x) (n - ↑x) h_arith2 (vecTakeTail 1 n (vecComm n 1 r))
              let vz := hypercubeVec (F := F) (n - (↑x + 1)) (hypercubeVecRightSubtr n (↑x + 1) 1 y)

              have h13_1 :
                (vecTakeHeadConditional (n + 1) (↑x + 1) (n + 1 - (↑x + 1)) h_arith1 r, v)
                =
                (Prod.map id (vecRightSubtr_Inv n (↑x + 1) 1)
                  (vecApp_X_Id_Inv (↑x + 1) 1 (n - (↑x + 1))
                    (vecComm_P_Id 1 (↑x + 1) (n - (↑x + 1))
                      (vecSplit_Inv 1 (↑x + 1)
                        (Prod.map (Prod.map id (vecSplit_Inv (↑x) 1)) id
                          (vecProdAssoc4_Inv 1 (↑x) 1 (n - (↑x + 1))
                            (r0, (vy, v), vz))).1,
                        (Prod.map (Prod.map id (vecSplit_Inv (↑x) 1)) id
                          (vecProdAssoc4_Inv 1 (↑x) 1 (n - (↑x + 1))
                            (r0, (vy, v), vz))).2
                      )))).1
                := by
                simp [vecProdAssoc4_Inv, vecComm_P_Id, vecApp_X_Id_Inv]
                simp [vecSumSplit_Inv_X_Id_Inv, vecToVecSum_Inv_X_Id_Inv]
                have h0 :
                  vecSumSplit (↑x + 1) 1
                    (vecToVecSum (↑x + 1) 1
                      (vecComm 1 (↑x + 1)
                        (vecSplit_Inv 1 (↑x + 1)
                          (r0, vecSplit_Inv (↑x) 1 (vy, v)))))
                  =
                  ⟨vecComm 1 ↑x (vecSplit_Inv 1 ↑x ⟨r0, vy⟩), v⟩
                  := by

                  have h0_1 (w : vec F (1 + (↑x + 1))) :
                    vecComm 1 (↑x + 1) w = vecComm_X_Id 1 ↑x 1 (vecAssoc_Inv 1 ↑x 1 w)
                    := by
                    rfl
                  rw [h0_1]

                  have h0_2 (w : vec F 1 × (vec F ↑x × vec F 1)) :
                    vecAssoc_Inv (F := F) 1 ↑x 1
                      (vecSplit_Inv (F := F) 1 (↑x + 1)
                        (vecId_X_App (F := F) 1 ↑x 1 w))
                    =
                    vecSplit_Inv (F := F) (1 + ↑x) 1
                      (vecApp_X_Id (F := F) 1 ↑x 1
                        (vecProdAssoc_Inv (F := F) 1 ↑x 1 w))
                    := by
                    exact congrArg (fun f => f w)
                      (vecAppHeadTail_commutation 1 ↑x 1)

                  unfold vecApp_X_Id vecToVecSum_Inv_X_Id vecSumSplit_Inv_X_Id at h0_2
                  unfold vecId_X_App vecId_X_ToVecSum_Inv vecId_X_vecSumSplit_Inv at h0_2
                  simp [Prod.map, Function.comp, vecSplit_Inv, ] at h0_2

                  simp [vecSplit_Inv, Function.comp]

                  rw [h0_2]

                  have h0_3 (w : vec F (↑x + 1 + 1)) :
                    vecSumSplit (↑x + 1) 1 (vecToVecSum (↑x + 1) 1 w)
                    =
                    vecSplit (↑x + 1) 1 w
                    := by
                    simp [vecSplit]

                  rw [h0_3]

                  have h0_4 (a b : ℕ) (w : vec F a × vec F b) :
                    vecToVecSum_Inv a b (vecSumSplit_Inv a b w)
                    =
                    vecSplit_Inv a b w
                    := by
                    simp [vecSplit_Inv]

                  simp [h0_4]

                  have h0_5 (w : vec F (1 + ↑x) × vec F 1) :
                    vecComm_X_Id 1 ↑x 1 (vecSplit_Inv (1 + ↑x) 1 w)
                    =
                    vecSplit_Inv (↑x + 1) 1 (vecComm_P_Id 1 ↑x 1 w)
                    := by
                    exact congrArg (fun f => f w)
                      (vecSplit_Inv_vecComm_P_Id_is_vecComm_X_Id_vecSplit_Inv 1 ↑x 1).symm

                  rw [h0_5]

                  have h0_6 (w : vec F (↑x + 1) × vec F 1) :
                    vecSplit (↑x + 1) 1 (vecSplit_Inv (↑x + 1) 1 w) = w
                    := by
                    exact congrArg (fun f => f w)
                      (vecSplit_vecSplit_Inv_is_id (↑x + 1) 1)

                  rw [h0_6]
                  simp [vecProdAssoc_Inv, vecComm_P_Id]

                rw [h0]
                simp [r0, vy]

                classical
                funext i

                have h_arith3 : (x.1 + 1) = (1 + x.1) := by
                  simp [Nat.add_comm]

                -- split i into head/tail of (1 + x)
                -- by_cases returns the inequality hypothesis
                by_cases hhead : (Fin.cast h_arith3 i).1 < 1
                · -- HEAD BRANCH
                  -- from val < 1, the val must be 0
                  have hval0 : (Fin.cast h_arith3 i).1 = 0 := by
                    exact Nat.lt_one_iff.mp hhead

                  -- casting doesn't change `.1`, so i.1 = 0 too
                  have hi0 : i.1 = 0 := by
                    -- `Fin.cast` preserves `val`
                    simpa using hval0

                  -- rewrite i to 0 (as an element of Fin (x+1))
                  have hi : i = (0 : Fin (x.1 + 1)) := by
                    apply Fin.ext
                    simp [hi0]

                  subst hi

                  simp [vecTakeHeadConditional, finEmbedHeadConditional,
                        vecTakeHead, vecTakeTail,
                        finEmbedHead, finEmbedTail,
                        Function.comp, vecComm, Sum.elim,
                        finAddToFinSum, finComm]
                  rfl

                · -- TAIL BRANCH
                  have hge1 : 1 ≤ (Fin.cast h_arith3 i).1 := by
                    exact Nat.le_of_not_gt hhead

                  -- extract the tail index ix : Fin x such that cast i = natAdd 1 ix
                  let ix : Fin x.1 :=
                    ⟨(Fin.cast h_arith3 i).1 - 1,
                      by
                        have hlt : (Fin.cast h_arith3 i).1 < x.1 + 1 := by
                          simpa [h_arith3] using (i.2)

                        have hneq0 : (Fin.cast h_arith3 i).1 ≠ 0
                          := by
                          exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hge1)

                        -- Now pred both sides: (val - 1) < x
                        -- since (x+1).pred = x
                        have : Nat.pred (Fin.cast h_arith3 i).1 < Nat.pred (x.1 + 1) := by
                          exact Nat.pred_lt_pred hneq0 hlt

                        -- rewrite `Nat.pred (x+1)` and `Nat.pred val` into subtraction form
                        simpa [Nat.pred, Nat.succ_eq_add_one] using this
                    ⟩

                  have hcast : Fin.cast h_arith3 i = Fin.natAdd 1 ix
                    := by
                    apply Fin.ext
                    have hge1' : 1 ≤ i.1 := by simpa using hge1
                    -- the simp will reduce to Nat goal and close it
                    simp [ix, Fin.natAdd]
                    have : (i.1 - 1) + 1 = i.1 := Nat.sub_add_cancel (by simpa using hge1)
                    -- rewrite RHS `1 + (i-1)` to `(i-1)+1`
                    have : i.1 = 1 + (i.1 - 1) := by
                      -- from (i-1)+1=i
                      -- and commutativity
                      simpa [Nat.add_comm] using this.symm
                    exact this

                  simp [hcast,
                        vecTakeHeadConditional, finEmbedHeadConditional,
                        vecTakeHead, vecTakeTail,
                        finEmbedHead, finEmbedTail,
                        Function.comp, vecComm, Sum.elim,
                        finAddToFinSum, finComm]
                  apply congrArg r
                  apply Fin.ext
                  simp [finCast, ix]
                  have hge1 : 1 ≤ (i : Fin (x.1 + 1)).1 :=
                    by exact hge1
                  exact (Nat.sub_add_cancel hge1).symm

              rw [h13_1]


              have h13_2 :
                hypercubeVec (n + 1 - (↑x + 1 + 1)) y
                =
                (Prod.map id (vecRightSubtr_Inv n (↑x + 1) 1)
                  (vecApp_X_Id_Inv (↑x + 1) 1 (n - (↑x + 1))
                    (vecComm_P_Id 1 (↑x + 1) (n - (↑x + 1))
                      (vecSplit_Inv 1 (↑x + 1)
                        (Prod.map (Prod.map id (vecSplit_Inv (↑x) 1)) id
                          (vecProdAssoc4_Inv 1 (↑x) 1 (n - (↑x + 1)) (r0, (vy, v), vz))).1,
                        (Prod.map (Prod.map id (vecSplit_Inv (↑x) 1)) id
                          (vecProdAssoc4_Inv 1 (↑x) 1 (n - (↑x + 1)) (r0, (vy, v), vz))).2
                      )))).2
                := by
                simp [vecProdAssoc4_Inv, vecComm_P_Id, vecApp_X_Id_Inv]
                simp [vecSumSplit_Inv_X_Id_Inv, vecToVecSum_Inv_X_Id_Inv]
                simp [vz]
                unfold vecRightSubtr_Inv hypercubeVecRightSubtr
                simp [finRightSubtr_Inv, finRightSubtr, hypercubeVec]
                funext j
                simp [Function.comp]

              rw [h13_2]

            rw [h_proverComp]
        rw [ht]
        simpa [p', r'] using (h_inductive (p := p') (r := r'))

end NEO
