import Lookup.Protocol.lookup

namespace Lookup
universe u
variable {F : Type u} [Field F]

/-- Honest inverse witness from α and a function t.
    (Caveat: requires α - t(xs) ≠ 0 on the Boolean cube if you want it total; as a first pass,
     we just define it in the field with `Inv.inv` and later add a “good α” assumption.) -/
def honestInv (n : ℕ) (α : F) (t : func F n) : func F n :=
  fun xs => (α - t xs)⁻¹

/-- Honest witness given α. -/
def honestWitness (n : ℕ) (inst : Instance (F := F) n) (α : F) : Witness (F := F) n :=
  { zT := honestInv (F := F) n α inst.t
    zB := honestInv (F := F) n α inst.b }

/-- Honest transcript: run your sum-check honest transcript 3 times. -/
def honestTranscript (n : ℕ) (inst : Instance (F := F) n) (α : F)
    (rInvT rInvB rDiff : vec F n) : Transcript (F := F) n :=
  let wit := honestWitness (F := F) n inst α
  let pInvT : func F n := invConstraint (F := F) n α inst.t wit.zT
  let pInvB : func F n := invConstraint (F := F) n α inst.b wit.zB
  let pDiff : func F n := invDiff (F := F) n wit.zT wit.zB
  { α := α
    tr_invT := SumCheck.honestProverTranscript (F := F) n pInvT rInvT
    tr_invB := SumCheck.honestProverTranscript (F := F) n pInvB rInvB
    tr_diff := SumCheck.honestProverTranscript (F := F) n pDiff rDiff }

/-- Completeness statement at the same abstraction level as your SumCheck:
    “if the witness is honest and the sum-check transcripts are honest,
     then the lookup verifier accepts”, *assuming* the three claimed sums are 0.

    Later you’ll add the lemma that these sums are 0 under the true multiset condition. -/
theorem lookupCompleteness_skeleton
  (n : ℕ) (inst : Instance (F := F) n) (α : F)
  (rInvT rInvB rDiff : vec F n) :
  let wit := honestWitness (F := F) n inst α
  let tr := honestTranscript (F := F) n inst α rInvT rInvB rDiff
  -- assumptions about claimed sums (placeholders for the real algebraic facts):
  (tr.tr_invT.claimedSum = 0) →
  (tr.tr_invB.claimedSum = 0) →
  (tr.tr_diff.claimedSum = 0) →
  verifierChecks (F := F) n inst wit tr := by
  intro wit tr h1 h2 h3
  -- unfold the verifier and discharge the SumCheck parts via your completeness lemma
  simp [verifierChecks, honestTranscript, h1, h2, h3]
  constructor
  · exact h1
  constructor
  · exact h2
  constructor
  · exact h3
  constructor
  ·
    -- SumCheck completeness for invT
    exact SumCheck.funcSumCheckCompleteness (F := F)
      (p := invConstraint (F := F) n α inst.t wit.zT) (r := rInvT)
  constructor
  ·
    -- invB
    exact SumCheck.funcSumCheckCompleteness (F := F)
      (p := invConstraint (F := F) n α inst.b wit.zB) (r := rInvB)
  ·
    -- diff
    exact SumCheck.funcSumCheckCompleteness (F := F)
      (p := invDiff (F := F) n wit.zT wit.zB) (r := rDiff)

end Lookup
