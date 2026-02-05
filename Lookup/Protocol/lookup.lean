import Lookup.Spec.rational

namespace Lookup
universe u
variable {F : Type u} [Field F]

/-- Lookup “instance”: two functions over `{0,1}^n` that should be multiset-equal
    by the sum-of-inverses fingerprint. (Think: `t` is table MLE, `b` is query+remainder MLE.) -/
structure Instance (n : ℕ) where
  t : func F n
  b : func F n

/-- Lookup “witness”: inverse witnesses for t and b. -/
structure Witness (n : ℕ) where
  zT : func F n
  zB : func F n

/-- Lookup transcript: includes α plus sum-check transcripts proving the three cube-sum claims. -/
structure Transcript (n : ℕ) where
  α : F
  tr_invT : SumCheck.Transcript (F := F) n
  tr_invB : SumCheck.Transcript (F := F) n
  tr_diff : SumCheck.Transcript (F := F) n

/-- Verifier for the lookup protocol, “function-only skeleton” version.

    It checks 3 sum-check instances:
    1) Σ_x invConstraint α t zT = 0
    2) Σ_x invConstraint α b zB = 0
    3) Σ_x (zT - zB) = 0  (the multiset fingerprint equality)

    Note: this is *not yet* full soundness (we’re not enforcing degree bounds),
    but it matches your SumCheck file’s level of abstraction. -/
def verifierChecks
  (n : ℕ) (inst : Instance (F := F) n) (wit : Witness (F := F) n) (tr : Transcript (F := F) n) : Prop :=
  let pInvT : func F n := invConstraint (F := F) n tr.α inst.t wit.zT
  let pInvB : func F n := invConstraint (F := F) n tr.α inst.b wit.zB
  let pDiff : func F n := invDiff (F := F) n wit.zT wit.zB

  -- Each sum-check transcript should certify that the claimed sum is correct.
  -- Here we want each claimed sum = 0, so we’ll also demand that in the transcript fields.
  (tr.tr_invT.claimedSum = 0) ∧
  (tr.tr_invB.claimedSum = 0) ∧
  (tr.tr_diff.claimedSum = 0) ∧
  SumCheck.verifierChecks (F := F) n pInvT tr.tr_invT ∧
  SumCheck.verifierChecks (F := F) n pInvB tr.tr_invB ∧
  SumCheck.verifierChecks (F := F) n pDiff tr.tr_diff

end Lookup
