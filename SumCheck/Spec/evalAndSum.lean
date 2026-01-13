import SumCheck.Spec.headTail

noncomputable section
open Classical
open SumCheck

namespace SumCheck

universe u
variable {F : Type u} [Field F]


def funcSubsHeadSingle {F : Type u} [Field F] (n : ℕ) :
    F → func F (1 + n) → func F n :=
  fun r p => fun xs => p (vecAppHeadSingle (F := F) n r xs)


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ev_(m+1) = ev_m ∘ ev_1 ∘ α ∘ (β × id)

def funcSubsHead {F : Type u} [Field F] (n : ℕ) :
    (m : ℕ) → (r : vec F m) → func F (m + n) → func F n
| 0, _, p =>
    funcZeroAdd (F := F) n p
| Nat.succ m, r, p =>
    funcSubsHead
      (F := F) (n := n) (m := m)
      (fun i => r i.succ)
      (funcSubsHeadSingle (F := F) (n := m + n) (r 0)
        (funcAssoc (F := F) 1 m n (funcComm_X_Id (F := F) m 1 n p)))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



/-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Summation over the tail variables X_n+1,...,X_n+k ∈ {0,1}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-/

def funcSumTailSingle (n : ℕ) : func F (n + 1) → func F n :=
  fun p xs => (p (vecAppTailSingle n xs 0) + p (vecAppTailSingle n xs 1))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑(k+1) = ∑k ∘ ∑1 ∘ α

def funcSumTail (n : ℕ) : (k : ℕ) → func F (n + k) → func F n
| 0, p =>
    -- p: vec (n+0) -> F
    funcAddZero n p -- fun xs => p (vecAddZero_Inv n xs)

| Nat.succ k, p =>
    -- p : func F (n + (k + 1))
    funcSumTail
      (n := n)
      (k := k)
      (funcSumTailSingle
        (F := F)
        (n := n + k)
        (funcAssoc_Inv n k 1 p)
      )

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/-- Hypercube sum `∑_{x∈{0,1}^n} p x`. -/
def funcSumTotal (n : ℕ) : func F n → F :=
  fun p =>
    funcZero
      (funcSumTail (F := F) (n := 0) (k := n)
        (funcZeroAdd_Inv (F := F) (n := n) p))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑1 ∘ (λ × id) = λ ∘ ∑1

theorem funcSumTailSingle_funcZeroAdd_X_Id_is_funcZeroAdd_funcSumTailSingle
  (a : ℕ) :
  (funcSumTailSingle (F := F) a) ∘ (funcZeroAdd_X_Id (F := F) a 1)
    =
  (funcZeroAdd (F := F) a) ∘ (funcSumTailSingle (F := F) (0 + a))
  := by
  unfold funcSumTailSingle
  unfold funcZeroAdd funcZeroAdd_X_Id
  unfold vecZeroAdd_Inv vecZeroAdd_X_Id_Inv
  unfold finZeroAdd finZeroAdd_X_Id
  unfold vecAppTailSingle
  unfold Function.comp
  ring_nf
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑1 ∘ (ρ × id) = ρ ∘ ∑1

theorem funcSumTailSingle_funcAddZero_X_Id_is_funcAddZero_funcSumTailSingle
  (a : ℕ) :
  (funcSumTailSingle (F := F) a) ∘ (funcAddZero_X_Id (F := F) a 1)
    =
  (funcAddZero (F := F) a) ∘ (funcSumTailSingle (F := F) (a + 0))
  := by
  unfold funcSumTailSingle
  unfold funcAddZero funcAddZero_X_Id
  unfold vecAddZero_X_Id_Inv vecAddZero
  unfold vecAppTailSingle
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑1 ∘ (α × id) = α ∘ ∑1

theorem sumTailSingle_funcAssoc_X_Id_is_funcAssoc_sumTailSingle (a b c : ℕ) :
  (funcSumTailSingle (F := F) (a + (b + c))) ∘ (funcAssoc_X_Id (F := F) a b c 1)
    =
  (funcAssoc (F := F) a b c) ∘ (funcSumTailSingle (F := F) (a + b + c))
  := by
    unfold funcSumTailSingle
    unfold funcAssoc_X_Id funcAssoc
    funext p xs
    ring_nf
    have h (r_tail : F) :
      vecAssoc_X_Id_Inv a b c 1 (vecAppTailSingle (a + (b + c)) xs r_tail)
        =
      vecAppTailSingle ((a + b) + c) (vecAssoc_Inv a b c xs) r_tail := by
      -- lemma evaluated at xs
      exact (congrArg (fun f => f xs)
      (vecAssoc_X_Id_Inv_vecAppentTail_is_vecAppendTail_vecAssoc_Inv
        (F := F) a b c r_tail))
    dsimp [Function.comp]
    rw [h 0, h 1]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑1 ∘ (α × id)⁻¹ = α⁻¹ ∘ ∑1

theorem sumTailSingle_funcAssoc_X_Id_Inv_is_funcAssoc_Inv_sumTailSingle
  (a b c : ℕ) :
  (funcSumTailSingle (F := F) (a + b + c)) ∘ (funcAssoc_X_Id_Inv (F := F) a b c 1)
    =
  (funcAssoc_Inv (F := F) a b c) ∘ (funcSumTailSingle (F := F) (a + (b + c)))
  := by
  have h :
      (funcAssoc_Inv (F := F) a b c) ∘ (funcSumTailSingle (F := F) (a + (b + c)))
        =
      (funcSumTailSingle (F := F) (a + b + c)) ∘ (funcAssoc_X_Id_Inv (F := F) a b c 1) := by
    -- reassociate and cancel inverse pairs (these should be `[simp]` now)
    simpa [Function.comp_assoc] using (congrArg
      (fun t =>
        (funcAssoc_Inv (F := F) a b c) ∘ t ∘
        (funcAssoc_X_Id_Inv (F := F) a b c 1))
      (sumTailSingle_funcAssoc_X_Id_is_funcAssoc_sumTailSingle (F := F) a b c))

  -- Now match the goal orientation
  simpa using h.symm


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑1 ∘ (β × id × id) = (β × id) ∘ ∑1

theorem funcSumTailSingle_funcComm_X_Id_X_Id_is_funcComm_X_Id_funcSumTailSingle
  (a b c : ℕ) :
  funcSumTailSingle (F := F) (b + a + c) ∘ funcComm_X_Id_X_Id (F := F) a b c 1
  =
  funcComm_X_Id (F := F) a b c ∘ funcSumTailSingle (F := F) (a + b + c)
  := by
    unfold funcSumTailSingle funcComm_X_Id_X_Id funcComm_X_Id
    funext p xs
    simp
    ring_nf
    have h (r_tail : F) :
      vecComm_X_Id_X_Id b a c 1 (vecAppTailSingle (b + a + c) xs r_tail)
        =
      vecAppTailSingle (a + b + c) (vecComm_X_Id b a c xs) r_tail
      := by
      exact (congrArg (fun f => f xs)
      (vecComm_X_Id_X_Id_vecAppendTail_is_vecAppendTail_vecComm_X_Id
        (F := F) b a c r_tail))
    rw [h 0, h 1]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑1 ∘ ((id × β) × id) = (id × β) ∘ ∑1

theorem funcSumTailSingle_funcId_X_Comm_XX_Id_is_funcId_X_Comm_funcSumTailSingle
  (a b c : ℕ) :
  (funcSumTailSingle (F := F) (a + (c + b))) ∘ (funcId_X_Comm_XX_Id (F := F) a b c 1)
  =
  (funcId_X_Comm (F := F) a b c) ∘ (funcSumTailSingle (F := F) (a + (b + c)))
  := by
    unfold funcSumTailSingle
    unfold funcId_X_Comm_XX_Id funcId_X_Comm
    funext p xs
    unfold Function.comp
    simp
    have h (r_tail : F) :
      vecId_X_Comm_XX_Id a c b 1 (vecAppTailSingle (a + (c + b)) xs r_tail)
      =
      vecAppTailSingle (a + (b + c)) (vecId_X_Comm a c b xs) r_tail
      := by
      exact (congrArg (fun f => f xs)
      (vecId_X_Comm_XX_Id_vecAppTailSingle_is_vecAppTailSingle_vecId_X_Comm
        (F := F) a b c r_tail ))
    rw [h 0, h 1]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑(k+1) = ∑1 ∘ ∑k ∘ α⁻¹ ∘ (id × β)

theorem funcSumTail_is_funcSumTailSingle_funcSumTail_funcAssoc_Inv_funcId_X_Comm
  (n k : ℕ) :
  (funcSumTail (F := F) n (k + 1))
  =
  (funcSumTailSingle (F := F) n) ∘
    (funcSumTail (F := F) (n + 1) k) ∘
      (funcAssoc_Inv (F := F) n 1 k) ∘
        (funcId_X_Comm (F := F) n k 1)
  := by
  funext p
  induction k with
  | zero =>
    unfold Function.comp
    unfold funcSumTail
    conv_rhs =>
      unfold funcSumTail
    unfold funcSumTail
    funext xs
    simp
    rfl
  | succ k hk =>
    unfold Function.comp at hk
    unfold Function.comp
    conv_lhs =>
      unfold funcSumTail
    conv_rhs =>
      unfold funcSumTail
    rw [hk]

    have h1 (g : func F (n + (k + 1) + 1)) :
      funcSumTailSingle (F := F) (n + (1 + k)) (funcId_X_Comm_XX_Id (F := F) n k 1 1 g)
      =
      funcId_X_Comm (F := F) n k 1 (funcSumTailSingle (F := F) (n + (k + 1)) g)
      := by
      exact (congrArg (fun f => f g)
        (funcSumTailSingle_funcId_X_Comm_XX_Id_is_funcId_X_Comm_funcSumTailSingle n k 1))

    rw [← h1]

    have h2 (g : func F ((n + (1 + k)) + 1)) :
      funcSumTailSingle (F := F) (n + 1 + k) (funcAssoc_X_Id_Inv (F := F) n 1 k 1 g)
      =
      funcAssoc_Inv (F := F) n 1 k (funcSumTailSingle (F := F) (n + (1 + k)) g)
      := by
      exact (congrArg (fun f => f g)
        (sumTailSingle_funcAssoc_X_Id_Inv_is_funcAssoc_Inv_sumTailSingle (F := F) n 1 k))
    rw [← h2]
    unfold funcAssoc_Inv funcAssoc_X_Id_Inv
    unfold funcId_X_Comm funcId_X_Comm_XX_Id
    unfold vecAssoc vecAssoc_X_Id
    unfold vecId_X_Comm vecId_X_Comm_XX_Id
    rfl


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


-- Summation over tail of length 1 is a single summation

theorem funcSumTail_1_is_funcSumTailSingle (n : ℕ) :
  funcSumTail (F := F) n 1 = funcSumTailSingle (F := F) n
  := by
  funext p
  unfold funcSumTail
  unfold funcSumTail
  have h (g : func F (n + 0 + 1)) :
    funcSumTailSingle (F := F) n (funcAddZero_X_Id (F := F) n 1 g)
    =
    funcAddZero (F := F) n (funcSumTailSingle (F := F) (n + 0) g)
    := by
      simpa [Function.comp] using
        congrArg
          (fun (f : func F (n + 0 + 1) → func F n) => f g)
          (funcSumTailSingle_funcAddZero_X_Id_is_funcAddZero_funcSumTailSingle (F := F) n)
  rw [← h]
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ev₁ ∘ (id × α) = α × ev₁

theorem funcSubsHeadSingle_funcId_X_Assoc_is_funcAssoc_funcSubsHeadSingle
  (a b c : ℕ) (r_head : F) :
  funcSubsHeadSingle (F := F) (a + (b + c)) r_head
      ∘ funcId_X_Assoc (F := F) 1 a b c
  =
  funcAssoc (F := F) a b c
      ∘ funcSubsHeadSingle (F := F) (a + b + c) r_head
  := by
  unfold funcSubsHeadSingle funcId_X_Assoc funcAssoc
  funext p xs
  dsimp [Function.comp]
  -- directly apply the composition lemma at `xs`
  simpa using congrArg p
    (congrArg (fun f => f xs)
      (vecId_X_Assoc_Inv_vecAppendHead_is_vecAppendHead_vecAssoc_Inv
        (F := F) a b c r_head))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ev₁ ∘ (id × id × α) = (id × α) × ev₁

theorem funcSubsHeadSingle_funcId_X_Id_X_Assoc_is_funcId_X_Assoc_funcSubsHeadSingle
  (a b c d : ℕ) (r_head : F) :
  funcSubsHeadSingle (F := F) (a + (b + (c + d))) r_head
      ∘ funcId_X_Id_X_Assoc (F := F) 1 a b c d
  =
  funcId_X_Assoc (F := F) a b c d
      ∘ funcSubsHeadSingle (F := F) (a + (b + c + d)) r_head
  := by
  unfold funcSubsHeadSingle funcId_X_Assoc funcId_X_Id_X_Assoc
  funext p xs
  dsimp [Function.comp]
  -- directly apply the composition lemma at `xs`
  have hv :
      vecId_X_Id_X_Assoc_Inv (F := F) 1 a b c d
        (vecAppHeadSingle (F := F) (n := a + (b + (c + d))) r_head xs)
      =
      vecAppHeadSingle (F := F) (n := a + (b + c + d)) r_head
        (vecId_X_Assoc_Inv (F := F) a b c d xs) := by
    -- “lemma evaluated at xs”
    exact (congrArg (fun f => f xs)
      (vecId_X_Id_X_Assoc_Inv_vecAppendHead_is_vecAppendHead_vecId_X_Assoc_Inv
        (F := F) a b c d r_head))

  -- apply `p` to both sides
  simpa using congrArg p hv

 -- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ev₁ ∘ (id × id × α)⁻¹ = (id × α)⁻¹ × ev₁

 theorem funcSubsHeadSingle_funcId_X_Id_X_Assoc_Inv_is_funcId_X_Assoc_Inv_funcSubsHeadSingle
  (a b c d : ℕ) (r_head : F) :
  funcSubsHeadSingle (F := F) (a + (b + c + d)) r_head
      ∘ funcId_X_Id_X_Assoc_Inv (F := F) 1 a b c d
  =
  funcId_X_Assoc_Inv (F := F) a b c d
      ∘ funcSubsHeadSingle (F := F) (a + (b + (c + d))) r_head
  := by
  have h :=
    funcSubsHeadSingle_funcId_X_Id_X_Assoc_is_funcId_X_Assoc_funcSubsHeadSingle
      (F := F) a b c d r_head

  have h1 :=
    congrArg (fun T => T ∘ (funcId_X_Id_X_Assoc_Inv (F := F) 1 a b c d)) h

  have h2 :=
    congrArg (fun T => (funcId_X_Assoc_Inv (F := F) a b c d) ∘ T) h1

  -- h2 is: B⁻¹ ∘ S₁ = B⁻¹ ∘ B ∘ S₂ ∘ A⁻¹
  -- cancel B⁻¹ ∘ B, then flip sides
  have h3 :
      (funcId_X_Assoc_Inv (F := F) a b c d) ∘
          (funcSubsHeadSingle (F := F) (a + (b + (c + d))) r_head)
        =
      (funcSubsHeadSingle (F := F) (a + (b + c + d)) r_head) ∘
          (funcId_X_Id_X_Assoc_Inv (F := F) 1 a b c d) := by
    -- reassociate, then simp cancels (B⁻¹ ∘ B)
    simpa [Function.comp_assoc] using h2

  -- your goal is the symmetric orientation
  rw [h3]

 -- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ev_m ∘ (id × α) = α ∘ ev_m

theorem funcAssoc_funcSubsHead_is_funcSubsHead_funcId_X_Assoc
  (m a b c : ℕ) (r : vec F m) :
  (funcAssoc (F := F) a b c) ∘ (funcSubsHead (F := F) ((a + b) + c) (m := m) r)
    =
  (funcSubsHead (F := F) (a + (b + c)) (m := m) r) ∘ (funcId_X_Assoc (F := F) m a b c) := by
  induction m with
  | zero =>
      -- funcSubsHead (m := 0) is the base case: funcZeroAdd
      -- and funcId_X_Assoc (m := 0) is definitional/cast, so simp closes
      funext p xs
      simp [funcSubsHead, Function.comp, funcAssoc]
      rfl
  | succ m ih =>
      funext p xs
      simp [funcSubsHead, Function.comp]
      unfold Function.comp at ih
      have h_ih (g : func F (m + ((a + b) + c))) :
        funcAssoc (F := F) a b c
          (funcSubsHead (F := F) (a + b + c) (m := m) (fun i => r i.succ) g)
        =
        funcSubsHead (F := F) (a + (b + c)) (m := m) (fun i => r i.succ)
          (funcId_X_Assoc (F := F) m a b c g)
        := by
        exact congrArg (fun T => T g) (ih (fun i => r i.succ))
      simp [h_ih]

      have h_step (g : func F (1 + (m + ((a + b) + c)))) :
        funcSubsHeadSingle (F := F) (m + (a + (b + c))) (r 0)
          (funcId_X_Id_X_Assoc (F := F) 1 m a b c g)
        =
        funcId_X_Assoc (F := F) m a b c
          (funcSubsHeadSingle (F := F) (m + ((a + b) + c)) (r 0) g)
        := by
        exact congrArg (fun T => T g)
          (funcSubsHeadSingle_funcId_X_Id_X_Assoc_is_funcId_X_Assoc_funcSubsHeadSingle
            (F := F) (a := m) (b := a) (c := b) (d := c) (r_head := r 0))
      simp [← h_step]
      rfl

 -- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ev_m ∘ (id × α)⁻¹ = α⁻¹ ∘ ev_m

theorem funcSubsHead_funcId_X_Assoc_Inv_is_funcAssoc_Inv_funcSubsHead
  (m a b c : ℕ) (r : vec F m) :
  (funcSubsHead (F := F) ((a + b) + c) (m := m) r) ∘ (funcId_X_Assoc_Inv (F := F) m a b c)
    =
  (funcAssoc_Inv (F := F) a b c) ∘ (funcSubsHead (F := F) (a + (b + c)) (m := m) r)
  := by
  -- your forward lemma
  have h :=
    funcAssoc_funcSubsHead_is_funcSubsHead_funcId_X_Assoc
      (F := F) (m := m) (a := a) (b := b) (c := c) (r := r)

  -- postcompose by (funcId_X_Assoc_Inv m a b c)
  have h1 :=
    congrArg (fun T => T ∘ (funcId_X_Assoc_Inv (F := F) m a b c)) h

  -- precompose by (funcAssoc_Inv a b c)
  have h2 :=
    congrArg (fun T => (funcAssoc_Inv (F := F) a b c) ∘ T) h1

  -- now cancel (funcAssoc_Inv ∘ funcAssoc) and (funcId_X_Assoc ∘ funcId_X_Assoc_Inv)
  have h3 :
      (funcAssoc_Inv (F := F) a b c) ∘
          ((funcAssoc (F := F) a b c) ∘ (funcSubsHead (F := F) ((a + b) + c) (m := m) r)) ∘
          (funcId_X_Assoc_Inv (F := F) m a b c)
        =
      (funcAssoc_Inv (F := F) a b c) ∘
          ((funcSubsHead (F := F) (a + (b + c)) (m := m) r) ∘ (funcId_X_Assoc (F := F) m a b c)) ∘
          (funcId_X_Assoc_Inv (F := F) m a b c) := by
    -- just restating h2 in a named form (optional)
    exact h2

  -- simplify and extract the desired equality
  -- (this is the analogue of your `simpa [Function.comp_assoc] using h2`)
  have h4 :
      (funcSubsHead (F := F) ((a + b) + c) (m := m) r) ∘
          (funcId_X_Assoc_Inv (F := F) m a b c)
        =
      (funcAssoc_Inv (F := F) a b c) ∘
          (funcSubsHead (F := F) (a + (b + c)) (m := m) r) := by
    simpa [Function.comp_assoc] using h2

  -- match the statement orientation
  exact h4

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑1 ∘ ev₁ ∘ α = ev₁ ∘ ∑1

theorem funcSumTailSingle_funcSubsHeadSingle_funcAssoc_is_funcSubsHeadSingle_funcSumTailSingle
  {F : Type u} [Field F]
  (n : ℕ) (r_head : F) :
  funcSumTailSingle (F := F) (n := n)
      ∘ (fun p : func F (1 + n + 1) =>
            funcSubsHeadSingle (F := F) (n := n + 1) r_head
              (funcAssoc (F := F) 1 n 1 p))
  =
  funcSubsHeadSingle (F := F) (n := n) r_head
      ∘ funcSumTailSingle (F := F) (n := 1 + n) := by
  funext p v
  -- expanding both sides and using your pointwise comm lemma
  simp [Function.comp, funcSumTailSingle, funcSubsHeadSingle, funcAssoc]

  -- single reusable rewrite for any tail value
  have hv (r_tail : F) :
      vecAppTailSingle (1 + n) (vecAppHeadSingle n r_head v) r_tail
        =
      vecAssoc_Inv 1 n 1
        (vecAppHeadSingle (n + 1) r_head (vecAppTailSingle n v r_tail)) := by
    have h :=
      congrArg (fun f => f v)
        (vecAppendTail_vecAppendHead_is_vecAssoc_Inv_vecAppendHead_vecAppendTail
          (n := n) (r_head := r_head) (r_tail := r_tail))
    simpa [Function.comp] using h

  -- finish by specializing hv at 0 and 1 directly in simp
  simp [hv (0 : F), hv (1 : F)]


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ev_m ∘ ∑1 = ∑1 ∘ ev_m ∘ α

-- m, n, 1 case
theorem funcSubsHead_funcSumTailSingle_is_funcSumTailSingle_funcSubsHead_funcAssoc
  {F : Type u} [Field F]
  (m n : ℕ) (r : vec F m) :
  (funcSubsHead n m r) ∘ (funcSumTailSingle (m + n))
  =
  (funcSumTailSingle n) ∘ ((funcSubsHead (n + 1) m r) ∘ (funcAssoc m n 1))
  := by
  funext p xs
  -- simp [Function.comp]
  induction m with
  | zero =>
      unfold funcSumTailSingle
      simp [funcSubsHead]
      unfold funcAssoc funcZeroAdd
      -- funext xs
      ring_nf
      have h0 (a : F) (xs : vec F n) :
        vecAssoc_Inv 0 n 1 (vecZeroAdd_Inv (n + 1) (vecAppTailSingle n xs a))
          =
        vecAppTailSingle (0 + n) (vecZeroAdd_Inv n xs) a := by
        -- evaluate the composition equality at `xs`
        simpa [Function.comp] using
          (congrArg (fun f => f xs)
            (vecAppendTail_vecZeroAdd_Inv_is_vecAssoc_Inv_vecZeroAdd_Inv_vecAppendTail
              (F := F) (n := n) (r_tail := a))).symm
      rw [h0 0, h0 1]
  | succ m hm =>
      simp [funcSubsHead]
      simp [funcComm_X_Id_funcAssoc_is_funcAssoc_funcComm_X_Id_Id]
      simp [← funcPentagonIdentity]
      --funext xs
      have h1 (g : func F (1 + (m + n + 1))) :
        funcSubsHeadSingle (m + (n + 1)) (r 0) (funcId_X_Assoc 1 m n 1 g)
        =
        funcAssoc m n 1 (funcSubsHeadSingle (m + n + 1) (r 0) g)
        := by
        -- take the composition equality and evaluate it at `g`
        exact
          (by
            simpa [Function.comp, Nat.add_assoc] using
            congrArg
              (fun h => h g)
              (funcSubsHeadSingle_funcId_X_Assoc_is_funcAssoc_funcSubsHeadSingle
                (F := F) m n 1 (r 0)
              )
          )
      simp [h1]
      have h2 (g : func F (m + 1 + n + 1)) :
        funcSumTailSingle (F := F) (1 + m + n) (funcComm_X_Id_X_Id (F := F) m 1 n 1 g)
        =
        funcComm_X_Id (F := F) m 1 n (funcSumTailSingle (F := F) (m + 1 + n) g)
        := by
        -- evaluate the composition equality at `g`
          exact
          (by
          -- first, rewrite the indices to match the theorem's `(b + a + c)` and `(a + b + c)`
            simpa [Function.comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              congrArg
                (fun h => h g)
                (funcSumTailSingle_funcComm_X_Id_X_Id_is_funcComm_X_Id_funcSumTailSingle
                  (F := F) (a := m) (b := 1) (c := n))
          )
      simp [← h2]
      have h3 (g : func F (1 + m + n + 1)) :
        funcSumTailSingle (1 + (m + n)) (funcAssoc_X_Id 1 m n 1 g)
        =
        funcAssoc 1 m n (funcSumTailSingle (1 + m + n) g)
        := by
        exact
          (by
            simpa [Function.comp, Nat.add_assoc] using
            congrArg
              (fun h => h g)
              (
                sumTailSingle_funcAssoc_X_Id_is_funcAssoc_sumTailSingle
                (F := F) 1 m n
              )
          )
      simp [← h3]
      have h4 (g : func F (1 + (m + n) + 1)) (r_head : F) :
        funcSumTailSingle (F := F) (n := m + n)
          (funcSubsHeadSingle (F := F) (n := m + n + 1) r_head
            (funcAssoc (F := F) 1 (m + n) 1 g))
        =
        funcSubsHeadSingle (F := F) (n := m + n) r_head
          (funcSumTailSingle (F := F) (n := 1 + (m + n)) g)
        := by
        exact
          (by
          -- take the composition theorem and apply it to `g`
            simpa [Function.comp] using
              congrArg
                (fun h => h g)
                (funcSumTailSingle_funcSubsHeadSingle_funcAssoc_is_funcSubsHeadSingle_funcSumTailSingle (F := F) (n := m + n) r_head)
          )
      simp [← h4]

      simp [Function.comp] at hm
      exact
        hm
          (r := fun i => r i.succ)
          (p := funcSubsHeadSingle (F := F) (n := m + n + 1) (r 0)
            (funcAssoc (F := F) 1 (m + n) 1
              (funcAssoc_X_Id (F := F) 1 m n 1
                (funcComm_X_Id_X_Id (F := F) m 1 n 1 p))))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ∑k ∘ ev_m α = ev_m ∘ ∑k

theorem sumTailLong_substHeadLong_comm
  {F : Type u} [Field F]
  (m n k : ℕ) (r : vec F m) :
  funcSumTail (F := F) (n := n) (k := k)
    ∘
    (funcSubsHead (F := F) (n := n + k) (m := m) r
        ∘
        funcAssoc (F := F) m n k)
  =
  funcSubsHead (F := F) (n := n) (m := m) r
    ∘
    funcSumTail (F := F) (n := m + n) (k := k)
  := by
  funext p
  induction k with
  | zero =>
      simp [funcSumTail]
      induction m with
        | zero =>
            funext xs
            simp [funcSubsHead]
            rfl
        | succ m h_mn0 =>
            funext xs
            simp [funcSubsHead]
            rfl
  | succ k h_mnk =>
      induction m with
      | zero =>
          simp [funcSubsHead] at h_mnk
          simp [funcSumTail, funcSubsHead]
          simp [← h_mnk]
          have h1 (g : func F (0 + n + k + 1)):
            funcAssoc 0 n k (funcSumTailSingle (0 + n + k) g)
            =
            funcSumTailSingle (0 + (n +k)) (funcAssoc_X_Id 0 n k 1 g)
            := by
            funext xs
            have h :=
              sumTailSingle_funcAssoc_X_Id_is_funcAssoc_sumTailSingle (F := F) 0 n k
            exact (by
              simpa [Function.comp] using
                (congrArg
                  (fun T => T g xs)
                  h
                ).symm)
          simp [h1]

          have h2 (g : func F (0 + (n + k) + 1)) :
            funcSumTailSingle (F := F) (n + k) (funcZeroAdd_X_Id (F := F) (n + k) 1 g)
            =
            funcZeroAdd (F := F) (n + k) (funcSumTailSingle (F := F) (0 + (n + k)) g) := by
            -- evaluate both sides at g
            exact congrArg
              (fun T => T g) (funcSumTailSingle_funcZeroAdd_X_Id_is_funcZeroAdd_funcSumTailSingle
                (F := F) (a := n + k))
          simp [← h2]
          rfl
      | succ m h_gen =>
          simp [funcSumTail, funcSubsHead]
          simp [Function.comp] at h_gen
          simp [Function.comp] at h_mnk
          simp [funcSubsHead] at h_mnk
          simp [← h_mnk]
          have h1 (g : func F (m + 1 + n + k + 1)) :
            funcAssoc (F := F) (m + 1) n k
                (funcSumTailSingle (F := F) ((m + 1) + n + k)
                  g)
              =
            funcSumTailSingle (F := F) ((m + 1) + (n + k))
                (funcAssoc_X_Id (F := F) (m + 1) n k 1
                  g)
            := by
          -- take the composition lemma, flip it, then evaluate at `g`
            exact congrArg
              (fun T => T g)
                ((sumTailSingle_funcAssoc_X_Id_is_funcAssoc_sumTailSingle
                (F := F) (a := m + 1) (b := n) (c := k)).symm)

          -- now use it inside your big goal (RHS contains exactly that subterm)
          simp [h1]

          have h2 (g : func F (m + 1 + (n + k) + 1)) :
            funcComm_X_Id (F := F) m 1 (n + k)
                (funcSumTailSingle (F := F) (m + 1 + (n + k)) g)
              =
            funcSumTailSingle (F := F) (1 + m + (n + k))
                (funcComm_X_Id_X_Id (F := F) m 1 (n + k) 1 g) := by
            exact congrArg (fun T => T g)
              ((funcSumTailSingle_funcComm_X_Id_X_Id_is_funcComm_X_Id_funcSumTailSingle
                  (F := F) (a := m) (b := 1) (c := n + k)).symm)

        -- apply it to the exact g that appears in your goal
          simp [h2]

          have h1_1
          (g : func F (1 + m + (n + k) + 1)) :
              funcSumTailSingle (F := F) (1 + (m + (n + k)))
                (funcAssoc_X_Id (F := F) 1 m (n + k) 1 g)
              =
              funcAssoc (F := F) 1 m (n + k)
                (funcSumTailSingle (F := F) ((1 + m) + (n + k)) g) := by
            -- apply function equality to the argument `g`
            exact (by
              simpa [Function.comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                congrArg (fun f => f g)
                  (sumTailSingle_funcAssoc_X_Id_is_funcAssoc_sumTailSingle
                    (F := F) (a := 1) (b := m) (c := n + k))
            )
          simp [← h1_1]

          have h3
          (g : func F ((1 + (m + (n + k))) + 1)) :
            funcSumTailSingle (F := F) (n := m + (n + k))
                (funcSubsHeadSingle (F := F) (n := (m + (n + k)) + 1) (r 0)
                  (funcAssoc (F := F) 1 (m + (n + k)) 1 g))
              =
            funcSubsHeadSingle (F := F) (n := m + (n + k)) (r 0)
              (funcSumTailSingle (F := F) (n := 1 + (m + (n + k))) g)
            := by
            exact (by
              -- just to normalize ((1+N)+1) ↔ (1+N+1) if needed
              simpa [Function.comp, Nat.add_assoc] using
                congrArg (fun T => T g)
                  (funcSumTailSingle_funcSubsHeadSingle_funcAssoc_is_funcSubsHeadSingle_funcSumTailSingle
                    (F := F) (n := m + (n + k)) (r_head := r 0))
            )
          simp [← h3]

          have h4
          (g : func F (m + (n + k) + 1)) :
            funcSubsHead (n + k) m (fun i => r i.succ)
              (funcSumTailSingle (m + (n + k)) g)
            =
            funcSumTailSingle (n + k)
              (funcSubsHead (n + k + 1) m (fun i => r i.succ)
                (funcAssoc m (n + k) 1 g))
            := by
            exact (by
            -- apply the function equality to the argument `g`
              simpa [Function.comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                congrArg (fun f => f g)
                  (funcSubsHead_funcSumTailSingle_is_funcSumTailSingle_funcSubsHead_funcAssoc
                    (F := F) (m := m) (n := n + k) (r := fun i => r i.succ))
            )

          simp [h4]

          have h5 (g : func F (1 + ((m + (n + k)) + 1))) :
            funcAssoc m (n + k) 1
              (funcSubsHeadSingle ((m + (n + k)) + 1) (r 0) g)
            =
            funcSubsHeadSingle (m + ((n + k) + 1)) (r 0) (funcId_X_Assoc 1 m (n + k) 1 g)
          := by
            exact (by
              simpa [Function.comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (congrArg (fun f => f g)
                  (funcSubsHeadSingle_funcId_X_Assoc_is_funcAssoc_funcSubsHeadSingle
                    (F := F) (a := m) (b := n + k) (c := 1) (r_head := r 0))).symm
            )
          simp [h5]

          have h6 (g : func F (m + (n + (k + 1)))) :
            funcSubsHead (n + k + 1) m (fun i => r i.succ) (funcId_X_Assoc_Inv m n k 1 g)
            =
            funcAssoc_Inv n k 1 (funcSubsHead (n + (k + 1)) m (fun i => r i.succ) g)
            := by
              exact (by
              -- apply the function equality to the argument `g`
                simpa [Function.comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  congrArg (fun f => f g)
                    (funcSubsHead_funcId_X_Assoc_Inv_is_funcAssoc_Inv_funcSubsHead
                      (F := F) (m := m) (a := n) (b := k) (c := 1) (r := fun i => r i.succ))
              )
          simp [← h6]

          have h7 (g : func F (1 + (m + (n + (k + 1))))) :
            funcId_X_Assoc_Inv m n k 1
              (funcSubsHeadSingle (m + (n + (k + 1))) (r 0) g)
            =
            funcSubsHeadSingle (m + (n + k + 1)) (r 0)
              (funcId_X_Id_X_Assoc_Inv 1 m n k 1 g)
            := by
            exact (by
              -- lemma gives: Subs ∘ Id_X_Id_X_Assoc_Inv = Id_X_Assoc_Inv ∘ Subs
              -- we want: Id_X_Assoc_Inv (Subs g) = Subs (Id_X_Id_X_Assoc_Inv g)
              -- so we use `.symm` after applying to `g`.
              simpa [Function.comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (congrArg (fun f => f g)
                  (funcSubsHeadSingle_funcId_X_Id_X_Assoc_Inv_is_funcId_X_Assoc_Inv_funcSubsHeadSingle
                    (F := F) (a := m) (b := n) (c := k) (d := 1) (r_head := r 0))).symm
              )
          simp [h7]
          rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end SumCheck
