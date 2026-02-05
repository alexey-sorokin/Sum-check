import SumCheck.func
import SumCheck.hypercube

noncomputable section
open Classical
open NEO
open scoped BigOperators

namespace NEO

universe u
variable {F : Type u} [Field F]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- SUM and EVAL DEFS

/--
Given `p : func F (a+b)`, produce a function `func F a` by summing over the `b`-hypercube:
`va ↦ ∑ vb∈{0,1}^b p (vecSplit_Inv (va, vb))`.
-/
def funcSumTail (a b : ℕ) : func F (a + b) → func F a :=
  fun p va =>
    ∑ x : HyperCube b,
      p (vecSplit_Inv (F := F) a b ⟨va, hypercubeVec (F := F) b x⟩)

def funcSumTotal (n : ℕ) : func F n → F :=
  funcZero ∘ (funcSumTail 0 n) ∘ (funcZeroAdd_Inv n)

/--
Evaluate the first `a` coordinates of a function on `a+b` variables,
leaving a function of the remaining `b` variables.
-/
def funcSubsHead (a b : ℕ) : vec F a → func F (a + b) → func F b :=
  fun va p vb => p (vecSplit_Inv (F := F) a b ⟨va, vb⟩)

def funcSubsTotal (n : ℕ) : vec F n → func F n → F :=
  fun v => funcZero ∘ (funcSubsHead n 0 v) ∘ (funcAddZero n)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- SUM and EVAL THEOREMS

/--
`func F (a+b+c) → func F b`, pointwise in `va : vec F a`.
-/
theorem funcSubsHead_funcSumTail_is_funcSumTail_funcSubsHead_funcAssoc
  (a b c : ℕ) (va : vec F a) :
    (funcSubsHead (F := F) a b va) ∘ (funcSumTail (F := F) (a + b) c)
      =
    (funcSumTail (F := F) b c) ∘ (funcSubsHead (F := F) a (b + c) va) ∘ (funcAssoc (F := F) a b c)
  := by
  funext p vb
  simp [funcSumTail, funcSubsHead, funcAssoc, Function.comp]
  refine Finset.sum_congr rfl ?_
  intro x hx

  have h0 := congrArg
    (fun f => f ⟨va, vb, hypercubeVec (F := F) c x⟩)
    (vecAppHeadTail_commutation (F := F) a b c).symm
  simp at h0

  have h0_lhs :
    vecApp_X_Id a b c (vecProdAssoc_Inv a b c (va, vb, hypercubeVec c x))
    =
    (vecSplit_Inv a b (va, vb), hypercubeVec c x)
    := by
    rfl

  have h0_rhs :
    vecId_X_App a b c (va, vb, hypercubeVec c x)
    =
    (va, vecSplit_Inv b c (vb, hypercubeVec c x))
    := by
    rfl

  rw [h0_rhs] at h0
  rw [← h0]
  simp [vecProdAssoc_Inv]


@[simp]
theorem finAddToFinSum_finZeroAdd_Inv_is_SumInr (n : ℕ) :
  (finAddToFinSum 0 n) ∘ (finZeroAdd_Inv n)
  =
  Sum.inr
  := by
  unfold finAddToFinSum finZeroAdd_Inv
  funext i
  simp [Fin.addCases]

theorem vecZeroAdd_vecSplit_Inv_is_ProdSnd (n : ℕ) :
  (vecZeroAdd n) ∘ (vecSplit_Inv (F := F) 0 n) = Prod.snd
  := by
  unfold vecSplit_Inv
  rw [← Function.comp_assoc]
  unfold vecZeroAdd
  unfold vecToVecSum_Inv
  unfold Function.comp
  funext ⟨v0, vn⟩
  have h (x : Fin n) :
    finAddToFinSum 0 n (finZeroAdd_Inv n x) = Sum.inr x
    := by
    simpa [Function.comp] using
      congrArg (fun f => f x) (finAddToFinSum_finZeroAdd_Inv_is_SumInr n)
  simp [h]

theorem funcSumTail00_funcZeroAdd_Inv0_is_id :
  (funcSumTail 0 0) ∘ (funcZeroAdd_Inv (F := F) 0) = id
  := by
  unfold funcSumTail funcZeroAdd_Inv id
  funext p va
  simp



@[simp]
theorem funcSumTail_is_funcSumTail_funcId_X_Comm (a b c : ℕ) :
  funcSumTail (F := F) a (b + c)
  =
  (funcSumTail (F := F) a (c + b)) ∘ (funcId_X_Comm (F := F) a b c)
  := by
  classical
  -- unfold both sides to pointwise equality
  funext p va
  unfold funcSumTail
  unfold funcId_X_Comm
  simp
  have h (v : vec F a × vec F (c + b)) :
    vecId_X_Comm (F:= F) a c b (vecSplit_Inv (F:= F) a (c + b) v)
    =
    vecSplit_Inv (F:= F) a (b + c) (vecProdId_X_vecComm (F:= F) a c b v)
    := by
    exact congrArg
      (fun f => f v)
      (vecSplit_Inv_vecProdId_X_vecComm_is_vecId_X_Comm_vecSplit_Inv a c b).symm
  simp [h]
  unfold vecProdId_X_vecComm
  simp
  have h1 (x : HyperCube (c + b)) :
    vecComm c b (hypercubeVec (c + b) x)
    =
    hypercubeVec (F := F) (b + c) (hypercubeVecComm c b x)
    := by
    exact congrArg
      (fun f => f x)
      (vecComm_hypercubeVec_is_hypercubeVec_hypercubeVecComm (F := F) c b)
  simp [h1]
  unfold hypercubeVecComm

  -- define the integrand on HyperCube (b+c)
  let G : HyperCube (b + c) → F :=
    fun x => p (vecSplit_Inv (F := F) a (b + c) (va, hypercubeVec (F := F) (b + c) x))

  -- use the reindexing lemma with (a := c) (b := b): HyperCube (c+b) → HyperCube (b+c)
  -- then flip sides to match your goal
  -- (after `unfold hypercubeVecComm`, the reindexing map is exactly (· ∘ finComm b c))
  have h2 := (hypercubeSumCommReindex (F := F) (a := c) (b := b) (g := G))
  -- `this` says: ∑ x : HyperCube (c+b), G (x ∘ finComm b c) = ∑ y : HyperCube (b+c), G y
  -- so we want its symmetry
  simpa [G, Function.comp] using h2.symm

@[simp]
theorem funcSumTail_is_funcSumTail_funcId_X_RightCancell
  (a b : ℕ) :
  funcSumTail (F := F) a (b + a - a)
  =
  (funcSumTail (F := F) a b) ∘ (funcId_X_RightCancell a b)
  := by
  unfold funcSumTail
  unfold funcId_X_RightCancell
  funext p va
  simp
  have h (v : vec F a × vec F b) :
    vecId_X_RightCancell_Inv (F:= F) a b (vecSplit_Inv (F:= F) a b v)
    =
    vecSplit_Inv (F:= F) a (b + a - a) (vecProdRightCancell_Inv (F:= F) a b v)
    := by
    exact congrArg
      (fun f => f v)
      (vecSplit_Inv_vecProdRightCancell_Inv_is_vecId_X_RightCancell_Inv_vecSplit_Inv a b).symm
  simp [h]
  unfold vecProdRightCancell_Inv
  simp
  let g : HyperCube b → F :=
    fun x =>
      p (vecSplit_Inv (F := F) a (b + a - a)
          (va, vecRightCancell_Inv (F := F) a b (hypercubeVec (F := F) b x)))

  have hcube (x : HyperCube (b + a - a)) :
      vecRightCancell_Inv (F := F) a b
          (hypercubeVec (F := F) b (hypercubeVecRightCancell a b x))
        =
      hypercubeVec (F := F) (b + a - a) x := by
    funext i
    simp [hypercubeVec, vecRightCancell_Inv, hypercubeVecRightCancell, Function.comp]
    rfl

  rw [← hypercubeSumRightCancellReindex (F := F) a b g]
  simp [g]
  simp [hcube]

@[simp]
theorem funcSumTail_funcSumTail_is_funcSumTail_funcAssoc (a b c : ℕ) :
  (funcSumTail (F := F) a b) ∘ (funcSumTail (F := F) (a + b) c)
    =
  (funcSumTail (F := F) a (b + c)) ∘ (funcAssoc (F := F) a b c)
:= by
  classical
  funext p va
  simp [funcSumTail, funcAssoc, Function.comp]

  let e := hypercubeSum_iso_hypercube_X_hypercube b c

  let g : HyperCube b → HyperCube c → F :=
    fun xb xc =>
      p (vecSplit_Inv (F := F) (a + b) c
          ⟨vecSplit_Inv (F := F) a b ⟨va, hypercubeVec (F := F) b xb⟩,
           hypercubeVec (F := F) c xc⟩)

  rw [hypercubeSum_hypercubeSum_is_hypercubeSum (F := F) b c g]
  rw [hypercubeSumOverProduct_is_hypercubeSumOverSum (F := F) b c g]
  refine Finset.sum_congr rfl ?_
  intro x hx

  have h0_raw :
      vecAssoc_Inv (F := F) a b c
          (vecSplit_Inv (F := F) a (b + c)
            ⟨va,
             vecSplit_Inv (F := F) b c
               ⟨hypercubeVec (F := F) b (e x).1,
                hypercubeVec (F := F) c (e x).2⟩⟩)
        =
      vecSplit_Inv (F := F) (a + b) c
          ⟨vecSplit_Inv (F := F) a b
              ⟨va, hypercubeVec (F := F) b (e x).1⟩,
           hypercubeVec (F := F) c (e x).2⟩ := by
    simpa [vecId_X_App, vecApp_X_Id, vecProdAssoc_Inv] using
      congrArg
      (fun f =>
        f ⟨va, hypercubeVec (F := F) b (e x).1, hypercubeVec (F := F) c (e x).2⟩)
          (vecAppHeadTail_commutation (F := F) a b c)

  rw [vecSplit_Inv_hypercubeVec_is_hypercubeVec (F := F) b c x] at h0_raw


  have h0' :
      vecAssoc_Inv (F := F) a b c
          (vecSplit_Inv (F := F) a (b + c)
            ⟨va, hypercubeVec (F := F) (b + c) x⟩)
        =
      vecSplit_Inv (F := F) (a + b) c
          ⟨vecSplit_Inv (F := F) a b
              ⟨va, hypercubeVec (F := F) b (e x).1⟩,
           hypercubeVec (F := F) c (e x).2⟩ := by
    -- rewrite the LHS of `h0_raw` using `hs`
    simpa [vecSplit_Inv_hypercubeVec_is_hypercubeVec (F := F) b c x] using h0_raw

  -- finish
  simp [g, h0']
  rfl

@[simp]
theorem funcSubsHead01_is_funcZeroAdd1 (r : vec F 0) :
  funcSubsHead (F := F) 0 1 r = funcZeroAdd (F := F) 1 := by
  unfold funcSubsHead
  unfold funcZeroAdd
  unfold vecSplit_Inv
  unfold vecToVecSum_Inv
  unfold vecSumSplit_Inv
  funext p v
  simp
  have h :
    (Sum.elim Fin.elim0 v) ∘ (finAddToFinSum 0 1) = v := by
      funext i
      unfold finAddToFinSum
      unfold Function.comp
      unfold Sum.elim
      simp [Fin.addCases]
  simp [h]



end NEO
