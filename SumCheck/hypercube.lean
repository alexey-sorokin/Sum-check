import SumCheck.func

noncomputable section

open Classical
open NEO
open scoped BigOperators

namespace NEO

universe u
variable {F : Type u} [Field F]

def HyperCube (n : ℕ) := Fin n → Fin 2

noncomputable instance (n : ℕ) : Fintype (HyperCube n) := by
  classical
  dsimp [HyperCube]
  infer_instance

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- Hypercube DEFS

def hypercubeVec (n : ℕ) : HyperCube n → vec F n :=
  (fin2ToF ∘ ·)

def hypercubeVecCast (n1 n2 : ℕ) (h : n1 = n2) : HyperCube n1 → HyperCube n2 :=
  (· ∘ finCast n2 n1 h.symm)

def hypercubeVecComm (a b : ℕ) : HyperCube (a + b) → HyperCube (b + a) :=
  (· ∘ finComm b a)

def hypercubeVecRightCancell (a b : ℕ) :
    HyperCube (b + a - a) → HyperCube b :=
  (· ∘ finRightCancell_Inv a b)

def hypercubeVecRightCancell_Inv (a b : ℕ) :
    HyperCube b → HyperCube (b + a - a) :=
  (· ∘ finRightCancell a b)

def hypercubeVecRightSubtr (a b c : ℕ) :
    HyperCube (a + c - (b + c)) → HyperCube (a - b) :=
  (· ∘ finRightSubtr_Inv a b c)

def hypercubeVecRightSubtr_Inv (a b c : ℕ) :
    HyperCube (a - b) → HyperCube (a + c - (b + c)) :=
  (· ∘ finRightSubtr a b c)



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- Hypercube THEOREMS

@[simp]
theorem hyperCube0_subsingleton : Subsingleton (HyperCube 0) := by
  dsimp [HyperCube]
  infer_instance

noncomputable instance hyperCube0Uniqueness : Unique (HyperCube 0) := by
  classical
  unfold HyperCube
  refine ⟨?_, ?_⟩
  · exact ⟨fun i => i.elim0⟩
  · intro f
    funext i
    exact i.elim0

/-- Split a hypercube on `a+b` coordinates into the first `a` and last `b`. -/
instance hypercubeSum_iso_hypercube_X_hypercube
  (a b : ℕ) :
  HyperCube (a + b) ≃ HyperCube a × HyperCube b :=
by
  classical
  refine
    { toFun := fun x =>
        ( (fun i : Fin a => x (Fin.castAdd b i))
        , (fun j : Fin b => x (Fin.natAdd a j)) )
      invFun := fun x =>
        fun i => Fin.addCases (fun i : Fin a => x.1 i) (fun j : Fin b => x.2 j) i
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    funext i
    cases i using Fin.addCases <;> simp
  · intro x
    cases' x with xa xb
    apply Prod.ext <;> funext i <;> simp

@[simp]
theorem hypercubeVecCast_bijective (n1 n2 : ℕ) (h : n1 = n2) :
    Function.Bijective (hypercubeVecCast n1 n2 h) := by
  constructor
  · intro x y hxy
    unfold hypercubeVecCast at hxy
    funext i
    have h0 := congrArg (fun f => f (finCast n1 n2 h i)) hxy
    simpa [Function.comp] using h0
  · intro y
    refine ⟨hypercubeVecCast n2 n1 h.symm y, ?_⟩
    unfold hypercubeVecCast
    rw [Function.comp_assoc]
    simp

@[simp]
theorem hypercubeVecRightSubtr_hypercubeVecRightSubtr_Inv_is_id (a b c : ℕ) :
  (hypercubeVecRightSubtr a b c) ∘ (hypercubeVecRightSubtr_Inv a b c) = id := by
  rfl

@[simp]
theorem hypercubeVecRightSubtr_Inv_hypercubeVecRightSubtr_is_id (a b c : ℕ) :
  (hypercubeVecRightSubtr_Inv a b c) ∘ (hypercubeVecRightSubtr a b c) = id := by
  rfl

@[simp]
theorem hypercubeVecRightCancell_hypercubeVecRightCancell_Inv_is_id (a b : ℕ) :
  (hypercubeVecRightCancell a b) ∘ (hypercubeVecRightCancell_Inv a b) = id := by
  rfl

@[simp]
theorem hypercubeVecRightCancell_Inv_hypercubeVecRightCancell_is_id (a b : ℕ) :
  (hypercubeVecRightCancell_Inv a b) ∘ (hypercubeVecRightCancell a b) = id := by
  rfl



@[simp]
theorem hypercubeVecComm_involutive (a b : ℕ) :
  (hypercubeVecComm b a) ∘ (hypercubeVecComm a b) = id := by
  rfl

@[simp]
theorem hypercubeVecComm_bijective (a b : ℕ) :
    Function.Bijective (hypercubeVecComm a b)
  := by
  constructor
  · -- injective
    intro x y hxy
    have := congrArg (hypercubeVecComm b a) hxy
    simpa [Function.comp] using this
  · -- surjective
    intro y
    refine ⟨hypercubeVecComm b a y, ?_⟩
    have := congrArg (fun f => f y) (hypercubeVecComm_involutive (a := b) (b := a))
    simpa [Function.comp] using this

@[simp]
theorem hypercubeVecRightCancell_bijective (a b : ℕ) :
    Function.Bijective (hypercubeVecRightCancell a b)
  := by
  constructor
  · -- injective
    intro x y hxy
    have := congrArg (hypercubeVecRightCancell_Inv a b) hxy
    simpa [Function.comp] using this
  · -- surjective
    intro y
    refine ⟨hypercubeVecRightCancell_Inv a b y, ?_⟩
    have := congrArg (fun f => f y) (hypercubeVecRightCancell_hypercubeVecRightCancell_Inv_is_id a b)
    simpa [Function.comp] using this

@[simp]
theorem hypercubeVecRightSubtr_bijective (a b c : ℕ) :
    Function.Bijective (hypercubeVecRightSubtr a b c)
  := by
  constructor
  · -- injective
    intro x y hxy
    have := congrArg (hypercubeVecRightSubtr_Inv a b c) hxy
    simpa [Function.comp] using this
  · -- surjective
    intro y
    refine ⟨hypercubeVecRightSubtr_Inv a b c y, ?_⟩
    have := congrArg (fun f => f y) (hypercubeVecRightSubtr_hypercubeVecRightSubtr_Inv_is_id a b c)
    simpa [Function.comp] using this


/-- Reindex a sum over `HyperCube (b+a)` along the commutation map. -/
@[simp]
theorem hypercubeSumCommReindex
  (a b : ℕ) (g : HyperCube (b + a) → F) :
    (∑ x : HyperCube (a + b), g (hypercubeVecComm a b x))
      =
    (∑ y : HyperCube (b + a), g y)
  := by
  classical
  let e : HyperCube (a + b) → HyperCube (b + a) := hypercubeVecComm a b
  have he : Function.Bijective e := hypercubeVecComm_bijective a b
  -- `sum_bijective` wants: ∑ x, f x = ∑ y, g y, with f x = g (e x)
  simpa [e] using
    (Fintype.sum_bijective e he (fun x => g (e x)) g (by intro x; rfl))

/-- Reindex a sum over `HyperCube (b + a - a)` along the right-cancellation map. -/
@[simp]
theorem hypercubeSumRightCancellReindex
  (a b : ℕ) (g : HyperCube b → F) :
    (∑ x : HyperCube (b + a - a), g (hypercubeVecRightCancell a b x))
      =
    (∑ y : HyperCube b, g y)
  := by
  classical
  let e : HyperCube (b + a - a) → HyperCube b := hypercubeVecRightCancell a b
  have he : Function.Bijective e := hypercubeVecRightCancell_bijective a b
  -- `sum_bijective` wants: ∑ x, f x = ∑ y, g y, with f x = g (e x)
  simpa [e] using
    (Fintype.sum_bijective e he (fun x => g (e x)) g (by intro x; rfl))

@[simp]
theorem hypercubeSumRightSubtrReindex
  (a b c : ℕ) (g : HyperCube (a - b) → F) :
    (∑ x : HyperCube (a + c - (b + c)), g (hypercubeVecRightSubtr a b c x))
      =
    (∑ y : HyperCube (a - b), g y)
  := by
  classical
  let e : HyperCube (a + c - (b + c)) → HyperCube (a - b) := hypercubeVecRightSubtr a b c
  have he : Function.Bijective e := hypercubeVecRightSubtr_bijective a b c
  -- `sum_bijective` wants: ∑ x, f x = ∑ y, g y, with f x = g (e x)
  simpa [e] using
    (Fintype.sum_bijective e he (fun x => g (e x)) g (by intro x; rfl))

@[simp]
theorem vecComm_hypercubeVec_is_hypercubeVec_hypercubeVecComm (a b : ℕ) :
  (vecComm (F := F) a b) ∘ (hypercubeVec (F := F) (a + b))
  =
  (hypercubeVec (F := F) (b + a)) ∘ (hypercubeVecComm a b)
  := by
  unfold hypercubeVec
  unfold hypercubeVecComm
  unfold vecComm
  funext i
  simp
  rfl



--@[simp]
theorem hypercubeSum_hypercubeSum_is_hypercubeSum
(a b : ℕ) (g : HyperCube a → HyperCube b → F) :
  (∑ xa : HyperCube a, ∑ xb : HyperCube b, g xa xb)
  =
  ∑ xab : HyperCube a × HyperCube b, g xab.1 xab.2
  := by
  simpa using (Fintype.sum_prod_type' g).symm

--@[simp]
theorem hypercubeSumOverProduct_is_hypercubeSumOverSum
(a b : ℕ) (g : HyperCube a → HyperCube b → F) :
  (∑ xab : HyperCube a × HyperCube b, g xab.1 xab.2)
  =
  ∑ x : HyperCube (a + b),
    g
    (hypercubeSum_iso_hypercube_X_hypercube a b x).1
    (hypercubeSum_iso_hypercube_X_hypercube a b x).2
  := by
  symm
  refine Fintype.sum_equiv (hypercubeSum_iso_hypercube_X_hypercube a b)
    (fun x => g
      (hypercubeSum_iso_hypercube_X_hypercube a b x).1 (hypercubeSum_iso_hypercube_X_hypercube a b x).2)
    (fun x => g x.1 x.2) ?_
  intro x
  rfl

/-Split a Boolean hypercube point `x : HyperCube (b + c)` into its first `b` and last `c` coordinates-/
@[simp]
theorem vecSplit_Inv_hypercubeVec_is_hypercubeVec
  (a b : ℕ) (x : HyperCube (a + b)) :
    vecSplit_Inv (F := F) a b
      ⟨hypercubeVec (F := F) a (hypercubeSum_iso_hypercube_X_hypercube a b x).1,
       hypercubeVec (F := F) b (hypercubeSum_iso_hypercube_X_hypercube a b x).2⟩
      =
    hypercubeVec (F := F) (a + b) x := by
  classical
  funext i
  cases i using Fin.addCases <;>
    simp [hypercubeVec, vecSplit_Inv, vecSumSplit_Inv, vecToVecSum_Inv,
      Function.comp, finAddToFinSum,
      hypercubeSum_iso_hypercube_X_hypercube]
