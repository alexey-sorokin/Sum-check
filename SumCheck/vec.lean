import SumCheck.fin

noncomputable section
open Classical
open NEO

namespace NEO

universe u
variable {F : Type u} [Field F]

def diag {α : Type u} : α → α × α :=
  fun x => ⟨x, x⟩

def vec (F : Type u) [Field F] (n : ℕ) : Type u :=
  Fin n → F

def vecSum (F : Type u) [Field F] (a b : ℕ) : Type u :=
  (Fin a ⊕ Fin b) → F

-- (a ⊕ (b ⊕ c)) → F
def vecSum3R (F : Type u) [Field F] (a b c : ℕ) : Type u :=
  (Fin a ⊕ (Fin b ⊕ Fin c)) → F

-- ((a ⊕ b) ⊕ c) → F
def vecSum3L (F : Type u) [Field F] (a b c : ℕ) : Type u :=
  ((Fin a ⊕ Fin b) ⊕ Fin c) → F

def fin2ToF : vec F 2
| ⟨0, _⟩ => 0
| ⟨1, _⟩ => 1

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- TRIVIAL DEFS

def vecZero : vec F 0 := Fin.elim0

def vecOne : vec F 1 → F :=
  fun v => v ⟨0, by simp⟩

def vecOne_Inv : F → vec F 1 :=
  fun x => fun _i => x

def vecCast (n1 n2 : ℕ) (h : n1 = n2) : vec F n1 → vec F n2 :=
  (· ∘ finCast n2 n1 h.symm)

def vecSumCast (a1 b1 a2 b2 : ℕ) (ha : a1 = a2) (hb : b1 = b2) :
  vecSum F a1 b1 → vecSum F a2 b2 :=
  (· ∘ finSumCast a2 b2 a1 b1 ha.symm hb.symm)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- LAMBDA DEFS

/- F^{0 + n} → F^{n} -/
def vecZeroAdd (n : ℕ) : vec F (0 + n) → vec F n :=
  (· ∘ finZeroAdd_Inv n)

/- F^{n} → F^{0 + n} -/
def vecZeroAdd_Inv (n : ℕ) : vec F n → vec F (0 + n) :=
  (· ∘ finZeroAdd n)

/- F^{0 + a + b} → F^{a + b} -/
def vecZeroAdd_X_Id (a b : ℕ) : vec F (0 + a + b) → vec F (a + b) :=
  (· ∘ finZeroAdd_X_Id_Inv a b)

/- F^{a + b} → F^{0 + a + b} -/
def vecZeroAdd_X_Id_Inv (a b : ℕ) : vec F (a + b) → vec F (0 + a + b) :=
  (· ∘ finZeroAdd_X_Id a b)

/- F^{a + (0 + b)} → F^{a + b} -/
def vecId_X_ZeroAdd (a b : ℕ) :
    vec F (a + (0 + b)) → vec F (a + b) :=
  (· ∘ finId_X_ZeroAdd_Inv a b)

/- F^{a + b} → F^{a + (0 + b)} -/
def vecId_X_ZeroAdd_Inv (a b : ℕ) :
    vec F (a + b) → vec F (a + (0 + b)) :=
  (· ∘ finId_X_ZeroAdd a b)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- RHO DEFS

/- F^{n + 0} → F^{n} -/
def vecAddZero (n : ℕ) : vec F (n + 0) → vec F n :=
  (· ∘ finAddZero_Inv n)

/- F^{n} → F^{n + 0} -/
def vecAddZero_Inv (n : ℕ) : vec F n → vec F (n + 0) :=
  (· ∘ finAddZero n)

/- F^{a + 0 + b} → F^{a + b} -/
def vecAddZero_X_Id (a b : ℕ) : vec F (a + 0 + b) → vec F (a + b) :=
  (· ∘ finAddZero_X_Id_Inv a b)

/- F^{a + b} → F^{a + 0 + b} -/
def vecAddZero_X_Id_Inv (a b : ℕ) : vec F (a + b) → vec F (a + 0 + b) :=
  (· ∘ finAddZero_X_Id a b)

/- F^{a + 0 + b + c} → F^{a + b + c} -/
def vecAddZero_X_Id_X_Id (a b c : ℕ) :
    vec F (a + 0 + b + c) → vec F (a + b + c) :=
  (· ∘ finAddZero_X_Id_X_Id_Inv (a := a) (b := b) (c := c))

/- F^{a + b + c} → F^{a + 0 + b + c} -/
def vecAddZero_X_Id_X_Id_Inv (a b c : ℕ) :
    vec F (a + b + c) → vec F (a + 0 + b + c) :=
  (· ∘ finAddZero_X_Id_X_Id (a := a) (b := b) (c := c))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ASSOCITIVITY DEFS

/- F^{n + k + l} → F^{n + (k + l)} -/
def vecAssoc (n k l : ℕ) : vec F (n + k + l) → vec F (n + (k + l)) :=
  (· ∘ finAssoc_Inv n k l)

/- F^{n + (k + l)} → F^{n + k + l} -/
def vecAssoc_Inv (n k l : ℕ) : vec F (n + (k + l)) → vec F (n + k + l) :=
  (· ∘ finAssoc n k l)

/- F^{a + b + c + d} → F^{a + (b + c) + d} -/
def vecAssoc_X_Id (a b c d : ℕ) : vec F (a + b + c + d) → vec F (a + (b + c) + d) :=
  (· ∘ finAssoc_X_Id_Inv a b c d)

/- F^{a + (b + c) + d} → F^{a + b + c + d} -/
def vecAssoc_X_Id_Inv (a b c d : ℕ) : vec F (a + (b + c) + d) → vec F (a + b + c + d) :=
  (· ∘ finAssoc_X_Id a b c d)

/- F^{a + (b + c + d)} → F^{a + (b + (c + d))} -/
def vecId_X_Assoc (a b c d : ℕ) : vec F (a + (b + c + d)) → vec F (a + (b + (c + d))) :=
  (· ∘ finId_X_Assoc_Inv a b c d)

/- F^{a + (b + (c + d))} → F^{a + (b + c + d)} -/
def vecId_X_Assoc_Inv (a b c d : ℕ) : vec F (a + (b + (c + d))) → vec F (a + (b + c + d)) :=
  (· ∘ finId_X_Assoc a b c d)

/- F^{a + (b + (c + d + e))} → F^{a + (b + (c + (d + e)))} -/
def vecId_X_Id_X_Assoc (a b c d e : ℕ) :
    vec F (a + (b + (c + d + e))) → vec F (a + (b + (c + (d + e)))) :=
  (· ∘ finId_X_Id_X_Assoc_Inv a b c d e)

/- F^{a + (b + (c + (d + e)))} → F^{a + (b + (c + d + e))} -/
def vecId_X_Id_X_Assoc_Inv (a b c d e : ℕ) :
    vec F (a + (b + (c + (d + e)))) → vec F (a + (b + (c + d + e))) :=
  (· ∘ finId_X_Id_X_Assoc a b c d e)

/- F^{(a ⊕ b) ⊕ c} → F^{a ⊕ (b ⊕ c)} -/
def vecSumAssoc (a b c : ℕ) :
    vecSum3L F a b c → vecSum3R F a b c :=
  (· ∘ finSumAssoc_Inv a b c)

/- F^{a ⊕ (b ⊕ c)} → F^{(a ⊕ b) ⊕ c} -/
def vecSumAssoc_Inv (a b c : ℕ) :
    vecSum3R F a b c → vecSum3L F a b c :=
  (· ∘ finSumAssoc a b c)

/- (F^{a} × F^{b}) × F^{c} → F^{a} × (F^{b} × F^{c}) -/
def vecProdAssoc (a b c : ℕ) :
    ((vec F a × vec F b) × vec F c) → (vec F a × (vec F b × vec F c)) :=
  fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩

/- F^{a} × (F^{b} × F^{c}) → (F^{a} × F^{b}) × F^{c} -/
def vecProdAssoc_Inv (a b c : ℕ) :
    (vec F a × (vec F b × vec F c)) → ((vec F a × vec F b) × vec F c) :=
  fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩

/- F^a × ((F^b × F^c) × F^d) → (F^a × (F^b × F^c)) × F^d -/
def vecProdAssoc4_Inv (a b c d : ℕ) :
    vec F a × ((vec F b × vec F c) × vec F d) → (vec F a × (vec F b × vec F c)) × vec F d :=
  fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- COMMUTATIVITY DEFS

/- F^{a + b} → F^{b + a} -/
def vecComm (a b : ℕ) : vec F (a + b) → vec F (b + a) :=
  (· ∘ finComm b a)

/- F^{a + b + c} → F^{b + a + c} -/
def vecComm_X_Id (a b c : ℕ) : vec F (a + b + c) → vec F (b + a + c) :=
  (· ∘ finComm_X_Id b a c)

/- F^{a + (b + c)} → F^{a + (c + b)} -/
def vecId_X_Comm (a b c : ℕ) : vec F (a + (b + c)) → vec F (a + (c + b)) :=
  (· ∘ finId_X_Comm a c b)

/- F^{a + b + c + d} → F^{b + a + c + d} -/
def vecComm_X_Id_X_Id (a b c d : ℕ) : vec F (a + b + c + d) → vec F (b + a + c + d) :=
  (· ∘ finComm_X_Id_X_Id b a c d)

/- F^{a + (b + c) + d} → F^{a + (c + b) + d} -/
def vecId_X_Comm_XX_Id (a b c d : ℕ) :
    vec F (a + (b + c) + d) → vec F (a + (c + b) + d) :=
  (· ∘ finId_X_Comm_XX_Id a c b d)

/-
   F^(a+b) × F^c  ─────── vecComm_P_Id ───────▶  F^(b+a) × F^c
-/
def vecComm_P_Id (a b c : ℕ) :
    vec F (a + b) × vec F c → vec F (b + a) × vec F c :=
  Prod.map (vecComm a b) id

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- Splitting DEFS

def vecTakeHead (a b : ℕ) : vec F (a + b) → vec F a :=
  (· ∘ finEmbedHead a b)

def vecTakeTail (a b : ℕ) : vec F (a + b) → vec F b :=
  (· ∘ finEmbedTail a b)

def vecTakeHeadConditional (n a b : ℕ) (h : n = a + b) :
    vec F n → vec F a :=
  (· ∘ finEmbedHeadConditional n a b h)

def vecTakeTailConditional (n a b : ℕ) (h : n = a + b) :
    vec F n → vec F b :=
  (· ∘ finEmbedTailConditional n a b h)

/- F^{a + b} → F^{a ⊕ b} -/
def vecToVecSum (a b : ℕ) :
    vec F (a + b) → vecSum F a b :=
  (· ∘ finAddToFinSum_Inv a b)

/- F^{a ⊕ b} → F^{a + b} -/
def vecToVecSum_Inv (a b : ℕ) :
    vecSum F a b → vec F (a + b) :=
  (· ∘ finAddToFinSum a b)

/- F^{a ⊕ b} → F^{a} × F^{b} -/
def vecSumSplit (a b : ℕ) :
    vecSum F a b → vec F a × vec F b :=
  Prod.map (· ∘ Sum.inl) (· ∘ Sum.inr) ∘ diag

/- F^{a} × F^{b} → F^{a ⊕ b} -/
def vecSumSplit_Inv (a b : ℕ) :
    (vec F a × vec F b) → vecSum F a b :=
  Prod.rec Sum.elim

/- F^{a} × (F^{b} × F^{c}) → F^{a} × F^{b ⊕ c} -/
def vecId_X_vecSumSplit_Inv (a b c : ℕ) :
    vec F a × (vec F b × vec F c) → vec F a × vecSum F b c :=
  Prod.map id (vecSumSplit_Inv b c)

/- F^{a} × F^{b ⊕ c} → F^{a} × (F^{b} × F^{c}) -/
def vecId_X_vecSumSplit_Inv_Inv (a b c : ℕ) :
    vec F a × vecSum F b c → vec F a × (vec F b × vec F c) :=
  Prod.map id (vecSumSplit b c)

/- (F^{a} × F^{b}) × F^{c} → F^{a ⊕ b} × F^{c} -/
def vecSumSplit_Inv_X_Id (a b c : ℕ) :
    (vec F a × vec F b) × vec F c → vecSum F a b × vec F c :=
  Prod.map (vecSumSplit_Inv a b) id

/- F^{a ⊕ b} × F^{c} → (F^{a} × F^{b}) × F^{c} -/
def vecSumSplit_Inv_X_Id_Inv (a b c : ℕ) :
    vecSum F a b × vec F c → (vec F a × vec F b) × vec F c :=
  Prod.map (vecSumSplit a b) id

/- F^{a} × F^{b ⊕ c} → F^{a} × F^{b + c} -/
def vecId_X_ToVecSum_Inv (a b c : ℕ) :
    vec F a × vecSum F b c → vec F a × vec F (b + c) :=
  Prod.map id (vecToVecSum_Inv b c)

/- F^{a} × F^{b + c} → F^{a} × F^{b ⊕ c} -/
def vecId_X_ToVecSum_Inv_Inv (a b c : ℕ) :
    vec F a × vec F (b + c) → vec F a × vecSum F b c :=
  Prod.map id (vecToVecSum b c)

/- F^{a ⊕ b} × F^{c} → F^{a + b} × F^{c} -/
def vecToVecSum_Inv_X_Id (a b c : ℕ) :
    vecSum F a b × vec F c → vec F (a + b) × vec F c :=
  Prod.map (vecToVecSum_Inv a b) id

/- F^{a + b} × F^{c} → F^{a ⊕ b} × F^{c} -/
def vecToVecSum_Inv_X_Id_Inv (a b c : ℕ) :
    vec F (a + b) × vec F c → vecSum F a b × vec F c :=
  Prod.map (vecToVecSum a b) id

/- F^{a} × (F^{b} × F^{c}) → F^{a} × F^{b + c} -/
def vecId_X_App (a b c : ℕ) :
    vec F a × (vec F b × vec F c) → vec F a × vec F (b + c) :=
  (vecId_X_ToVecSum_Inv a b c) ∘ (vecId_X_vecSumSplit_Inv a b c)

/- F^{a} × F^{b + c} → F^{a} × (F^{b} × F^{c}) -/
def vecId_X_App_Inv (a b c : ℕ) :
    vec F a × vec F (b + c) → vec F a × (vec F b × vec F c) :=
  (vecId_X_vecSumSplit_Inv_Inv a b c) ∘ (vecId_X_ToVecSum_Inv_Inv a b c)

/- (F^{a} × F^{b}) × F^{c} → F^{a + b} × F^{c} -/
def vecApp_X_Id (a b c : ℕ) :
    (vec F a × vec F b) × vec F c → vec F (a + b) × vec F c :=
  (vecToVecSum_Inv_X_Id a b c) ∘ (vecSumSplit_Inv_X_Id a b c)

/- F^{a + b} × F^{c} → (F^{a} × F^{b}) × F^{c} -/
def vecApp_X_Id_Inv (a b c : ℕ) :
    vec F (a + b) × vec F c → (vec F a × vec F b) × vec F c :=
  (vecSumSplit_Inv_X_Id_Inv a b c) ∘ (vecToVecSum_Inv_X_Id_Inv a b c)

/- F^{a ⊕ (b ⊕ c)} → F^{a} × F^{b ⊕ c} -/
def vecSum3RSplit (a b c : ℕ) :
    vecSum3R F a b c → (vec F a × vecSum F b c) :=
  Prod.map (· ∘ Sum.inl) (· ∘ Sum.inr) ∘ diag

/- F^{a} × F^{b ⊕ c} → F^{a ⊕ (b ⊕ c)} -/
def vecSum3RSplit_Inv (a b c : ℕ) :
    (vec F a × vecSum F b c) → vecSum3R F a b c :=
  Prod.rec Sum.elim

/- F^{(a ⊕ b) ⊕ c} → F^{a ⊕ b} × F^{c} -/
def vecSum3LSplit (a b c : ℕ) :
    vecSum3L F a b c → (vecSum F a b × vec F c) :=
  Prod.map (· ∘ Sum.inl) (· ∘ Sum.inr) ∘ diag

/- F^{a ⊕ b} × F^{c} → F^{(a ⊕ b) ⊕ c} -/
def vecSum3LSplit_Inv (a b c : ℕ) :
    (vecSum F a b × vec F c) → vecSum3L F a b c :=
  Prod.rec Sum.elim

/- F^{a ⊕ (b ⊕ c)} → F^{a ⊕ (b + c)} -/
def vecSum3RToVecSum (a b c : ℕ) :
    vecSum3R F a b c → vecSum F a (b + c) :=
  (· ∘ finId_X_AddToFinSum a b c)

/- F^{(a ⊕ b) ⊕ c} → F^{(a + b) ⊕ c} -/
def vecSum3LToVecSum (a b c : ℕ) :
    vecSum3L F a b c → vecSum F (a + b) c :=
  (· ∘ finAddToFinSum_X_Id a b c)

/- F^{a + b} → F^{a} × F^{b} -/
def vecSplit (a b : ℕ) :
    vec F (a + b) → vec F a × vec F b :=
  (vecSumSplit (F := F) a b) ∘ (vecToVecSum (F := F) a b)

/- F^{a} × F^{b} → F^{a + b} -/
def vecSplit_Inv (a b : ℕ) :
    (vec F a × vec F b) → vec F (a + b) :=
  (vecToVecSum_Inv (F := F) a b) ∘ vecSumSplit_Inv a b

/- F^{n} → F^{a + b}  (given n = a + b) -/
def vecDesum (n a b : ℕ) (h : n = a + b) :
    vec F n → vec F (a + b) :=
  (· ∘ finDesum_Inv (n := n) (a := a) (b := b) h)

/- F^{a + b} → F^{n}  (given n = a + b) -/
def vecDesum_Inv (n a b : ℕ) (h : n = a + b) :
    vec F (a + b) → vec F n :=
  (· ∘ finDesum (n := n) (a := a) (b := b) h)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- OTHER DEFS

def vecRightComm (a b c : ℕ) : vec F (a + b + c) → vec F (a + c + b) :=
  fun v i => v (finRightComm a c b i)

def vecLeftComm (a b c : ℕ) : vec F (a + (b + c)) → vec F (b + (a + c)) :=
  fun v i => v (finLeftComm b a c i)

/-
   vecId_X_CastToPrefixOneSuffix

   F^(a + ((i.1+1) + (b-(i.1+1))))  ─────────────────────────▶  F^(a + b)
-/
def vecId_X_CastToPrefixOneSuffix (a b : ℕ) (i : Fin b) :
    vec F (a + ((i.1 + 1) + (b - (i.1 + 1)))) → vec F (a + b) :=
  (· ∘ finId_X_CastToPrefixOneSuffix a b i)

/-
   vecCastToPrefixOneSuffix

   F^((i.1+1) + (n-(i.1+1)))  ─────────────────────────▶  F^n
-/
def vecCastToPrefixOneSuffix (n : ℕ) (i : Fin n) :
    vec F ((i.1 + 1) + (n - (i.1 + 1))) → vec F n :=
  (· ∘ finCastToPrefixOneSuffix n i)

/-
   vecId_P_CastToPrefixOneSuffix

   F^a × F^((i.1+1) + (b-(i.1+1)))  ─────────────────────────▶  F^a × F^b
-/
def vecId_P_CastToPrefixOneSuffix (a b : ℕ) (i : Fin b) :
    vec F a × vec F ((i.1 + 1) + (b - (i.1 + 1))) → vec F a × vec F b :=
  Prod.map id (vecCastToPrefixOneSuffix b i)


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^(a - b)  ─────── vecRightSubtr_Inv ───────▶  F^(a + c - (b + c))
-/
def vecRightSubtr_Inv (a b c : ℕ) : vec F (a - b) → vec F (a + c - (b + c)) :=
  (· ∘ finRightSubtr a b c)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^(a + c - (b + c))  ─────── vecRightSubtr ───────▶  F^(a - b)
-/
def vecRightSubtr (a b c : ℕ) : vec F (a + c - (b + c)) → vec F (a - b) :=
  (· ∘ finRightSubtr_Inv a b c)


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^b  ─── vecRightCancell_Inv ───▶  F^(b + a - a)
-/
def vecRightCancell_Inv (a b : ℕ) : vec F b → vec F (b + a - a) :=
  (· ∘ finRightCancell a b)


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^a ⊕ F^b  ─── vecSumId_X_RightCancell_Inv ───▶  F^a ⊕ F^(b + a - a)
-/
def vecSumId_X_RightCancell_Inv (a b : ℕ) :
    vecSum F a b → vecSum F a (b + a - a) :=
  (· ∘ finSumId_X_RightCancell a b)


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^(a + b)  ─── vecId_X_RightCancell_Inv ───▶  F^(a + (b + a - a))
-/
def vecId_X_RightCancell_Inv (a b : ℕ) :
    vec F (a + b) → vec F (a + (b + a - a)) :=
  (· ∘ finId_X_RightCancell a b)


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^a × F^b  ─── vecProdRightCancell_Inv ───▶  F^a × F^(b + a - a)
-/
def vecProdRightCancell_Inv (a b : ℕ) :
    vec F a × vec F b → vec F a × vec F (b + a - a) :=
  Prod.map id (vecRightCancell_Inv a b)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^a ⊕ F^(b + c)  ─── vecSumId_X_vecComm ───▶  F^a ⊕ F^(c + b)
-/
def vecSumId_X_vecComm (a b c : ℕ) :
    vecSum F a (b + c) → vecSum F a (c + b) :=
  (· ∘ finSumId_X_finComm a c b)


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^a × F^(b + c)  ─── vecProdId_X_vecComm ───▶  F^a × F^(c + b)
-/
def vecProdId_X_vecComm (a b c : ℕ) :
    vec F a × vec F (b + c) → vec F a × vec F (c + b) :=
  Prod.map id (vecComm b c)

-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================
-- ==========================================================================

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- TRIVIAL THEOREMS

@[simp]
theorem vecOne_vecOneInv_is_id :
  (vecOne (F := F)) ∘ (vecOne_Inv (F := F)) = id := by
  funext x
  rfl

@[simp]
theorem vecOneInv_vecOne_is_id :
  (vecOne_Inv (F := F)) ∘ (vecOne (F := F)) = id := by
  funext v
  -- both sides are the same value, since vecOneInv produces a constant function
  funext i
  simp [vecOne, vecOne_Inv, Function.comp]
  have hi : i = (0 : Fin 1) := by
    simpa using (Fin.eq_zero i)
  -- now rewrite
  simp [hi]

@[simp]
theorem vecCast_rfl {n : ℕ} :
    vecCast (F := F) (n1 := n) (n2 := n) rfl = id := by
  rfl

/-- `vecCast` and its inverse (casting back) compose to `id`. -/
@[simp]
theorem vecCast_involutive (n1 n2 : ℕ) (h : n1 = n2) :
    (vecCast (n1 := n2) (n2 := n1) h.symm) ∘
      (vecCast (F := F) (n1 := n1) (n2 := n2) h) = id := by
  funext v
  funext i
  -- both sides are definitional once `Fin.cast` cancels
  simp [vecCast, Function.comp]
  rfl

@[simp]
theorem vecZeroAdd_is_vecCast0 (n : ℕ) :
  vecZeroAdd (F := F) n = vecCast (F := F) (0 + n) n (by simp)
  := by
  rfl

@[simp]
theorem vecAddZero_is_vecCast0 (n : ℕ) :
  vecAddZero (F := F) n = vecCast (F := F) (n + 0) n (by simp)
  := by
  rfl

@[simp]
theorem vecZeroAdd_Inv_is_vecCast0 (n : ℕ) :
  vecZeroAdd_Inv (F := F) n = vecCast (F := F) n (0 + n) (by simp)
  := by
  rfl

@[simp]
theorem vecAddZero_Inv_is_vecCast0 (n : ℕ) :
  vecAddZero (F := F) n = vecCast (F := F) n (n + 0) (by simp)
  := by
  rfl

@[simp]
theorem vecZeroEqElim0 (v0 : vec F 0) :
    v0 = Fin.elim0
  := by
  funext i
  exact Fin.elim0 i

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- LAMBDA THEOREMS

@[simp]
theorem vecZeroAdd_vecZeroAdd_Inv_is_id
  (n : ℕ) :
    (vecZeroAdd (F := F) n) ∘ (vecZeroAdd_Inv (F := F) n) = id := by
  funext xs i
  unfold vecZeroAdd vecZeroAdd_Inv
  rfl

@[simp]
theorem vecZeroAdd_Inv_vecZeroAdd_is_id
  (n : ℕ) :
    (vecZeroAdd_Inv (F := F) n) ∘ (vecZeroAdd (F := F) n) = id := by
  funext xs i
  unfold vecZeroAdd vecZeroAdd_Inv
  rfl

@[simp]
theorem vecZeroAdd_X_Id_vecZeroAdd_X_Id_Inv_is_id
  (a b : ℕ) :
    (vecZeroAdd_X_Id (F := F) a b) ∘ (vecZeroAdd_X_Id_Inv (F := F) a b) = id := by
  funext xs i
  unfold vecZeroAdd_X_Id vecZeroAdd_X_Id_Inv
  rfl

@[simp]
theorem vecZeroAdd_X_Id_Inv_vecZeroAdd_X_Id_is_id
  (a b : ℕ) :
    (vecZeroAdd_X_Id_Inv (F := F) a b) ∘ (vecZeroAdd_X_Id (F := F) a b) = id := by
  funext xs i
  unfold vecZeroAdd_X_Id vecZeroAdd_X_Id_Inv
  rfl

@[simp]
theorem vecId_X_ZeroAdd_vecId_X_ZeroAdd_Inv_is_id
  (a b : ℕ) :
    (vecId_X_ZeroAdd (F := F) a b) ∘
      (vecId_X_ZeroAdd_Inv (F := F) a b)
  = id
  := by
  funext xs
  funext i
  simp [vecId_X_ZeroAdd, vecId_X_ZeroAdd_Inv, Function.comp]
  rfl

@[simp]
theorem vecId_X_ZeroAdd_Inv_vecId_X_ZeroAdd_is_id
  (a b : ℕ) :
    (vecId_X_ZeroAdd_Inv (F := F) a b) ∘
      (vecId_X_ZeroAdd (F := F) a b)
  = id
  := by
  funext xs
  funext i
  simp [vecId_X_ZeroAdd, vecId_X_ZeroAdd_Inv, Function.comp]
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- RHO THEOREMS

@[simp]
theorem vecAddZero_vecAddZero_Inv_is_id
  (n : ℕ) :
    (vecAddZero (F := F) n) ∘ (vecAddZero_Inv (F := F) n) = id := by
  funext xs i
  unfold vecAddZero vecAddZero_Inv
  rfl

@[simp]
theorem vecAddZero_Inv_vecAddZero_is_id
  (n : ℕ) :
    (vecAddZero_Inv (F := F) n) ∘ (vecAddZero (F := F) n) = id := by
  funext xs i
  unfold vecAddZero vecAddZero_Inv
  rfl

@[simp]
theorem vecAddZero_X_Id_vecAddZero_X_Id_Inv_is_id
  (a b : ℕ) :
    (vecAddZero_X_Id (F := F) a b) ∘ (vecAddZero_X_Id_Inv (F := F) a b) = id := by
  funext xs i
  unfold vecAddZero_X_Id vecAddZero_X_Id_Inv
  rfl

@[simp]
theorem vecAddZero_X_Id_Inv_vecAddZero_X_Id_is_id
  (a b : ℕ) :
    (vecAddZero_X_Id_Inv (F := F) a b) ∘ (vecAddZero_X_Id (F := F) a b) = id := by
  funext xs i
  unfold vecAddZero_X_Id vecAddZero_X_Id_Inv
  rfl

@[simp]
theorem vecAddZero_X_Id_X_Id_vecAddZero_X_Id_X_Id_Inv_is_id
  (a b c : ℕ) :
  (vecAddZero_X_Id_X_Id (F := F) a b c) ∘
      (vecAddZero_X_Id_X_Id_Inv (F := F) a b c)
    =
  id := by
  funext v i
  simp [vecAddZero_X_Id_X_Id, vecAddZero_X_Id_X_Id_Inv, Function.comp]
  rfl

@[simp]
theorem vecAddZero_X_Id_X_Id_Inv_vecAddZero_X_Id_X_Id_is_id
  (a b c : ℕ) :
  (vecAddZero_X_Id_X_Id_Inv (F := F) a b c) ∘
      (vecAddZero_X_Id_X_Id (F := F) a b c)
    =
  id := by
  funext v i
  simp [vecAddZero_X_Id_X_Id, vecAddZero_X_Id_X_Id_Inv, Function.comp]
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- ASSOCITIVITY THEOREMS

@[simp]
theorem vecAssoc_vecAssoc_Inv_is_id
  (n k l : ℕ) :
    (vecAssoc (F := F) n k l) ∘ (vecAssoc_Inv (F := F) n k l) = id := by
  funext v i
  unfold vecAssoc vecAssoc_Inv
  rfl

@[simp]
theorem vecAssoc_Inv_vecAssoc_is_id
  (n k l : ℕ) :
    (vecAssoc_Inv (F := F) n k l) ∘ (vecAssoc (F := F) n k l) = id := by
  funext v i
  unfold vecAssoc vecAssoc_Inv
  rfl

@[simp]
theorem vecAssoc_X_Id_vecAssoc_X_Id_Inv_is_id
  (a b c d : ℕ) :
    (vecAssoc_X_Id (F := F) a b c d) ∘ (vecAssoc_X_Id_Inv (F := F) a b c d) = id := by
  funext v i
  unfold vecAssoc_X_Id vecAssoc_X_Id_Inv
  rfl

@[simp]
theorem vecAssoc_X_Id_Inv_vecAssoc_X_Id_is_id
  (a b c d : ℕ) :
    (vecAssoc_X_Id_Inv (F := F) a b c d) ∘ (vecAssoc_X_Id (F := F) a b c d) = id := by
  funext v i
  unfold vecAssoc_X_Id vecAssoc_X_Id_Inv
  rfl

@[simp]
theorem vecId_X_Assoc_vecId_X_Assoc_Inv_is_id
  (a b c d : ℕ) :
    (vecId_X_Assoc (F := F) a b c d) ∘ (vecId_X_Assoc_Inv (F := F) a b c d) = id := by
  funext v i
  unfold vecId_X_Assoc vecId_X_Assoc_Inv
  rfl

@[simp]
theorem vecId_X_Assoc_Inv_vecId_X_Assoc_is_id
  (a b c d : ℕ) :
    (vecId_X_Assoc_Inv (F := F) a b c d) ∘ (vecId_X_Assoc (F := F) a b c d) = id := by
  funext v i
  unfold vecId_X_Assoc vecId_X_Assoc_Inv
  rfl

@[simp]
theorem vecId_X_Id_X_Assoc_vecId_X_Id_X_Assoc_Inv_is_id
  (a b c d e : ℕ) :
    (vecId_X_Id_X_Assoc (F := F) a b c d e) ∘
      (vecId_X_Id_X_Assoc_Inv (F := F) a b c d e) = id := by
  funext v i
  unfold vecId_X_Id_X_Assoc vecId_X_Id_X_Assoc_Inv
  simp [Function.comp]
  rfl

@[simp]
theorem vecId_X_Id_X_Assoc_Inv_vecId_X_Id_X_Assoc_is_id
  (a b c d e : ℕ) :
    (vecId_X_Id_X_Assoc_Inv (F := F) a b c d e) ∘
      (vecId_X_Id_X_Assoc (F := F) a b c d e) = id := by
  funext v i
  unfold vecId_X_Id_X_Assoc vecId_X_Id_X_Assoc_Inv
  simp [Function.comp]
  rfl

@[simp]
theorem vecSumAssoc_vecSumAssoc_Inv_is_id (a b c : ℕ) :
    (vecSumAssoc (F := F) a b c) ∘ (vecSumAssoc_Inv (F := F) a b c) = id
  := by
  unfold vecSumAssoc vecSumAssoc_Inv
  funext v
  simp [Function.comp_assoc]

@[simp]
theorem vecSumAssoc_Inv_vecSumAssoc_is_id (a b c : ℕ) :
    (vecSumAssoc_Inv (F := F) a b c) ∘ (vecSumAssoc (F := F) a b c) = id
  := by
  unfold vecSumAssoc vecSumAssoc_Inv
  funext v
  simp [Function.comp_assoc]

@[simp] theorem vecProdAssoc_vecProdAssoc_Inv_is_id (a b c : ℕ) :
    (vecProdAssoc (F := F) a b c) ∘ (vecProdAssoc_Inv (F := F) a b c) = id := by
  funext x
  cases x with
  | mk va bc =>
    cases bc with
    | mk vb vc =>
      rfl

@[simp] theorem vecProdAssoc_Inv_vecProdAssoc_is_id (a b c : ℕ) :
    (vecProdAssoc_Inv (F := F) a b c) ∘ (vecProdAssoc (F := F) a b c) = id := by
  funext x
  cases x with
  | mk ab vc =>
    cases ab with
    | mk va vb =>
      rfl

/-
                       Prod.map id (Prod.map (vecSplit_Inv b c) id)
   F^a × ((F^b × F^c) × F^d) ───────────────────────────────────────▶ F^a × (F^(b+c) × F^d)
            │                                                                    │
            │ vecProdAssoc4_Inv a b c d                                          │                                                      vecProdAssoc_Inv a (b+c) d
            ▼                                                                    ▼
   (F^a × (F^b × F^c)) × F^d ───────────────────────────────────────▶ (F^a × F^(b+c)) × F^d
                       Prod.map (Prod.map id (vecSplit_Inv b c)) id
-/
@[simp]
theorem vecProdAssoc_Inv_vecSplit_Inv_comm (a b c d : ℕ) :
  (vecProdAssoc_Inv (F := F) a (b + c) d)
    ∘ (Prod.map id (Prod.map (vecSplit_Inv (F := F) b c) id))
  =
  (Prod.map (Prod.map id (vecSplit_Inv (F := F) b c)) id)
    ∘ (vecProdAssoc4_Inv (F := F) a b c d)
  := by
  unfold vecProdAssoc_Inv
  unfold vecProdAssoc4_Inv
  unfold vecSplit_Inv
  unfold vecSumSplit_Inv vecToVecSum_Inv
  funext ⟨va, ⟨⟨vb, vc⟩, vd⟩⟩
  simp [Function.comp]



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- COMMUTATIVITY THEOREMS

@[simp]
theorem vecComm_involutive (a b : ℕ) :
  (vecComm b a) ∘ (vecComm (F := F) a b) = id := by
  rfl

@[simp]
theorem vecComm_X_Id_involutive (a b c : ℕ) :
  (vecComm_X_Id b a c) ∘ (vecComm_X_Id (F := F) a b c) = id := by
  rfl

@[simp]
theorem vecId_X_Comm_involutive (a b c : ℕ) :
  (vecId_X_Comm a c b) ∘ (vecId_X_Comm (F := F) a b c) = id := by
  rfl

@[simp]
theorem vecId_X_Comm_XX_Id_involutive (a b c d : ℕ) :
  (vecId_X_Comm_XX_Id a c b d) ∘ (vecId_X_Comm_XX_Id (F := F) a b c d) = id := by
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- MIXED THEOREMS

@[simp]
theorem vecPentagonIdentity (a b c d : ℕ) :
  (vecAssoc_X_Id_Inv a b c d)
    ∘ (vecAssoc_Inv a (b + c) d)
    ∘ (vecId_X_Assoc_Inv a b c d)
  =
  (vecAssoc_Inv (a + b) c d)
    ∘ (vecAssoc_Inv (F := F) a b (c + d))
  := by
  rfl

@[simp]
theorem vecComm_vecZeroAddInv_is_vecAddZeroInv (n : ℕ) :
  (vecComm 0 n) ∘ (vecZeroAdd_Inv n) = vecAddZero_Inv (F := F) n := by
  rfl

@[simp]
theorem vecComm_X_Id_finAssocInv_is_finAssocInv_finComm_X_Id_Id
  (a b c d : ℕ) :
  (vecAssoc_Inv (b + a) c d)
    ∘ (vecComm_X_Id a b (c + d))
  =
  (vecComm_X_Id_X_Id a b c d)
    ∘ (vecAssoc_Inv (F := F) (a + b) c d)
  := by
  rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- Splitting THEOREMS

@[simp]
theorem vecDesum_Inv_vecDesum_is_id (n a b : ℕ) (h : n = a + b) :
    (vecDesum_Inv (F := F) (n := n) (a := a) (b := b) h) ∘
      (vecDesum (F := F) (n := n) (a := a) (b := b) h)
    = id
  := by
  rfl

@[simp]
theorem vecDesum_vecDesum_Inv_is_id (n a b : ℕ) (h : n = a + b) :
    (vecDesum (F := F) (n := n) (a := a) (b := b) h) ∘
      (vecDesum_Inv (F := F) (n := n) (a := a) (b := b) h)
    = id
  := by
  rfl

@[simp] theorem vecSumSplit_Inv_vecSumSplit_is_id (a b : ℕ) :
    (vecSumSplit_Inv (F := F) a b) ∘ (vecSumSplit (F := F) a b) = id
  := by
  funext w
  funext s
  cases s with
  | inl i => rfl
  | inr j => rfl

@[simp] theorem vecSumSplit_vecSumSplit_Inv_is_id (a b : ℕ) :
    (vecSumSplit (F := F) a b) ∘ (vecSumSplit_Inv (F := F) a b) = id
  := by
  funext p
  cases p with
  | mk va vb =>
    apply Prod.ext <;> funext i <;> rfl

@[simp]
theorem vecToVecSum_Inv_vecToVecSum_is_id (a b : ℕ) :
    (vecToVecSum_Inv (F := F) a b) ∘ (vecToVecSum (F := F) a b) = id
  := by
  funext v
  unfold vecToVecSum_Inv vecToVecSum
  simp [Function.comp_assoc]

@[simp]
theorem vecToVecSum_vecToVecSum_Inv_is_id (a b : ℕ) :
    (vecToVecSum (F := F) a b) ∘ (vecToVecSum_Inv (F := F) a b) = id := by
  funext v
  unfold vecToVecSum_Inv vecToVecSum
  simp [Function.comp_assoc]

@[simp]
theorem vecId_X_vecSumSplit_Inv_vecId_X_vecSumSplit_Inv_Inv_is_id
(a b c : ℕ) :
  (vecId_X_vecSumSplit_Inv (F := F) a b c) ∘
    (vecId_X_vecSumSplit_Inv_Inv (F := F) a b c) = id
  := by
  unfold vecId_X_vecSumSplit_Inv vecId_X_vecSumSplit_Inv_Inv
  funext w
  simp [Function.comp, Prod.map]
  have h0 : vecSumSplit_Inv b c (vecSumSplit b c w.2) = w.2
    := by
    exact congrArg
      (fun f => f w.2)
      (vecSumSplit_Inv_vecSumSplit_is_id b c)
  rw [h0]

@[simp]
theorem vecId_X_vecSumSplit_Inv_Inv_vecId_X_vecSumSplit_Inv_is_id
(a b c : ℕ) :
  (vecId_X_vecSumSplit_Inv_Inv (F := F) a b c) ∘
    (vecId_X_vecSumSplit_Inv (F := F) a b c) = id
  := by
  unfold vecId_X_vecSumSplit_Inv vecId_X_vecSumSplit_Inv_Inv
  funext w
  simp [Function.comp, Prod.map]
  have h0 : vecSumSplit b c (vecSumSplit_Inv b c w.2) = w.2
    := by
    exact congrArg
      (fun f => f w.2)
      (vecSumSplit_vecSumSplit_Inv_is_id b c)
  rw [h0]

@[simp]
theorem vecSumSplit_Inv_X_Id_vecSumSplit_Inv_X_Id_Inv_is_id
  (a b c : ℕ) :
    (vecSumSplit_Inv_X_Id (F := F) a b c) ∘
      (vecSumSplit_Inv_X_Id_Inv (F := F) a b c)
    = id := by
  unfold vecSumSplit_Inv_X_Id vecSumSplit_Inv_X_Id_Inv
  funext w
  simp [Function.comp, Prod.map]
  -- remaining goal is the vecSum part
  have h0 : vecSumSplit_Inv a b (vecSumSplit a b w.1) = w.1 := by
    exact congrArg (fun f => f w.1) (vecSumSplit_Inv_vecSumSplit_is_id a b)
  simp [h0]

@[simp]
theorem vecSumSplit_Inv_X_Id_Inv_vecSumSplit_Inv_X_Id_is_id
  (a b c : ℕ) :
    (vecSumSplit_Inv_X_Id_Inv (F := F) a b c) ∘
      (vecSumSplit_Inv_X_Id (F := F) a b c)
    = id := by
  unfold vecSumSplit_Inv_X_Id vecSumSplit_Inv_X_Id_Inv
  funext w
  simp [Function.comp, Prod.map]
  -- remaining goal is the vecSum part
  have h0 : vecSumSplit a b (vecSumSplit_Inv a b w.1) = w.1
  := by
    exact congrArg (fun f => f w.1) (vecSumSplit_vecSumSplit_Inv_is_id a b)
  simp [h0]

@[simp]
theorem vecId_X_ToVecSum_Inv_vecId_X_ToVecSum_Inv_Inv_is_id
(a b c : ℕ) :
  (vecId_X_ToVecSum_Inv (F := F) a b c ) ∘
    (vecId_X_ToVecSum_Inv_Inv (F := F) a b c) = id
  := by
  unfold vecId_X_ToVecSum_Inv vecId_X_ToVecSum_Inv_Inv
  funext w
  simp [Function.comp, Prod.map]
  have h0 : vecToVecSum_Inv b c (vecToVecSum b c w.2) = w.2
  := by
    exact congrArg (fun f => f w.2) (vecToVecSum_Inv_vecToVecSum_is_id b c)
  simp [h0]

@[simp]
theorem vecId_X_ToVecSum_Inv_Inv_vecId_X_ToVecSum_Inv_is_id
(a b c : ℕ) :
  (vecId_X_ToVecSum_Inv_Inv (F := F) a b c ) ∘
    (vecId_X_ToVecSum_Inv (F := F) a b c) = id
  := by
  unfold vecId_X_ToVecSum_Inv vecId_X_ToVecSum_Inv_Inv
  funext w
  simp [Function.comp, Prod.map]
  have h0 : vecToVecSum b c (vecToVecSum_Inv b c w.2) = w.2
    := by
    exact congrArg (fun f => f w.2) (vecToVecSum_vecToVecSum_Inv_is_id b c)
  simp [h0]

@[simp]
theorem vecToVecSum_Inv_X_Id_vecToVecSum_Inv_X_Id_Inv_is_id
(a b c : ℕ) :
  (vecToVecSum_Inv_X_Id (F := F) a b c) ∘
    (vecToVecSum_Inv_X_Id_Inv (F := F) a b c) = id
  := by
  unfold vecToVecSum_Inv_X_Id vecToVecSum_Inv_X_Id_Inv
  funext w
  simp [Function.comp, Prod.map]
  have h0 : vecToVecSum_Inv a b (vecToVecSum a b w.1) = w.1
    := by
    exact congrArg (fun f => f w.1) (vecToVecSum_Inv_vecToVecSum_is_id a b)
  simp [h0]

@[simp]
theorem vecToVecSum_Inv_X_Id_Inv_vecToVecSum_Inv_X_Id_is_id
(a b c : ℕ) :
  (vecToVecSum_Inv_X_Id_Inv (F := F) a b c) ∘
    (vecToVecSum_Inv_X_Id (F := F) a b c) = id
  := by
  unfold vecToVecSum_Inv_X_Id vecToVecSum_Inv_X_Id_Inv
  funext w
  simp [Function.comp, Prod.map]
  have h0 : vecToVecSum a b (vecToVecSum_Inv a b w.1) = w.1
    := by
    exact congrArg (fun f => f w.1) (vecToVecSum_vecToVecSum_Inv_is_id a b)
  simp [h0]

@[simp]
theorem vecId_X_App_vecId_X_App_Inv_is_id
(a b c : ℕ) :
  (vecId_X_App (F := F) a b c) ∘ (vecId_X_App_Inv (F := F) a b c) = id
  := by
  unfold vecId_X_App vecId_X_App_Inv
  rw [Function.comp_assoc]
  nth_rewrite 2 [← Function.comp_assoc]
  simp

@[simp]
theorem vecId_X_App_Inv_vecId_X_App_is_id
  (a b c : ℕ) :
  (vecId_X_App_Inv (F := F) a b c) ∘ (vecId_X_App (F := F) a b c) = id
  := by
  unfold vecId_X_App vecId_X_App_Inv
  rw [Function.comp_assoc]
  nth_rewrite 2 [← Function.comp_assoc]
  simp

@[simp]
theorem vecApp_X_Id_vecApp_X_Id_Inv_is_id
(a b c : ℕ) :
  (vecApp_X_Id (F := F) a b c) ∘ (vecApp_X_Id_Inv (F := F) a b c) = id
  := by
  unfold vecApp_X_Id vecApp_X_Id_Inv
  rw [Function.comp_assoc]
  nth_rewrite 2 [← Function.comp_assoc]
  simp

@[simp]
theorem vecApp_X_Id_Inv_vecApp_X_Id_is_id
(a b c : ℕ) :
  (vecApp_X_Id_Inv (F := F) a b c) ∘ (vecApp_X_Id (F := F) a b c) = id
  := by
  unfold vecApp_X_Id vecApp_X_Id_Inv
  rw [Function.comp_assoc]
  nth_rewrite 2 [← Function.comp_assoc]
  simp


@[simp]
theorem vecSplit_vecSplit_Inv_is_id (a b : ℕ) :
  (vecSplit (F := F) a b) ∘ (vecSplit_Inv (F := F) a b) = id
  := by
  unfold vecSplit vecSplit_Inv
  rw [Function.comp_assoc]
  nth_rewrite 2 [← Function.comp_assoc]
  simp

@[simp]
theorem vecSplit_Inv_vecSplit_is_id (a b : ℕ) :
  (vecSplit_Inv (F := F) a b) ∘ (vecSplit (F := F) a b) = id
  := by
  unfold vecSplit vecSplit_Inv
  rw [Function.comp_assoc]
  nth_rewrite 2 [← Function.comp_assoc]
  simp


@[simp] lemma vecSumSplit_Inv_apply (a b : ℕ) (va : vec F a) (vb : vec F b) (s : Fin a ⊕ Fin b) :
    (vecSumSplit_Inv (F := F) a b (va, vb)) s = Sum.elim va vb s := by
  rfl

@[simp] lemma vecToVecSum_Inv_apply (a b : ℕ) (f : vecSum F a b) (i : Fin (a + b)) :
    (vecToVecSum_Inv (F := F) a b f) i = f (finAddToFinSum a b i) := by
  rfl

@[simp] lemma vecSplit_Inv_apply (a b : ℕ) (va : vec F a) (vb : vec F b) (i : Fin (a + b)) :
    (vecSplit_Inv (F := F) a b (va, vb)) i
      = Sum.elim va vb (finAddToFinSum a b i) := by
  rfl

@[simp] lemma vecSplit_Inv_castAdd (a b : ℕ) (va : vec F a) (vb : vec F b) (i : Fin a) :
    (vecSplit_Inv (F := F) a b (va, vb)) (Fin.castAdd b i) = va i := by
  -- unfold to Sum.elim ... (finAddToFinSum ...)
  simp [vecSplit_Inv_apply, finAddToFinSum]

@[simp] lemma vecSplit_Inv_natAdd (a b : ℕ) (va : vec F a) (vb : vec F b) (j : Fin b) :
    (vecSplit_Inv (F := F) a b (va, vb)) (Fin.natAdd a j) = vb j := by
  simp [vecSplit_Inv_apply, finAddToFinSum]


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
Naturality of vecSumToVec w.r.t. casts:

        vecSumCast a1 b1 a2 b2 ha hb
vec F (Fin a1 ⊕ Fin b1)  ----▶  vec F (Fin a2 ⊕ Fin b2)
        |                                   |
        | vecSumToVec a1 b1                 | vecSumToVec a2 b2
        ▼                                   ▼
vec F (a1 + b1)  ----▶  vec F (a2 + b2)
      vecCast (a1+b1) (a2+b2) (by rw [ha, hb])

Commutativity:
  vecSumToVec ∘ vecSumCast
    =
  vecCast ∘ vecSumToVec
-/
@[simp]
theorem vecSumToVec_vecSumCast_is_vecCast_vecSumCast
  (a1 b1 a2 b2 : ℕ) (ha : a1 = a2) (hb : b1 = b2) :
    (vecToVecSum_Inv (F := F) a2 b2) ∘ (vecSumCast (F := F) a1 b1 a2 b2 ha hb)
      =
    (vecCast (F := F) (a1 + b1) (a2 + b2) (by rw [ha, hb])) ∘ (vecToVecSum_Inv (F := F) a1 b1)
  := by
  unfold vecToVecSum_Inv
  unfold vecSumCast
  unfold vecCast
  funext v i
  simp [Function.comp]
  simpa [Function.comp] using congrArg (fun f => v (f i))
    (finSumCast_finAddToFinSum_is_finAddToFinSum_finCast
      (a1 := a2) (b1 := b2) (a2 := a1) (b2 := b1) ha.symm hb.symm)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
Naturality of vecSumSplit_Inv w.r.t. casts (for ⊕-indexed vectors):

        Prod.map (vecCast a1 a2 ha) (vecCast b1 b2 hb)
(vec F a1 × vec F b1)  ----▶  (vec F a2 × vec F b2)
        |                                |
        | vecSumSplit_Inv a1 b1          | vecSumSplit_Inv a2 b2
        ▼                                ▼
vec F (Fin a1 ⊕ Fin b1)  ----▶  vec F (Fin a2 ⊕ Fin b2)
                vecSumCast a1 b1 a2 b2 ha hb

Commutativity:
  vecSumCast ∘ vecSumSplit_Inv
    =
  vecSumSplit_Inv ∘ Prod.map (vecCast ...) (vecCast ...)
-/
@[simp]
theorem vecSumCast_vecSumSplit_Inv_is_vecSumSplit_Inv_vecCast_X_vecCast
  (a1 b1 a2 b2 : ℕ) (ha : a1 = a2) (hb : b1 = b2) :
    (vecSumCast (F := F) a1 b1 a2 b2 ha hb) ∘ (vecSumSplit_Inv (F := F) a1 b1)
      =
    (vecSumSplit_Inv (F := F) a2 b2) ∘
      (Prod.map
        (vecCast (F := F) a1 a2 ha)
        (vecCast (F := F) b1 b2 hb) )
  := by
  funext x s
  cases x with
  | mk va vb =>
    -- now s : Fin a2 ⊕ Fin b2
    cases s with
    | inl ia2 =>
        -- both sides should be va transported along ha, evaluated at ia2
        cases ha
        -- after cases ha, ia2 : Fin a1 and vecCast is identity-on-terms
        simp [vecSumCast, vecSumSplit_Inv, vecCast, finSumCast, Function.comp]
    | inr ib2 =>
        cases hb
        simp [vecSumCast, vecSumSplit_Inv, vecCast, finSumCast, Function.comp]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
Naturality of vecSplit_Inv w.r.t. casts:

        Prod.map (vecCast a1 a2 ha) (vecCast b1 b2 hb)
(vec F a1 × vec F b1)  ----▶  (vec F a2 × vec F b2)
        |                                |
        | vecSplit_Inv a1 b1             | vecSplit_Inv a2 b2
        ▼                                ▼
vec F (a1 + b1)  ----▶  vec F (a2 + b2)
      vecCast (a1+b1) (a2+b2) (by rw [ha, hb])

Commutativity:
  vecCast ∘ vecSplit_Inv
    =
  vecSplit_Inv ∘ Prod.map (vecCast ...) (vecCast ...)
-/
@[simp]
theorem vecCast_vecSplit_Inv_is_vecSplit_Inv_vecCast_X_vecCast
  (a1 b1 a2 b2 : ℕ) (ha : a1 = a2) (hb : b1 = b2) :
    (vecCast (F := F) (a1 + b1) (a2 + b2) (by rw [ha, hb]))
      ∘ (vecSplit_Inv (F := F) a1 b1)
    =
    (vecSplit_Inv (F := F) a2 b2)
      ∘ (Prod.map
          (vecCast (F := F) a1 a2 ha)
          (vecCast (F := F) b1 b2 hb))
  := by
  -- expand vecSplit_Inv as vecSumToVec ∘ vecSumSplit_Inv
  unfold vecSplit_Inv
  -- reassociate so we can rewrite with your two simp-lemmas
  rw [Function.comp_assoc]
  rw [← vecSumCast_vecSumSplit_Inv_is_vecSumSplit_Inv_vecCast_X_vecCast]
  rw [← Function.comp_assoc]
  rw [← vecSumToVec_vecSumCast_is_vecCast_vecSumCast]
  rw [← Function.comp_assoc]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- OTHER THEOREMS

/-
                        vecComm_P_Id
   F^(a+b) × F^c  ─────────────────────────────────▶  F^(b+a) × F^c
        │                                                │
        │ vecSplit_Inv (a+b) c                           │ vecSplit_Inv (b+a) c
        ▼                                                ▼
      F^((a+b)+c)  ─────── vecComm_X_Id ───────────▶  F^((b+a)+c)
-/
@[simp]
theorem vecSplit_Inv_vecComm_P_Id_is_vecComm_X_Id_vecSplit_Inv (a b c : ℕ) :
    (vecSplit_Inv (F := F) (b + a) c) ∘ (vecComm_P_Id (F := F) a b c)
    =
    (vecComm_X_Id (F := F) a b c) ∘ (vecSplit_Inv (F := F) (a + b) c)
  := by
  unfold vecSplit_Inv
  unfold vecSumSplit_Inv vecToVecSum_Inv
  unfold vecComm_X_Id vecComm_P_Id vecComm
  funext ⟨vab, vc⟩
  funext j
  simp [Function.comp]
  refine Fin.addCases (fun jba => ?_) (fun jc => ?_) j
  · -- j = in the (b+a)-block
    simp [finAddToFinSum, finComm_X_Id, finComm,
      Function.comp, Fin.addCases, Fin.castAdd, Sum.elim, Fin.subNat, Fin.castLE]
    have hj : (↑jba : ℕ) < a + b
      := by
      simpa [Nat.add_comm] using jba.2
    simp [hj]
    rfl
  · -- j = in the c-block
    simp [finAddToFinSum, finComm_X_Id]


/-
                   vecId_P_CastToPrefixOneSuffix
   F^a × F^b  ───────────────────────────────────────────▶  F^a × F^((i.1+1) + (b-(i.1+1)))
      │                                                         │
      │ vecSplit_Inv a b                                        │ vecSplit_Inv a ((i.1+1) + (b-(i.1+1)))
      ▼                                                         ▼
   F^(a+b)  ───────────────────────────────────────────────▶  F^(a + ((i.1+1) + (b-(i.1+1))))
                   vecId_X_CastToPrefixOneSuffix
-/
@[simp]
theorem vecSplit_Inv_vecId_P_CastToPrefixOneSuffix_is_vecId_X_CastToPrefixOneSuffix_vecSplit_Inv (a b : ℕ) (i : Fin b) :
  (vecSplit_Inv (F := F) a b)
    ∘ (vecId_P_CastToPrefixOneSuffix (F := F) a b i)
  =
  (vecId_X_CastToPrefixOneSuffix (F := F) a b i)
    ∘ (vecSplit_Inv (F := F) a ((i.1 + 1) + (b - (i.1 + 1))))
  := by
  unfold vecId_P_CastToPrefixOneSuffix
  unfold vecId_X_CastToPrefixOneSuffix
  unfold vecCastToPrefixOneSuffix
  unfold vecSplit_Inv
  unfold vecToVecSum_Inv
  unfold vecSumSplit_Inv
  funext ⟨va, vb⟩
  funext j
  simp [Function.comp]
    -- split j into the a-block / b-block
  refine Fin.addCases (fun ja => ?_) (fun jb => ?_) j
  · simp
      [finAddToFinSum, finId_X_CastToPrefixOneSuffix, finCastToPrefixOneSuffix,
          finCast, Function.comp, Sum.elim]
  · simp
      [finAddToFinSum, finId_X_CastToPrefixOneSuffix, finCastToPrefixOneSuffix,
          finCast, Function.comp, Sum.elim, Fin.addCases]
    simp [Fin.subNat, Fin.natAdd, Fin.cast]



@[simp]
theorem vecSumSplit_Inv_vecId_X_ToVecSum_Inv_is_vecSum3RToVecSum_vecSum3RSplitLeft_Inv
  (a b c : ℕ) :
  (vecSumSplit_Inv (F := F) a (b + c))
    ∘ (vecId_X_ToVecSum_Inv (F := F) a b c)
  =
  (vecSum3RToVecSum (F := F) a b c)
    ∘ (vecSum3RSplit_Inv a b c)
  := by
  unfold vecSumSplit_Inv
  unfold vecId_X_ToVecSum_Inv
  unfold vecSum3RToVecSum
  unfold vecSum3RSplit_Inv
  unfold vecToVecSum_Inv
  funext v
  simp
  funext i
  rcases i with i1 | i2
  rfl
  rfl

@[simp]
theorem vecSumSplit_Inv_vecSum3LSplitRight_Inv_is_vecSum3LToVecSum_vecSum3LSplitRight_Inv
  (a b c : ℕ) :
  (vecSumSplit_Inv (F := F) (a + b) c)
    ∘ (vecToVecSum_Inv_X_Id (F := F) a b c)
  =
  (vecSum3LToVecSum a b c)
    ∘ (vecSum3LSplit_Inv (F := F) a b c)
  := by
  unfold vecSumSplit_Inv
  unfold vecToVecSum_Inv_X_Id
  unfold vecSum3LToVecSum
  unfold vecSum3LSplit_Inv
  unfold vecToVecSum_Inv
  funext v
  simp
  funext i
  rcases i with i1 | i2
  rfl
  rfl

@[simp]
theorem vecProdVecSum3Assoc
  (a b c : ℕ) :
  (vecSumAssoc_Inv (F := F) a b c)
    ∘ (vecSum3RSplit_Inv (F := F) a b c)
    ∘ (vecId_X_vecSumSplit_Inv (F := F) a b c)
  =
  (vecSum3LSplit_Inv (F := F) a b c)
  ∘ (vecSumSplit_Inv_X_Id (F := F) a b c)
  ∘ (vecProdAssoc_Inv (F := F) a b c)
  := by
  unfold vecSumAssoc_Inv
  unfold vecSum3RSplit_Inv
  unfold vecId_X_vecSumSplit_Inv
  unfold vecSum3LSplit_Inv
  unfold vecSumSplit_Inv_X_Id
  unfold vecProdAssoc_Inv
  unfold vecSumSplit_Inv
  funext ⟨va, vb, vc⟩
  -- simp
  funext i
  simp [finSumAssoc]
  rcases i with (i1 | i2) | i3
  rfl
  rfl
  rfl

@[simp]
theorem vecSumVecFinAssoc
  (a b c : ℕ) :
  (vecAssoc_Inv (F := F) a b c)
  ∘ (vecToVecSum_Inv (F := F) a (b + c))
  ∘ (vecSum3RToVecSum (F := F) a b c)
  =
  (vecToVecSum_Inv (F := F) (a + b) c)
  ∘ (vecSum3LToVecSum (F := F) a b c)
  ∘ (vecSumAssoc_Inv (F := F) a b c)
  := by
  unfold vecAssoc_Inv
  unfold vecToVecSum_Inv
  unfold vecSum3RToVecSum
  unfold vecSum3LToVecSum
  unfold vecSumAssoc_Inv
  funext v
  simp
  repeat rw [Function.comp_assoc]
  rw [finHexagon]



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                   vecRightSubtr_Inv
   F^(a - b)  ───────────────────────────────────▶  F^(a + c - (b + c))
      │                                                │
      │ id                                             │ vecRightSubtr
      ▼                                                ▼
   F^(a - b)  ───────────────────────────────────▶  F^(a - b)
                        id
-/
@[simp]
theorem vecRightSubtr_vecRightSubtr_Inv_is_id (a b c : ℕ) :
  (vecRightSubtr (F := F) a b c) ∘ (vecRightSubtr_Inv (F := F) a b c) = id := by
  rfl


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                    vecRightSubtr
   F^(a + c - (b + c))  ───────────────────────▶  F^(a - b)
            │                                       │
            │ id                                    │ vecRightSubtr_Inv
            ▼                                       ▼
   F^(a + c - (b + c))  ───────────────────────▶  F^(a + c - (b + c))
                           id
-/
@[simp]
theorem vecRightSubtr_Inv_vecRightSubtr_is_id (a b c : ℕ) :
  (vecRightSubtr_Inv (F := F) a b c) ∘ (vecRightSubtr (F := F) a b c) = id := by
  rfl



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^(a + (b + (c - d)))  ─── vecId_XX_Id_RightSubtr_Inv ───▶  F^(a + (b + ((c + e) - (d + e))))
-/
def vecId_XX_Id_RightSubtr_Inv (a b c d e : ℕ) :
    vec F (a + (b + (c - d))) → vec F (a + (b + ((c + e) - (d + e)))) :=
  (· ∘ finId_XX_Id_RightSubtr a b c d e)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
   F^(a + (b - c))  ─── vecId_X_RightSubtr_Inv ───▶  F^(a + ((b + d) - (c + d)))
-/
def vecId_X_RightSubtr_Inv (a b c d : ℕ) :
    vec F (a + (b - c)) → vec F (a + ((b + d) - (c + d))) :=
  (· ∘ finId_X_RightSubtr a b c d)



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                           vecAssoc_Inv
   F^(a + (b + (c - d)))  ───────────────────────────────▶  F^((a+b) + (c - d))
            │                                                     │
            │ vecId_XX_Id_RightSubtr_Inv                           │ vecId_X_RightSubtr_Inv
            ▼                                                     ▼
   F^(a + (b + ((c+e) - (d+e))))  ─────────────────────────▶  F^((a+b) + ((c+e) - (d+e)))
                           vecAssoc_Inv
-/
@[simp]
theorem vecId_X_RightSubtr_Inv_vecAssoc_Inv_is_vecAssoc_Inv_vecId_XX_Id_RightSubtr_Inv
(a b c d e : ℕ) :
  (vecId_X_RightSubtr_Inv (F := F) (a + b) c d e)
    ∘ (vecAssoc_Inv (F := F) a b (c - d))
  =
  (vecAssoc_Inv (F := F) a b ((c + e) - (d + e)))
    ∘ (vecId_XX_Id_RightSubtr_Inv (F := F) a b c d e)
  := by
  rfl



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                     Prod.map id (vecId_X_RightSubtr_Inv b c d e)
   F^a × F^(b + (c - d))  ─────────────────────────────────────────▶  F^a × F^(b + ((c+e) - (d+e)))
           │                                                                │
           │ vecSplit_Inv a (b + (c - d))                     vecSplit_Inv a (b + ((c+e) - (d+e)))
           ▼                                                                ▼
     F^(a + (b + (c - d)))  ─────────────────────────────────────────▶  F^(a + (b + ((c+e) - (d+e))))
                          vecId_XX_Id_RightSubtr_Inv a b c d e
-/
@[simp]
theorem vecSplit_Inv_Id_XX_Id_RightSubtr_Inv_commute
(a b c d e : ℕ) :
  (vecSplit_Inv (F := F) a (b + ((c + e) - (d + e))))
    ∘ (Prod.map id (vecId_X_RightSubtr_Inv (F := F) b c d e))
  =
  (vecId_XX_Id_RightSubtr_Inv (F := F) a b c d e)
    ∘ (vecSplit_Inv (F := F) a (b + (c - d)))
  := by
  unfold vecId_X_RightSubtr_Inv
  unfold vecId_XX_Id_RightSubtr_Inv
  unfold vecSplit_Inv vecToVecSum_Inv vecSumSplit_Inv
  unfold finId_XX_Id_RightSubtr finId_X_RightSubtr finAddToFinSum
  funext ⟨x, y⟩
  simp [Function.comp]
  funext i
  refine Fin.addCases (fun ia => ?_) (fun jb => ?_) i
  ·
    simp [Function.comp]
  ·
    simp [Function.comp, Fin.addCases]
    apply congrArg y
    apply Fin.ext
    simp

@[simp]
theorem vecSplit_Inv_vecRightSubtr_Inv_commute
(a b c d : ℕ) :
  (vecSplit_Inv (F := F) a ((b + d) - (c + d)))
    ∘ (Prod.map id (vecRightSubtr_Inv (F := F) b c d))
  =
  (vecId_X_RightSubtr_Inv (F := F) a b c d)
    ∘ (vecSplit_Inv (F := F) a (b - c))
  := by
  unfold vecId_X_RightSubtr_Inv vecRightSubtr_Inv
  unfold vecSplit_Inv vecToVecSum_Inv vecSumSplit_Inv
  unfold finAddToFinSum finRightSubtr finId_X_RightSubtr
  funext ⟨x, y⟩
  simp [Function.comp]
  funext i
  refine Fin.addCases (fun ia => ?_) (fun jb => ?_) i
  ·
    simp [Function.comp]
  ·
    simp [Function.comp, Fin.addCases]
    apply congrArg y
    apply Fin.ext
    simp


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                     vecSumId_X_RightCancell_Inv
   F^a ⊕ F^b  ─────────────────────────────────────────▶  F^a ⊕ F^(b + a - a)
      │                                                     │
      │ vecToVecSum_Inv a b                                 │ vecToVecSum_Inv a (b + a - a)
      ▼                                                     ▼
   F^(a + b)  ─────────── vecId_X_RightCancell_Inv ─────────▶  F^(a + (b + a - a))
-/
@[simp]
theorem vecToVecSum_Inv_vecSumId_X_RightCancell_Inv_is_vecId_X_RightCancell_Inv_vecToVecSum_Inv
(a b : ℕ) :
  (vecToVecSum_Inv (F:= F) a (b + a - a)) ∘ (vecSumId_X_RightCancell_Inv (F:= F) a b)
    =
  (vecId_X_RightCancell_Inv (F:= F) a b) ∘ (vecToVecSum_Inv (F:= F) a b)
  := by
  unfold vecId_X_RightCancell_Inv
  unfold vecToVecSum_Inv
  unfold vecSumId_X_RightCancell_Inv
  funext v
  simp [Function.comp_assoc]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                     vecProdRightCancell_Inv
   F^a × F^b  ───────────────────────────────────────▶  F^a × F^(b + a - a)
      │                                                   │
      │ vecSumSplit_Inv a b                                │ vecSumSplit_Inv a (b + a - a)
      ▼                                                   ▼
   F^a ⊕ F^b  ───────── vecSumId_X_RightCancell_Inv ───────▶  F^a ⊕ F^(b + a - a)
-/
@[simp]
theorem vecSumSplit_Inv_vecProdRightCancell_Inv_is_vecSumId_X_RightCancell_Inv_vecSumSplit_Inv
(a b : ℕ) :
  (vecSumSplit_Inv (F:= F) a (b + a - a)) ∘ (vecProdRightCancell_Inv (F := F) a b)
  =
  (vecSumId_X_RightCancell_Inv (F:= F) a b) ∘ (vecSumSplit_Inv (F:= F) a b)
  := by
  unfold vecSumId_X_RightCancell_Inv
  unfold vecSumSplit_Inv
  unfold vecProdRightCancell_Inv
  unfold vecRightCancell_Inv
  funext ⟨va, vb⟩
  simp [Function.comp]
  funext i
  rcases i with ia | ib
  · -- ia : Fin a
    rfl
  · -- ib : Fin b
    rfl

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                     vecProdRightCancell_Inv
   F^a × F^b  ───────────────────────────────────────▶  F^a × F^(b + a - a)
      │                                                   │
      │ vecSplit_Inv a b                                   │ vecSplit_Inv a (b + a - a)
      ▼                                                   ▼
   F^(a + b)  ─────────── vecId_X_RightCancell_Inv ───────▶  F^(a + (b + a - a))
-/
@[simp]
theorem vecSplit_Inv_vecProdRightCancell_Inv_is_vecId_X_RightCancell_Inv_vecSplit_Inv
(a b : ℕ) :
  (vecSplit_Inv (F:= F) a (b + a - a)) ∘ (vecProdRightCancell_Inv (F := F) a b)
  =
  (vecId_X_RightCancell_Inv (F:= F) a b) ∘ (vecSplit_Inv (F:= F) a b)
  := by
  unfold vecSplit_Inv
  rw [← Function.comp_assoc]
  rw [← vecToVecSum_Inv_vecSumId_X_RightCancell_Inv_is_vecId_X_RightCancell_Inv_vecToVecSum_Inv a b]
  rw [Function.comp_assoc, Function.comp_assoc]
  rw [← vecSumSplit_Inv_vecProdRightCancell_Inv_is_vecSumId_X_RightCancell_Inv_vecSumSplit_Inv a b]



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                       vecSumId_X_vecComm
   F^a ⊕ F^(b + c)  ─────────────────────────────────▶  F^a ⊕ F^(c + b)
        │                                                   │
        │ vecToVecSum_Inv a (b + c)                          │ vecToVecSum_Inv a (c + b)
        ▼                                                   ▼
   F^(a + (b + c))  ───────────── vecId_X_Comm ───────────▶  F^(a + (c + b))
-/
@[simp]
theorem vecToVecSum_Inv_vecSumId_X_vecComm_is_vecId_X_Comm_vecToVecSum_Inv (a b c : ℕ) :
  (vecToVecSum_Inv (F:= F) a (c + b)) ∘ (vecSumId_X_vecComm (F:= F) a b c)
  =
  (vecId_X_Comm (F:= F) a b c) ∘ (vecToVecSum_Inv (F:= F) a (b + c))
  := by
  unfold vecId_X_Comm
  unfold vecToVecSum_Inv
  unfold vecSumId_X_vecComm
  funext i
  simp [Function.comp, Function.comp_assoc]



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                       vecSumSplit_Inv a (b + c)
   F^a × F^(b + c)  ─────────────────────────────────────▶  F^a ⊕ F^(b + c)
        │                                                       │
        │ vecProdId_X_vecComm                                   │ vecSumId_X_vecComm
        ▼                                                       ▼
   F^a × F^(c + b)  ─────────────────────────────────────▶  F^a ⊕ F^(c + b)
                       vecSumSplit_Inv a (c + b)
-/
@[simp]
theorem vecSumId_X_vecComm_vecSumSplit_Inv_is_vecSumSplit_Inv_vecProdId_X_vecComm
  (a b c : ℕ) :
  (vecSumId_X_vecComm (F:= F) a b c) ∘ (vecSumSplit_Inv (F:= F) a (b + c))
  =
  (vecSumSplit_Inv (F:= F) a (c + b)) ∘ (vecProdId_X_vecComm (F:= F) a b c)
  := by
  unfold vecSumId_X_vecComm
  unfold vecSumSplit_Inv
  unfold vecProdId_X_vecComm
  unfold vecComm
  funext ⟨va, vbc⟩
  funext i
  simp [Function.comp]
  unfold Sum.elim
  rcases i with ia | ibc
  rfl
  rfl



-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/-
                        vecProdId_X_vecComm
   F^a × F^(b + c)  ─────────────────────────────────▶  F^a × F^(c + b)
        │                                                   │
        │ vecSplit_Inv a (b + c)                              │ vecSplit_Inv a (c + b)
        ▼                                                   ▼
   F^(a + (b + c))  ───────────── vecId_X_Comm ───────────▶  F^(a + (c + b))
-/
@[simp]
theorem vecSplit_Inv_vecProdId_X_vecComm_is_vecId_X_Comm_vecSplit_Inv
  (a b c : ℕ) :
  (vecSplit_Inv (F:= F) a (c + b)) ∘ (vecProdId_X_vecComm (F:= F) a b c)
  =
  (vecId_X_Comm (F:= F) a b c) ∘ (vecSplit_Inv (F:= F) a (b + c))
  := by
  unfold vecSplit_Inv
  rw [← Function.comp_assoc]
  rw [← vecToVecSum_Inv_vecSumId_X_vecComm_is_vecId_X_Comm_vecToVecSum_Inv]
  rw [Function.comp_assoc, Function.comp_assoc]
  rw [← vecSumId_X_vecComm_vecSumSplit_Inv_is_vecSumSplit_Inv_vecProdId_X_vecComm]



-- @[simp]
theorem vecAppHeadTail_commutation
  (a b c : ℕ) :
  (vecAssoc_Inv (F := F) a b c)
    ∘ (vecSplit_Inv (F := F) a (b + c))
    ∘ (vecId_X_App (F := F) a b c)
  =
  (vecSplit_Inv (F := F) (a + b) c)
    ∘ (vecApp_X_Id (F := F) a b c)
    ∘ (vecProdAssoc_Inv (F := F) a b c)
  := by
  unfold vecSplit_Inv
  unfold vecId_X_App
  unfold vecApp_X_Id
  rw [Function.comp_assoc]
  nth_rewrite 3 [← Function.comp_assoc]
  rw [vecSumSplit_Inv_vecId_X_ToVecSum_Inv_is_vecSum3RToVecSum_vecSum3RSplitLeft_Inv]
  nth_rewrite 2 [Function.comp_assoc]
  nth_rewrite 4 [← Function.comp_assoc]
  nth_rewrite 4 [← Function.comp_assoc]
  rw [vecSumSplit_Inv_vecSum3LSplitRight_Inv_is_vecSum3LToVecSum_vecSum3LSplitRight_Inv]
  nth_rewrite 3 [Function.comp_assoc]
  nth_rewrite 2 [Function.comp_assoc]
  nth_rewrite 2 [Function.comp_assoc]
  rw [← vecProdVecSum3Assoc]
  repeat' rw [← Function.comp_assoc]
  nth_rewrite 6 [Function.comp_assoc]
  rw [← vecSumVecFinAssoc]
  simp [Function.comp_assoc]

@[simp]
theorem vecApp_X_Id_is_vecSplit_Inv_P_id_pointwise
  (a b c : ℕ) (w : (vec F a × vec F b) × vec F c) :
  vecApp_X_Id (F := F) a b c w = ⟨(vecSplit_Inv (F := F) a b) w.1, w.2⟩
  := by
  unfold vecApp_X_Id vecSplit_Inv
  rfl


@[simp]
theorem vecTakeHeadConditional0_is_vecZero (n b : ℕ) (h : n = 0 + b) (r : vec F n) :
  vecTakeHeadConditional (F := F) n 0 b h r = vecZero (F := F)
  := by
  unfold vecTakeHeadConditional
  unfold vecZero
  unfold finEmbedHeadConditional
  unfold finEmbedHead
  unfold finCast
  unfold Function.comp
  funext i
  rcases i with ⟨j, hj⟩
  simp
  trivial


end NEO
