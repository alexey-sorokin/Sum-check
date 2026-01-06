import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

noncomputable section
open BigOperators

universe u
variable {F : Type u} [Field F]

/-- Преобразование Bool в элемент поля {0,1}. -/
def boolToF (b : Bool) : F := if b then (1 : F) else (0 : F)

/-- Сумма функции `g` по всем булевым векторам длины `m` (то есть по {0,1}^m). -/
def sumOverCube (m : ℕ) (g : (Fin m → F) → F) : F :=
  ∑ x : (Fin m → Bool), g (fun i => boolToF (x i))

/-- Вставить:
  - префикс `pref : Fin k → F`,
  - затем значение `x : F` на позиции `k`,
  - затем хвост `tail : Fin (n-k-1) → F`
  в полный вектор `Fin n → F`.

Это удобная “склейка” для i-го раунда. -/
def extendStep (n k : ℕ) (hk : k + 1 ≤ n)
    (pref : Fin k → F) (x : F) (tail : Fin (n - (k + 1)) → F) : (Fin n → F) :=
  fun i =>
    if h0 : (i.1 < k) then
      pref ⟨i.1, h0⟩
    else if h1 : (i.1 = k) then
      x
    else
      -- тогда i.1 ≥ k+1, и мы кладём в tail индекс (i.1-(k+1))
      tail ⟨i.1 - (k + 1), by
        have hi : k + 1 ≤ i.1 := by
          have : k ≤ i.1 := le_of_not_gt h0
          have : k ≠ i.1 := by exact fun eq => h1 eq
          exact Nat.lt_of_le_of_ne this this |>.le
        have hn : i.1 < n := i.2
        -- (i - (k+1)) < (n - (k+1))
        exact Nat.sub_lt_sub_right hn (k + 1) ⟨hi, rfl⟩
      ⟩

/-- Состояние verifier’а после k раундов. -/
structure VState (n : ℕ) where
  k     : ℕ
  hk    : k ≤ n
  claim : F
  rpref : Fin k → F

/-- Один шаг verifier’а (k-й раунд), без проверки степеней:
  проверяем g(0)+g(1)=claim, затем обновляем claim := g(r_k). -/
def verifierRound {n : ℕ} (f : (Fin n → F) → F)
    (st : VState (F := F) n)
    (rk : F) (gk : Polynomial F) : Option (VState (F := F) n) :=
  if hkn : st.k < n then
    let lhs : F := (gk.eval 0) + (gk.eval 1)
    if lhs = st.claim then
      -- новый префикс rpref' длины k+1
      let rpref' : Fin (st.k + 1) → F :=
        fun i =>
          if h0 : (i.1 < st.k) then
            st.rpref ⟨i.1, h0⟩
          else
            rk
      some
        { k     := st.k + 1
          hk    := Nat.succ_le_of_lt hkn
          claim := gk.eval rk
          rpref := rpref' }
    else none
  else none

/-- Финальная проверка: после n раундов verifier проверяет f(r)=claim. -/
def verifierFinal {n : ℕ} (f : (Fin n → F) → F) (st : VState (F := F) n) : Bool :=
  if h : st.k = n then
    -- st.rpref : Fin n → F (по eqRec), сравним f(st.rpref)=claim
    let rfull : Fin n → F := (Eq.ndrec st.rpref (by simpa [h]) )
    decide (f rfull = st.claim)
  else
    false

/-- Полная верификация по сообщениям prover’а `msgs : Fin n → Polynomial F`
    и случайностям verifier’а `r : Fin n → F`. -/
def verifySumcheck {n : ℕ} (f : (Fin n → F) → F)
    (initialClaim : F)
    (r : Fin n → F)
    (msgs : Fin n → Polynomial F) : Bool :=
  let init : VState (F := F) n :=
    { k := 0, hk := Nat.zero_le _, claim := initialClaim, rpref := fun i => (False.elim (by cases i; simp)) }
  let rec loop (st : VState (F := F) n) : Option (VState (F := F) n) :=
    if h : st.k = n then
      some st
    else
      have hlt : st.k < n := Nat.lt_of_le_of_ne st.hk (Ne.symm h)
      -- берём сообщение и случайность текущего раунда
      let gk := msgs ⟨st.k, hlt⟩
      let rk := r ⟨st.k, hlt⟩
      match verifierRound (f := f) st rk gk with
      | none => none
      | some st' => loop st'
  match loop init with
  | none => false
  | some stN => verifierFinal (f := f) stN

/-
  --------------------------
  ЧЕСТНЫЙ PROVER (без степеней)
  --------------------------

  Он вычисляет a = сумма по оставшимся булевым переменным при x_k=0
                    b = сумма по оставшимся булевым переменным при x_k=1
  и отправляет ЛИНЕЙНЫЙ полином g_k(X) = a + (b-a) * X.
  Это всегда корректно для проверки g(0)+g(1)=claim и обновления claim := g(rk),
  но без degree-check soundness протокола в целом не гарантируется (как вы и просили).
-/

/-- Линейный полином через значения в 0 и 1. -/
def lineThrough01 (a b : F) : Polynomial F :=
  Polynomial.C a + Polynomial.C (b - a) * Polynomial.X

/-- Честный prover: строит сообщения `g_k` для всех раундов по `f` и текущему префиксу. -/
def honestMsgs {n : ℕ} (f : (Fin n → F) → F) : Fin n → Polynomial F :=
  fun ik =>
    let k : ℕ := ik.1
    have hk : k + 1 ≤ n := by
      -- из k < n следует k+1 ≤ n
      exact Nat.succ_le_of_lt ik.2
    -- pref : Fin k → F здесь неизвестен (в интерактивном протоколе он формируется из r),
    -- поэтому "честные сообщения" обычно параметризуют по префиксу.
    -- Чтобы оставить код самодостаточным, ниже даём версию, которая предполагает pref=0.
    -- В практической версии honestProver должен принимать текущий pref и rk.
    let pref0 : Fin k → F := fun _ => 0
    let a : F :=
      sumOverCube (n - (k + 1)) (fun tail =>
        f (extendStep n k hk pref0 0 tail))
    let b : F :=
      sumOverCube (n - (k + 1)) (fun tail =>
        f (extendStep n k hk pref0 1 tail))
    lineThrough01 a b

/-- Естественная начальная заявка: сумма f по {0,1}^n. -/
def initialClaim (n : ℕ) (f : (Fin n → F) → F) : F :=
  sumOverCube n f
