import Lean.Level
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Relation

open CategoryTheory

set_option autoImplicit false

------------------------------------BASIC DEFINITIONS-------------------------------

notation (priority := default) "Position" => Nat

def Nat.toType (P : Position) : Type := Fin P

instance : CoeSort Position Type where
  coe := Nat.toType

inductive Arity : Type where
  | mk : (dom : Position) → (dom.toType → Arity) → Arity

variable {n m : Nat}

@[reducible]
def A0 : Arity := Arity.mk 0 Fin.elim0

def Arity.dom : Arity → Position := fun ⟨X,_⟩ => X

def Arity.arity : (α : Arity) → (α.dom → Arity) := fun ⟨_,p⟩ => p

instance : CoeSort Arity Type where
  coe α := α.dom.toType

instance : CoeFun Arity (fun α => α → Arity) where
  coe := Arity.arity

def Arity.ext (u v : Arity) (e : u.dom = v.dom) :
    (∀ (x : u.dom), u.arity x = v.arity (Fin.cast e x)) → u = v := by
  intro h
  cases u with | mk dom_u f_u =>
  cases v with | mk dom_v f_v =>
  simp [Arity.dom, Arity.arity] at e h
  subst e
  have : f_u = f_v := by
    funext x
    exact h x
  subst this
  rfl

@[reducible]
def concat_dom (α : Arity) (β : Arity) : Position :=
  α.dom + β.dom

def concat_arr (α : Arity) (β : Arity) : concat_dom α β → Arity := fun x => by
  unfold concat_dom Nat.toType at x
  if h : x < α.dom then exact α ⟨x , h⟩
  else
    let x' : Fin β.dom := by use x - α.dom ; omega
    exact β x'

@[reducible]
def concat (α : Arity) (β : Arity) : Arity :=
    .mk (concat_dom α β) (concat_arr α β)

notation (priority := default+1) γ:31 " ⊕ " δ:31 => concat γ δ


------------------ASSOCIATIVITY AND UNITALITY OF ARITY CONCATENATION--------------------

lemma Arity.unitR (α : Arity) : concat α A0 = α := by
  unfold concat A0 concat_dom concat_arr
  simp_all only [Fin.eta]
  induction α
  simp_all only [mk.injEq, heq_eq_eq]
  apply And.intro
  · rfl
  · simp!

lemma Arity.unitL (α : Arity) : concat A0 α = α := by
  apply Arity.ext
  intro x
  case e => simp!
  case a =>
    unfold concat A0
    simp!
    unfold concat_arr
    unfold Arity.dom concat A0 concat_dom Nat.toType at x
    simp! only at x
    simp! only
    split
    next h => simp! at h
    next h =>
      induction x
      simp!

lemma Arity.assoc (α β γ : Arity) : ((α ⊕ β) ⊕ γ) = (α ⊕ (β ⊕ γ)) := by
  apply Arity.ext
  intro x
  unfold concat_dom concat at x
  simp! at x
  unfold Nat.toType at x
  unfold concat_dom at x
  simp! at x
  case e =>
    unfold concat Arity.dom
    simp_all only
    unfold concat_dom
    unfold Arity.dom
    simp!
    omega
  case a =>
    unfold concat
    simp!
    unfold concat_arr
    simp!
    split_ifs with h k l m n
    · rfl
    · rfl
    · exfalso
      unfold concat_dom at h
      omega
    · exfalso
      unfold concat_dom at  h
      omega
    · exfalso
      unfold concat_dom at h
      omega
    · unfold concat_dom
      apply congrArg
      simp_all only [Fin.mk.injEq]
      simp_all only [not_lt]
      omega

notation (priority := default) "Shape" => Arity

@[reducible]
def V (γ : Shape) (α : Arity) : Type := { x : γ | γ x = α }

instance {γ : Shape} {α : Arity} : CoeOut (V γ α) γ where
  coe x := x.val

def Position.toList (P : Position) : List (Fin P) := List.finRange P

------------------------------A MEASURE ON ARITY----------------------------------------

def Arity.rank (α : Arity) : Nat :=
  let .mk X A := α
  match (List.map (λ x => Arity.rank (A x)) (Position.toList X)).maximum with
  | none   => 0
  | some n => n + 1

lemma Arity.TypeListMem (α : Arity) (x : α.dom.toType) : x ∈ Position.toList α.dom :=
  let .mk X A := α
  match X with
  | Nat.zero => Fin.elim0 x
  | Nat.succ n => by
    unfold Position.toList List.finRange
    aesop

lemma Arity.TypeListMem' {n m : Nat} (l : List Nat) (p : n ∈ l) (q : List.maximum l = some m) : n ≤ m :=
  (List.maximum_eq_coe_iff.1 q).2 n p

lemma Arity.subArityLe (α : Arity) (x : α) : (α x).rank < α.rank :=
  match α with
  | .mk X A =>
    match hmax : (List.map (λ x => (A x).rank) (Position.toList X)).maximum with
    | some n => by calc
      (A x).rank ≤
        (List.map (λ x => (A x).rank) (Position.toList X)).maximum.getD 0 := by
        rw [hmax]
        simp
        apply Arity.TypeListMem' (List.map (λ x => (A x).rank) (Position.toList X))
        . simp
          use x
          . simp
            apply Arity.TypeListMem
        . assumption
      _ = n := by aesop
      _ < n + 1 := by simp
      _ = (Arity.mk X A).rank := by unfold Arity.rank ; aesop
    | none => by
      have h_empty : (List.map (λ x => (A x).rank) (Position.toList X)) = [] :=
        List.maximum_eq_bot.mp hmax
      have mem : x ∈ (Position.toList X) := Arity.TypeListMem (Arity.mk X A) x
      have mem_mapped : (A x).rank ∈ List.map (λ x => (A x).rank) (Position.toList X) := by
        simp [mem]
        use x
      rw [h_empty] at mem_mapped
      simp at mem_mapped

--------------------------THE TYPE OF EXPRESSIONS-------------------------------------

inductive Expr : (σ γ : Shape) → (α : Arity) → Type where
  | sym (σ : Shape) γ α : (s : σ) → ((i : σ s) →  Expr σ γ (concat α (σ s i))) → Expr σ γ α
  | free σ (γ : Shape) α : (x : γ) → ((i : γ x) → Expr σ γ (concat α (γ x i))) → Expr σ γ α
  | bound σ γ (α : Arity) : (y : α) → ((i : α y) → Expr σ γ (concat α (α y i))) → Expr σ γ α

--------------------------A MEASURE ON EXPR-------------------------------------------

@[reducible]
def Expr.rank {σ δ : Shape} {α : Arity} (E : Expr σ δ α) : Nat :=
  match E with
  | .sym _ _ _ s e =>
    match (List.map (λ i => Expr.rank (e i)) (List.finRange ((σ s).dom))).maximum with
    | none => 0
    | some n => n + 1
  | .free _ _ _ x e =>
    match (List.map (λ i => Expr.rank (e i)) (List.finRange ((δ x).dom))).maximum with
    | none => 0
    | some n => n + 1
  | .bound _ _ _ y e =>
    match (List.map (λ i => Expr.rank (e i)) (List.finRange ((α y).dom))).maximum with
    | none => 0
    | some n => n + 1

def Expr.subExprLeSym {σ δ : Shape} {α : Arity}
  {s : σ} {e : (i : σ s) →  Expr σ δ (α ⊕ (σ s i))} :
    ∀ (i : σ s), (e i).rank < (Expr.sym σ δ α s e).rank := by
  intro i
  exact
  match hmax : (List.map (λ i => Expr.rank (e i)) (List.finRange ((σ s).dom))).maximum with
  | some n => by calc
    (e i).rank ≤
      (List.map (λ i => Expr.rank (e i)) (List.finRange ((σ s).dom))).maximum.getD 0 := by
      rw [hmax]
      simp
      apply Arity.TypeListMem' (List.map (λ i => Expr.rank (e i)) (List.finRange ((σ s).dom)))
      · simp
        use i
        · simp
          apply Arity.TypeListMem
      · assumption
    _ = n := by aesop
    _ < n + 1 := by simp
    _ = (sym σ δ α s e).rank := by unfold Expr.rank ; aesop
    | none => by
      let h_empty : List.map (λ i => Expr.rank (e i)) (List.finRange ((σ s).dom)) = [] := by
        apply List.maximum_eq_bot.mp
        exact hmax
      let mem : i ∈ List.finRange (σ s).dom := Arity.TypeListMem (σ s) i
      have mem_mapped : (e i).rank ∈ List.map (λ i => Expr.rank (e i)) (List.finRange ((σ s).dom)) := by
        simp [mem]
        use i
      rw [h_empty] at mem_mapped
      simp at mem_mapped

def Expr.subExprLeFree {σ δ : Shape} {α : Arity}
  {x : δ} {e : (i : δ x) →  Expr σ δ (concat α (δ x i))} :
    ∀ (i : δ x), (e i).rank < (Expr.free σ δ α x e).rank := by
  intro i
  exact
  match hmax : (List.map (λ i => Expr.rank (e i)) (List.finRange ((δ x).dom))).maximum with
  | some n => by calc
    (e i).rank ≤
      (List.map (λ i => Expr.rank (e i)) (List.finRange ((δ x).dom))).maximum.getD 0 := by
      rw [hmax]
      simp
      apply Arity.TypeListMem' (List.map (λ i => Expr.rank (e i)) (List.finRange ((δ x).dom)))
      · simp
        use i
        · simp
          apply Arity.TypeListMem
      · assumption
    _ = n := by aesop
    _ < n + 1 := by simp
    _ = (free σ δ α x e).rank := by unfold Expr.rank ; aesop
    | none => by
      let h_empty : List.map (λ i => Expr.rank (e i)) (List.finRange ((δ x).dom)) = [] := by
        apply List.maximum_eq_bot.mp
        exact hmax
      let mem : i ∈ List.finRange (δ x).dom := Arity.TypeListMem (δ x) i
      have mem_mapped : (e i).rank ∈ List.map (λ i => Expr.rank (e i)) (List.finRange ((δ x).dom)) := by
        simp [mem]
        use i
      rw [h_empty] at mem_mapped
      simp at mem_mapped

def Expr.subExprLeBound {σ δ : Shape} {α : Arity}
  {y : α} {e : (i : α y) →  Expr σ δ (concat α (α y i))} :
    ∀ (i : α y), (e i).rank < (Expr.bound σ δ α y e).rank := by
  intro i
  exact
  match hmax : (List.map (λ i => Expr.rank (e i)) (List.finRange ((α y).dom))).maximum with
  | some n => by calc
    (e i).rank ≤
      (List.map (λ i => Expr.rank (e i)) (List.finRange ((α y).dom))).maximum.getD 0 := by
      rw [hmax]
      simp
      apply Arity.TypeListMem' (List.map (λ i => Expr.rank (e i)) (List.finRange ((α y).dom)))
      · simp
        use i
        · simp
          apply Arity.TypeListMem
      · assumption
    _ = n := by aesop
    _ < n + 1 := by simp
    _ = (bound σ δ α y e).rank := by unfold Expr.rank ; aesop
    | none => by
      let h_empty : List.map (λ i => Expr.rank (e i)) (List.finRange ((α y).dom)) = [] := by
        apply List.maximum_eq_bot.mp
        exact hmax
      let mem : i ∈ List.finRange (α y).dom := Arity.TypeListMem (α y) i
      have mem_mapped : (e i).rank ∈ List.map (λ i => Expr.rank (e i)) (List.finRange ((α y).dom)) := by
        simp [mem]
        use i
      rw [h_empty] at mem_mapped
      simp at mem_mapped

----------------------UNITALITY LEMMAS FOR EXPR--------------------------------------------

def ExprUnitR {σ γ : Shape} {α : Arity} :
  Expr σ γ (concat α A0) → Expr σ γ α := fun x => by
  rw [← Arity.unitR α]
  exact x

def ExprUnitR' {σ γ : Shape} {α : Arity} :
  Expr σ γ α → Expr σ γ (concat α A0) := fun x => by
  rw [Arity.unitR α]
  exact x

def ExprUnitL {σ γ : Shape} {α : Arity} :
  Expr σ γ (A0 ⊕ α) → Expr σ γ α := fun x => by
  rw [← Arity.unitL α]
  exact x

def ExprUnitL' {σ γ : Shape} {α : Arity} :
  Expr σ γ α → Expr σ γ (A0 ⊕ α) := fun x => by
  rw [Arity.unitL α]
  exact x

------------------------------------UNIT OF THE MONAD----------------------------------



-----------------------------WEAKENING AND LIFTING OF ARITIES----------------------------------------

@[reducible]
def Arity.wkL {α β : Arity} : (x : α) → α ⊕ β := fun x =>
  Fin.castLE (by simp!) x

@[reducible]
def Arity.wkLEq {α β : Arity} : (x : α) → α x = (α ⊕ β) (Arity.wkL x) := fun x => by
  simp!
  unfold concat_arr
  simp!

@[reducible]
def Arity.wkR {α β : Arity} : (x : β) → α ⊕ β := fun x => by
  use x.val + α.dom
  simp!
  unfold concat_dom
  omega

@[reducible]
def Arity.wkREq {α β : Arity} : (x : β) → β x = (α ⊕ β) (Arity.wkR x) := fun x => by
  unfold Arity.wkR concat concat_arr
  simp!
  split_ifs with h
  · exfalso
    omega
  · simp!

@[reducible]
def Arity.liftL {α β : Arity} : (x : α ⊕ β) → (p : x.val < α.dom) → α := fun x p => by
  use x.val

@[reducible]
def Arity.liftLEq {α β : Arity} (x : α ⊕ β) (p : x.val < α.dom) :
  α (Arity.liftL x p) = (α ⊕ β) x := by
  unfold concat concat_arr
  simp!
  simp [p]

@[reducible]
def Arity.liftR {α β : Arity} : (x : α ⊕ β) → (p : ¬ x.val < α.dom) → β := fun x p => by
  unfold concat concat_dom Nat.toType at x
  simp! at x
  use x.val - α.dom
  let h := x.isLt
  calc
    ↑x - α.dom < α.dom + β.dom - α.dom := by
      refine Nat.sub_lt_sub_right ?_ h
      omega
    _ = β.dom := by simp

@[reducible]
def Arity.liftREq {α β : Arity} {x : α ⊕ β} {p : ¬ x.val < α.dom} :
  β (Arity.liftR x p) = (α ⊕ β) x := by
  unfold concat concat_arr
  simp!
  simp [p]

def foo {α β : Arity} (h : α = β) (x : α) : α x = β (by rw [h] at x ; exact x) := by aesop

---------------------------SHIFTING----------------------------------------------------

def Expr.shiftRightR {σ γ δ : Shape} {α : Arity} : Expr σ (γ ⊕ δ) α → Expr σ γ (δ ⊕ α) := fun E =>
  match E with
  | .sym _ _ _ s e => by
    apply Expr.sym σ γ (δ  ⊕ α) s
    intro i
    rw [Arity.assoc]
    exact Expr.shiftRightR (e i)
  | .free _ _ _ x e => by
    simp! at x
    unfold concat_dom Nat.toType at x
    if H : x.val < γ.dom then
      apply Expr.free σ γ (δ ⊕ α) (Arity.liftL x H)
      intro i
      rw [Arity.assoc]
      let i' : (γ ⊕ δ) x := by
        rw [Arity.liftLEq] at i
        exact i
      have h := Arity.liftLEq x H
      rw [foo h i]
      exact Expr.shiftRightR (e i')
    else
      apply Expr.bound σ γ (δ ⊕ α) (Arity.wkL (Arity.liftR x H))
      intro i
      let i' := by
        rw [← Arity.wkLEq] at i
        rw [Arity.liftREq] at i
        exact i
      rw [foo (Eq.symm (Arity.wkLEq (Arity.liftR x H))) i]
      rw [foo Arity.liftREq]
      rw [Arity.assoc]
      exact Expr.shiftRightR (e i')
  | .bound _ _ _ y e => by
    apply Expr.bound σ γ (δ ⊕ α) (Arity.wkR y)
    intro i
    let i' := by rw [← Arity.wkREq] at i ; exact i
    rw [foo (Eq.symm (Arity.wkREq y)) i]
    rw [Arity.assoc]
    exact Expr.shiftRightR (e i')

def Expr.shiftRightL {σ γ δ : Shape} {α : Arity} : Expr (σ ⊕ γ) δ α → Expr σ (γ ⊕ δ) α := fun E =>
  match E with
  | .sym _ _ _   s e =>
    if H : s.val < σ.dom then by
      apply Expr.sym σ (γ ⊕ δ) α (Arity.liftL s H)
      intro i
      let i' := by rw [Arity.liftLEq] at i ; exact i
      rw [foo (Arity.liftLEq s H)]
      exact Expr.shiftRightL (e i')
    else by
      apply Expr.free σ (γ ⊕ δ) α (Arity.wkL (Arity.liftR s H))
      intro i
      let i' := by
        rw [← Arity.wkLEq] at i
        rw [Arity.liftREq] at i
        exact i
      rw [foo (Eq.symm (Arity.wkLEq (Arity.liftR s H)))]
      rw [foo (Arity.liftREq)]
      exact Expr.shiftRightL (e i')
  | .free _ _ _  x e => by
    apply Expr.free σ (γ ⊕ δ) α (Arity.wkR x)
    intro i
    let i' := by rw [← Arity.wkREq] at i ; exact i
    rw [foo (Eq.symm (Arity.wkREq x))]
    exact Expr.shiftRightL (e i')
  | .bound _ _ _ y e => by
    apply Expr.bound σ (γ ⊕ δ) α y
    intro i
    exact Expr.shiftRightL (e i)

def Expr.shiftLeftR {σ γ : Shape} {α β : Arity} (E : Expr σ γ (α ⊕ β)) : Expr σ (γ ⊕ α) β :=
  match E with
  | .sym _ _ _ s e => by
    apply Expr.sym σ (γ ⊕ α) β
    intro i
    let ei := e i
    let cat := Expr.shiftLeftR (e i)
    let cat' := by rw [← Arity.assoc] at cat ; exact cat
    exact Expr.shiftRightR cat'
  | .free _ _ _ x e => by
    apply Expr.free σ (γ ⊕ α) β (Arity.wkL x)
    intro i
    let i' := by rw [← Arity.wkLEq] at i ; exact i
    let ei := e i'
    let cat := Expr.shiftLeftR (e i')
    let cat' := by rw [← Arity.assoc] at cat ; exact cat
    rw [foo (Eq.symm (Arity.wkLEq x))]
    exact Expr.shiftRightR cat'
  | .bound _ _ _ y e =>
    if H : y.val < α.dom then by
      apply Expr.free σ (γ ⊕ α) β (Arity.wkR (Arity.liftL y H))
      intro i
      let i' := by
        rw [← Arity.wkREq] at i
        rw [Arity.liftLEq] at i
        exact i
      let cat := Expr.shiftLeftR (e i')
      rw [← Arity.assoc] at cat
      rw [foo (Eq.symm (Arity.wkREq (Arity.liftL y H)))]
      rw [foo (Arity.liftLEq y H)]
      exact Expr.shiftRightR cat
    else by
      apply Expr.bound σ (γ ⊕ α) β (Arity.liftR y H)
      intro i
      let i' := by rw [Arity.liftREq] at i ; exact i
      let cat := Expr.shiftLeftR (e i')
      rw [← Arity.assoc] at cat
      rw [foo Arity.liftREq]
      exact Expr.shiftRightR cat
termination_by E.rank
decreasing_by
  · apply Expr.subExprLeSym
  · apply Expr.subExprLeFree
  · apply Expr.subExprLeBound
  · apply Expr.subExprLeBound

def Expr.shiftLeftL {σ δ γ : Shape} {α : Arity} : Expr σ (γ ⊕ δ) α → Expr (σ ⊕ γ) δ α := fun E =>
  match E with
  | .sym _ _ _ s e => by
    apply Expr.sym (σ ⊕ γ) δ α (Arity.wkL s)
    intro i
    let i' := by rw [← Arity.wkLEq] at i ; exact i
    rw [foo (Eq.symm (Arity.wkLEq s))]
    exact Expr.shiftLeftL (e i')
  | .free _ _ _ x e =>
    if H : x.val < γ.dom then by
      apply Expr.sym (σ ⊕ γ) δ α (Arity.wkR (Arity.liftL x H))
      intro i
      let i' := by
        rw [← Arity.wkREq] at i
        rw [Arity.liftLEq] at i
        exact i
      rw [foo (Eq.symm (Arity.wkREq (Arity.liftL x H)))]
      rw [foo (Arity.liftLEq x H)]
      exact Expr.shiftLeftL (e i')
    else by
      apply Expr.free (σ ⊕ γ) δ α (Arity.liftR x H)
      intro i
      let i' := by rw [Arity.liftREq] at i ; exact i
      rw [foo (Arity.liftREq)]
      exact Expr.shiftLeftL (e i')
  | .bound _ _ _ y e => by
    apply Expr.bound (σ ⊕ γ) δ α y
    intro i
    exact Expr.shiftLeftL (e i)

def I {σ δ : Shape} {α : Arity} : Expr σ δ α → Expr (σ ⊕ δ) α A0 := fun E =>
  Expr.shiftLeftL (Expr.shiftLeftR (ExprUnitR' E))

def J {σ δ : Shape} {α : Arity} : Expr (σ ⊕ δ) α A0 → Expr σ δ α := fun E =>
  ExprUnitR (Expr.shiftRightR (Expr.shiftRightL E))

def L {σ δ : Shape} {α β : Arity} : Expr σ δ (α ⊕ β) → Expr (σ ⊕ δ) α β := fun E =>
  Expr.shiftLeftL (Expr.shiftLeftR E)

-----------------------------LIFTING---------------------------------------------------

def lift (σ γ δ : Shape) (f : (α : Arity) → V γ α → Expr σ δ α)
  (α : Arity) (E : Expr σ γ α) : Expr σ δ α :=
  match E with
  | .sym _ _ _ s e => by
    apply Expr.sym _ _ _ s
    intro i
    exact lift σ γ δ f (α ⊕ σ s i) (e i)
  | .free _ _ _ x e => by
    let g : (β : Arity) → V (γ x) β → Expr (σ ⊕ δ) α β := by
      intro β i
      let this := L (lift σ γ δ f (α ⊕ (γ.arity x) i) (e i))
      obtain ⟨val, p⟩ := i
      rw [← p]
      exact this
    exact J (lift (σ ⊕ δ) (γ x) α g A0 (I (f (γ x) ⟨x , by simp⟩)))
  | .bound _ _ _ y e => by
    apply Expr.bound _ _ _ y
    intro i
    exact lift σ γ δ f (α ⊕ α y i) (e i)
termination_by (γ.rank, E.rank)
decreasing_by
  · apply Prod.Lex.right
    apply Expr.subExprLeSym
  · apply Prod.Lex.right
    apply Expr.subExprLeFree
  · apply Prod.Lex.right
    apply Expr.subExprLeFree
  · apply Prod.Lex.right
    apply Expr.subExprLeFree
  · apply Prod.Lex.left
    apply Arity.subArityLe
  · apply Prod.Lex.right
    apply Expr.subExprLeBound
