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

lemma Arity.assoc (α β γ : Arity) : ((α ⊕ β) ⊕ γ) = (α ⊕ (β ⊕ γ)) := by sorry

notation (priority := default) "Shape" => Arity

@[reducible]
def V (γ : Shape) (α : Arity) : Type := { x : γ | γ x = α }

instance {γ : Shape} {α : Arity} : CoeOut (V γ α) γ where
  coe x := x.val

def Position.toList (P : Position) : List (Fin P) := List.finRange P

def Arity.rank (α : Arity) :=
  let .mk X A := α
  match (List.map (λ x => Arity.rank (A x)) (Position.toList X)).maximum with
  | none   => 0
  | some n => n + 1

lemma ArityTypeListMem (α : Arity) (x : α.dom.toType) : x ∈ Position.toList α.dom :=
  let .mk X A := α
  match X with
  | Nat.zero => Fin.elim0 x
  | Nat.succ n => by
    unfold Position.toList List.finRange
    aesop

lemma SizeSubArityLeAux {n m : Nat} (l : List Nat) (p : n ∈ l) (q : List.maximum l = some m) : n ≤ m :=
  (List.maximum_eq_coe_iff.1 q).2 n p

lemma SizeSubArityLe (α : Arity) (x : α) : (α x).rank < α.rank :=
  match α with
  | .mk X A =>
    match hmax : (List.map (λ x => (A x).rank) (Position.toList X)).maximum with
    | some n => by calc
      (A x).rank ≤
        (List.map (λ x => (A x).rank) (Position.toList X)).maximum.getD 0 := by
        rw [hmax]
        simp
        apply SizeSubArityLeAux (List.map (λ x => (A x).rank) (Position.toList X))
        . simp
          use x
          . simp
            apply ArityTypeListMem
        . assumption
      _ = n := by aesop
      _ < n + 1 := by simp
      _ = (Arity.mk X A).rank := by unfold Arity.rank ; aesop
    | none => by
      have h_empty : (List.map (λ x => (A x).rank) (Position.toList X)) = [] :=
        List.maximum_eq_bot.mp hmax
      have mem : x ∈ (Position.toList X) := ArityTypeListMem (Arity.mk X A) x
      have mem_mapped : (A x).rank ∈ List.map (λ x => (A x).rank) (Position.toList X) := by
        simp [mem]
        use x
      rw [h_empty] at mem_mapped
      simp at mem_mapped

inductive Expr : (σ γ : Shape) → (α : Arity) → Type where
  | sym (σ : Shape) γ α : (s : σ) → ((i : σ s) →  Expr σ γ (concat α (σ s i))) → Expr σ γ α
  | free σ (γ : Shape) α : (x : γ) → ((i : γ x) → Expr σ γ (concat α (γ x i))) → Expr σ γ α
  | bound σ γ (α : Arity) : (y : α) → ((i : α y) → Expr σ γ (concat α (α y i))) → Expr σ γ α

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

#check Fin.castAdd

#check Fin.castLE

-----------------------------WEAKENING AND LIFTING----------------------------------------

@[reducible]
def Arity.wkL {α β : Arity} : (x : α) → α ⊕ β := fun x =>
  Fin.castLE (by simp!) x

@[reducible]
def Arity.wkLEq {α β : Arity} : (x : α) → α x = (α ⊕ β) (Arity.wkL x) := fun x => by
  simp!
  unfold concat_arr
  simp!

def Arity.wkR {α β : Arity} : (x : β) → α ⊕ β := fun x =>
  Fin.castLE (by simp!) x

def Arity.wkREq {α β : Arity} : (x : β) → β x = (α ⊕ β) (Arity.wkR x) := fun x => by
  simp!
  unfold concat_arr
  simp!
  sorry

@[reducible]
def Arity.liftL {α β : Arity} : (x : α ⊕ β) → (p : x.val < α.dom) → α := fun x p => by
  use x.val

@[reducible]
def Arity.liftLTr {α β : Arity} (x : α ⊕ β) (p : x.val < α.dom) :
  α (Arity.liftL x p) = (α ⊕ β) x := by sorry
  -- intro i
  -- simp!
  -- unfold concat_arr
  -- simp_all only [↓reduceDIte]
  -- exact i


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
def Arity.liftRTr {α β : Arity} {x : α ⊕ β} {p : ¬ x.val < α.dom} :
  β (Arity.liftR x p) = (α ⊕ β) x := by sorry


  -- intro i
  -- simp!
  -- unfold concat_arr
  -- simp_all only [↓reduceDIte]
  -- exact i

-- lemma Arity.liftLTrEq {α β : Arity} {x : α ⊕ β} {p : x.val < α.dom} (i : α (Arity.liftL x p)) :
--   α (Arity.liftL x p) i = (α ⊕ β) x (Arity.liftLTr i) := by
--   simp!
--   unfold concat_arr Arity.liftL
--   simp_all only
--   simp!
--   sorry

-- lemma Arity.liftRTrEq {α β : Arity} {x : α ⊕ β} {p : ¬ x.val < α.dom} (i : β (Arity.liftR x p)) :
--   β (Arity.liftR x p) i = (α ⊕ β) x (Arity.liftRTr i) := by
--   sorry

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
        rw [Arity.liftLTr] at i
        exact i
      let ei := e i'
      let ei' := Expr.shiftRightR ei
      have h := Arity.liftLTr x H
      sorry
      -- exact Expr.shiftRightR (e i')
    else
      apply Expr.bound σ γ (δ ⊕ α) (Arity.wkL (Arity.liftR x H))
      sorry

def Expr.shiftRightL {σ γ δ : Shape} {α : Arity} : Expr (σ ⊕ γ) δ α → Expr σ (γ ⊕ δ) α := fun E => by sorry

def Expr.shiftLeftR {σ γ : Shape} {α β : Arity} : Expr σ γ (α ⊕ β) → Expr σ (γ ⊕ α) β := by sorry

def Expr.shiftLeftL {σ δ γ : Shape} {α : Arity} : Expr σ (γ ⊕ δ) α → Expr (σ ⊕ γ) δ α := by sorry

def I {σ δ : Shape} {α : Arity} : Expr σ δ α → Expr (σ ⊕ δ) α A0 := fun E =>
  Expr.shiftLeftL (Expr.shiftLeftR (ExprUnitR' E))

def J {σ δ : Shape} {α : Arity} : Expr (σ ⊕ δ) α A0 → Expr σ δ α := fun E =>
  ExprUnitR (Expr.shiftRightR (Expr.shiftRightL E))

def L {σ δ : Shape} {α β : Arity} : Expr σ δ (α ⊕ β) → Expr (σ ⊕ δ) α β := fun E =>
  Expr.shiftLeftL (Expr.shiftLeftR E)

def lift (σ γ δ : Shape) (f : (α : Arity) → V γ α → Expr σ δ α) :
  (α : Arity) → Expr σ γ α → Expr σ δ α := fun α E =>
  match E with
  | .sym _ _ _ s e => by
    apply Expr.sym _ _ _ s
    intro i
    exact lift σ γ δ f (α ⊕ σ s i) (e i)
  | .free _ _ _ x e => by
    let foo : Expr σ δ (γ x) := f (γ x) ⟨x , by simp ⟩
    let bar : Expr (σ ⊕ δ) (γ x) A0 := I foo
    let g : (β : Arity) → V (γ x) β → Expr (σ ⊕ δ) α β := by
      intro β i
      let ei' : Expr σ γ (α ⊕ β) := by
        obtain ⟨val, p⟩ := i
        subst p
        apply e
      let cat : Expr σ δ (α ⊕ β) := lift σ γ δ f (α ⊕ β) ei'
      exact L cat
    let owl := lift (σ ⊕ δ) (γ x) α g A0 bar
    exact J owl
  | .bound _ _ _ y e => by sorry
