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

notation (priority := default) "Shape" => Arity

inductive Expr : (σ γ : Shape) → (α : Arity) → Type where
  | sym (σ : Shape) γ α : (s : σ) → ((i : σ s) →  Expr σ γ (concat α (σ s i))) → Expr σ γ α
  | free σ (γ : Shape) α : (x : γ) → ((i : γ x) → Expr σ γ (concat α (γ x i))) → Expr σ γ α
  | bound σ γ (α : Arity) : (y : α) → ((i : α y) → Expr σ γ (concat α (α y i))) → Expr σ γ α

def ExprUnitR {σ γ : Shape} {α : Arity} :
  Expr σ γ (concat α A0) → Expr σ γ α := fun x => by
  rw [← Arity.unitR α]
  exact x

def ExprUnitL {σ γ : Shape} {α : Arity} :
  Expr σ γ (concat A0 α) → Expr σ γ α := fun x => by
  rw [← Arity.unitL α]
  exact x

def V (γ : Shape) (α : Arity) : Type := { x : γ | γ x = α }

instance {γ : Shape} {α : Arity} : CoeOut (V γ α) γ where
  coe x := x.val

-- def Arity.subArities (α : Arity) : List Arity :=
--   match α with
--   | Arity.mk X p =>
--     match X with
--     | .empty => []
--     | .slot => [p ()]
--     | .oplus X1 X2 =>
--       let α1 : Arity := Arity.mk X1 (λ x => p (Sum.inl x))
--       let α2 : Arity := Arity.mk X2 (λ x => p (Sum.inr x))
--       α1.subArities ++ α2.subArities

def Arity.rank (α : Arity) :=
  match α with
  | .mk X A =>
    match (List.map (λ x => Arity.rank (A x)) (List.finRange X)).maximum with
    | none   => 0
    | some n => n + 1

-- match α with
--   | .mk X A =>
--     match (List.map (λ x => (A x).rank) X.toList).maximum with
--     | none   => 0
--     | some n => n + 1

-- lemma ArityTypeListMem (α : Arity) (x : α.dom.toType) : x ∈ α.dom.toList :=
--   match α with
--   | .mk X A =>
--     match X with
--     | .empty => by
--       exfalso
--       exact x.elim
--     | .slot => by apply List.mem_cons_self
--     | .oplus Y Z => match x with
--       | .inl y => by
--         apply List.mem_append_left
--         apply List.mem_map_of_mem
--         let α' : Arity := .mk Y (fun _ => .mk .empty Empty.elim)
--         exact ArityTypeListMem α' y
--       | .inr z => by
--         apply List.mem_append_right
--         apply List.mem_map_of_mem
--         let α' : Arity := .mk Z (fun _ => .mk .empty Empty.elim)
--         exact ArityTypeListMem α' z

-- lemma SizeSubArityLeAux {n m : Nat} (l : List Nat) (p : n ∈ l) (q : List.maximum l = some m) : n ≤ m :=
--   (List.maximum_eq_coe_iff.1 q).2 n p

-- lemma SizeSubArityLe (α : Arity) (x : α) : (α x).sizeOf < α.sizeOf :=
--   match α with
--   | .mk X A =>
--     match hmax : (List.map (λ x => (A x).sizeOf) X.toList).maximum with
--     | some n => by calc
--       (A x).sizeOf ≤
--         (List.map (λ x => (A x).sizeOf) X.toList).maximum.getD 0 := by
--         rw [hmax]
--         simp
--         apply SizeSubArityLeAux (List.map (λ x => (A x).sizeOf) X.toList)
--         . simp
--           use x
--           . simp
--             apply ArityTypeListMem
--         . assumption
--       _ = n := by aesop
--       _ < n + 1 := by simp
--       _ = (Arity.mk X A).sizeOf := by unfold Arity.sizeOf ; aesop
--     | none => by
--       have h_empty : (List.map (λ x => (A x).sizeOf) X.toList) = [] :=
--         List.maximum_eq_bot.mp hmax
--       have mem : x ∈ X.toList := ArityTypeListMem (Arity.mk X A) x
--       have mem_mapped : (A x).sizeOf ∈ List.map (λ x => (A x).sizeOf) X.toList := by
--         simp [mem]
--         use x
--       rw [h_empty] at mem_mapped
--       simp at mem_mapped

-- def var {γ : Shape} {α : Arity} : V γ α → Expression γ α := by
--   intro ⟨x,p⟩
--   cases p
--   exact .app (Sum.inl x) (λ (i : γ x) => var ⟨Sum.inr i, by aesop⟩)
-- termination_by α.sizeOf
-- decreasing_by
--   simp_all
--   calc
--   (((γ ⊕ γ x) (.inl x)) i).sizeOf = (γ x i).sizeOf := by aesop
--   _ < (γ x).sizeOf := SizeSubArityLe (γ x) i
