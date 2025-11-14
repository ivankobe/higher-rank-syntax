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

open CategoryTheory

set_option autoImplicit false

inductive Position where
  | empty : Position
  | slot : Position
  | oplus : Position → Position → Position

def Position.toType : Position → Type
  | empty => Empty
  | slot => Unit
  | oplus p q => Sum (toType p) (toType q)

instance : CoeSort Position Type where
  coe := Position.toType

def Position.toList : (X : Position) → List X.toType
  | empty => []
  | slot => [.unit]
  | oplus p q => (.map .inl p.toList) ++ (.map .inr q.toList)

inductive Arity : Type where
  | mk : (dom : Position) → (dom → Arity) → Arity

def Arity.dom : Arity → Position := fun ⟨X,_⟩ => X

instance : CoeSort Arity Type where
  coe α := α.dom.toType

def Arity.arity : (α : Arity) → (α.dom → Arity) := fun ⟨_,p⟩ => p

instance : CoeFun Arity (fun α => α.dom → Arity) where
  coe := Arity.arity

def ArityCat := Discrete Arity

structure Shape : Type where
  dom : Position
  arity : dom → Arity

instance : CoeSort Shape Type where
  coe γ := γ.dom.toType

instance : CoeFun Shape (fun γ => γ.dom → Arity) where
  coe := Shape.arity

instance ShapeCat : Category Shape where
  Hom γ δ := match γ , δ with
    | ⟨X,p⟩ , ⟨Y,q⟩ => Σ' (f : X → Y) , (p = q ∘ f)
  id γ := match γ with
    | ⟨X,s⟩ => ⟨ id, by simp ⟩
  comp f g := match f , g with
    | ⟨f,hf⟩, ⟨g,hg⟩ => ⟨ g ∘ f , by aesop ⟩

def concat (γ : Shape) (α : Arity) : Shape :=
  { dom := .oplus γ.dom α.dom ,
    arity := fun z => match z with
      | .inl x => γ.arity x
      | .inr y => α.arity y
    }

notation (priority := default+1) γ:31 " ⊕ " δ:31 => concat γ δ

inductive ExpressionAux : Shape → Type :=
  | app : ∀ {γ : Shape} (x : γ),
      (∀ (i : γ x),  ExpressionAux (γ ⊕ γ x i)) → ExpressionAux γ

def Expression : Shape → Arity → Type := fun γ α =>
  ExpressionAux (γ ⊕ α)

def V (γ : Shape) (α : Arity) : Type := { x : γ | γ x = α }

instance {γ : Shape} {α : Arity} : CoeOut (V γ α) γ where
  coe x := x.val

def Arity.subArities (α : Arity) : List Arity :=
  match α with
  | Arity.mk X p =>
    match X with
    | .empty => []
    | .slot => [p ()]
    | .oplus X1 X2 =>
      let α1 : Arity := Arity.mk X1 (λ x => p (Sum.inl x))
      let α2 : Arity := Arity.mk X2 (λ x => p (Sum.inr x))
      α1.subArities ++ α2.subArities

def Arity.sizeOf (α : Arity) : Nat := match α with
  | .mk X A =>
    match (List.map (λ x => (A x).sizeOf) X.toList).maximum with
    | none   => 0
    | some n => n + 1

lemma ArityTypeListMem (α : Arity) (x : α.dom.toType) : x ∈ α.dom.toList :=
  match α with
  | .mk X A =>
    match X with
    | .empty => by
      exfalso
      exact x.elim
    | .slot => by apply List.mem_cons_self
    | .oplus Y Z => match x with
      | .inl y => by
        apply List.mem_append_left
        apply List.mem_map_of_mem
        let α' : Arity := .mk Y (fun _ => .mk .empty Empty.elim)
        exact ArityTypeListMem α' y
      | .inr z => by
        apply List.mem_append_right
        apply List.mem_map_of_mem
        let α' : Arity := .mk Z (fun _ => .mk .empty Empty.elim)
        exact ArityTypeListMem α' z

lemma SizeSubArityLeAux {n m : Nat} (l : List Nat) (p : n ∈ l) (q : List.maximum l = some m) : n ≤ m :=
  (List.maximum_eq_coe_iff.1 q).2 n p

lemma SizeSubArityLe (α : Arity) (x : α) : (α x).sizeOf < α.sizeOf :=
  match α with
  | .mk X A =>
    match hmax : (List.map (λ x => (A x).sizeOf) X.toList).maximum with
    | some n => by calc
      (A x).sizeOf ≤
        (List.map (λ x => (A x).sizeOf) X.toList).maximum.getD 0 := by
        rw [hmax]
        simp
        apply SizeSubArityLeAux (List.map (λ x => (A x).sizeOf) X.toList)
        . simp
          use x
          . simp
            apply ArityTypeListMem
        . assumption
      _ = n := by aesop
      _ < n + 1 := by simp
      _ = (Arity.mk X A).sizeOf := by unfold Arity.sizeOf ; aesop
    | none => by
      have h_empty : (List.map (λ x => (A x).sizeOf) X.toList) = [] :=
        List.maximum_eq_bot.mp hmax
      have mem : x ∈ X.toList := ArityTypeListMem (Arity.mk X A) x
      have mem_mapped : (A x).sizeOf ∈ List.map (λ x => (A x).sizeOf) X.toList := by
        simp [mem]
        use x
      rw [h_empty] at mem_mapped
      simp at mem_mapped

def var {γ : Shape} {α : Arity} : V γ α → Expression γ α := by
  intro ⟨x,p⟩
  cases p
  exact .app (Sum.inl x) (λ (i : γ x) => var ⟨Sum.inr i, by aesop⟩)
termination_by α.sizeOf
decreasing_by
  simp_all
  calc
  (((γ ⊕ γ x) (.inl x)) i).sizeOf = (γ x i).sizeOf := by aesop
  _ < (γ x).sizeOf := SizeSubArityLe (γ x) i
