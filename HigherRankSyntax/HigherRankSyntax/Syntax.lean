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

inductive Position' where
  | empty : Position'
  | slot : Position'
  | oplus : Position' → Position' → Position'

inductive Position'.eq : Position' → Position' → Prop where
  | refl : (P : Position') → Position'.eq P P
  | unitR : (P : Position') → Position'.eq P (.oplus P .empty)
  | unitR' : (P : Position') → Position'.eq (.oplus P .empty) P
  | unitL : (P : Position') → Position'.eq P (.oplus .empty P)
  | assoc : (P Q R : Position') →
      Position'.eq (.oplus P (.oplus Q R)) (.oplus (.oplus P Q) R)
  | oplusCongrL : (P P' Q : Position') → P.eq P' → Position'.eq (P.oplus Q) (P'.oplus Q)
  | oplusCongrR : (P Q Q' : Position') → Q.eq Q' → Position'.eq (P.oplus Q) (P.oplus Q')

def Position : Type := Quot Position'.eq

@[reducible]
def Position'.len : Position' → Nat
  | .empty => 0
  | .slot => 1
  | .oplus P Q => P.len + Q.len

lemma Position'.len.wd (P Q : Position') (h : P.eq Q) : P.len = Q.len :=
  match h with
  | .refl _ => .refl _
  | .unitL P => by simp
  | .unitR P => by simp
  | .unitR' P => by simp
  | .assoc P Q R => by
      unfold Position'.len
      have h : (Q.oplus R).len = Q.len + R.len := by simp
      have h' : (P.oplus Q).len = P.len + Q.len := by simp
      rw [h, h']
      omega
  | .oplusCongrL P Q R e => by
      unfold Position'.len
      rw [Position'.len.wd P Q e]
  | .oplusCongrR P Q R e => by
      unfold Position'.len
      rw [Position'.len.wd Q R e]

@[reducible]
def Position'.toType (P : Position') : Type := Fin P.len

lemma Position.toType.wd (P Q : Position') (e : P.eq Q) : P.toType = Q.toType := by
  unfold Position'.toType
  rw [Position'.len.wd P Q e]

@[reducible]
def Position.toType : Position → Type :=
  Quot.lift Position'.toType Position.toType.wd

instance : CoeSort Position Type where
  coe := Position.toType

inductive Arity : Type where
  | mk : (dom : Position) → (dom.toType → Arity) → Arity

@[reducible]
def A0 : Arity := Arity.mk (.mk _ Position'.empty) Fin.elim0

def Arity.dom : Arity → Position := fun ⟨X,_⟩ => X

def Arity.arity : (α : Arity) → (α.dom → Arity) := fun ⟨_,p⟩ => p

instance : CoeSort Arity Type where
  coe α := α.dom.toType

instance : CoeFun Arity (fun α => α → Arity) where
  coe := Arity.arity

@[reducible]
def Position.len (P : Position) : Nat :=
  Quot.lift Position'.len Position'.len.wd P

@[reducible]
def Position'.oplus' (α β : Position') : Position := .mk _ (α.oplus β)

def Position'.oplus'.wd₀ (P Q Q' : Position') (h : Q.eq Q') :
  P.oplus' Q = P.oplus' Q' := match h with
  | .refl _ => .refl _
  | .unitR _ => by
    unfold oplus'
    apply Quot.sound
    exact Position'.eq.oplusCongrR _ _ _ (Position'.eq.unitR Q)
  | .unitR' _ => by
    unfold oplus'
    apply Quot.sound
    apply Position'.eq.oplusCongrR
    apply Position'.eq.unitR' _
  | .unitL _ => by
    unfold oplus'
    apply Quot.sound
    exact Position'.eq.oplusCongrR _ _ _ (Position'.eq.unitL Q)
  | .assoc R S T => by
    unfold oplus'
    apply Quot.sound
    apply Position'.eq.oplusCongrR
    apply Position'.eq.assoc
  | .oplusCongrL R S T e => by
    unfold oplus'
    apply Quot.sound
    apply Position'.eq.oplusCongrR
    apply Position'.eq.oplusCongrL
    exact e
  | .oplusCongrR R S T e => by
    unfold oplus'
    apply Quot.sound
    apply Position'.eq.oplusCongrR
    apply Position'.eq.oplusCongrR
    exact e

def Position'.oplus'.wd₁ (P P' Q : Position') (h : P.eq P') :
  P.oplus' Q = P'.oplus' Q := match h with
  | .refl _ => .refl _
  | .unitL P => by
    unfold oplus'
    apply Quot.sound
    exact Position'.eq.oplusCongrL _ _ _ (Position'.eq.unitL P)
  | .unitR _ => by
    unfold oplus'
    apply Quot.sound
    exact Position'.eq.oplusCongrL _ _ _ (Position'.eq.unitR P)
  | .unitR' _ => by
    unfold oplus'
    apply Quot.sound
    apply Position'.eq.oplusCongrL
    apply Position'.eq.unitR' _
  | .assoc R S T => by
    unfold oplus'
    apply Quot.sound
    apply Position'.eq.oplusCongrL
    apply Position'.eq.assoc
  | .oplusCongrL R S T e => by
    unfold oplus'
    apply Quot.sound
    apply Position'.eq.oplusCongrL
    apply Position'.eq.oplusCongrL
    exact e
  | .oplusCongrR R S T e => by
    unfold oplus'
    apply Quot.sound
    apply Position'.eq.oplusCongrL
    apply Position'.eq.oplusCongrR
    exact e

@[reducible]
def Position.oplus : (α β : Position) → Position :=
  Quot.lift₂ Position'.oplus' Position'.oplus'.wd₀  Position'.oplus'.wd₁

lemma foo (P Q : Position) : (Position.oplus P Q).toType = Fin (P.len + Q.len) := by
  refine Quot.induction_on₂ P Q (λ p q => ?_)
  aesop

lemma bar (P : Position) : P.toType = Fin P.len := by
  refine Quot.induction_on P (λ p => ?_)
  aesop

@[reducible]
def concat_dom (α : Arity) (β : Arity) : Position :=
  Position.oplus α.dom β.dom

def concat_arr (α : Arity) (β : Arity) : concat_dom α β → Arity := fun x => by
  unfold concat_dom at x
  rewrite [foo α.dom β.dom] at x
  exact match x with
  | ⟨n,h⟩ =>
    if h : (n : Nat) < α.dom.len then by
      apply α.arity
      rw [bar α.dom]
      use n
    else by
      let j : β.dom.toType := by
        rw [bar β.dom]
        use n - α.dom.len
        omega
      exact β j

@[reducible]
def concat (α : Arity) (β : Arity) : Arity :=
    .mk (concat_dom α β) (concat_arr α β)

def unitR_aux (dom : Position) (arr : dom → Arity) : (Arity.mk dom arr).dom.oplus A0.dom = dom := by
  unfold A0
  simp [Position.oplus]
  show Quot.lift₂ Position'.oplus' Position'.oplus'.wd₀ Position'.oplus'.wd₁ dom (Quot.mk Position'.eq Position'.empty) = dom
  refine Quot.induction_on dom (fun P => ?_)
  apply Quot.sound
  exact Position'.eq.unitR' P

lemma unitR (α : Arity) : concat α A0 = α := by
  match α with
  | ⟨dom, arr⟩ =>
    simp_all only [Arity.mk.injEq]
    apply And.intro
    have hdom_eq : concat_dom (Arity.mk dom arr) A0 = dom := by
      unfold concat_dom
      simp [A0]
      exact unitR_aux dom arr
    · unfold concat_dom
      exact hdom_eq
    · unfold concat_arr
      congr!
      · exact unitR_aux dom arr
      · simp!
        aesop?
        · sorry
        · sorry

notation (priority := default) "Shape" => Arity

inductive Expr : (σ γ : Shape) → (α : Arity) → Type where
  | sym (σ : Shape) γ α : (s : σ) → ((i : σ s) →  Expr σ γ (concat α (σ s i))) → Expr σ γ α
  | free σ (γ : Shape) α : (x : γ) → ((i : γ x) → Expr σ γ (concat α (γ x i))) → Expr σ γ α
  | bound σ γ (α : Arity) : (y : α) → ((i : α y) → Expr σ γ (concat α (α y i))) → Expr σ γ α

def ExprUnitR {σ γ : Shape} {α : Arity} :
  Expr σ γ (concat α A0) → Expr σ γ α := fun x => by
  rw [← unitR α]
  exact x


-- inductive ExpressionAux : Shape → Type :=
--   | app : ∀ {γ : Shape} (x : γ),
--       (∀ (i : γ x),  ExpressionAux (γ ⊕ γ x i)) → ExpressionAux γ

-- def Expression : Shape → Arity → Type := fun γ α =>
--   ExpressionAux (γ ⊕ α)

-- def V (γ : Shape) (α : Arity) : Type := { x : γ | γ x = α }

-- instance {γ : Shape} {α : Arity} : CoeOut (V γ α) γ where
--   coe x := x.val

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

-- def Arity.sizeOf (α : Arity) : Nat := match α with
--   | .mk X A =>
--     match (List.map (λ x => (A x).sizeOf) X.toList).maximum with
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
