
import Lean.Level
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.Data.Fintype.Basic

open CategoryTheory

set_option autoImplicit false

-- universe u

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

def V (γ : Shape) (α : Arity) : Type := { x : γ // γ x = α }

-- Weird: since when must subtype coercions be made explicit?
instance {γ : Shape} {α : Arity} : CoeOut (V γ α) γ where
  coe x := x.val


def var {γ : Shape} {α : Arity} : V γ α → Expression γ α := by
  intro ⟨x,p⟩
  cases p
  exact .app (Sum.inl x) (λ (i : γ x) => var ⟨Sum.inr i, by aesop⟩)


  -- Σ' (x : domShape γ) , ((i : domArity (mapShape γ x)) →
  --   ExpressionAux (γ ⊕ (mapArity (mapShape γ x) i)))



-- inductive Shape where
--   /-- the empty shape -/
-- | empty : Shape
--   /-- the shape containing precisely one item -/
-- | slot : Shape → Shape
--   /-- shape extension -/
-- | oplus : Shape → Shape → Shape
-- deriving Repr
-- -- TODO: implement better Repr instance for shapes

-- @[inherit_doc]
-- notation "𝟘" => Shape.empty

-- @[inherit_doc]
-- notation (priority := default+1) γ:31 " ⊕ " δ:31 => Shape.oplus γ δ

-- /-- A synonym for a shape, used when we think of a shape as specifying
--     the arity of a variable. -/
-- abbrev Arity := Shape

-- /-- The rank of a shape is the level of nesting of the slots -/
-- @[reducible]
-- def Shape.rank : Shape → Nat
-- | 𝟘 => 0
-- | .slot γ  => 1 + rank γ
-- | γ ⊕ δ => max (rank γ) (rank δ)

-- /-- Variables of given arity in a given shape -/
-- inductive var_in  : Arity → Shape → Type where
-- | varHere : ∀ {α : Shape}, var_in α α.slot
-- | varLeft : ∀ {γ δ} {{α}}, var_in α γ → var_in α (γ ⊕ δ)
-- | varRight : ∀ {γ δ} {{α}}, var_in α δ → var_in α (γ ⊕ δ)

-- /-- Fold on all variables in a given shape -/
-- def Shape.fold.{u} (γ : Shape) {A : Type u} (a : A) (f : A → ∀ ⦃α⦄, var_in α γ → A) : A :=
--   match γ with
--   | 𝟘 => a
--   | .slot _ => f a .varHere
--   | γ₁ ⊕ γ₂ => γ₂.fold (γ₁.fold a (fun b _ x => f b x.varLeft)) (fun b _ x => f b x.varRight)

-- theorem rank_Var_lt {α γ} (x : var_in α γ) : α.rank < γ.rank := by
--   induction x
--   case varHere => simp
--   case varLeft δ β α _ _ =>
--     simp [Shape.rank]
--     calc
--       α.rank < δ.rank := by assumption
--            _ ≤ max δ.rank β.rank := by exact Nat.le_max_left δ.rank β.rank
--   case varRight δ β α _ _ =>
--     simp [Shape.rank]
--     calc
--       α.rank < β.rank := by assumption
--            _ ≤ max δ.rank β.rank := by exact Nat.le_max_right δ.rank β.rank

-- /-- Expressions over a given shape -/
-- inductive Expr : Shape → Arity → Type where
-- /-- Apply a free variable to arguments -/
-- | applyFree  : ∀ {γ δ α}, var_in α γ → (∀ ⦃β⦄, var_in β α → Expr (γ ⊕ δ) β) →  Expr γ δ
-- /-- Apply a bound variable to arguments -/
-- | applyBound : ∀ {γ δ α}, var_in α δ → (∀ ⦃β⦄, var_in β α → Expr (γ ⊕ δ) β) →  Expr γ δ

-- @[inherit_doc]
-- infix:80 " ◃ " => Expr.applyFree

-- @[inherit_doc]
-- infix:80 " ◂ " => Expr.applyBound

-- @[reducible]
-- def Expr.sizeOf {γ δ} : Expr γ δ → Nat
-- | @Expr.applyFree _ _ α _ ts => 1 + α.fold 0 (fun n _ y => n + (ts y).sizeOf)
-- | @Expr.applyBound _ _ α _ ts => 1 + α.fold 0 (fun n _ y => n + (ts y).sizeOf)

-- theorem Expr.sizeOfFreeArg {γ δ α} (x : var_in α γ) (ts : ∀ ⦃β⦄, var_in β α → Expr (γ ⊕ δ) β) {θ} (y : var_in θ α) :
--   (ts y).sizeOf < (x ◃ ts).sizeOf := sorry

-- theorem Expr.sizeOfBoundArg {γ δ α} (x : var_in α δ) (ts : ∀ ⦃β⦄, var_in β α → Expr (γ ⊕ δ) β) {θ} (y : var_in θ α) :
--   (ts y).sizeOf < (x ◂ ts).sizeOf := sorry

-- instance {γ δ} : SizeOf (Expr γ δ) where sizeOf := Expr.sizeOf
