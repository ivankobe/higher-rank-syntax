import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Types
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Relation

import HigherRankSyntax.Syntax
import HigherRankSyntax.RelativeMonads.RelativeMonad

open CategoryTheory

@[reducible]
instance ArityCat : Category Arity where
  Hom γ δ :=  Σ' (f : γ → δ), (γ.arity = δ.arity ∘ f)
  id γ := ⟨id, by simp⟩
  comp f g := by
    use g.1 ∘ f.1
    have _ := f.2
    have _ := g.2
    aesop

@[reducible]
def fV (σ : Shape) : Shape ⥤ (Arity → Type) where
  obj := λ γ α => V σ γ α
  map := λ f α x => by
    use f.1 x.1
    have _ := f.2
    aesop

@[reducible]
def RelModExpr_map (σ : Shape) : Shape → Arity → Type :=
  λ γ α => Expr σ γ α

@[reducible]
def RelModExpr_η (σ : Shape) :
  (γ : Shape) → (α : Arity) → (fV σ).obj γ α → Expr σ γ α :=
  λ γ α => var σ γ α

-- ⊢ J (lift (σ ⊕ γ) (γ.arity x) α (fun β i ↦ ⋯ ▸ L (e ↑i))
      -- A0 (I (var σ γ (γ.arity x) ⟨x, ⋯⟩)))
-- = Expr.free σ γ α x e

-- e : (i : (γ.arity x).dom.toType) → Expr σ γ (α ⊕ (γ.arity x).arity i)
-- ⋯ ▸ L (e ↑i) : Expr (σ ⊕ γ) α ((γ.arity x).arity ↑i)
-- fun β i ↦ ⋯ ▸ L (e ↑i) : (β : Shape) → { x_1 // (γ.arity x).arity x_1 = β } → Expr (σ ⊕ γ) α β

-- (i : (γ.arity x).dom.toType) → Expr σ γ (α ⊕ (γ.arity x).arity i)

@[simp]
lemma Arity.liftL_wkL {α β : Arity} (x : α)
    (h : (Arity.wkL (β := β) x).val < α.dom) :
    Arity.liftL (β := β) (Arity.wkL x) h = x := by
  apply Fin.ext
  rfl

@[simp]
lemma Arity.wkL_liftL {α β : Arity} (x : α ⊕ β)
    (h : x.val < α.dom) :
    Arity.wkL (β := β) (Arity.liftL x h) = x := by
  apply Fin.ext
  rfl

@[simp]
lemma Arity.liftR_wkR {α β : Arity} (x : β)
    (h : ¬ (Arity.wkR (α := α) x).val < α.dom) :
    Arity.liftR (α := α) (Arity.wkR x) h = x := by
  apply Fin.ext
  simp [Arity.liftR, Arity.wkR]

@[simp]
lemma Arity.wkR_liftR {α β : Arity} (x : α ⊕ β)
    (h : ¬ x.val < α.dom) :
    Arity.wkR (α := α) (Arity.liftR x h) = x := by
  apply Fin.ext
  simp [Arity.liftR, Arity.wkR]
  omega

lemma fooR {α β : Arity} (h : α = β) (x : β) :
    α (by rw [h]; exact x) = β x := by
  subst h
  rfl

lemma fooR_cast {α β : Arity} (h : α = β) (x : β) :
    α (cast (congrArg (fun a : Arity => a.dom.toType) h.symm) x) = β x := by
  subst h
  rfl

lemma shiftRightR_shiftRightL_L {σ γ : Shape} {α β : Arity}
    (E : Expr σ γ (α ⊕ β)) :
    Expr.shiftRightR (Expr.shiftRightL (L E)) = E := by
  sorry

lemma J_sym_wkR_L {σ γ : Shape} {α : Arity} (x : γ)
    (e : (i : γ x) → Expr σ γ (α ⊕ (γ x) i)) :
    J (Expr.sym (σ ⊕ γ) α A0 (Arity.wkR (α := σ) x)
        (fun i => by
          let i' : γ x := cast
            (congrArg (fun a : Arity => a.dom.toType) (Arity.wkREq x).symm) i
          exact cast (by
            apply congrArg (fun β => Expr (σ ⊕ γ) α (A0 ⊕ β))
            exact fooR_cast (Arity.wkREq x) i)
            (ExprUnitL' (L (e i'))))) =
      Expr.free σ γ α x e := by
  cases σ with
  | mk σdom σarity =>
  cases γ with
  | mk γdom γarity =>
  cases α with
  | mk αdom αarity =>
  simp! [J, L, Expr.shiftRightL, Expr.shiftRightR, Expr.shiftLeftL, Expr.shiftLeftR, ExprUnitR]
  split_ifs with h
  · omega
  · simp! [Expr.shiftRightR, ExprUnitR, ExprUnitL', Arity.unitR, Arity.unitL, Arity.assoc,
      Arity.liftL, Arity.wkR]
    sorry

def RelModExpr_unit_right (σ γ : Shape) (α : Arity) (E : Expr σ γ α) :
  lift σ γ γ (RelModExpr_η σ γ) α E = E := by
  match E with
  | .sym _ _ _ s e =>
    unfold lift
    simp!
    funext i
    exact RelModExpr_unit_right σ γ (α ⊕ (σ.arity s).arity i) (e i)
  | .free _ _ _ x e =>
    unfold lift
    simp!
    have _ : ∀ (i : _), lift σ γ γ (RelModExpr_η σ γ) (α ⊕ (γ.arity x).arity ↑i) (e ↑i) = e ↑i := by
      intro i
      apply RelModExpr_unit_right
    simp_all only
    unfold RelModExpr_η
    unfold cast
    unfold var
    simp!
    unfold I Expr.shiftRightL Expr.shiftRightR ExprUnitR'
    simp!
    sorry
  | .bound _ _ _ y e =>
    unfold lift
    simp!
    funext i
    exact RelModExpr_unit_right σ γ (α ⊕ (α.arity y).arity i) (e i)
termination_by (γ.rank, E.rank)
decreasing_by
  · apply Prod.Lex.right; apply Expr.subExprLeSym
  · apply Prod.Lex.right; apply Expr.subExprLeFree
  · apply Prod.Lex.right
    exact Expr.subExprLeBound i

def RelModExpr (σ : Shape) : RelativeMonad (fV σ) where
  map := RelModExpr_map σ
  η := RelModExpr_η σ
  lift := by
    intro γ δ f
    exact lift σ γ δ f
  unit_right := by
    intro γ
    funext α E
    simp!
    exact RelModExpr_unit_right σ γ α E
  unit_left := by sorry
  comp_lift := by sorry
