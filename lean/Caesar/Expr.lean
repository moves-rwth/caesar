import Batteries.Data.Rat.Basic
import Lean.ToExpr
import Mathlib.Data.Rat.Lemmas

namespace Caesar

structure Ident where
  name : String
deriving Lean.ToExpr, DecidableEq, Hashable, Inhabited

inductive BinOp where
  /- The `+` operator (addition). -/
  | Add
  /- The `-` operator (subtraction). -/
  | Sub
  /- The `*` operator (multiplication). -/
  | Mul
  /- The `/` operator (divison). -/
  | Div
  /- The `%` operator (modulo). -/
  | Mod
  /- The `&&` operator (logical and). -/
  | And
  /- The `||` operator (logical or). -/
  | Or
  /- The `==` operator (equality). -/
  | Eq
  /- The `<` operator (less than). -/
  | Lt
  /- The `<=` operator (less than or equal to). -/
  | Le
  /- The `!=` operator (not equal to). -/
  | Ne
  /- The `>=` operator (greater than or equal to). -/
  | Ge
  /- The `>` operator (greater than). -/
  | Gt
  /- The `⊓` operator (infimum). -/
  | Inf
  /- The `⊔` operator (supremum). -/
  | Sup
  /- The `→` operator (implication). -/
  | Impl
  /- The `←` operator (co-implication). -/
  | CoImpl
  /- The `↘` operator (hard implication/compare). -/
  | Compare
  /- The `↖` operator (hard co-implication/co-compare). -/
  | CoCompare
deriving Lean.ToExpr, DecidableEq

inductive UnOp where
  /- The `!` operator (negation). -/
  | Not
  /- The `~` operator (dual of negation), -/
  | Non
  /- Boolean embedding (maps true to top in the lattice). -/
  | Embed
  /- Iverson bracket (maps true to 1). -/
  | Iverson
  /- Parentheses (just to print ASTs faithfully). -/
  | Parens
deriving Lean.ToExpr, DecidableEq

inductive QuantOp where
  /- The infimum of a set. -/
  | Inf
  /- The supremum of a set. -/
  | Sup
  /- Boolean forall (equivalent to `Inf` on the lattice of booleans). -/
  | Forall
  /- Boolean exists (equivalent to `Sup` on the lattice of booleans). -/
  | Exists
deriving Lean.ToExpr, DecidableEq

inductive Ty where
  /- The primitive boolean type `Bool`. -/
  | Bool
  /- A signed integer type. -/
  | Int
  /- A unsigned integer type. -/
  | UInt
  /- Real numbers. -/
  | Real
  /- Unsigned real numbers -/
  | UReal
  /- Unsigned real numbers with infinity. -/
  | EUReal
deriving Lean.ToExpr, DecidableEq

inductive VarKind where
  /- Input parameters (cannot be modified). -/
  | Input
  /- Output parameters (cannot be accessed in the pre). -/
  | Output
  /- Mutable variables. -/
  | Mut
  /- Variables bound by a quantifier. -/
  | Quant
  /- Variables from a substitution (cannot be modified). -/
  | Subst
  /- Variables for slicing (cannot be modified). -/
  | Slice
deriving Lean.ToExpr, DecidableEq

structure VarDecl where
  name : Ident
  ty : Ty
  kind : VarKind
deriving Lean.ToExpr, DecidableEq

structure DeBruijnIndex where
  index : Nat
deriving Lean.ToExpr, DecidableEq

inductive QuantVar where
  | Shadow : Ident → QuantVar
  | Fresh : VarDecl → QuantVar
  | DeBrujin : QuantVar
deriving Lean.ToExpr, DecidableEq

structure Trigger where
  -- TODO: these makes expr cyclic which can prevent induction. add later
  terms : List Unit
deriving Lean.ToExpr, DecidableEq

-- structure QuantAnn where
--   triggers : List Trigger
-- deriving Lean.ToExpr, DecidableEq

structure Symbol where
  name : String
deriving Lean.ToExpr, DecidableEq

open Lean in
instance : Lean.ToExpr Rat where
  toExpr r :=
    if r.den == 1 then toExpr r.num else  mkApp2 (.const ``Div.div []) (toExpr r.num) (toExpr r.den)
  toTypeExpr := .const ``Rat []

inductive Lit where
  /- A string literal (`"something"`). -/
  | Str : String → Lit
  /- An unsigned integer literal (`123`). -/
  -- TODO: this should have been u128
  | UInt : UInt64 → Lit
  /- A number literal represented by a fraction. -/
  | Frac : Rat → Lit
  /- Infinity, -/
  | Infinity : Lit
  /- A boolean literal. -/
  | Bool : Bool → Lit
deriving Lean.ToExpr, DecidableEq

inductive Expr where
  /- A variable. -/
  | Var : Ident → Expr
  /- A call to a procedure or function. -/
  | Call : Ident → List Expr → Expr
  /- Boolean if-then-else -/
  | Ite : Expr → Expr → Expr → Expr
  /- Use of a binary operator. -/
  | Binary : BinOp → Expr → Expr → Expr
  /- Use of an unary operator. -/
  | Unary : UnOp → Expr → Expr
  /- Type casting. -/
  | Cast : Expr → Expr
  /- A quantifier over some variables. -/
  | Quant : QuantOp → List QuantVar → Expr → Expr
  /- A substitution. -/
  | Subst : Ident → Expr → Expr → Expr
  /- A value literal. -/
  | Lit : Lit → Expr
  /- A de Bruijn index. -/
  | DeBruijn : DeBruijnIndex → Expr
deriving Lean.ToExpr, Inhabited

instance (n : Nat) : OfNat DeBruijnIndex n := ⟨⟨n⟩⟩

def DeBruijnIndex.succ (i : DeBruijnIndex) : DeBruijnIndex := ⟨i.index + 1⟩

instance : LinearOrder DeBruijnIndex where
  le a b := a.index ≤ b.index
  le_refl := by simp
  le_trans := fun _ _ _ ↦ Nat.le_trans
  le_antisymm := fun ⟨_⟩ ⟨_⟩ ↦ by simp; exact Nat.le_antisymm
  le_total := fun ⟨_⟩ ⟨_⟩ ↦ by simp; apply Nat.le_total
  decidableLE a b := if h : a.index ≤ b.index then .isTrue h else .isFalse h

end Caesar
