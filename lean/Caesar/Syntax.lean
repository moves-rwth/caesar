import Caesar.Expr

namespace Caesar

open Lean PrettyPrinter

declare_syntax_cat hvl_ident
syntax "[hvl_ident|" hvl_ident "]" : term
declare_syntax_cat hvl_expr
syntax "[hvl_expr|" hvl_expr "]" : term
declare_syntax_cat hvl_ty
syntax "[hvl_ty|" hvl_ty "]" : term
declare_syntax_cat hvl_quant_op
syntax "[hvl_quant_op|" hvl_quant_op "]" : term
declare_syntax_cat hvl_quant_var
syntax "[hvl_quant_var|" hvl_quant_var "]" : term
declare_syntax_cat hvl_quant_ann
syntax "[hvl_quant_ann|" hvl_quant_ann "]" : term
declare_syntax_cat hvl_var_decl
syntax "[hvl_var_decl|" hvl_var_decl "]" : term

syntax "inf" : hvl_quant_op
syntax "sup" : hvl_quant_op
syntax "exists" : hvl_quant_op
syntax "forall" : hvl_quant_op

syntax ident : hvl_ident
syntax "@" term:max : hvl_ident

syntax "Int" : hvl_ty
syntax "Bool" : hvl_ty
syntax "UInt" : hvl_ty
syntax "Real" : hvl_ty
syntax "UReal" : hvl_ty
syntax "EUReal" : hvl_ty

syntax hvl_ident ": " hvl_ty : hvl_var_decl

syntax hvl_var_decl : hvl_quant_var
syntax "shadow " hvl_ident : hvl_quant_var
syntax "dbj" : hvl_quant_var

syntax hvl_ident : hvl_expr
syntax hvl_expr "[" hvl_ident " ↦ " hvl_expr "]" : hvl_expr
syntax hvl_quant_op hvl_quant_var+ ". " hvl_expr : hvl_expr
syntax hvl_quant_op hvl_quant_var+ ". " hvl_expr : hvl_expr

syntax "@" term:max : hvl_expr

section Operators

syntax:50 hvl_expr:50 " + " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " - " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " * " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " / " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " % " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " && " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " || " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " == " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " < " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " <= " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " != " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " >= " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " > " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " ⊓ " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " ⊔ " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " → " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " ← " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " ↘ " hvl_expr:50 : hvl_expr
syntax:50 hvl_expr:50 " ↖ " hvl_expr:50 : hvl_expr

syntax "!" hvl_expr : hvl_expr
syntax "~" hvl_expr : hvl_expr
syntax "[" hvl_expr "]" : hvl_expr
syntax "(" hvl_expr ")" : hvl_expr

-- TODO:
-- /- Boolean embedding (maps true to top in the lattice). -/
-- | Embed

macro_rules
-- binary
| `([hvl_expr|$l + $r]) => `(Expr.Binary BinOp.Add [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l - $r]) => `(Expr.Binary BinOp.Sub [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l * $r]) => `(Expr.Binary BinOp.Mul [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l / $r]) => `(Expr.Binary BinOp.Div [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l % $r]) => `(Expr.Binary BinOp.Mod [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l && $r]) => `(Expr.Binary BinOp.And [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l || $r]) => `(Expr.Binary BinOp.Or [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l == $r]) => `(Expr.Binary BinOp.Eq [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l < $r]) => `(Expr.Binary BinOp.Lt [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l <= $r]) => `(Expr.Binary BinOp.Le [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l != $r]) => `(Expr.Binary BinOp.Ne [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l >= $r]) => `(Expr.Binary BinOp.Ge [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l > $r]) => `(Expr.Binary BinOp.Gt [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l ⊓ $r]) => `(Expr.Binary BinOp.Inf [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l ⊔ $r]) => `(Expr.Binary BinOp.Sup [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l → $r]) => `(Expr.Binary BinOp.Impl [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l ← $r]) => `(Expr.Binary BinOp.CoImpl [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l ↘ $r]) => `(Expr.Binary BinOp.Compare [hvl_expr|$l] [hvl_expr|$r])
| `([hvl_expr|$l ↖ $r]) => `(Expr.Binary BinOp.CoCompare [hvl_expr|$l] [hvl_expr|$r])
-- unary
| `([hvl_expr|! $x:hvl_expr]) => `(Expr.Unary .Not [hvl_expr|$x])
| `([hvl_expr|~ $x:hvl_expr]) => `(Expr.Unary .Non [hvl_expr|$x])
| `([hvl_expr|[$x:hvl_expr]]) => `(Expr.Unary .Iverson [hvl_expr|$x])
| `([hvl_expr|($x:hvl_expr)]) => `(Expr.Unary .Parens [hvl_expr|$x])

end Operators

macro_rules
| `([hvl_ident| $n:ident ]) => `(term|({name:=$(quote n.getId.toString)} : Ident))
| `([hvl_ident| @$n:term ]) => `($n)

open Lean in
macro_rules
-- types
| `([hvl_ty|Int]) => `(Ty.Int)
| `([hvl_ty|Bool]) => `(Ty.Bool)
-- var decl
| `([hvl_var_decl|$x:hvl_ident : $ty]) => `(VarDecl.mk [hvl_ident|$x] [hvl_ty|$ty])
-- quant op
| `([hvl_quant_op|inf]) => `(QuantOp.Inf)
| `([hvl_quant_op|sup]) => `(Caesar.QuantOp.Sup)
| `([hvl_quant_op|exists]) => `(Caesar.QuantOp.Exists)
| `([hvl_quant_op|forall]) => `(Caesar.QuantOp.Forall)
-- quant var
| `([hvl_quant_var|$x:hvl_var_decl]) => `(QuantVar.Fresh ([hvl_var_decl|$x] .Quant))
| `([hvl_quant_var|shadow $x:hvl_ident]) => `(QuantVar.Shadow [hvl_ident|$x])
| `([hvl_quant_var|dbj]) => `(QuantVar.DeBrujin)
-- expr
| `([hvl_expr|$i:hvl_ident]) => `(Caesar.Expr.Var [hvl_ident|$i])
| `([hvl_expr|$x[$a ↦ $b]]) => `(Caesar.Expr.Subst [hvl_ident|$a] [hvl_expr|$x] [hvl_expr|$b])
| `([hvl_expr|inf $ann*. $e]) => `(Caesar.Expr.Quant .Inf [$[[hvl_quant_var|$ann]],*] [hvl_expr|$e])
| `([hvl_expr|sup $ann*. $e]) => `(Caesar.Expr.Quant .Sup [$[[hvl_quant_var|$ann]],*] [hvl_expr|$e])
| `([hvl_expr|exists $ann*. $e]) => `(Caesar.Expr.Quant .Exists [$[[hvl_quant_var|$ann]],*] [hvl_expr|$e])
| `([hvl_expr|forall $ann*. $e]) => `(Caesar.Expr.Quant .Forall [$[[hvl_quant_var|$ann]],*] [hvl_expr|$e])
| `([hvl_expr|@ $e]) => `($e)

/-- info: QuantVar.Fresh { name := { name := "x" }, ty := Ty.Int, kind := VarKind.Quant } -/
#guard_msgs in
#eval [hvl_quant_var|x : Int]

/--
info: Expr.Quant QuantOp.Inf [QuantVar.Fresh { name := { name := "x" }, ty := Ty.Int, kind := VarKind.Quant }]
  (Expr.Var { name := "x" })
-/
#guard_msgs in
#eval [hvl_expr|inf x : Int. x]

/-- info: Expr.Quant QuantOp.Inf [QuantVar.DeBrujin] (Expr.Var { name := "x" }) -/
#guard_msgs in
#eval [hvl_expr|inf dbj . x]

@[app_unexpander Caesar.Expr.Var]
def Expr.unexpandVar : Unexpander
| `($_lit $s) =>
  match s with
    | `({name:=$y:str}) =>
      let name := mkIdent $ Name.mkSimple y.getString
      `([hvl_expr|$name:ident])
    | _ =>
      `([hvl_expr|@$s])
| _ => throw ()

/-- info: [hvl_expr|x] -/
#guard_msgs in
#eval [hvl_expr|x]

/-- info: fun x ↦ [hvl_expr|@x] : Ident → Expr -/
#guard_msgs in
#check fun (x : Ident) ↦ Expr.Var x

@[app_unexpander Caesar.Expr.Subst]
def Expr.unexpandSubst : Unexpander
| `($_lit {name:=$a:str} [hvl_expr|$x] [hvl_expr|$b]) =>
  let a := mkIdent $ Name.mkSimple a.getString
  `([hvl_expr|$x[$a:ident ↦ $b]])
| _ => throw ()

/-- info: [hvl_expr|a[b ↦ c]] -/
#guard_msgs in
#eval [hvl_expr|a[b ↦ c]]

open Lean in
@[app_unexpander Caesar.Expr.Quant]
def Expr.unexpandQuant : Unexpander
| `($_lit $op $vars* $e) => do
  let e ← match e with | `([hvl_expr|$e]) => `(hvl_expr|$e) | _ => `(hvl_expr|@$e)
  match vars[0]! with
  -- | `([QuantVar.Fresh {name:=$x:str}]) => mkIdent $ Name.mkSimple x.getString
  | `([QuantVar.Fresh {name:={name:=$x:str},ty:=$y,kind:=$z}]) =>
    let ty : UnexpandM (TSyntax `hvl_ty) := match y with
      | `(Ty.Int) => `(hvl_ty|Int)
      | `(Ty.Bool) => `(hvl_ty|Bool)
      | `(Ty.UInt) => `(hvl_ty|UInt)
      | `(Ty.Real) => `(hvl_ty|Real)
      | `(Ty.UReal) => `(hvl_ty|UReal)
      | `(Ty.EUReal) => `(hvl_ty|EUReal)
      | _ => `(hvl_ty|Int)
    let name := mkIdent $ Name.mkSimple x.getString
    let ty ← ty
    match op with
    | `(QuantOp.Inf) => `([hvl_expr|inf $name:ident : $ty. $e])
    | `(QuantOp.Sup) => `([hvl_expr|sup $name:ident : $ty. $e])
    | `(QuantOp.Exists) => `([hvl_expr|exists $name:ident : $ty. $e])
    | `(QuantOp.Forall) => `([hvl_expr|forall $name:ident : $ty. $e])
    | _ => `(hi)
  | `([QuantVar.Shadow {name:=$x:str}]) =>
    let name := mkIdent $ Name.mkSimple x.getString
    match op with
    | `(QuantOp.Inf) => `([hvl_expr|inf shadow $name:ident. $e])
    | `(QuantOp.Sup) => `([hvl_expr|sup shadow $name:ident. $e])
    | `(QuantOp.Exists) => `([hvl_expr|exists shadow $name:ident. $e])
    | `(QuantOp.Forall) => `([hvl_expr|forall shadow $name:ident. $e])
    | _ => `(hi)
  | `([QuantVar.DeBrujin]) =>
    -- let name := mkIdent $ Name.mkSimple x.getString
    match op with
    | `(QuantOp.Inf) => `([hvl_expr|inf dbj. $e])
    | `(QuantOp.Sup) => `([hvl_expr|sup dbj. $e])
    | `(QuantOp.Exists) => `([hvl_expr|exists dbj. $e])
    | `(QuantOp.Forall) => `([hvl_expr|forall dbj. $e])
    | _ => `(hi)
  | _ => throw ()
| _ => throw ()

/-- info: [hvl_expr|inf shadow x. x] -/
#guard_msgs in
#eval [hvl_expr|inf shadow x. x]

/-- info: [hvl_expr|inf a: Bool. x] -/
#guard_msgs in
#eval [hvl_expr|inf a: Bool. x]

/-- info: [hvl_expr|inf dbj. x] -/
#guard_msgs in
#eval [hvl_expr|inf dbj . x]

/-- info: [hvl_expr|a[b ↦ c]] -/
#guard_msgs in
#eval [hvl_expr|a[b ↦ c]]

open Lean in
@[app_unexpander Caesar.Expr.Binary]
def Expr.unexpandBinary : Unexpander
| `($_bin $op $l $r) => do
  let l ← match l with | `([hvl_expr|$l]) => `(hvl_expr|$l) | _ => `(hvl_expr|@$l)
  let r ← match r with | `([hvl_expr|$r]) => `(hvl_expr|$r) | _ => `(hvl_expr|@$r)
  match op with
    | `(BinOp.Add) => `([hvl_expr|$l + $r])
    | `(BinOp.Sub) => `([hvl_expr|$l - $r])
    | `(BinOp.Mul) => `([hvl_expr|$l * $r])
    | `(BinOp.Div) => `([hvl_expr|$l / $r])
    | `(BinOp.Mod) => `([hvl_expr|$l % $r])
    | `(BinOp.And) => `([hvl_expr|$l && $r])
    | `(BinOp.Or) => `([hvl_expr|$l || $r])
    | `(BinOp.Eq) => `([hvl_expr|$l == $r])
    | `(BinOp.Lt) => `([hvl_expr|$l < $r])
    | `(BinOp.Le) => `([hvl_expr|$l <= $r])
    | `(BinOp.Ne) => `([hvl_expr|$l != $r])
    | `(BinOp.Ge) => `([hvl_expr|$l >= $r])
    | `(BinOp.Gt) => `([hvl_expr|$l > $r])
    | `(BinOp.Inf) => `([hvl_expr|$l ⊓ $r])
    | `(BinOp.Sup) => `([hvl_expr|$l ⊔ $r])
    | `(BinOp.Impl) => `([hvl_expr|$l → $r])
    | `(BinOp.CoImpl) => `([hvl_expr|$l ← $r])
    | `(BinOp.Compare) => `([hvl_expr|$l ↘ $r])
    | `(BinOp.CoCompare) => `([hvl_expr|$l ↖ $r])
    | _ => throw ()
| _ => throw ()

open Lean in
@[app_unexpander Caesar.Expr.Unary]
def Expr.unexpandUnary : Unexpander
| `($_un $op $x) => do
  let x ← match x with | `([hvl_expr|$x]) => `(hvl_expr|$x) | _ => `(hvl_expr|@$x)
  match op with
    | `(UnOp.Not) => `([hvl_expr|!$x])
    | `(UnOp.Non) => `([hvl_expr|~$x])
    | `(UnOp.Iverson) => `([hvl_expr|[$x]])
    | `(UnOp.Parens) => `([hvl_expr|($x)])
    | _ => throw ()
| _ => throw ()

/-- info: [hvl_expr|!b + x * x + inf x: Int. (x + y)] -/
#guard_msgs in
#eval [hvl_expr|!b + x * x + inf x : Int. (x + y)]

/-- info: fun b ↦ [hvl_expr|!@b] : Expr → Expr -/
#guard_msgs in
#check fun b ↦ [hvl_expr|!@b]

open Lean in
@[app_unexpander Caesar.Expr.DeBruijn]
def Expr.unexpandDeBruijn : Unexpander
| `($(_) {index:=$n:num}) =>
  let name := s!"𝒹{Nat.toSubscriptString n.getNat}"
  let name := mkIdent $ Name.mkSimple name
  `([hvl_expr|$name:ident])
| _ => throw ()

/-- info: [hvl_expr|𝒹₀] -/
#guard_msgs in
#eval Expr.DeBruijn 0

end Caesar
