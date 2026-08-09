import Caesar.Syntax
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

namespace Caesar

@[simp]
def Expr.Subexprs (e : Expr) : Set Expr := {e} ∪ match e with
  | .Var _ => {}
  | .DeBruijn _ => {}
  | .Quant _ _ ex => ex.Subexprs
  | [hvl_expr|@x [@_ ↦ @y]] => x.Subexprs ∪ y.Subexprs
  | .Binary _ l r => l.Subexprs ∪ r.Subexprs
  | .Unary _ x => x.Subexprs
  | .Lit _ => {}
  | .Cast x => x.Subexprs
  | .Ite c t e => c.Subexprs ∪ t.Subexprs ∪ e.Subexprs
  | .Call _ args => ⋃ arg ∈ args, arg.Subexprs

@[simp]
def Expr.splitQuant' (op : QuantOp) (vars : List QuantVar) (e : Expr) : Expr :=
  match vars with
  | [] => e
  | x :: vars => .Quant op [x] (Expr.splitQuant' op vars e)

theorem Expr.splitQuant'_all_one : ∀ e' : (Expr.splitQuant' op vars e).Subexprs,
  (e'.val ∈ e.Subexprs) ∨
    match _ : e'.val with
    | .Quant op vars e => vars.length = 1
    | _ => true
:= by
  induction vars with
  | nil => simp_all
  | cons head tail ih => simp_all

@[simp]
def Expr.splitQuant (e : Expr) : Expr := match _ : e with
  | .Var x => .Var x
  | .DeBruijn x => .DeBruijn x
  | .Quant op vars e => splitQuant' op vars e.splitQuant
  | [hvl_expr|@x [@i ↦ @y]] =>
    [hvl_expr|@x.splitQuant [@i ↦ @y.splitQuant]]
  | .Binary op l r => .Binary op l.splitQuant r.splitQuant
  | .Unary op x => .Unary op x.splitQuant
  | .Lit l => .Lit l
  | .Cast x => .Cast x.splitQuant
  | .Ite c t e => .Ite c.splitQuant t.splitQuant e.splitQuant
  | .Call m args => .Call m (args.attach.map (·.val.splitQuant))
decreasing_by
  all_goals (try simp [Expr.Cast]; try omega)
  rename_i x
  obtain ⟨x, hx⟩ := x
  simp only
  have := List.sizeOf_lt_of_mem hx
  omega

theorem Expr.splitQuant_all_one (e : Expr) : ∀ e' : e.splitQuant.Subexprs,
  match _ : e'.val with
  | .Quant _ vars _ => vars.length = 1
  | _ => true
:= by
  simp
  induction e using splitQuant.induct <;> try simp_all
  next op vars e ih =>
    intro e' h
    split
    · have := Expr.splitQuant'_all_one (op:=op) (vars:=vars) (e:=e.splitQuant)
      simp_all
      replace this := this _ h
      simp_all
      rcases this with this | this
      · have := ih _ this
        simp_all
      · assumption
    · simp_all
  next => rintro e (he | he) <;> simp_all
  next op l r ihl ihr => rintro e (he | he) <;> simp_all
  next => rintro e ((he | he) | he) <;> simp_all
  next m args ih =>
    intro e₁ e₂ h₁ h₂
    exact ih e₂ h₁ e₁ h₂

def Expr.IsDeBruinjN (e : Expr) (n : DeBruijnIndex) : «Bool» := match _ : e with
  | .Var x => true
  | .DeBruijn x => x ≤ n
  | .Quant op vars e =>
    e.IsDeBruinjN (⟨n.index + vars.length⟩)
  | [hvl_expr|@x [@i ↦ @y]] =>
    x.IsDeBruinjN n ∧ y.IsDeBruinjN n
  | .Binary op l r => l.IsDeBruinjN n ∧ r.IsDeBruinjN n
  | .Unary op x => x.IsDeBruinjN n
  | .Lit l => true
  | .Cast x => x.IsDeBruinjN n
  | .Ite c t e => c.IsDeBruinjN n ∧ t.IsDeBruinjN n ∧ e.IsDeBruinjN n
  | .Call m args => args.attach.all (·.val.IsDeBruinjN n)
termination_by SizeOf.sizeOf e
decreasing_by
  all_goals (try simp [Expr.Cast]; try omega)
  rename_i x
  obtain ⟨x, hx⟩ := x
  simp only
  have := List.sizeOf_lt_of_mem hx
  omega

def QuantVar.IsDeBruinj (q : QuantVar) : «Bool» := match q with | .DeBrujin => true | _ => false

def Expr.IsDeBruinj (e : Expr) : Prop := ∀ e' ∈ e.Subexprs,
  match e' with
  | .Quant _ vars _ => vars.all (·.IsDeBruinj)
  | _ => true

def QuantVar.name (q : QuantVar) : Ident := match q with
  | .Shadow s => s
  | .Fresh v => v.name
  | .DeBrujin => ⟨"𝒟ℯℬ𝓇𝓊𝒾𝓃𝒿"⟩

@[simp]
def Expr.deBruinj' (e : Expr) (m : Ident → Option DeBruijnIndex) : Expr := match e with
  | .Var v => if let some i := m v then .DeBruijn i else .Var v
  | .Binary op l r =>
    let l := l.deBruinj' m
    let r := r.deBruinj' m
    .Binary op l r
  | [hvl_expr|@x [@i ↦ @y]] =>
    let x := x.deBruinj' m
    let y := y.deBruinj' m
    [hvl_expr|@x [@i ↦ @y]]
  | .Quant _ [] exp => exp.deBruinj' m
  | .Quant op (x :: vars) exp =>
    let exp := Expr.Quant op vars exp
    let exp := exp.deBruinj' (fun i ↦ if i = x.name then some 0 else m i |>.map (·.succ))
    .Quant op [.DeBrujin] exp
  | .Unary op x => .Unary op (x.deBruinj' m)
  | .Lit l => .Lit l
  | .Cast x => .Cast (x.deBruinj' m)
  | .Ite c t e => .Ite (c.deBruinj' m) (t.deBruinj' m) (e.deBruinj' m)
  | .Call f args => .Call f $ args.map (·.deBruinj' m)
  | .DeBruijn i => .DeBruijn i

def Expr.deBruinj (e : Expr) : Expr := e.deBruinj' default

theorem Expr.deBruinj'_IsDeBruinj : (Expr.deBruinj' e m).IsDeBruinj := by
  induction e, m using Expr.deBruinj'.induct <;> try simp_all [IsDeBruinj]
  next m op l r ihl ihr => aesop
  next m i x y ihx ihy => aesop
  next m op q vars exp exp' ihs => exact And.symm ⟨ihs, rfl⟩
  next m c t e ihc iht ihe => aesop
  next m f args ih => exact fun a x a_1 a_2 ↦ ih x a_1 a a_2

theorem Expr.deBruinj_IsDeBruinj : (Expr.deBruinj e).IsDeBruinj := Expr.deBruinj'_IsDeBruinj

/-- info: [hvl_expr|inf dbj. 𝒹₀] -/
#guard_msgs in
#eval [hvl_expr|inf x : Int. x].deBruinj

/-- info: [hvl_expr|inf dbj. inf dbj. (𝒹₁ + 𝒹₀)] -/
#guard_msgs in
#eval [hvl_expr|inf x : Int. inf y : Int. (x + y)].deBruinj

def Expr.StructuralEquiv (e₁ e₂ : Expr) : «Bool» :=
  match e₁, e₂ with
  | .Var v₁, .Var v₂ => v₁ = v₂
  | .Binary op₁ l₁ r₁, .Binary op₂ l₂ r₂ => op₁ = op₂ ∧ l₁.StructuralEquiv l₂ ∧ r₁.StructuralEquiv r₂
  | _, _ => false

def Expr.normalize (e : Expr) : Expr := match e with
  | .Var v => .Var v
  | .Lit l => .Lit l
  | [hvl_expr|@x [@i ↦ @y]] => sorry

structure Expr.Equiv (e₁ e₂ : Expr) : Prop where
  prop : e₁.normalize.StructuralEquiv e₂.normalize

def Expr.is_const : Expr → «Bool»
| _ => false

structure TyCtx where
  fresh_counter : Nat
deriving Inhabited

abbrev TyEnv (α : Type) := StateM TyCtx α

inductive Qq where | Inf | Sup

def QuantVar.getShadow : QuantVar → Option Ident | .Shadow s => some s | _ => none

def Expr.subst (e : Expr) (iter : List (Ident × Expr)) : Expr :=
  iter.foldl (fun acc (lhs, rhs) ↦ [hvl_expr|@acc [@lhs ↦ @rhs]]) e

/-- info: [hvl_expr|(x + y)[x ↦ z][z ↦ w]] -/
#guard_msgs in
#eval [hvl_expr|(x + y)].subst [(⟨"x"⟩, [hvl_expr|z]), (⟨"z"⟩, [hvl_expr|w])]

def Expr.subst_by (e : Expr) (idents : List Ident) (f : Ident → TyEnv Expr) : TyEnv Expr :=
  return e.subst (← idents.mapM fun ident ↦ return (ident, ← f ident))

instance : ToString Ident where
  toString i := i.name

def TyCtx.fresh_ident (cx : TyCtx) (ident : Ident) : Ident × TyCtx :=
  (⟨s!"{ident}𝒻{Nat.toSubscriptString cx.fresh_counter}"⟩, {cx with fresh_counter := cx.fresh_counter + 1})

def TyEnv.fresh_ident (ident : Ident) : TyEnv Ident := do
  let s ← get
  let (i, s) := s.fresh_ident ident
  set s
  return i

def TyEnv.clone_var (ident : Ident) (kind : VarKind) : TyEnv Ident := do
  let new_ident := ← TyEnv.fresh_ident ident
  -- TODO: stuff here
  return new_ident

def elim_quant (vars : List QuantVar) (opr : Expr) : TyEnv Expr :=
  let idents := vars.filterMap QuantVar.getShadow
  opr.subst_by idents fun ident ↦ do
    let clone_var ← TyEnv.clone_var ident .Quant
    let fresh_ident := clone_var
    return .Var fresh_ident

def Expr.qelim : Qq → Expr → TyEnv Expr
-- Inf
| .Inf, .Var i => return .Var i
| .Inf, .Call n args => return .Call n args
| .Inf, .Ite c lhs rhs => return .Ite c (← lhs.qelim .Inf) (← rhs.qelim .Inf)
| .Inf, .Binary op a b => match op with
  | .Add
  | .And
  | .Or
  | .Inf
  | .Sup =>
    return .Binary op (← a.qelim .Inf) (← b.qelim .Inf)
  | .Mul => if a.is_const then return .Binary op a (← b.qelim .Inf) else return .Binary op a b
  | .Impl | .Compare =>
      return .Binary op (← a.qelim .Sup) (← b.qelim .Inf)
  | _ => return .Binary op a b
| .Inf, .Unary op opr =>
  if op = .Not then return .Unary op (← opr.qelim .Sup) else return .Unary op opr
| .Inf, .Cast inner => return .Cast (← inner.qelim .Inf)
| .Inf, .Quant op vars opr => match op with
  | .Inf | .Forall =>
    return ← elim_quant vars (← opr.qelim .Inf)
  | _ => return .Quant op vars opr
| .Inf, .Subst a b c => return .Subst a b c
| .Inf, .Lit a => return .Lit a
| .Inf, .DeBruijn i => return .DeBruijn i
-- Sup
| .Sup, .Var i => return .Var i
| .Sup, .Call n args => return .Call n args
| .Sup, .Ite c lhs rhs => return .Ite c (← lhs.qelim .Sup) (← rhs.qelim .Sup)
| .Sup, .Binary op a b => match op with
  | .Add
  | .And
  | .Or
  | .Inf
  | .Sup =>
    return .Binary op (← a.qelim .Sup) (← b.qelim .Sup)
  | .Mul => if a.is_const then return .Binary op a (← b.qelim .Sup) else return .Binary op a b
  | .CoImpl | .CoCompare =>
      return .Binary op (← a.qelim .Inf) (← b.qelim .Sup)
  | _ => return .Binary op a b
| .Sup, .Unary op opr =>
  if op = .Non then return .Unary op (← opr.qelim .Inf) else return .Unary op opr
| .Sup, .Cast inner => return .Cast (← inner.qelim .Sup)
| .Sup, .Quant op vars opr => match op with
  | .Sup | .Exists =>
    return ← elim_quant vars (← opr.qelim .Sup)
  | _ => return .Quant op vars opr
| .Sup, .Subst a b c => return .Subst a b c
| .Sup, .Lit a => return .Lit a
| .Sup, .DeBruijn i => return .DeBruijn i

def TyEnv.eval {α : Type} (f : TyEnv α) : α := (f default).fst

instance : MonadEval TyEnv IO := ⟨(pure ·.eval)⟩

/-- info: [hvl_expr|inf shadow x. x] -/
#guard_msgs in
#eval [hvl_expr|inf shadow x. x]

/-- info: [hvl_expr|(x + x)[x ↦ x𝒻₀]] -/
#guard_msgs in
#eval [hvl_expr|inf shadow x. (x + x)].qelim .Inf

section Subst

def Expr.free_vars (e : Expr) : List Ident := match e with
  | .Var x => [x]
  | _ => []

structure SubstFrame where
  substs : Std.HashMap Ident Expr
  free_vars : Std.HashSet Ident
deriving Inhabited

structure Subst where
  cur : SubstFrame
  stack : List SubstFrame
deriving Inhabited
def Subst.push_subst (s : Subst) (i : Ident) (x : Expr) : Subst :=
  let free_vars : Std.HashSet Ident := Std.HashSet.ofList x.free_vars
  ⟨{s.cur with free_vars := free_vars ∪ s.cur.free_vars, substs := s.cur.substs.insert i x}, s.cur :: s.stack⟩
def Subst.push_quant (s : Subst) (vars : List QuantVar) : TyEnv (List QuantVar × Subst) := do
  let fresh ← vars.mapM (TyEnv.fresh_ident ·.name)
  return Id.run do
    let mut s := {s with stack := s.cur :: s.stack}
    let mut new_vars : List QuantVar := []
    for (var, i) in vars.zipIdx do
      let ident := var.name
      s ← {s with cur := {s.cur with substs := s.cur.substs.erase ident}}
      if s.cur.free_vars.contains ident then
        let new_ident : Ident := fresh[i]!
        let new_expr : Expr := .Var new_ident
        new_vars ← .Shadow new_ident :: new_vars
        s ← {s with cur := {s.cur with substs := s.cur.substs.insert ident new_expr}}
      else
        new_vars ← var :: new_vars
    return (new_vars, s)

def Subst.push_quant' (cx : TyCtx) (s : Subst) (vars : List QuantVar) : (List QuantVar × Subst × TyCtx) :=
  vars.foldl (init := ([], {s with stack := s.cur :: s.stack}, cx)) fun (new_vars, s, cx) var ↦
    let ident := var.name
    let s := {s with cur :={s.cur with substs := s.cur.substs.erase ident}}
    if s.cur.free_vars.contains ident then
      let (new_ident, cx) := cx.fresh_ident ident
      let new_expr : Expr := .Var new_ident
      (.Shadow new_ident :: new_vars, {s with cur := {s.cur with substs := s.cur.substs.insert ident new_expr}}, cx)
    else
      (var :: new_vars, s, cx)

def Subst.lookup_var (s : Subst) (ident : Ident) : Option Expr :=
  s.cur.substs.get? ident

def Expr.perform_subst (e : Expr) (subst : Caesar.Subst) : TyEnv Expr := match e with
  | .Var x => return if let some e' := subst.lookup_var x then e' else e
  | .DeBruijn i => return .DeBruijn i
  | .Quant op vars e => do
    let (vars, subst) ← subst.push_quant vars
    return .Quant op vars (← e.perform_subst subst)
  | [hvl_expr|@x [@i ↦ @y]] => do
    let y' := ← y.perform_subst subst
    x.perform_subst (subst.push_subst i y')
  | .Binary op l r => return .Binary op (← l.perform_subst subst) (← r.perform_subst subst)
  | .Unary op x => return .Unary op (← x.perform_subst subst)
  | .Lit l => return .Lit l
  | .Cast x => return .Cast (← x.perform_subst subst)
  | .Ite c t e => return .Ite (← c.perform_subst subst) (← t.perform_subst subst) (← e.perform_subst subst)
  | .Call m args => return .Call m (← args.mapM (·.perform_subst subst))

def Expr.perform_subst' (e : Expr) (cx : TyCtx) (subst : Caesar.Subst) : Expr × TyCtx := match e with
  | .Var x => (if let some e' := subst.lookup_var x then e' else e, cx)
  | .DeBruijn i => (.DeBruijn i, cx)
  | .Quant op vars e =>
    let (vars, subst, cx) := subst.push_quant' cx vars
    let (e, cx) := e.perform_subst' cx subst
    (.Quant op vars e, cx)
  | [hvl_expr|@x [@i ↦ @y]] =>
    let (y', cx) := y.perform_subst' cx subst
    x.perform_subst' cx (subst.push_subst i y')
  | .Binary op l r =>
    let (l, cx) := l.perform_subst' cx subst
    let (r, cx) := r.perform_subst' cx subst
    (.Binary op l r, cx)
  | .Unary op x =>
    let (x, cx) := x.perform_subst' cx subst
    (.Unary op x, cx)
  | .Lit l => (.Lit l, cx)
  | .Cast x => let (x, cx) := x.perform_subst' cx subst; (.Cast x, cx)
  | .Ite c t e =>
    let (c, cx) := c.perform_subst' cx subst
    let (t, cx) := t.perform_subst' cx subst
    let (e, cx) := e.perform_subst' cx subst
    (.Ite c t e, cx)
  | .Call m args =>
    let (args, cx) := args.foldl (init := ([], cx)) fun (args, cx) arg ↦
      let (arg, cx) := arg.perform_subst' cx subst
      (arg :: args, cx)
    (.Call m args, cx)

def Expr.apply_subst : Expr → TyEnv Expr := (·.perform_subst default)
def Expr.apply_subst' (cx : TyCtx) : Expr → Expr × TyCtx := (·.perform_subst' cx default)

/-- info: [hvl_expr|y] -/
#guard_msgs in
#eval [hvl_expr|x[x ↦ y]].apply_subst' default |>.1
/-- info: [hvl_expr|(inf shadow y. y + a + inf shadow y. y)] -/
#guard_msgs in
#eval [hvl_expr|(x + a + x)[x ↦ inf shadow y. y]].apply_subst' default |>.1

/-- info: [hvl_expr|(y + inf x: Int. (x + y))] -/
#guard_msgs in
#eval [hvl_expr|(x + inf x: Int. (x + y))[x ↦ y]].apply_subst' default |>.1

/-- info: [hvl_expr|(inf shadow x𝒻₀. (x𝒻₀ + x))] -/
#guard_msgs in
#eval [hvl_expr|(inf x: Int. (x + y))[y ↦ x]].apply_subst' default |>.1

end Subst

section Semantics

inductive Value where
  | Bool : «Bool» → Value
  | Int : «Int» → Value
  | Missing
deriving Inhabited

def Value.Bool? : Value → Option _root_.Bool
| .Bool b => some b
| _ => none
def Value.Int? : Value → Option _root_.Int
| .Int b => some b
| _ => none

structure Memory where
  values : Std.HashMap Ident Value

instance : Coe _root_.Bool Value where
  coe := .Bool

def Memory.subst (σ : Memory) (ident : Ident) (value : Value) : Memory :=
  ⟨σ.values.insert ident value⟩

def Expr.eval (e : Expr) (σ : Memory) : Option Value := match e with
  | .Var x => σ.values.get? x
  | [hvl_expr|!@e] => return !(← (← e.eval σ).Bool?)
  | [hvl_expr|(@e)] => e.eval σ
  -- | [hvl_expr|@l + @r] => return .Int $ (← (← l.eval σ).Int?) + (← (← r.eval σ).Int?)
  | [hvl_expr|@l + @r] => match _ : l.eval σ, r.eval σ with
    | some (.Int l), some (.Int r) => some (.Int (l + r))
    | _, _ => none
  | [hvl_expr|@x [@i ↦ @y]] => return ← x.eval (σ.subst i (← y.eval σ))
  | _ => none

/-- info: Caesar.Value.Int 3 -/
#guard_msgs in
#eval [hvl_expr|x + y].eval ⟨Std.HashMap.ofList [(⟨"x"⟩, .Int 1), (⟨"y"⟩, .Int 2)]⟩ |>.getD .Missing

/-- info: Caesar.Value.Int 4 -/
#guard_msgs in
#eval [hvl_expr|(x + y)[x ↦ y]].eval ⟨Std.HashMap.ofList [(⟨"x"⟩, .Int 1), (⟨"y"⟩, .Int 2)]⟩ |>.getD .Missing

theorem Expr.perform_subst_var : (Expr.Var x).perform_subst s = do match s.lookup_var x with | some x' => return x' | none => return Expr.Var x := by
  simp [TyEnv.eval, default, perform_subst, pure, StateT.pure]
  aesop

@[simp]
theorem asdasd (s : Subst) : (s.push_subst a x).lookup_var b = if a = b then some x else s.lookup_var b := by
  simp [Subst.push_subst, Subst.lookup_var]
  split_ifs
  · simp_all
  · simp_all [Std.HashMap.getElem?_insert]

@[simp] theorem asjhdasjhd : Subst.lookup_var default s = none := by simp [Subst.lookup_var, default]

def Subst.vars (s : Subst) : List Ident := s.cur.substs.keys

def Memory.subst' (σ : Memory) (s : Subst) : Memory :=
  let s' : Std.HashMap Ident Value := s.cur.substs.map (fun _ b ↦ b.eval σ |>.getD .Missing)
  ⟨σ.values ∪ s'⟩

protected def Std.HashMap.getElem_union {α : Type} {β : Type} [BEq α] [Hashable α] (m₁ m₂ : Std.HashMap α β) (j : α) : (m₁ ∪ m₂)[j]? = m₁[j]?.or m₂[j]? := by
  ext x
  simp [Std.HashMap.instUnion]
  simp [Std.HashMap.union]
  sorry

@[simp]
theorem ashdjashdj (σ : Memory) : (σ.subst' s).values[j]? = if let some e := s.lookup_var j then e.eval σ else σ.values.get? j := by
  ext v
  simp [Memory.subst']
  simp [Std.HashMap.getElem_union]
  split
  · simp_all
  · simp_all

theorem askjdas (e : Expr) : (e.perform_subst' cx s).1.eval σ = e.eval (σ.subst' s) := by
  ext v
  induction e, σ using Expr.eval.induct generalizing v cx s
  next σ j =>
    simp [Expr.apply_subst', Expr.perform_subst', Expr.eval]
    split <;> simp_all [Expr.eval]
  next σ x ih =>
    -- simp_all [Expr.eval]
    simp_all [Expr.perform_subst']
    simp [Expr.eval, Expr.perform_subst']

    simp_all [Expr.apply_subst, Expr.perform_subst, pure, StateT.pure, TyEnv.eval, Expr.eval, Value.Bool?]
    -- aesop
    sorry
  next σ e ih => simp_all [Expr.apply_subst', Expr.perform_subst', Expr.eval]
  next σ l r lv rv hl hr ihl ihr =>
    simp_all [Expr.apply_subst', Expr.perform_subst', Expr.eval, Value.Int?]
    split <;> split <;> simp_all <;> subst_eqs
    · congr!
      sorry
    ·
      rintro ⟨_⟩
      rename_i h _
      contrapose! h
      simp_all
      exists lv
      have := ihl (.Int lv)
      simp_all


      have := h lv rv
      simp at this

      have h₁ := ihr (.Int rv)
      have h₂ := ihl (.Int lv)
      simp at h₁ h₂
      simp_all
      sorry
  next =>
    simp_all
    sorry
  next =>
    simp_all [Expr.apply_subst', Expr.perform_subst', Expr.eval, Value.Int?]

    sorry

end Semantics

end Caesar
