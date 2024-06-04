import copy
from fractions import Fraction
from textwrap import indent
from typing import Dict, List, Set, Tuple, Union

# trunk-ignore(flake8/F401)
from pgcl2heyvl.heyvl import (
    Calculus,
    Direction,
    HeyAssert,
    HeyAssign,
    HeyAssume,
    HeyBlock,
    HeyBoolType,
    HeyComment,
    HeyCompare,
    HeyDecl,
    HeyEURealType,
    HeyExpr,
    HeyHavoc,
    HeyInstr,
    HeyIte,
    HeyNegate,
    HeyNondet,
    HeyObjects,
    HeyProc,
    HeySkip,
    HeyTick,
    HeyType,
    HeyUIntType,
    HeyURealType,
    HeyValidate,
)
from probably.pgcl.ast import (
    AsgnInstr,
    Binop,
    BinopExpr,
    BoolLitExpr,
    BoolType,
    CategoricalExpr,
    ChoiceInstr,
    CUniformExpr,
    DUniformExpr,
    Expr,
    IfInstr,
    Instr,
    NatLitExpr,
    NatType,
    Program,
    RealLitExpr,
    RealType,
    SkipInstr,
    SubstExpr,
    TickInstr,
    Type,
    Unop,
    UnopExpr,
    Var,
    VarExpr,
    WhileInstr,
)
from probably.pgcl.substitute import substitute_expr
from probably.pgcl.ast.walk import Walk, walk_expr, walk_instrs
from probably.util.ref import Mut

_encode_direction: Direction = Direction.DOWN
_loop_annotation_stack: List[Tuple[int, Expr]] = []
_bmc: bool = False


def encode_k_ind(program: Program, post: Expr, pre: Expr, calculus: Calculus,
                 loop_annotations: List[Tuple[int, Expr]]) -> HeyObjects:
    """
    Encode the proof for a lower/upper bound of an expectation of a pGCL loop using k-induction.

    Parameters
    ----------

    program: Program
        The pGCL Program to be encoded.
    invariant: Expr
        The loop invariant.
    post: Expr
        The post expectation.
    pre: Expr
        The pre expectation.
    direction: Direction
    loop_annotations: List[Tupe[int,Expr]]

    Returns
    -------
    HeyObjects
        Encoding of the proof using k-induction.

    """
    hey_post = _encode_expr(post)

    # Replace the variables with their initial versions before encoding
    hey_init_pre = _encode_expr(_to_init_expr(pre))

    global _encode_direction

    if calculus == Calculus.WLP:
        _encode_direction = Direction.DOWN
    elif calculus == Calculus.WP or calculus == Calculus.ERT:
        _encode_direction = Direction.UP
    else:
        raise Exception("unsupported calculus.")

    global _loop_annotation_stack
    assert len(_loop_annotation_stack) == 0
    _loop_annotation_stack = [(k, _encode_expr(inv))
                              for (k, inv) in loop_annotations]

    prob_choice_decl = []
    if _has_prob_choices(program):
        prob_choice_decl = [HeyDecl("prob_choice", BoolType())]

    if calculus != Calculus.ERT:
        _remove_tick_instrs(program)

    return [
        HeyComment(
            "HeyVL file to show\n" +
            f"    {str(_encode_expr(pre))} {'>=' if _encode_direction == Direction.UP else '<='} {calculus}[C]({str(hey_post)})\n"
            +
            f"using k-induction with {', '.join([f'k = {k} and invariant = {_encode_expr(inv)}' for (k,inv) in loop_annotations])}\n"
            + "for the pGCL program C:\n\n" +
            f"{indent(str(program), '    ')}"),
        _encode_proc(name="k_induction",
                     body=prob_choice_decl + _encode_init_assign(program) +
                     _encode_instrs(program.instructions),
                     input=_encode_var_dict(_get_init_vars(program)),
                     output=_encode_var_dict(program.variables),
                     direction=_encode_direction,
                     pre=hey_init_pre,
                     post=hey_post)
    ]


def encode_bounded_mc(program: Program, post: Expr, pre: Expr,
                      calculus: Calculus,
                      loop_annotations: List[Tuple[int, Expr]]) -> HeyObjects:
    """
    Encode the proof for refuting a lower/upper bound of an expectation of a pGCL loop using bounded model checking.

    Parameters
    ----------

    program: Program
        The pGCL Program to be encoded.
    invariant: Expr
        The loop invariant.
    post: Expr
        The post expectation.
    pre: Expr
        The pre expectation.
    direction: Direction
    loop_annotations: List[Tupe[int,Expr]]

    Returns
    -------
    HeyObjects
        Encoding of the proof using k-induction.

    """
    hey_post = _encode_expr(post)

    # Replace the variables with their initial versions before encoding
    hey_init_pre = _encode_expr(_to_init_expr(pre))

    global _encode_direction

    if calculus == Calculus.WLP:
        _encode_direction = Direction.DOWN
    elif calculus == Calculus.WP or calculus == Calculus.ERT:
        _encode_direction = Direction.UP
    else:
        raise Exception("unsupported calculus.")

    # Set the bmc flag to true, the rest is the same as k-induction
    global _bmc
    _bmc = True

    global _loop_annotation_stack
    assert len(_loop_annotation_stack) == 0
    _loop_annotation_stack = [(k, _encode_expr(inv))
                              for (k, inv) in loop_annotations]

    prob_choice_decl = []
    if _has_prob_choices(program):
        prob_choice_decl = [HeyDecl("prob_choice", BoolType())]

    if calculus != Calculus.ERT:
        _remove_tick_instrs(program)

    return [
        HeyComment(
            "HeyVL file to show that\n" +
            f"    {str(_encode_expr(pre))} {'>=' if _encode_direction == Direction.UP else '<='} {calculus}[C]({str(hey_post)})\n"
            + "DOES NOT HOLD\n" +
            f"using bounded model checking with {', '.join([f'k = {k} and invariant = {_encode_expr(inv)}' for (k,inv) in loop_annotations])}\n"
            + "for the pGCL program C:\n\n" +
            f"{indent(str(program), '    ')}"),
        _encode_proc(name="bounded_model_checking",
                     body=prob_choice_decl + _encode_init_assign(program) +
                     _encode_instrs(program.instructions),
                     input=_encode_var_dict(_get_init_vars(program)),
                     output=_encode_var_dict(program.variables),
                     direction=_encode_direction,
                     pre=hey_init_pre,
                     post=hey_post)
    ]


def encode_ast_mciver(program: Program, invariant: Expr, variant: Expr,
                      prob: Expr, decrease: Expr) -> HeyObjects:
    """
    Encode the proof rule for almost-sure termination of a pGCL loop
    by McIver et al. (2018)

    Parameters
    ----------

    program: Program
        The pGCL Program to be encoded.
    invariant: Expr
        The loop invariant.
    variant: Expr
        The variant function.
    prob: Expr
        The antitone probability function.
    decrease: Expr
        The antitone decrease function.

    Returns
    -------
    HeyObjects
        Encoding of the proof using the proof rule from McIver (2018).


    """

    # There should be only one loop in the program
    loops_in_program = [
        loop for loop in program.instructions if isinstance(loop, WhileInstr)
    ]
    assert len(loops_in_program) == 1
    loop = loops_in_program[0]

    prob_choice_decl = []
    if _has_prob_choices(program):
        prob_choice_decl = [HeyDecl("prob_choice", BoolType())]

    if "v" in program.variables or "l" in program.variables:
        raise Exception("Program mustn't include a variable named 'v' and 'l'")

    # Encode expressions into HeyLo expressions
    hey_variant = _encode_expr(variant)
    hey_loop_cond = _encode_expr(loop.cond)

    # Substitute variables with their init versions for the progress condition
    init_variant = _to_init_expr(variant)

    # [I] * [phi] * (p o V)
    progress_pre_expr = _times(
        _iverson(invariant),
        _times(_iverson(loop.cond), _substitute_vars(prob, {"v": variant})))

    # Replace all variables with their init versions for the preexpectation
    progress_pre_expr = _to_init_expr(progress_pre_expr)

    #  V <= V(s) - d(V(s))
    progress_post_expr = _iverson(
        _leq(
            variant,
            _minus(init_variant, _substitute_vars(decrease,
                                                  {"v": init_variant}))))

    free_var_name = "l"
    hey_prob_free_var = _encode_expr(
        _substitute_vars(prob, {"v": VarExpr(free_var_name)}))
    hey_decrease_free_var = _encode_expr(
        _substitute_vars(decrease, {"v": VarExpr(free_var_name)}))

    hey_prob = _encode_expr(prob)
    hey_decrease = _encode_expr(decrease)

    return [
        HeyComment(
            "HeyVL file to show that C is almost-surely terminating\n" +
            "using AST rule by McIver et al. (2018) with\n" +
            f"invariant = {_encode_expr(invariant)}, variant = {hey_variant}, probability function p(v) = {_encode_expr(prob)}, decrease function d(v) = {_encode_expr(decrease)}\n"
            + "for the pGCL program C:\n\n" +
            f"{indent(str(program), '    ')}"),
        # Check if prob is antitone
        _encode_proc(
            name="prob_antitone",
            body=[
                HeyAssert(
                    Direction.DOWN,
                    HeyExpr(
                        f"forall {free_var_name}: UReal.  (v <= {free_var_name}) ==> ({hey_prob_free_var} <= {hey_prob})"
                    ).embed())
            ],
            input=_encode_var_dict(program.variables) | {"v": HeyURealType()},
            direction=Direction.DOWN,
            comment=
            f"forall {free_var_name}. (v <= {free_var_name}) ==> (prob({free_var_name}) <= prob(v))"
        ),
        # Check if decrease is antitone
        _encode_proc(
            name="decrease_antitone",
            body=[
                HeyAssert(
                    Direction.DOWN,
                    HeyExpr(
                        f"forall {free_var_name}: UReal. (v <= {free_var_name}) ==> ({hey_decrease_free_var} <= {hey_decrease})"
                    ).embed())
            ],
            input=_encode_var_dict(program.variables) | {"v": HeyURealType()},
            direction=Direction.DOWN,
            comment=
            f"forall {free_var_name}. (v <= {free_var_name}) ==> (decrease({free_var_name}) <= decrease(v))"
        ),
        # Check that [I] is a wp-subinvariant of the loop w.r.t. [I]
        _encode_proc(name="I_wp_subinvariant",
                     body=prob_choice_decl + _encode_init_assign(program) +
                     _encode_iter(loop, None, []),
                     input=_encode_var_dict(_get_init_vars(program)),
                     output=_encode_var_dict(program.variables),
                     direction=Direction.DOWN,
                     pre=_encode_expr(_to_init_expr(_iverson(invariant))),
                     post=_encode_expr(_iverson(invariant)),
                     comment="[I] <= \\Phi_{[I]}([I])"),
        # Check that V = 0 indicates termination, i.e. !G iff V = 0
        _encode_proc(
            name="termination_condition",
            body=[
                HeyAssert(
                    Direction.DOWN,
                    HeyExpr(f"?(!({hey_loop_cond}) == ({hey_variant} == 0))"))
            ],
            input=_encode_var_dict(program.variables),
            direction=Direction.DOWN,
            comment="!G iff V = 0"),
        # Check that V is a wp-superinvariant of the loop w.r.t V
        _encode_proc(name="V_wp_superinvariant",
                     body=prob_choice_decl + _encode_init_assign(program) +
                     _encode_iter(loop, None, []),
                     input=_encode_var_dict(_get_init_vars(program)),
                     output=_encode_var_dict(program.variables),
                     direction=Direction.UP,
                     pre=_encode_expr(init_variant),
                     post=_encode_expr(variant),
                     comment="\\Phi_{V}(V) <= V"),
        # Check that V satisfies the progress condition
        _encode_proc(
            name="progress_condition",
            body=prob_choice_decl + _encode_init_assign(program) +
            _encode_instrs(loop.body),
            input=_encode_var_dict(_get_init_vars(program)),
            output=_encode_var_dict(program.variables),
            direction=Direction.DOWN,
            pre=_encode_expr(progress_pre_expr),
            post=_encode_expr(progress_post_expr),
            comment="[I] * [G] * (p o V) <= \\s. wp[P]([V <= V(s) - d(V(s))])(s)"
        )
    ]


def encode_past(program: Program, invariant: Expr, eps: Expr,
                k: Expr) -> HeyObjects:
    """
    Encode the proof rule for positive almost-sure termination
    by Chakarov et al. (2013)

    Parameters
    ----------
    program: Program
        The pGCL Program to be encoded.
    invariant: Expr
        The loop invariant.
    eps:Expr
    k:Expr

    Returns
    -------
    HeyObjects
        Encoding of the proof using the proof rule from Chakarov (2013).

    """

    loops_in_program = [
        loop for loop in program.instructions if isinstance(loop, WhileInstr)
    ]
    assert len(loops_in_program) == 1
    loop = loops_in_program[0]

    if isinstance(eps, (RealLitExpr, NatLitExpr)) and isinstance(
            k, (RealLitExpr, NatLitExpr)):
        if eps.value >= k.value:
            raise Exception("eps must be smaller than k.")
    else:
        raise Exception("k and eps must be constant positive numbers.")

    prob_choice_decl = []
    if _has_prob_choices(program):
        prob_choice_decl = [HeyDecl("prob_choice", BoolType())]

    # [!G] * I <= K
    hey_cond1_expr = _encode_expr(
        _leq(_times(_iverson(_neg(loop.cond)), invariant), k)).embed()

    # [G] * K <= [G] * I + [!G]
    hey_cond2_expr = _encode_expr(
        _leq(
            _times(_iverson(loop.cond), k),
            _plus(_times(_iverson(loop.cond), invariant),
                  _iverson(_neg(loop.cond))))).embed()
    # [G] * (I - eps)
    hey_cond3_pre = _encode_expr(
        _to_init_expr(_times(_iverson(loop.cond), _minus(invariant, eps))))

    return [
        HeyComment(
            "HeyVL file to show that C is positively almost-surely terminating\n"
            + "using PAST rule by Chakarov et al. (2013) with\n" +
            f"invariant = {_encode_expr(invariant)} eps = {_encode_expr(eps)} and k = {_encode_expr(k)}\n"
            + "for the pGCL program C:\n\n" +
            f"{indent(str(program), '    ')}"),
        # Condition 1: [!G] * I <= K
        _encode_proc(name="condition_1",
                     body=[HeyAssert(Direction.DOWN, hey_cond1_expr)],
                     input=_encode_var_dict(program.variables),
                     direction=Direction.DOWN,
                     comment="[!G] * I <= K"),
        # Condition 2: [G] * K <= [G] * I + [!G]
        _encode_proc(name="condition_2",
                     body=[HeyAssert(Direction.DOWN, hey_cond2_expr)],
                     input=_encode_var_dict(program.variables),
                     direction=Direction.DOWN,
                     comment="[G] * K <= [G] * I + [!G]"),
        # Condition 3: \Phi_0(I) <= [G] * (I - eps)
        _encode_proc(name="condition_3",
                     body=prob_choice_decl + _encode_init_assign(program) +
                     _encode_iter(loop, _encode_expr(invariant),
                                  _hey_const(_encode_expr(invariant))),
                     input=_encode_var_dict(_get_init_vars(program)),
                     output=_encode_var_dict(program.variables),
                     direction=Direction.UP,
                     pre=hey_cond3_pre,
                     post=HeyExpr("0"),
                     comment="\\Phi_0(I) <= [G] * (I - eps)")
    ]


def encode_optional_stopping(program: Program, post: Expr, invariant: Expr,
                             past_inv: Expr, c: Expr) -> HeyObjects:
    """
    Encodes the proof for a lower bound to the wp of a pGCL program using
    the optional stopping theorem from Aiming Low is Harder paper.

    Parameters
    ----------
    program: Program
        The pGCL Program to be encoded.
    invariant: Expr
        The loop invariant.
    past_inv: Expr
        The invariant for proving PAST of the loop.
    c:Expr
        The upperbound to the conditional difference boundedness condition.

    Returns
    -------
    HeyObjects
        Encoding of the proof using the optional stopping theorem.

    """
    loops_in_program = [
        loop for loop in program.instructions if isinstance(loop, WhileInstr)
    ]
    assert len(loops_in_program) == 1
    loop = loops_in_program[0]

    prob_choice_decl = []
    if _has_prob_choices(program):
        prob_choice_decl = [HeyDecl("prob_choice", BoolType())]

    init_invariant = _to_init_expr(invariant)

    return [
        HeyComment(
            "HeyVL file to show that\n" +
            f"    {_encode_expr(invariant)} <= wp[C]({_encode_expr(post)})\n" +
            "using the Optional Stopping Theorem from Aiming Low is Harder paper with\n"
            +
            f"invariant = {_encode_expr(invariant)}, c = {_encode_expr(c)} and\n"
            +
            f"past-invariant = {_encode_expr(past_inv)} is used to show that C is PAST by showing\n "
            + f"    {_encode_expr(past_inv)} >= ert[C](0)\n" +
            "for the pGCL program C:\n\n" + f"{indent(str(program), '    ')}"),
        _encode_proc(
            name="lt_infinity",
            body=[
                HeyAssert(
                    Direction.DOWN,
                    HeyExpr(f"{_encode_expr(past_inv)} < ?(true)").embed())
            ],
            input=_encode_var_dict(program.variables),
            direction=Direction.DOWN,
            comment="past_I < ∞"),
        _encode_proc(
            name="past",
            body=prob_choice_decl + _encode_init_assign(program) +
            # Inserted tick instruction to argue about ERT of the loop instead of WP/WLP
            _encode_iter(loop, _encode_expr(past_inv), [HeyTick(HeyExpr("1"))]
                         + _hey_const(_encode_expr(past_inv))),
            input=_encode_var_dict(_get_init_vars(program)),
            output=_encode_var_dict(program.variables),
            direction=Direction.UP,
            pre=_encode_expr(_to_init_expr(past_inv)),
            post=HeyExpr("0"),
            comment="\\Phi_{0}(past_I) <= past_I, so ert[P](0) <= past_I"),
        _encode_proc(
            name="conditional_difference_bounded",
            body=prob_choice_decl + _encode_init_assign(program) +
            _encode_instrs(loop.body),
            input=_encode_var_dict(_get_init_vars(program)),
            output=_encode_var_dict(program.variables),
            direction=Direction.UP,
            pre=_encode_expr(c),
            post=HeyExpr(
                f"ite({_encode_expr(_leq(init_invariant, invariant))}," +
                f"{_encode_expr(_minus(invariant, init_invariant))}," +
                f"{_encode_expr(_minus(init_invariant, invariant))})"),
            comment="wp[P](|I(s)-I|)(s) <= c"),
        _encode_proc(name="lower_bound",
                     body=prob_choice_decl + _encode_init_assign(program) +
                     _encode_iter(loop, _encode_expr(invariant),
                                  _hey_const(_encode_expr(invariant))),
                     input=_encode_var_dict(_get_init_vars(program)),
                     output=_encode_var_dict(program.variables),
                     direction=Direction.DOWN,
                     pre=_encode_expr(_to_init_expr(invariant)),
                     post=_encode_expr(post),
                     comment="I <= \\Phi_{post}(I)"),
        _encode_proc(
            name="harmonize_I_f",
            body=[
                HeyAssert(
                    Direction.DOWN,
                    HeyExpr(
                        f"!{_encode_expr(loop.cond)} ==> ({_encode_expr(invariant)} == {_encode_expr(post)})"
                    ).embed())
            ],
            input=_encode_var_dict(program.variables),
            direction=Direction.DOWN,
            comment="!guard ==> (I = f)",
        ),
        # Check if \Phi_f(I) < ∞,
        _encode_proc(name="loopiter_lt_infty",
                     body=[
                         HeyValidate(Direction.DOWN),
                         HeyAssume(Direction.DOWN, HeyExpr("\\infty"))
                     ] + prob_choice_decl + _encode_init_assign(program) +
                     _encode_iter(loop, invariant, _hey_const(invariant)),
                     input=_encode_var_dict(_get_init_vars(program)),
                     output=_encode_var_dict(program.variables),
                     direction=Direction.UP,
                     pre=HeyExpr("0"),
                     post=_encode_expr(post),
                     comment="\\Phi_f(I) < ∞")
    ]


def encode_omega_inv(program: Program, calculus: Calculus, invariant: Expr,
                     post: Expr) -> HeyObjects:
    """
    Encodes the proof for a lower/upper bound of an expectation of a pGCL loop using omega invariants.

    Parameters
    ----------
    program: Program
        The pGCL Program to be encoded.
    invariant: Expr
        The omega invariant sequence bound by a parameter 'n'
    post: Expr
        The post expectation.

    Returns
    -------
    HeyObjects
        Encoding of the proof using omega invariant.

    """
    loops_in_program = [
        loop for loop in program.instructions if isinstance(loop, WhileInstr)
    ]
    assert len(loops_in_program) == 1
    loop = loops_in_program[0]

    global _encode_direction

    if calculus == Calculus.WLP:
        _encode_direction = Direction.UP
    elif calculus == Calculus.WP or calculus == Calculus.ERT:
        _encode_direction = Direction.DOWN
    else:
        raise Exception("unsupported calculus.")

    prob_choice_decl = []
    if _has_prob_choices(program):
        prob_choice_decl = [HeyDecl("prob_choice", BoolType())]

    if "n" in program.variables:
        raise Exception("Program shouldn't include a variable named n")

    program.variables["n"] = NatType(bounds=None)

    if calculus != Calculus.ERT:
        _remove_tick_instrs(program)

    n_plus_1 = _plus(VarExpr("n"), NatLitExpr(1))
    # I_{n+1}
    next_invariant = _substitute_vars(copy.deepcopy(invariant),
                                      {"n": n_plus_1})
    # I_0
    null_invariant = _substitute_vars(copy.deepcopy(invariant),
                                      {"n": NatLitExpr(0)})

    operator = '>=' if _encode_direction == Direction.UP else '<='

    char_func_name = 'Psi' if _encode_direction == Direction.UP else 'Phi'

    if calculus == Calculus.WLP:
        top_or_bottom = 1
    elif calculus == Calculus.WP or calculus == Calculus.ERT:
        top_or_bottom = 0
    else:
        raise Exception("unsupported calculus.")

    return [
        HeyComment(
            "HeyVL file to show\n" +
            f"    (sup n. {_encode_expr(invariant)}) <= {calculus}[C]({_encode_expr(post)})\n"
            +
            f"using omega-invariant = {_encode_expr(invariant)} for the pGCL program C:\n\n"
            + f"{indent(str(program), '    ')}"),
        # I_0 <= Phi_{post}(0) or Psi_{post}(1) <= I_0
        _encode_proc(name="condition_1",
                     body=prob_choice_decl + _encode_init_assign(program) +
                     _encode_iter(loop, "0", _hey_const(top_or_bottom)),
                     input=_encode_var_dict(_get_init_vars(program)),
                     output=_encode_var_dict(program.variables),
                     direction=_encode_direction,
                     pre=_encode_expr(_to_init_expr(null_invariant)),
                     post=_encode_expr(post),
                     comment="I_0 " + operator + f" {char_func_name}" +
                     "_{post}" + f"({top_or_bottom})"),
        # for all n. I_{n+1} <= Phi_{post}(I_n)
        _encode_proc(name="condition_2",
                     body=prob_choice_decl + _encode_init_assign(program) +
                     _encode_iter(loop, _encode_expr(invariant),
                                  _hey_const(_encode_expr(invariant))),
                     input=_encode_var_dict(_get_init_vars(program)),
                     output=_encode_var_dict(program.variables),
                     direction=_encode_direction,
                     pre=_encode_expr(_to_init_expr(next_invariant)),
                     post=_encode_expr(post),
                     comment="for all n. I_{n+1} " + operator +
                     f" {char_func_name}" + "_{post}(I_n)"),
    ]


def _encode_decls(program: Program) -> HeyBlock:
    return [HeyDecl(name, typ) for (name, typ) in program.variables.items()]


def _get_init_vars(program: Program) -> Dict[Var, Type]:
    return {f"init_{name}": typ for (name, typ) in program.variables.items()}


def _encode_init_assign(program: Program) -> HeyBlock:
    return [
        HeyAssign(name, f"init_{name}")
        for (name, typ) in program.variables.items()
    ]


def _to_init_expr(expr: Expr) -> Expr:
    return _substitute_vars(
        expr, {var: VarExpr(f"init_{var}")
               for var in _expr_vars(expr)})


def _encode_expr(expr: Expr) -> HeyExpr:

    def inner_encode(expr: Expr):
        res = _encode_expr(expr)
        if isinstance(
                expr,
            (VarExpr, BoolLitExpr, NatLitExpr, RealLitExpr, UnopExpr)):
            return res
        else:
            return f"({res})"

    if isinstance(expr, VarExpr):
        return HeyExpr(expr.var)
    elif isinstance(expr, BoolLitExpr):
        return HeyExpr(str(expr))
    elif isinstance(expr, NatLitExpr):
        return HeyExpr(str(expr))
    elif isinstance(expr, RealLitExpr):
        if expr.is_infinite():
            return HeyExpr("∞")
        else:
            return HeyExpr(f"({str(expr)})" if "/" in str(expr) else str(expr))
    elif isinstance(expr, UnopExpr):
        if expr.operator == Unop.NEG:
            return HeyExpr(f"!{inner_encode(expr.expr)}")
        elif expr.operator == Unop.IVERSON:
            return HeyExpr(f"[{_encode_expr(expr.expr)}]")
    elif isinstance(expr, BinopExpr):
        operator = {
            Binop.OR: "||",
            Binop.AND: "&&",
            Binop.LEQ: "<=",
            Binop.LT: "<",
            Binop.EQ: "==",
            Binop.GT: ">",
            Binop.GEQ: ">=",
            Binop.PLUS: "+",
            Binop.MINUS: "-",
            Binop.TIMES: "*",
            Binop.DIVIDE: "/",
            Binop.MODULO: "%"
        }[expr.operator]
        return HeyExpr(
            f"{inner_encode(expr.lhs)} {operator} {inner_encode(expr.rhs)}")
    else:
        raise Exception(f"unsupported expr : {expr}")


def _encode_loop(loop: WhileInstr, invariant: HeyExpr, k: int) -> HeyBlock:
    global _bmc
    global _encode_direction

    modified_vars = _collect_modified_vars(loop.body)
    spec_or_empty = _encode_spec(invariant, modified_vars,
                                 invariant) if not _bmc else []

    if k <= 0:
        return spec_or_empty

    if _bmc:
        if _encode_direction == Direction.UP:
            const_prog = _hey_const(HeyExpr("0"))
        else:
            const_prog = _hey_const(HeyExpr("1"))
        next_iter = _encode_bmc(loop, invariant, k - 1, const_prog)
    else:
        const_prog = _hey_const(invariant)
        next_iter = _encode_extend(loop, invariant, k - 1, const_prog)

    return spec_or_empty + _encode_iter(loop, invariant, next_iter)


def _encode_iter(loop: WhileInstr, invariant: HeyExpr,
                 next_iter: HeyBlock) -> HeyBlock:
    return [
        HeyIte(_encode_expr(loop.cond),
               _encode_instrs(loop.body) + next_iter, [])
    ]


def _encode_var_typ(typ: Type) -> HeyType:
    if isinstance(typ, BoolType):
        return HeyBoolType()
    if isinstance(typ, NatType):
        assert typ.bounds is None
        return HeyUIntType()
    if isinstance(typ, RealType):
        return HeyEURealType()
    raise Exception("unsupported type")


def _encode_var_dict(vars: Dict[Var, Type]) -> Dict[Var, HeyType]:
    return {var: _encode_var_typ(typ) for (var, typ) in vars.items()}


def _encode_proc(name: str,
                 body: HeyBlock,
                 input: Dict[Var, HeyType],
                 direction: Direction,
                 pre: HeyExpr = None,
                 post: HeyExpr = None,
                 output: Dict[Var, HeyType] = {},
                 comment: str = "") -> HeyProc:
    global _encode_direction
    _encode_direction = direction
    return HeyProc(_encode_direction, name, input, output, body, pre, post,
                   comment)


def _hey_const(expr: HeyExpr) -> HeyBlock:
    return [
        HeyAssert(Direction.DOWN, expr),
        HeyAssume(Direction.DOWN, HeyExpr("0"))
    ]


def _encode_bmc(loop: WhileInstr, invariant: HeyExpr, k: int,
                next_iter: HeyBlock):
    if k == 0:
        return next_iter
    next_iter = _encode_bmc(loop, invariant, k - 1, next_iter)
    global _encode_direction
    return _encode_iter(loop, invariant, next_iter)


def _encode_extend(loop: WhileInstr, invariant: HeyExpr, k: int,
                   next_iter: HeyBlock) -> HeyBlock:
    if k == 0:
        return next_iter
    next_iter = _encode_extend(loop, invariant, k - 1, next_iter)
    global _encode_direction
    return [HeyAssert(_encode_direction.flip(), invariant)] + _encode_iter(
        loop, invariant, next_iter)


def _encode_spec(pre: HeyExpr, variables: List[Var],
                 post: HeyExpr) -> HeyBlock:
    global _encode_direction
    return [
        HeyAssert(_encode_direction, pre),
        HeyHavoc(_encode_direction, variables),
        HeyValidate(_encode_direction),
        HeyAssume(_encode_direction, post)
    ]


def _encode_instrs(instrs: List[Instr]) -> HeyBlock:

    def generate():
        for instr in instrs:
            res = _encode_instr(instr)
            if isinstance(res, list):
                yield from res
            else:
                yield res

    return list(generate())


def _encode_instr(instr: Instr) -> Union[Instr, List[Instr]]:
    if isinstance(instr, SkipInstr):
        return HeySkip()
    if isinstance(instr, WhileInstr):
        (k, invariant) = _loop_annotation_stack.pop(0)
        return _encode_loop(instr, invariant, k)
    if isinstance(instr, IfInstr):
        return HeyIte(_encode_expr(instr.cond), _encode_instrs(instr.true),
                      _encode_instrs(instr.false))
    if isinstance(instr, AsgnInstr):
        assert not isinstance(instr.rhs,
                              (CUniformExpr, DUniformExpr, CategoricalExpr))
        return HeyAssign(instr.lhs, _encode_expr(instr.rhs))
    if isinstance(instr, ChoiceInstr):
        return [
            HeyAssign("prob_choice",
                      HeyExpr(f"flip({_encode_expr(instr.prob)})")),
            HeyIte(HeyExpr("prob_choice"), _encode_instrs(instr.lhs),
                   _encode_instrs(instr.rhs))
        ]
    if isinstance(instr, TickInstr):
        return HeyTick(_encode_expr(instr.expr))
    raise Exception("unsupported instruction")


def _collect_modified_vars(instrs: List[Instr]) -> List[Var]:
    modified: Set[Var] = set()
    for ref in walk_instrs(Walk.DOWN, instrs):
        if isinstance(ref.val, AsgnInstr):
            modified.add(ref.val.lhs)
    return sorted(modified)


def _prob_to_odds(prob: Fraction) -> Tuple[int, int]:
    return (prob.numerator, prob.denominator - prob.numerator)


def _has_prob_choices(program: Program) -> bool:
    for instr_ref in walk_instrs(Walk.DOWN, program.instructions):
        if isinstance(instr_ref.val, ChoiceInstr):
            return True
    return False


def _remove_tick_instrs(program: Program):
    for instr_ref in walk_instrs(Walk.DOWN, program.instructions):
        if isinstance(instr_ref.val, TickInstr):
            instr_ref.val = SkipInstr()


def _iverson(expr: Expr) -> Expr:
    return UnopExpr(Unop.IVERSON, expr)


def _times(lhs: Expr, rhs: Expr) -> Expr:
    return BinopExpr(Binop.TIMES, lhs, rhs)


def _leq(lhs: Expr, rhs: Expr) -> Expr:
    return BinopExpr(Binop.LEQ, lhs, rhs)


def _le(lhs: Expr, rhs: Expr) -> Expr:
    return BinopExpr(Binop.LE, lhs, rhs)


def _minus(lhs: Expr, rhs: Expr) -> Expr:
    return BinopExpr(Binop.MINUS, lhs, rhs)


def _neg(expr: Expr) -> Expr:
    return UnopExpr(Unop.NEG, expr)


def _plus(lhs: Expr, rhs: Expr) -> Expr:
    return BinopExpr(Binop.PLUS, lhs, rhs)


def _substitute_vars(expr: Expr, mapping: Dict[Var, Expr]) -> Expr:
    # Substitute variables in an expression
    expr = copy.deepcopy(expr)
    expr_ref = Mut.alloc(SubstExpr(mapping, expr))
    substitute_expr(expr_ref)
    return expr_ref.val


def _expr_vars(expr: Expr) -> List[str]:
    # Find the vars in an expression
    return [
        ref.val.var for ref in walk_expr(Walk.DOWN, Mut.alloc(expr))
        if isinstance(ref.val, VarExpr)
    ]
