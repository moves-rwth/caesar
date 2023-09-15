import os
import sys
from typing import List, Union

import click
import probably.pgcl.substitute as substitute
from pgcl2heyvl.encode import (
    encode_ast_mciver,
    encode_k_ind,
    encode_omega_inv,
    encode_optional_stopping,
    encode_past,
)
from pgcl2heyvl.heyvl import Calculus, hey_objects_str
from pgcl2heyvl.utils import CommentArgsCommand
from probably.pgcl.ast import Expr, Program, WhileInstr
from probably.pgcl.check import CheckFail
from probably.pgcl.parser import parse_expectation, parse_pgcl
from probably.util.ref import Mut


@click.group(cls=CommentArgsCommand,
             help="""
    Convert a pGCL program into a HeyVL program.

    The pGCL programs are parsed by the probably library for probabilistic programming.
    """,
             invoke_without_command=True,
             context_settings={
                 'ignore_unknown_options': True,
                 'allow_extra_args': True
             })
@click.pass_context
@click.argument("file", type=click.Path(exists=True))
@click.option("--encoding", type=click.STRING)
def main(ctx, file, encoding, **kwargs):
    dispatcher = {
        'encode-ast': encode_ast,
        "encode-ost-rule": encode_ost_rule,
        "encode-past-rule": encode_past_rule,
        "encode-omega-invariant": encode_omega_invariant,
        "encode-k-induction": encode_k_induction
    }
    try:
        command = dispatcher[encoding]
    except KeyError:
        raise ValueError(f'invalid input: {encoding}')

    kwargs["file"] = file
    ctx.invoke(command, **kwargs)


@main.command(help="""
    Encode the proof for a lower/upper bound of an expectation of a pGCL loop using omega invariants.

    Supported combinations are
    -lower bound on 'ert',
    -lower bound on 'wp',
    -upper bound on 'wlp'.

    The user needs to provide the parameters '--invariant' and '--post'.

    Omega invariant must be parameterized by a variable named 'n'.

    Given program mustn't include 'n' as a variable name! This is a reserved variable for the omega invariant.
    If this condition is violated, this will result in an exception.

    """)
@click.argument('file', type=click.Path(exists=True))
@click.option('--calculus',
              type=click.STRING,
              help="The calculus for the encoding.",
              metavar="EXPR")
@click.option(
    '--invariant',
    type=click.STRING,
    help="The omega invariant for the proof rule with a parameter 'n'",
    metavar="EXPR")
@click.option('--post',
              help="The post expectation",
              type=click.STRING,
              metavar="EXPR")
def encode_omega_invariant(file, calculus: str, invariant: str, post: str):

    with open(file, 'r') as handle:
        program_source = handle.read()

    program = parse_pgcl(program_source)
    if isinstance(program, CheckFail):
        print("Error: Cannot parse program:", program)
        sys.exit(1)
    substitute.substitute_constants(program)

    if invariant is None:
        print("Error: You need to provide a --invariant parameter.")
        sys.exit(1)

    invariant_expr = parse_expectation_with_constants(program, invariant)
    if isinstance(invariant_expr, CheckFail):
        print("Error: Cannot parse invariant:", invariant_expr)
        return

    if post is None:
        print("Error: You need to provide a --post parameter.")
        sys.exit(1)

    post_expr = parse_expectation_with_constants(program, post)
    if isinstance(post_expr, CheckFail):
        print("Error: Cannot parse post expression:", post_expr)
        return

    if calculus == "wp":
        calculus_type = Calculus.WP
    elif calculus == "ert":
        calculus_type = Calculus.ERT
    elif calculus == "wlp":
        calculus_type = Calculus.WLP
    else:
        print("Error: unsupported calculus type")
        sys.exit(1)

    print(
        _auto_gen_comment(file) + hey_objects_str(
            encode_omega_inv(
                program,
                calculus_type,
                invariant_expr,
                post_expr,
            )))


@main.command(help="""
    Encode the proof for the positive almost-sure termination of a pGCL loop using the proof rule from Chakarov et al. (2013).

    The user needs to provide the parameters '--invariant', '--eps' and '--k'.

    The parameters eps and k must be positive numbers and eps must be smaller than k.
    """)
@click.argument('file', type=click.Path(exists=True))
@click.option('--invariant',
              type=click.STRING,
              help="The invariant for the proof rule",
              metavar="EXPR")
@click.option('--eps',
              help="The positive constant epsilon",
              type=click.STRING,
              metavar="EXPR")
@click.option('--k',
              help="The positive constant k",
              type=click.STRING,
              metavar="EXPR")
def encode_past_rule(file, invariant: str, eps: str, k: str):

    with open(file, 'r') as handle:
        program_source = handle.read()

    program = parse_pgcl(program_source)
    if isinstance(program, CheckFail):
        print("Error: Cannot parse program:", program)
        sys.exit(1)
    substitute.substitute_constants(program)

    if invariant is None:
        print("Error: You need to provide a --invariant parameter.")
        sys.exit(1)

    invariant_expr = parse_expectation_with_constants(program, invariant)
    if isinstance(invariant_expr, CheckFail):
        print("Error: Cannot parse invariant:", invariant_expr)
        return

    if eps is None:
        print("Error: You need to provide a --eps parameter.")
        sys.exit(1)
    eps_expr = parse_expectation_with_constants(program, eps)
    if isinstance(eps_expr, CheckFail):
        print("Error: Cannot parse eps:", eps_expr)
        return

    if k is None:
        print("Error: You need to provide a --k parameter.")
        sys.exit(1)
    k_expr = parse_expectation_with_constants(program, k)
    if isinstance(k_expr, CheckFail):
        print("Error: Cannot parse k:", k_expr)
        return

    print(
        _auto_gen_comment(file) +
        hey_objects_str(encode_past(program, invariant_expr, eps_expr, k_expr))
    )


@main.command(help="""
    Encode the proof for a lower bound of a weakest-preexpectation (wp) of a pGCL loop using the Optional Stopping Theorem from Hark et al. (2020).

    The user needs to provide the parameters '--invariant', '--past-invariant' and '--c'.

    The past-invariant is for checking that the program is positively almost-surely terminating by proving an upper bound to the expected runtime of the loop.

    This past-invariant should be strictly less than infinity. This condition is checked and the HeyVL program won't verify if this is not satisfied.

    """)
@click.argument('file', type=click.Path(exists=True))
@click.option('--post',
              help="The post-expectation.",
              type=click.STRING,
              metavar="EXPR")
@click.option('--invariant',
              type=click.STRING,
              help="The invariant for the weakest preexpectation lowerbound.",
              metavar="EXPR")
@click.option('--past-invariant',
              type=click.STRING,
              help="The invariant for the weakest preexpectation lowerbound.",
              metavar="EXPR")
@click.option(
    '--c',
    help=
    "The constant upper-bound for conditional difference boundedness condition.",
    type=click.STRING,
    metavar="EXPR")
def encode_ost_rule(file, post: str, invariant: str, past_invariant: str,
                    c: str):

    with open(file, 'r') as handle:
        program_source = handle.read()

    program = parse_pgcl(program_source)
    if isinstance(program, CheckFail):
        print("Error: Cannot parse program:", program)
        sys.exit(1)
    substitute.substitute_constants(program)

    if post is None:
        print("Error: You need to provide a --post parameter")
        sys.exit(1)

    post_expr = parse_expectation_with_constants(program, post)
    if isinstance(post_expr, CheckFail):
        print("Error parsing post:", post_expr)
        sys.exit(1)

    if invariant is None:
        print("Error: You need to provide a --invariant parameter.")
        sys.exit(1)

    invariant_expr = parse_expectation_with_constants(program, invariant)
    if isinstance(invariant_expr, CheckFail):
        print("Error: Cannot parse invariant:", invariant_expr)
        return

    if past_invariant is None:
        print("Error: You need to provide a --past-invariant parameter.")
        sys.exit(1)

    past_invariant_expr = parse_expectation_with_constants(
        program, past_invariant)
    if isinstance(past_invariant_expr, CheckFail):
        print("Error: Cannot parse past-invariant:", past_invariant_expr)
        return

    if c is None:
        print("Error: You need to provide a --c parameter.")
        sys.exit(1)
    c_expr = parse_expectation_with_constants(program, c)
    if isinstance(c_expr, CheckFail):
        print("Error: Cannot parse c:", c_expr)
        return

    print(
        _auto_gen_comment(file) + hey_objects_str(
            encode_optional_stopping(program, post_expr, invariant_expr,
                                     past_invariant_expr, c_expr)))


@main.command(help="""
    Encode the proof for the almost-sure termination of a pGCL loop using the proof rule from McIver et al. (2018).

    The user needs to provide the parameters '--variant', '--prob' and '--decrease'.

    The parameter '--invariant' is optional and it defines the lower bound for the termination probability.
    The user doesn't need to provide this parameter for proving universal almost-sure termination.
    The default value of the invariant is 'true' which provides a lower bound of 1 to the probability of termination.

    The parameters '--prob' and '--decrease' must be antitone functions where the free variable is 'v'.

    Given program mustn't include 'v' and 'l' as variable names! These are reserved variables for the probability and decrease functions.
    If this condition is violated, this will result in an exception.
    """)
@click.argument('file', type=click.Path(exists=True))
@click.option('--invariant',
              type=click.STRING,
              help="The invariant for the termination probability lowerbound.",
              default="true",
              metavar="EXPR")
@click.option('--variant',
              help="The supermartingale variant function.",
              type=click.STRING,
              metavar="EXPR")
@click.option('--prob',
              help="The probability function for the progress condition.",
              type=click.STRING,
              metavar="EXPR")
@click.option('--decrease',
              help="The decrease function for the progress condition.",
              type=click.STRING,
              metavar="EXPR")
def encode_ast(file, invariant: str, variant: str, prob: str, decrease: str):

    with open(file, 'r') as handle:
        program_source = handle.read()

    program = parse_pgcl(program_source)
    if isinstance(program, CheckFail):
        print("Error: Cannot parse program:", program)
        sys.exit(1)
    substitute.substitute_constants(program)

    invariant_expr = parse_expectation_with_constants(program, invariant)
    if isinstance(invariant_expr, CheckFail):
        print("Error: Cannot parse invariant:", invariant_expr)
        return

    if variant is None:
        print("Error: You need to provide a --variant parameter.")
        sys.exit(1)
    variant_expr = parse_expectation_with_constants(program, variant)
    if isinstance(variant_expr, CheckFail):
        print("Error: Cannot parse variant:", variant_expr)
        return

    if prob is None:
        print("Error: You need to provide a --prob parameter.")
        sys.exit(1)
    prob_expr = parse_expectation_with_constants(program, prob)
    if isinstance(prob_expr, CheckFail):
        print("Error: Cannot parse probability expression:", prob_expr)
        return

    if decrease is None:
        print("Error: You need to provide a --decrease parameter.")
        sys.exit(1)
    decrease_expr = parse_expectation_with_constants(program, decrease)
    if isinstance(decrease_expr, CheckFail):
        print("Error: Cannot parse decrease expression:", decrease_expr)
        return

    print(
        _auto_gen_comment(file) + hey_objects_str(
            encode_ast_mciver(program, invariant_expr, variant_expr, prob_expr,
                              decrease_expr)))


@main.command(help="""
    Encode the proof for lower/upper bound of an expectation of a pGCL loop using k-induction.

    At the moment, only upper bound proofs (wp/ert) are supported.

    Loops are encoded using k-induction and the user needs to provide the parameters `--k` and `--invariant` for each loop. Repeated parameters are assigned to the loops in a depth-first manner. When the input program consists only of one loop, the `--invariant` parameter for it must be omitted and the value of `--pre` will be used as its invariant.

    All parameters except for `FILE` can be written as a comment in the first line of the input file, like this:

        // ARGS: --post c --pre "c+0.999999" --k 2

    If no overriding parameters are passed via the command-line, parameters from such a leading comment will be used.
    """)
@click.argument('file', type=click.Path(exists=True))
@click.option('--post',
              type=click.STRING,
              help="The post-expectation.",
              metavar="EXPR")
@click.option('--pre',
              type=click.STRING,
              help="The upper bound to the pre-expectation.",
              metavar="EXPR")
@click.option('--calculus',
              type=click.STRING,
              help="The calculus for the encoding.",
              metavar="EXPR")
@click.option('--k',
              type=click.INT,
              multiple=True,
              help="The k for the k-induction encoding.")
@click.option('--invariant',
              type=click.STRING,
              multiple=True,
              help="The invariant for the k-induction encoding.",
              metavar="EXPR")
# pylint: disable=redefined-builtin
def encode_k_induction(file, post: str, pre: str, k: List[int], calculus: str,
                       invariant: List[str]):
    k = list(map(int, k))

    with open(file, 'r') as handle:
        program_source = handle.read()

    program = parse_pgcl(program_source)
    if isinstance(program, CheckFail):
        print("Error: Cannot parse program:", program)
        sys.exit(1)
    substitute.substitute_constants(program)

    if post is None:
        print("Error: You need to provide a --post parameter")
        sys.exit(1)

    post_expr = parse_expectation_with_constants(program, post)
    if isinstance(post_expr, CheckFail):
        print("Error parsing post:", post_expr)
        sys.exit(1)

    if pre is None:
        print("Error: You need to provide a --pre parameter.")
        sys.exit(1)
    pre_expr = parse_expectation_with_constants(program, pre)
    if isinstance(pre_expr, CheckFail):
        print("Error: Cannot parse pre:", pre_expr)
        return

    if calculus == "wp":
        calculus_type = Calculus.WP
    elif calculus == "ert":
        calculus_type = Calculus.ERT
    elif calculus == "wlp":
        calculus_type = Calculus.WLP
    else:
        print("Error: unsupported calculus type")
        sys.exit(1)

    invariant_expr: List[Expr] = []
    for inv in invariant:
        inv_expr = parse_expectation_with_constants(program, inv)
        if isinstance(inv_expr, CheckFail):
            print("Error: cannot parse invariant:", inv_expr)
            sys.exit(1)
        invariant_expr.append(inv_expr)

    if isinstance(program.instructions[0], WhileInstr) and len(
            program.instructions) == 1:
        invariant_expr = [pre_expr] + invariant_expr
    assert len(invariant_expr) > 0
    assert len(invariant_expr) == len(k)

    loop_annotations = list(zip(k, invariant_expr))

    print(
        _auto_gen_comment(file) + hey_objects_str(
            encode_k_ind(program, post_expr, pre_expr, calculus_type,
                         loop_annotations)))


def parse_expectation_with_constants(program: Program,
                                     source: str) -> Union[Expr, CheckFail]:
    "This is just like probably's `compile_expectation`, but we don't do type-checking here."
    expr = parse_expectation(source)
    if isinstance(expr, CheckFail):
        return expr
    expr_ref = Mut.alloc(expr)
    substitute.substitute_constants_expr(program, expr_ref)
    return expr_ref.val


def _auto_gen_comment(file):
    file_path, file_name = os.path.split(str(file))
    return f"// Auto-generated by pgcl2heyvl from {file_name}\n" + "//\n"
