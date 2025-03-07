import os
from functools import wraps
from typing import Union

import probably.pgcl.substitute as substitute
import pytest
from pgcl2heyvl.direct_encode import (
    direct_encode_ast_mciver,
    direct_encode_k_ind,
    direct_encode_omega_inv,
    direct_encode_optional_stopping,
    direct_encode_past,
)
from pgcl2heyvl.heyvl import Calculus, hey_objects_str
from probably.pgcl.ast import Expr, Program
from probably.pgcl.check import CheckFail
from probably.pgcl.parser import parse_expectation, parse_pgcl
from probably.util.ref import Mut

dirname = os.path.dirname(__file__)


@pytest.fixture
def save(request):
    return request.config.getoption("--overwrite-golden")


# modified from https://tbenthompson.com/post/how_i_test/
def golden_test():

    def decorator(test_fnc):

        @wraps(test_fnc)
        def wrapper(save):
            result = test_fnc(save) + "\n"
            test_name = test_fnc.__name__
            filename = os.path.join(dirname, 'golden_files', 'outputs',
                                    test_name + '.heyvl')
            is_exist = os.path.exists(filename)
            open_type = "r+" if is_exist else "w+"
            with open(filename, open_type) as f:
                if save or not is_exist:
                    f.seek(0)
                    f.truncate()
                    f.write(result)
                    correct_file = result
                else:
                    correct_file = f.read()
            assert correct_file == result

        return wrapper

    return decorator


@golden_test()
def test_encode_ast_mciver(save):
    with open(f"{dirname}/golden_files/inputs/test_ast.pgcl", 'r') as handle:
        program_source = handle.read()
    program = parse_pgcl(program_source)
    invariant = _parse_expectation_with_constants(program, "true")
    variant = _parse_expectation_with_constants(program, "x")
    prob = _parse_expectation_with_constants(program, "1/(v+1)")
    decrease = _parse_expectation_with_constants(program, "1")
    return hey_objects_str(
       direct_encode_ast_mciver(program, invariant, variant, prob, decrease))


@golden_test()
def test_encode_k_ind(save):
    with open(f"{dirname}/golden_files/inputs/test_k_ind.pgcl", 'r') as handle:
        program_source = handle.read()
    program = parse_pgcl(program_source)
    post_expr = _parse_expectation_with_constants(program, "totalFailed")
    pre_expr = _parse_expectation_with_constants(
        program,
        "[toSend <= 4] *(totalFailed + 1) + [not (toSend <= 4) * \\infty]")
    k = 5
    loop_annotations = [(k, pre_expr)]
    return hey_objects_str(
        direct_encode_k_ind(program=program,
                     post=post_expr,
                     pre=pre_expr,
                     calculus=Calculus.WP,
                     loop_annotations=loop_annotations))


@golden_test()
def test_encode_omega_inv(save):
    with open(f"{dirname}/golden_files/inputs/test_omega.pgcl", 'r') as handle:
        program_source = handle.read()
    program = parse_pgcl(program_source)
    invariant = _parse_expectation_with_constants(program, "[x <= n] * x")
    post = _parse_expectation_with_constants(program, "0")
    return hey_objects_str(
       direct_encode_omega_inv(program, Calculus.ERT, invariant, post))


@golden_test()
def test_encode_optional_stopping(save):
    with open(f"{dirname}/golden_files/inputs/test_ost.pgcl", 'r') as handle:
        program_source = handle.read()
    program = parse_pgcl(program_source)
    invariant = _parse_expectation_with_constants(program, "b + [a]")
    c = _parse_expectation_with_constants(program, "1")
    past_inv = _parse_expectation_with_constants(program, "2 * [a]")
    post_expr = _parse_expectation_with_constants(program, "b")
    return hey_objects_str(
        direct_encode_optional_stopping(program, post_expr, invariant, past_inv, c))


@golden_test()
def test_encode_past(save):
    with open(f"{dirname}/golden_files/inputs/test_past.pgcl", 'r') as handle:
        program_source = handle.read()
    program = parse_pgcl(program_source)
    invariant = _parse_expectation_with_constants(program, "x+1")
    eps = _parse_expectation_with_constants(program, "0.5")
    k = _parse_expectation_with_constants(program, "1")
    return hey_objects_str(direct_encode_past(program, invariant, eps, k))


def _parse_expectation_with_constants(program: Program,
                                      source: str) -> Union[Expr, CheckFail]:
    "This is just like probably's `compile_expectation`, but we don't do type-checking here."
    expr = parse_expectation(source)
    if isinstance(expr, CheckFail):
        return expr
    expr_ref = Mut.alloc(expr)
    substitute.substitute_constants_expr(program, expr_ref)
    return expr_ref.val
