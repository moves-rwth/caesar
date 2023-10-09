import logging
import re
import shlex
import sys
from typing import Callable

import click


# Define a custom command class which reads arguments from the first line of the
# input program. Adapted from kipro2.
#
# See https://stackoverflow.com/a/46391887
class CommentArgsCommand(click.Group):

    def invoke(self, ctx):
        program_path = ctx.params["file"]
        if program_path is not None:
            with open(program_path, "r") as program_file:
                program_code = program_file.read()
                _read_args_from_code(self, ctx, program_code)
        # del ctx.params["file"]
        return super(CommentArgsCommand, self).invoke(ctx)


def _list_after_first_match(list: list, predicate: Callable):
    for i in range(len(list)):
        if predicate(list[i]):
            return list[i:]
    return []


def _read_args_from_code(group: click.Group, ctx: click.Context, code: str):
    lines = code.splitlines()
    if len(lines) == 0:
        return
    match = re.fullmatch('(\\/\\/|#)\\s*ARGS:(.*\\-\\-(encoding|pre|post).*)',
                         lines[0])
    if match is None:
        return
    args_str = match.group(2)
    args_parser = ctx.command.make_parser(ctx)

    args_list = shlex.split(args_str)

    # A copy is passed because parse_args modifies the input list
    try:
        args_values, _args_args, _args_order = args_parser.parse_args(
            args_list.copy())
    except Exception as e:
        raise Exception(
            "exception occurred during parsing of description comment", e)

    encoding_command = group.get_command(ctx, args_values["encoding"])

    # Add "encoding" to the params to be able to invoke the corresponding function later im cmd.py
    ctx.params["encoding"] = encoding_command.name

    # Make a new parser for the specific encoding_command
    encoding_parser = encoding_command.make_parser(ctx)

    # Remove encoding parameter and parse again the new parser

    args_list.remove("--encoding")
    args_list.remove(args_values["encoding"])
    opts_values, _, _ = encoding_parser.parse_args(args_list)

    # Parse the command line args to overwrite file ARGS (if present)
    sysargs, _, _ = encoding_parser.parse_args(
        _list_after_first_match(sys.argv[2:], lambda x: x.startswith("--")))
    # Add "encoding" to the params to be able to invoke the corresponding function later im cmd.py
    ctx.params["encoding"] = encoding_command.name

    used_defaults = dict()
    for param in opts_values:
        # If not already parsed in the first round and
        # if not overwritten by CLI
        if param not in args_values:
            if param in sysargs:
                ctx.params[param] = sysargs[param]
                used_defaults[param] = sysargs[param]
            else:
                ctx.params[param] = opts_values[param]
    logging.getLogger("pgcl2heyvl").info(
        "using default arguments from file comments: %s", used_defaults)
