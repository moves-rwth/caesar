import logging
import re
import shlex
import sys
from optparse import OptionParser
from typing import Set

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

        return super(CommentArgsCommand, self).invoke(ctx)


def _click_sysargs(ctx: click.Context) -> Set[str]:
    """
    Return the set of args given via the command-line. This is necessary to
    distinguish default values from non-default values in click's Context. With
    the `ParameterSource` in the as of yet unreleased click 8.0 this would be
    unnecessary. Oh well.
    """
    args_parser = ctx.command.make_parser(ctx)
    args_values, _args_args, _args_order = args_parser.parse_args(sys.argv[1:])
    return set(args_values.keys())


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

    try:
        args_values, _args_args, _args_order = args_parser.parse_args(
            shlex.split(args_str))
    except Exception as e:
        raise Exception(
            "exception occurred during parsing of description comment", e)
    sysargs = _click_sysargs(ctx)
    used_defaults = dict()
    encoding_command = group.get_command(ctx, args_values["encoding"])
    ctx.params["encoding"] = encoding_command.name

    # Using the built-in module 'optparse'
    # Because I couldn't find a way to do it with click
    encoding_parser = OptionParser()
    for param in encoding_command.params:
        action = "store"
        default = None
        if param.multiple:
            action = "append"
            default = []
        elif param.type == click.BOOL:
            action = "store_true"
            default = False

        encoding_parser.add_option(f"--{param.name}",
                                   dest=param.name,
                                   action=action,
                                   default=default)
    new_args_list = shlex.split(args_str)
    new_args_list.remove("--encoding")
    new_args_list.remove(args_values["encoding"])
    opts_values, _ = encoding_parser.parse_args(new_args_list)
    opts_dict = opts_values.__dict__

    for param, value in opts_dict.items():
        if param not in args_values and param not in sysargs:
            ctx.params[param] = opts_dict[param]
            used_defaults[param] = opts_dict[param]

    logging.getLogger("pgcl2heyvl").info(
        "using default arguments from file comments: %s", used_defaults)
