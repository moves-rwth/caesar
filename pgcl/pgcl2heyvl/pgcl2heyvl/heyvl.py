from abc import ABC, abstractmethod
from enum import Enum, auto
from textwrap import indent
from typing import Dict, List

import attr
from probably.pgcl.ast import BoolType, NatType, RealType, Type, Var


@attr.s
class HeyType(ABC):
    pass

    @abstractmethod
    def __str__(self) -> str:
        pass


@attr.s
class HeyURealType(HeyType):

    def __str__(self) -> str:
        return "UReal"


@attr.s
class HeyEURealType(HeyType):

    def __str__(self) -> str:
        return "EUReal"


@attr.s
class HeyUIntType(HeyType):

    def __str__(self) -> str:
        return "UInt"


@attr.s
class HeyBoolType(HeyType):

    def __str__(self) -> str:
        return "Bool"


@attr.s
class HeyExpr:
    expr: str = attr.ib()

    def embed(self) -> 'HeyExpr':
        return HeyExpr(f"?({self.expr})")

    def negate(self) -> 'HeyExpr':
        return HeyExpr(f"!({self.expr})")

    def __str__(self) -> str:
        return self.expr


@attr.s
class HeyInstr(ABC):
    pass

    @abstractmethod
    def __str__(self) -> str:
        pass


@attr.s
class HeyObject(ABC):
    pass

    @abstractmethod
    def __str__(self) -> str:
        pass


HeyBlock = List[HeyInstr]


def hey_block_str(block: HeyBlock) -> str:
    return "\n".join((str(instr) for instr in block))


def encode_typ(typ: Type) -> str:
    if isinstance(typ, BoolType):
        return HeyBoolType()
    if isinstance(typ, NatType):
        assert typ.bounds is None
        return HeyUIntType()
    if isinstance(typ, RealType):
        return HeyEURealType()
    raise Exception("unsupported type")


@attr.s
class HeyDecl(HeyInstr):
    name: Var = attr.ib()
    typ: Type = attr.ib()

    def __str__(self) -> str:
        return f"var {self.name}: {encode_typ(self.typ)}"


@attr.s
class HeySkip(HeyInstr):
    pass

    def __str__(self) -> str:
        return ""


@attr.s
class HeyAssign(HeyInstr):
    lhs: HeyExpr = attr.ib()
    rhs: HeyExpr = attr.ib()

    def __str__(self) -> str:
        return f"{self.lhs} = {self.rhs}"


class Direction(Enum):
    DOWN = 1
    UP = 2

    def flip(self) -> "Direction":
        if self == Direction.DOWN:
            return Direction.UP
        else:
            return Direction.DOWN

    def __str__(self) -> str:
        if self == Direction.DOWN:
            return ""
        else:
            return "co"


class Calculus(Enum):
    WP = auto()
    ERT = auto()
    WLP = auto()

    def __str__(self) -> str:
        if self == Calculus.WP:
            return "wp"
        elif self == Calculus.ERT:
            return "ert"
        else:
            return "wlp"


class Encoding(Enum):
    INVARIANT = auto()
    K_INDUCTION = auto()
    UNROLL = auto()
    PAST = auto()
    AST = auto()
    OMEGA = auto()
    OST = auto()

    def __str__(self):

        if self == Encoding.INVARIANT:
            return "invariant"
        elif self == Encoding.K_INDUCTION:
            return "k_induction"
        elif self == Encoding.UNROLL:
            return "unroll"
        elif self == Encoding.PAST:
            return "past"
        elif self == Encoding.AST:
            return "ast"
        elif self == Encoding.OMEGA:
            return "omega_invariant"
        elif self == Encoding.OST:
            return "ost"

@attr.s
class HeyHavoc(HeyInstr):
    direction: Direction = attr.ib()
    variables: List[Var] = attr.ib()

    def __str__(self) -> str:
        variable_list = ", ".join(self.variables)
        return f"{self.direction}havoc {variable_list}"


@attr.s
class HeyAssert(HeyInstr):
    direction: Direction = attr.ib()
    expr: HeyExpr = attr.ib()

    def __str__(self) -> str:
        return f"{self.direction}assert {self.expr}"


@attr.s
class HeyAssume(HeyInstr):
    direction: Direction = attr.ib()
    expr: HeyExpr = attr.ib()

    def __str__(self) -> str:
        return f"{self.direction}assume {self.expr}"


@attr.s
class HeyCompare(HeyInstr):
    direction: Direction = attr.ib()
    expr: HeyExpr = attr.ib()

    def __str__(self) -> str:
        return f"{self.direction}compare {self.expr}"


def _str_block(block: HeyBlock) -> str:
    hey_str = hey_block_str(block)
    if block == [] or hey_str == "":
        return "{}"
    return "{\n" + indent(hey_str, "    ") + "\n}"


@attr.s
class HeyValidate(HeyInstr):
    direction: Direction = attr.ib()

    def __str__(self) -> str:
        return f"{self.direction}validate"


@attr.s
class HeyNondet(HeyInstr):
    direction: Direction = attr.ib()
    branch1: HeyBlock = attr.ib()
    branch2: HeyBlock = attr.ib()

    def __str__(self) -> str:
        operator = "⊓" if self.direction == Direction.DOWN else "⊔"
        return f"if {operator} {_str_block(self.branch1)} else {_str_block(self.branch2)}"


@attr.s
class HeyIte(HeyInstr):
    cond: HeyExpr = attr.ib()
    branch1: HeyBlock = attr.ib()
    branch2: HeyBlock = attr.ib()

    def __str__(self) -> str:
        return f"if {self.cond} {_str_block(self.branch1)} else {_str_block(self.branch2)}"

    def encode(self) -> HeyInstr:
        "Encode this if-then-else instruction using a nondeterminstic choice."
        hey1: HeyBlock = [HeyAssert(Direction.DOWN, self.cond.embed())]
        hey1.extend(self.branch1)
        hey2: HeyBlock = [
            HeyAssert(Direction.DOWN,
                      self.cond.negate().embed())
        ]
        hey2.extend(self.branch2)
        return HeyNondet(Direction.DOWN, hey1, hey2)


@attr.s
class HeyProc(HeyObject):
    direction: Direction = attr.ib()
    proc_name: str = attr.ib()
    param: Dict[Var, HeyType] = attr.ib()
    out: Dict[Var, HeyType] = attr.ib()
    body: HeyBlock = attr.ib()
    pre: HeyExpr = attr.ib()
    post: HeyExpr = attr.ib()
    comment: str = attr.ib()

    def __str__(self) -> str:
        param_list = ", ".join(
            [f"{var_name}: {typ}" for (var_name, typ) in self.param.items()])

        out_list = ", ".join(
            [f"{var_name}: {typ}" for (var_name, typ) in self.out.items()])

        return (f"// {self.comment}\n" if self.comment != "" else "") \
               +f"{self.direction}proc {self.proc_name}({param_list}) -> ({out_list})" \
               +(f"\n    pre {self.pre}" if self.pre is not None else "") \
               +(f"\n    post {self.post}" if self.post is not None else "") \
               + f"\n{_str_block(self.body)}"


HeyObjects = List[HeyObject]


def hey_objects_str(procs: HeyObjects) -> str:
    return "\n\n".join((str(proc) for proc in procs))


@attr.s
class HeyNegate(HeyInstr):
    direction: Direction = attr.ib()

    def __str__(self) -> str:
        return f"{self.direction}negate"


@attr.s
class HeyTick(HeyInstr):
    expr: HeyExpr = attr.ib()

    def __str__(self) -> str:
        return f"tick {self.expr}"


@attr.s
class HeyComment(HeyObject, HeyInstr):
    comment: str = attr.ib()

    def __str__(self) -> str:
        # Two indents to differentiate between empty and filled lines
        return indent(
            indent(self.comment, "// ", lambda line: not line.isspace()), "//",
            lambda line: line.isspace())


@attr.s
class HeyEncodingAnnotation(HeyInstr):
    encoding: Encoding = attr.ib()
    args: List[HeyExpr] = attr.ib() 
    stmt: HeyInstr = attr.ib()
 

    def __str__(self):

        arg_list = ", ".join(
            [f"{arg}" for arg in self.args])
        
        return f"@{self.encoding}({arg_list})\n{self.stmt}" 


@attr.s 
class HeyCalculusAnnotation(HeyObject):
    calculus: Calculus = attr.ib()
    proc: HeyObject = attr.ib()

    def __str__(self) -> str:
        return f"@{self.calculus}\n{self.proc}"

@attr.s 
class HeyWhile(HeyInstr):
    cond: HeyExpr = attr.ib()
    body: HeyBlock = attr.ib()

    def __str__(self) -> str:
        return f"while {self.cond} {_str_block(self.body)}"
