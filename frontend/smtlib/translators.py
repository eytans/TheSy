import typing
import itertools
import functools

from pysmt.typing import Type, BOOL

from .smtlib26 import SmtLib20ParserPlus
from pysmt.smtlib.parser import SmtLibScript
from pysmt.fnode import FNode
from pysmt.exceptions import PysmtTypeError
from pysmt.shortcuts import Symbol, FunctionType, ForAll, Equals, \
    Iff, Function, Bool, get_free_variables, TRUE, FALSE, Implies, get_env


class ThesyFromSmt(object):
    """
    Reads definition in SMTLIB-2.6 format and exports them in TheSy S-Expression
    syntax.
    """
    script: SmtLibScript

    def __init__(self, s: typing.TextIO):
        sym = get_env().formula_manager.get_or_create_symbol
        Nat, list_, Token = Type('Nat'), Type('list'), Type('Token')

        p = SmtLibDocumentParser()
        p.predeclare(sym('is-cons', FunctionType(BOOL, [list_])))  #
        p.predeclare(sym('is-succ', FunctionType(BOOL, [Nat])))    # hard-coded :/
        p.predeclare(sym('is-ESC',  FunctionType(BOOL, [Token])))  #

        self.script = p.get_script(s)
        self._fresh_cnt = itertools.count()

    def iter_datatypes(self):
        used = set(self.iter_used_types())
        for cmd in self.script:
            if cmd.name == 'declare-datatypes':
                params, defs = cmd.args
                if params: print("*** warning: datatype declaration with parameters")
                for a in defs:
                    if a[0] in used: yield self.export_datatype(a)

    def iter_decls(self):
        used = set(self.iter_used_symbols())
        for cmd in self.script:
            if cmd.name == 'declare-fun' and cmd.args[0] in used:
                yield self.export_func(cmd.args[0])
            if cmd.name == 'declare-const' and cmd.args[0] in used:
                yield self.export_const(cmd.args[0])

    def iter_rws(self):
        for cmd in self.script:
            if cmd.name == 'assert':
                for rule in self.export_rules(cmd.args[0]):
                    yield rule

    def iter_definitions(self):
        for cmd in self.script:
            if cmd.name == 'define-fun':
                for defin in self.export_rule_def(cmd.args):
                    yield defin

    def iter_rules(self):
        for cmd in self.script:
            if cmd.name == 'define-fun':
                for defin in self.export_rule_def(cmd.args):
                    yield defin
            if cmd.name == 'assert':
                for rule in self.export_rules(cmd.args[0]):
                    yield rule

    def iter_goals(self):
        for cmd in self.script:
            if cmd.name == 'assert':
                for goal in self.export_goals(cmd.args[0]):
                    yield goal

    def iter_used_symbols(self):
        for cmd in self.script:
            if cmd.name == 'assert':
                for v in get_free_variables(cmd.args[0]):
                    yield v

    def iter_used_types(self):
        for cmd in self.script:
            if cmd.name == 'assert':
                formula = cmd.args[0]
                while formula.is_forall():
                    for v in formula.quantifier_vars(): yield v.symbol_type()
                    formula = formula.args()[0]

    def __iter__(self):
        for dt in self.iter_datatypes():
            yield dt
        for dl in self.iter_decls():
            yield dl
        for rule in self.iter_rules():
            yield rule
        for goal in self.iter_goals():
            yield goal

    def export_datatype(self, dt):
        (name, ctors) = dt
        ty = self.export_type
        return SExpression(['datatype', name, SExpression([]),
                SExpression([SExpression([nm] + [ty(t) for (_, t) in args] + [name])
                             for (nm, args) in ctors])])

    def export_func(self, df):
        type_ = df.symbol_type()
        ty = self.export_type
        return SExpression(['declare-fun', df.symbol_name(),
            SExpression([ty(t) for t in type_.param_types]), ty(type_.return_type)])

    def export_const(self, df):
        type_ = df.symbol_type()
        ty = self.export_type
        return SExpression(['declare-fun', df.symbol_name(),
                            SExpression([]), ty(type_)])

    def export_type(self, type_):
        assert not (type_.is_function_type() or type_.is_array_type()) # TODO compound types
        return type_

    def export_rule_def(self, defun):
        name, args, rettype, body = defun
        ftype = FunctionType(rettype, [a.symbol_type() for a in args])
        fsymb = Symbol(name, ftype)
        yield self.export_func(fsymb)

        eqop = Iff if rettype.is_bool_type() else Equals

        for rule in self.export_rules(ForAll(args, eqop(Function(fsymb, args), body))):
            yield rule

    def export_rules(self, formula):
        ex = self.export_expr
        for precondition, op, lhs, rhs in self.extract_rw_parts(formula):
            if precondition is not None:
                yield SExpression([op, self._fresh('rule%d'), ex(Implies(precondition._repr, formula._repr))])
            else:
                yield SExpression([op, self._fresh('rule%d'), lhs, rhs])

    def extract_rw_parts(self, formula):
        ex = self.export_expr
        uvars, formula = self.extract_universal(formula)
        precondition = None
        if formula.is_implies():
            precondition = formula.arg(0)
            formula = formula.arg(1)
        if formula.is_equals() or formula.is_iff():
            if uvars:
                re = {v: self._qvar_from_symbol(v) for v in uvars}
                formula = formula.substitute(re)
                uvars = re.values()
            uvars = set(uvars)
            fv = lambda phi: get_free_variables(phi) & uvars

            lhs, rhs = formula.args()
            for lhs, rhs in [(lhs, rhs), (rhs, lhs)]:
                if ((lhs not in uvars) and  # avoid e.g. x => x + 0
                        fv(lhs) >= fv(rhs)):
                    if precondition is not None:
                        yield precondition, '=>', ex(lhs), ex(rhs)
                    else:
                        yield None, '=>', ex(lhs), ex(rhs)
        elif not (formula.is_not() and self.extract_universal(formula.args()[0])[0]):
            # this is either a not exp or an expr
            if uvars:
                re = {v: self._qvar_from_symbol(v) for v in uvars}
                formula = formula.substitute(re)
                uvars = re.values()
            uvars = set(uvars)

            equals_to = TRUE()
            if formula.is_not():
                formula = formula.args()[0]
                equals_to = FALSE()
            op = '<=>'
            if uvars:
                op = '=>'
            if precondition is not None:
                yield precondition, op, ex(formula), ex(equals_to)
            else:
                yield None, op, ex(formula), ex(equals_to)

    def export_goals(self, formula):
        ex = self.export_expr
        for uvars, precondition, lhs, rhs in self.export_goal_parts(formula):
            if precondition is None and rhs is None:
                goal = ForAll(uvars, Equals(lhs, Bool(True)))
            elif precondition is None:
                goal = ForAll(uvars, Equals(lhs, rhs))
            elif rhs is None:
                goal = Implies(precondition, ForAll(uvars, Equals(lhs, Bool(True))))
            else:
                goal = Implies(precondition, ForAll(uvars, Equals(lhs, rhs)))
            yield SExpression(['prove', ex(goal)])

    def export_goal_parts(self, formula):
        if formula.is_not() and self.extract_universal(formula.args()[0])[0]:
            formula = formula.arg(0)
            uvars, inner = self.extract_universal(formula)
            if inner.is_equals() or inner.is_iff():
                yield uvars, None, inner.arg(0), inner.arg(1)
            elif inner.is_implies():
                if (not inner.arg(1).is_equals()) and (not inner.arg(1).is_iff()):
                    yield uvars, inner.arg(0), inner.arg(1), None
                else:
                    yield uvars, inner.arg(0), inner.arg(1).arg(0), inner.arg(1).arg(1)
            else:
                yield uvars, None, inner, None


    def export_expr(self, e):
        return SmtLibSExpression(e)

    def extract_universal(self, formula):
        uvars = []

        while formula.is_forall():
            uvars += formula.quantifier_vars()
            formula = formula.args()[0]

        return uvars, formula

    def _qvar(self, name, type_):
        try: return Symbol(name, type_)
        except PysmtTypeError:  # technically, not supposed to occur
            return Symbol(self._fresh("%s_%%d" % name), type_)

    def _qvar_from_symbol(self, symbol):
        return self._qvar("?%s" % symbol, symbol.symbol_type())

    def _fresh(self, template):
        return template % self._fresh_cnt.__next__()


class Rule(object):
    def __init__(self, name, lhs, rhs, rule_type=None, precondition=None, conditions=None):
        self.name = name
        self.lhs = lhs
        self.rhs = rhs
        self.rule_type = rule_type
        if rule_type is None:
            self.rule_type = "=>"
        self.precondition = precondition
        self.conditions = conditions

    def __str__(self):
        if self.precondition is None:
            fixed_precondition = ""
        else:
            fixed_precondition = f"if {self.precondition} then "
        if self.conditions is None:
            fixed_conditions = ""
        else:
            fixed_conditions = f" when {' and '.join([f'({c[0]} != {c[1]})' for c in self.conditions])}"
        return f"rw {self.name} {fixed_precondition}{self.lhs} {self.rule_type} {self.rhs}{fixed_conditions}"


class FunDef(object):
    def __init__(self, name, args, ret_type, body=None):
        self.name = name
        self.args = args
        self.ret_type = ret_type
        self.body = body

    def __str__(self):
        if self.body is None:
            fixed_body = ""
        else:
            with_args = functools.reduce(lambda x, y: str(x).replace(f"{y[0]}", f"?{y[0]}"), self.args, self.body)
            fixed_body = f" => {with_args}"
        return f"fun {self.name} {' '.join([f'({a} : {t})' for a, t in self.args])} -> {self.ret_type}{fixed_body}"


class Datatype(object):
    def __init__(self, name, type_params, ctors):
        self.name = name
        self.type_params = type_params
        self.ctors = ctors

    def ctor_str(self, ctr):
        args = [f'(x_{i} : {t})' for i, t in enumerate(ctr[1])] + [f"(res : {self.name})"]
        ctr_name = ctr[0]
        return f"({ctr_name} : {' -> '.join([x for x in args])})"

    def __str__(self):
        return f"datatype {self.name} ({' '.join(self.type_params)}) := {' '.join([f'{self.ctor_str(c)}' for c in self.ctors])}"


class Goal(object):
    def __init__(self, uvar, precondition, lhs, rhs):
        self.precondition = precondition
        self.lhs = lhs
        self.rhs = rhs
        for v in uvar:
            # Need to change v occurences in precondition, lhs, rhs to "?v"
            assert v.is_symbol()
            subs = {Symbol("%s" % v.symbol_name(), v.symbol_type()): Symbol("?%s" % v.symbol_name(), v.symbol_type())}
            if self.precondition is not None:
                self.precondition = self.precondition.substitute(subs)
            if self.rhs is not None:
                self.rhs = self.rhs.substitute(subs)
            self.lhs = self.lhs.substitute(subs)

    def __str__(self):
        fixed_precondition = ""
        if self.precondition:
            fixed_precondition = f" if {self.precondition.to_smtlib(daggify=False)} then"
        fixed_rhs = ""
        if self.rhs:
            fixed_rhs = f" = {self.rhs.to_smtlib(daggify=False)}"
        return f"prove{fixed_precondition} {self.lhs.to_smtlib(daggify=False)} {fixed_rhs}"


class NewThesyFromSmt(ThesyFromSmt):
    def export_rule_def(self, defun):
        name, args, rettype, body = defun
        if body:
            body = self.export_expr(body)
        yield FunDef(name, [(a, a.get_type()) for a in args], rettype, body)

    def export_datatype(self, dt):
        (name, ctors) = dt
        ctors = [(nm, [self.export_type(t) for (_, t) in args]) for (nm, args) in ctors]
        return Datatype(name, [], ctors)

    def export_func(self, df):
        type_ = df.symbol_type()
        return FunDef(df.symbol_name(), [(f'x_{i}', t) for i, t in enumerate(type_.param_types)], type_.return_type)

    def export_rules(self, formula):
        for precondition, op, lhs, rhs in self.extract_rw_parts(formula):
            yield Rule(self._fresh('rule%d'), lhs, rhs, rule_type=op, precondition=precondition)

    def export_goals(self, formula):
        for uvars, precondition, lhs, rhs in self.export_goal_parts(formula):
            yield Goal(uvars, precondition, lhs, rhs)


class SmtLibDocumentParser(SmtLib20ParserPlus):
    """
    Extends the parser with a configurable preamble.
    """
    
    def __init__(self, *a):
        self.preamble = {}
        super().__init__(*a)

    def predeclare(self, symbol):
        self.preamble[symbol.symbol_name()] = \
            functools.partial(self._function_call_helper, symbol)

    def _reset(self):
        super()._reset()
        self.cache.update(self.preamble)


class SExpression:
    def __init__(self, elements: list):
        self.elements = elements
    def __str__(self):
        return "(" + " ".join(str(x) for x in self.elements) + ")"        

class SmtLibSExpression(SExpression):
    def __init__(self, expr):
        super().__init__([])
        self._repr = expr
    def __str__(self):
        return self._repr.to_smtlib(daggify=False)
