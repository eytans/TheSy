import typing
import itertools
from .smtlib26 import SmtLib20ParserPlus
from pysmt.smtlib.parser import SmtLibScript
from pysmt.fnode import FNode
from pysmt.exceptions import PysmtTypeError
from pysmt.shortcuts import Symbol, FunctionType, ForAll, Equals, \
    Iff, Function, Bool, get_free_variables



class SmtLibDocument:
    """
    Reads definition in SMTLIB-2.6 format and exports them in TheSy S-Expression
    syntax.
    """
    script: SmtLibScript

    def __init__(self, s: typing.TextIO):
        p = SmtLib20ParserPlus()
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

        uvars, formula = self.extract_universal(formula)

        if formula.is_equals() or formula.is_iff():
            if uvars:
                re = {v: self._qvar_from_symbol(v) for v in uvars}
                formula = formula.substitute(re)
                uvars = re.values()
            uvars = set(uvars)
            fv = lambda phi: get_free_variables(phi) & uvars

            lhs, rhs = formula.args()
            for lhs, rhs in [(lhs, rhs), (rhs, lhs)]:
                if ((lhs not in uvars) and     # avoid e.g. x => x + 0
                        fv(lhs) >= fv(rhs)):
                    yield SExpression(['=>', self._fresh('rule%d'), ex(lhs), ex(rhs)])

    def export_goals(self, formula):
        ex = self.export_expr

        if formula.is_not():
            formula = formula.arg(0)
            uvars, inner = self.extract_universal(formula)
            if inner.is_equals() or inner.is_iff():
                goal = formula
            else:
                goal = ForAll(uvars, Iff(inner, Bool(True)))
            yield SExpression(['prove', ex(goal)])

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
