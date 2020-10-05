import typing
import itertools
from smtlib26 import SmtLib20ParserPlus
from pysmt.smtlib.parser import SmtLibScript
from pysmt.fnode import FNode
from pysmt.environment import get_env
from pysmt.shortcuts import Symbol, get_free_variables



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
            if cmd.name == 'assert':
                for rule in self.export_rules(cmd.args[0]):
                    yield rule

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

    def export_rules(self, formula):
        ex = self.export_expr
        uvars = []

        while formula.is_forall():
            uvars += formula.quantifier_vars()
            formula = formula.args()[0]

        if formula.is_equals():
            if uvars:
                re = {v: Symbol(self._fresh("?%s_%%d" % v), v.symbol_type()) for v in uvars}
                formula = formula.substitute(re)
                uvars = re.values()
            uvars = set(uvars)
            fv = lambda phi: get_free_variables(phi) & uvars

            lhs, rhs = formula.args()
            for lhs, rhs in [(lhs, rhs), (rhs, lhs)]:
                if ((lhs not in uvars) and     # avoid e.g. x => x + 0
                        fv(lhs) >= fv(rhs)):
                    yield SExpression(['=>', self._fresh('rule%d'), ex(lhs), ex(rhs)])

    def export_expr(self, e):
        return SmtLibSExpression(e)

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



def main():
    BENCHMARK_DIRS = ['benchmarks/cvc4-conj/benchmarks-dt/isaplanner']
    TARGET_DIR = '/tmp/thesy'

    import os

    try: os.makedirs(TARGET_DIR)
    except FileExistsError: pass

    for d in BENCHMARK_DIRS:
        for fn in os.listdir(d):
            print('--  %s --' % fn)
            infile = open(os.path.join(d, fn))

            doc = SmtLibDocument(infile)
            with open(os.path.join(TARGET_DIR, fn + '.th'), 'w') as outf:
                for el in doc:
                    print(el)
                    print(el, file=outf)

            print(set(doc.iter_used_symbols()))
            print(set(doc.iter_used_types()))



if __name__ == '__main__':
    main()

