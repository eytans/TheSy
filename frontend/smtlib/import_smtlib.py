import typing
from smtlib26 import SmtLib20ParserPlus
from pysmt.smtlib.parser import SmtLibScript
from pysmt.fnode import FNode


class SmtLibDocument:
    """
    Reads definition in SMTLIB-2.6 format and exports them in TheSy S-Expression
    syntax.
    """
    script: SmtLibScript

    def __init__(self, s: typing.TextIO):
        p = SmtLib20ParserPlus()
        self.script = p.get_script(s)

    def iter_datatypes(self):
        for cmd in self.script:
            if cmd.name == 'declare-datatypes':
                params, defs = cmd.args
                if params: print("*** warning: datatype declaration with parameters")
                for a in defs: yield self.export_datatype(a)

    def iter_decls(self):
        for cmd in self.script:
            if cmd.name == 'declare-fun':
                yield self.export_func(cmd.args[0])

    def iter_rules(self):
        for cmd in self.script:
            if cmd.name == 'assert':
                for rule in self.export_rules(cmd.args[0]):
                    yield rule

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
            lhs, rhs = formula.args()
            for lhs, rhs in [(lhs, rhs), (rhs, lhs)]:
                if lhs not in uvars:    # avoid e.g. x => x + 0
                    yield SExpression(['=>', ex(lhs), ex(rhs)])

    def export_expr(self, e):
        return SmtLibSExpression(e)


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

    import os
    for d in BENCHMARK_DIRS:
        for fn in os.listdir(d):
            print('--  %s --' % fn)
            infile = open(os.path.join(d, fn))

            doc = SmtLibDocument(infile)
            for el in doc:
                print(el)


if __name__ == '__main__':
    main()

