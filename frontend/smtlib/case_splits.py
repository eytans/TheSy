from pysmt.fnode import FNode
from pysmt.shortcuts import get_type, get_env, Function, FunctionType, FreshSymbol, Type
from .translators import ThesyFromSmt, SExpression, SmtLibSExpression


def get_top_fn(exp: SmtLibSExpression):
    applier = exp._repr._content.payload
    if isinstance(applier, tuple) or applier is None:
        return ("None", None)
    return applier._content.payload


class ExtractCaseSplits:
    def __init__(self, doc: ThesyFromSmt):
        self.doc = doc
        sym = get_env().formula_manager.get_symbol
        #fsym = lambda ty: FreshSymbol(ty, template='?c%d')
        nat = Type('Nat')
        skf1 = FreshSymbol(FunctionType(nat, [nat]), template='skf%d')
        self.ctor_pats = {
            nat: lambda ph: [sym('zero'),
                             Function(sym('succ'), [Function(skf1, [ph])])]
        }

    def guess_rules(self):
        # Collect definitions for declared funcs
        for f in self.doc.iter_decls():
            f_name = f.elements[1]
            param_types = f.elements[2]
            param_types = [d for d in self.doc.iter_datatypes() for p in param_types.elements if d.elements[1] == p]
            ret_type = f.elements[3]
            rules = [r for r in self.doc.iter_rws() if get_top_fn(r.elements[2])[0] == f_name]
            patterns = []
            for r in rules:
                patterns.append(r.elements[2]._repr._content.args)

        # i = [0]
        # def mk_rule(suffix):
        #     i[0] += 1
        #     return SExpression(['=|>', 'split%d' % i[0]] + rule_suffix)
        #
        # for rule in self.doc.iter_rules():
        #     lhs, rhs = rule.elements[2:]
        #     if isinstance(lhs, SmtLibSExpression) and lhs._repr.is_function_application():
        #         for rule_suffix in self._generalize_pattern(lhs._repr):
        #             yield mk_rule(rule_suffix)
        #         for rule_suffix in self._generalize_condition(lhs, rhs._repr):
        #             yield mk_rule(rule_suffix)

    def _generalize_pattern(self, term):
        head, args = term.function_name(), term.args()
        pat_idxs = [i for i, a in enumerate(args) if a.is_function_application()]
        if len(pat_idxs) > 1:
            args1pat = list(args)
            phs = []
            for i in pat_idxs[1:]:
                ph = FreshSymbol(get_type(args[i]), template='?splt%d')
                phs.append(ph)
                args1pat[i] = ph

            headpat = SmtLibSExpression(Function(head, args1pat))
            #print("=|>", pat_idxs, headpat, phs)

            for ph in phs:
                cases = list(self._get_cases(ph))
                if len(cases) > 1:
                    yield [headpat, SExpression(['potential_split', ph] + cases)]

    def _get_cases(self, ph):
        try:
            pats = self.ctor_pats[get_type(ph)](ph)
            return [SmtLibSExpression(p) for p in pats]
        except KeyError:
            return []

    def _generalize_condition(self, pat, term):
        if term.is_ite():
            cond = SmtLibSExpression(term.arg(0))
            yield [pat, SExpression(['potential_split', cond, 'true', 'false'])]
