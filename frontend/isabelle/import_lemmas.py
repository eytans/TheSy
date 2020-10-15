import functools
import typing
import re



class TheoryDocument:

    DATATYPE_RE = re.compile(r"^datatype (?:'\w+|\(.*?\))?\s*(\w+)\s*=\s*(.*)", re.MULTILINE)
    CTOR_RE = re.compile(r'(\w+)[^|]*')
    HIPSTER_RE = re.compile(r"^hipster (.*)", re.MULTILINE)

    LEMMA_RE = re.compile(r'^lemma (\w+)(?: \[.*?\])?:\s*"(.*?)"', re.MULTILINE)
    LEMMA_TOK_RE = re.compile(r'\s+|([()])')

    BUILTINS = set(['=>', 'not'])

    def __init__(self, s: typing.TextIO):
        self.datatypes = []
        self.ctors = []
        self.funcs = []
        self.lemmas = []

        self.aliases = {}

        whole_text = s.read()

        for mo in self.DATATYPE_RE.finditer(whole_text):
            self.datatypes += [mo.group(1)]
            self.ctors += self.CTOR_RE.findall(mo.group(2))

        for mo in self.HIPSTER_RE.finditer(whole_text):
            self.funcs += mo.group(1).split()

        for mo in self.LEMMA_RE.finditer(whole_text):
            if mo.group(1) != 'unknown':
                self.lemmas += [self.parse_lemma(mo.group(2))]

    def merge(self, other):
        self.ctors += other.ctors
        self.funcs += other.funcs
        self.lemmas += other.lemmas
        return self

    def parse_lemma(self, text):
        sides = [self.parse_expr(e) for e in text.split('=')]
        return text, sides

    def parse_expr(self, text):
        stack = [[]]
        for token in filter(lambda x: x, self.LEMMA_TOK_RE.split(text)):
            if token == '(':
                stack.append([])
            elif token == ')':
                e = stack.pop()
                stack[-1].append(SExpression(e))
            elif token == r'\<not>':
                if stack[-1] == []: stack.pop()
                stack.append(['not'])
                stack.append([])
            elif token == r'\<Longrightarrow>':
                e = stack.pop()
                stack.append(['=>', SExpression(e)])
                stack.append([])
            else:
                stack[-1].append(token)
        
        e = []
        while stack:
            e = [SExpression(stack.pop() + e)]
        return e[0]

    def export_lemma(self, lemma, as_goal=False):
        fv = functools.reduce(lambda a,b: a | b, (self.find_vars(e) for e in lemma))
        sig = {}
        if not as_goal:
            sig.update(self._mk_env(fv))
        for func in self.funcs:
            sig[func] = func.replace('twoSpec', '2').replace('Special', '')
        sig.update(self.aliases)
        phi = [self.subst(e, sig) for e in lemma]
        if len(phi) == 1: phi.append('true')
        if phi[0].elements[0] == '=>':
            precond, phi[0] = phi[0].elements[1:]
        else:
            precond = None

        S = SExpression
        eq = S(['='] + phi)
        if as_goal:
            #if precond: return None  #  no chance :(
            if precond: eq = S(['=>', precond, eq])
            qv = S([S([v, 'U']) for v in sorted(fv)])  # sorting just to keep order stable
            return S(['prove', S(['forall', qv, eq])])
        else:
            if precond: eq = S(['=>', precond, eq])
            return eq

    def export_rules(self, lemma):
        eq = self.export_lemma(lemma, as_goal=False)
        S = SExpression
        if eq.elements[0] == '=':
            for (d, (lhs, rhs)) in [('=>', eq.elements[1:]), ('<=', list(reversed(eq.elements[1:])))]:
                if self.find_qvars(rhs) < self.find_qvars(lhs):
                    yield S(['=>', f'"{f" {d} ".join(str(x) for x in lemma)}"', lhs, rhs])
            #yield S(['=>', f'"{" <= ".join(str(x) for x in lemma)}"'] + )
        else:
            yield S(['=>', f'"{lemma}"', eq])

    def find_vars(self, sexpr):
        fv = set()
        if isinstance(sexpr, SExpression):
            for e in sexpr.elements: fv |= self.find_vars(e)
        elif isinstance(sexpr, str):
            name = self._flat_name(sexpr)
            if all(name not in s for s in [self.ctors, self.funcs, self.BUILTINS]):
                fv.add(sexpr)
        return fv

    def find_qvars(self, sexpr):
        qv = set()
        if isinstance(sexpr, SExpression):
            for e in sexpr.elements: qv |= self.find_qvars(e)
        elif isinstance(sexpr, str) and sexpr.startswith('?'):
            qv.add(sexpr)
        return qv

    def subst(self, sexpr, subst):
        if isinstance(sexpr, str):
            sexpr = self._flat_name(sexpr)  # not so pretty here
        if sexpr in subst:
            return subst[sexpr]
        elif isinstance(sexpr, SExpression):
            return SExpression([self.subst(e, subst) for e in sexpr.elements])
        else:
            return sexpr

    def _mk_env(self, var_names):
        return {v: f"?{v}" for v in var_names}

    def _flat_name(self, name):
        return name.split('.')[-1]


class SExpression:
    """
    @todo merge with the one from frontend.smtlib
    """
    def __init__(self, elements: list):
        self.elements = elements
    def __str__(self):
        return "(" + " ".join(str(x) for x in self.elements) + ")"        
    __repr__ = __str__