import sys
import z3
import io

import pysmt.environment
import pysmt.solvers.z3 as pyz3
from pysmt.smtlib.parser import SmtLibZ3Parser, Tokenizer

def ground_quantifier(qexpr):
    body = qexpr.body()

    vars = list()
    for i in reversed(range(qexpr.num_vars())):
        vi_name = qexpr.var_name(i)
        vi_sort = qexpr.var_sort(i)
        vi = z3.Const(vi_name, vi_sort)
        vars.append(vi)

    body = z3.substitute_vars(body, *vars)
    return (body, vars)

def find_all_uninterp_consts(formula, res):
    if z3.is_quantifier(formula):
        formula = formula.body()

    worklist = []
    if z3.is_implies(formula):
        worklist.append(formula.arg(1))
        arg0 = formula.arg(0)
        if z3.is_and(arg0):
            worklist.extend(arg0.children())
        else:
            worklist.append(arg0)
    else:
        worklist.append(formula)

    for t in worklist:
        if z3.is_app(t) and t.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            res.append(t.decl())


class HornRule(object):
    def __init__(self, formula):
        self._formula = formula
        self._head = None
        self._body = []
        self._uninterp_sz = 0
        self._bound_constants = []

        self._update()

    def _update(self):
        if not self.has_formula():
            return

        rels = list()
        find_all_uninterp_consts(self._formula, rels)
        self._rels = frozenset(rels)
        body = self._formula
        if z3.is_quantifier(body):
            body, self._bound_constants = ground_quantifier(body)

        if z3.is_implies(body):
            self._head = body.arg(1)
            body = body.arg(0)
            if z3.is_and(body):
                body = body.children()
            else:
                body = [body]
        else:
            self._head = body
            body = []

        # remove all true constants
        body = [x for x in body if not z3.is_true(x)]

        if len(body) > 0:
            self._body = body

        for i in range(len(body)):
            f = body[i]
            if z3.is_app(f) and f.decl() in self._rels:
                self._uninterp_sz += 1
            else:
                break

        # reset _formula, it can be re-computed using mk_formula()
        # this ensures that any simplifications that are done during _update() are
        # also reflected in the formula view
        self._formula = None
        assert(self._head is not None)

    def __str__(self):
        return str(self._formula)
    def __repr__(self):
        return repr(self._formula)

    def used_rels(self):
        return self._rels

    def is_query(self):
        return z3.is_false(self._head)

    def is_simple_query(self):
        """Returns true if query is a simple.

        A simple query is an application of an uninterprted predicate

        """
        if not self.is_query():
            return False

        if self.uninterp_size() != 1:
            return False;

        predicate = self.body()[0]

        if predicate.num_args() > 0:
            return False

        _body = self.body()[1:];
        if len(_body) == 0:
            return True

        if len(_body) == 1:
            return z3.is_true(_body[0])

        _body = z3.simplify(z3.And(*_body))
        return z3.is_true(_body)

    ### based on the following inference
    ###
    ### forall v :: (expr ==> false)
    ###
    ### equivalent to
    ###
    ### forall v:: ( expr ==> q ) && forall v :: ( q ==> false )
    ###
    def split_query(self):
        """Split query if it is not simple into a query and a rule"""

        assert(self.is_query())
        if self.is_simple_query():
            return (self, None)

        q = z3.Bool("simple!!query")
        query = HornRule(z3.Implies(q, z3.BoolVal(False)))
        rule = HornRule(z3.ForAll(self._bound_constants,
                                  z3.Implies(z3.And(*self.body()), q)))
        return query, rule

    def is_fact(self):
        return self._uninterp_sz == 0

    def is_linear(self):
        return self._uninterp_sz <= 1

    def to_ast(self):
        return self._formula

    def head(self):
        return self._head

    def body(self):
        return self._body

    def uninterp_size(self):
        return self._uninterp_sz

    def has_formula(self):
        return self._formula is not None

    def get_formula(self):
        return self._formula

    def mk_formula(self):
        f = self._body
        if len(f) == 0:
            f = z3.BoolVal(True)
        elif len(f) == 1:
            f = f[0]
        else:
            f = z3.And(f)
        f = z3.Implies(f, self._head)

        if len(self._bound_constants) > 0:
            f = z3.ForAll(self._bound_constants, f)
        self._formula = f
        return self._formula

    def mk_query(self):
        assert(self.is_query())
        assert(len(self.body()) > 0)
        _body = self.body()
        if self.is_simple_query():
            return _body[0]

        if len(_body) == 1:
            f = _body[0]
        else:
            f = z3.And(_body)
        if len(self._bound_constants) > 0:
            f = z3.Exists(self._bound_constants, f)
        return f
    
    """def _mk_lemma_parser(self):
        if self._lemma_parser is not None:
            return
        self._lemma_parser = SmtLibZ3Parser()
        # register symbols that are expected to appear in the lemma
        for i, symbol in enumerate(self._pysmt_sig):
            name = self._mk_lemma_arg_name(i)
            self._lemma_parser.cache.bind(name, symbol)

    def pysmt_parse_lemma(self, input):
        self._mk_lemma_parser()
        tokens = Tokenizer(input, interactive = False)
        return self._lemma_parser.get_expression(tokens)"""

class HornRelation(object):
    def __init__(self, fdecl):
        self._fdecl = fdecl
        self._sig =  []
        self._pysmt_sig = []
        self._lemma_parser = None

        self._update()

    def _update(self):
        self._sig = []
        for i in range(self._fdecl.arity()):
            name = self._mk_arg_name(i)
            sort = self._fdecl.domain(i)
            self._sig.append(z3.Const(name, sort))


        # compute pysmt version of the signature
        env = pysmt.environment.get_env()
        mgr = env.formula_manager
        ctx = z3.get_ctx(None)
        converter = pyz3.Z3Converter(env, ctx)
        self._pysmt_sig = [mgr.Symbol(v.decl().name(),
                                      converter._z3_to_type(v.sort()))
                           for v in self._sig]

    def _mk_arg_name(self, i):
        # can be arbitrary convenient name
        return "{}_{}_n".format(self.name(), i)

    def _mk_lemma_arg_name(self, i):
        # must match name used in the lemma
        return "{}_{}_n".format(self.name(), i)

    def name(self):
        return str(self._fdecl.name())

    def __str__(self):
        return repr(self)

    def __repr__(self):
        import io
        out = io.StringIO()
        out.write(str(self.name()))
        out.write("(")
        for v in self._pysmt_sig:
            out.write(str(v))
            out.write(', ')
        out.write(")")
        return out.getvalue()

    def _mk_lemma_parser(self):
        if self._lemma_parser is not None:
            return
        self._lemma_parser = SmtLibZ3Parser()
        # register symbols that are expected to appear in the lemma
        for i, symbol in enumerate(self._pysmt_sig):
            name = self._mk_lemma_arg_name(i)
            self._lemma_parser.cache.bind(name, symbol)

    def pysmt_parse_lemma(self, input):
        self._mk_lemma_parser()
        tokens = Tokenizer(input, interactive = False)
        return self._lemma_parser.get_expression(tokens)

class HornClauseDb(object):
    def __init__(self, name = 'horn', simplify_queries = True):
        self._name = name
        self._rules = []
        self._queries = []
        self._rels_set = frozenset()
        self._rels = dict()
        self._sealed = True
        self._fp = False

        self._simple_query = simplify_queries

    def add_rule(self, horn_rule):
        self._sealed = False
        if False: #horn_rule.is_query():
            if self._simple_query and not horn_rule.is_simple_query():
                query, rule = horn_rule.split_query()
                self._rules.append(rule)
                self._queries.append(query)
            else:
                self._queries.append(horn_rule)
        else:
            self._rules.append(horn_rule)

    def get_rels(self):
        self.seal()
        return self._rels_set

    def has_rel(self, rel_name):
        return rel_name in self._rels.keys()
    def get_rel(self, rel_name):
        return self._rels[rel_name]
    def get_rules(self):
        return self._rules
    def get_queries(self):
        return self._queries

    def seal(self):
        if self._sealed:
            return

        rels = list()
        for r in self._rules:
            rels.extend(r.used_rels())
        for q in self._queries:
            rels.extend(r.used_rels())
        self._rels_set = frozenset(rels)
        self._sealed = True

        for rel in self._rels_set:
            self._rels[str(rel.name())] = HornRelation(rel)

    def __str__(self):
        out = io.StringIO()
        for r in self._rules:
            out.write(str(r))
            out.write('\n')
        out.write('\n')
        for q in self._queries:
            out.write(str(q))
        return out.getvalue()

    def load_from_fp(self, fp, queries):
        self._fp = fp
        if len(queries) > 0:
            for r in fp.get_rules():
                rule = HornRule(r)
                #import pdb; pdb.set_trace()
                self.add_rule(rule)
            for q in queries:
                rule = HornRule(z3.Implies(q, z3.BoolVal(False)))
                self.add_rule(rule)
        else:
            # fixedpoit object is not properly loaded, ignore it
            self._fp = None
            for a in fp.get_assertions():
                #import pdb; pdb.set_trace()
                rule = HornRule(a) #doesn't work?
                self.add_rule(rule)
        self.seal()

    def has_fixedpoint(self):
        return self._fp is not None
    def get_fixedpoint(self):
        return self._fp

    def mk_fixedpoint(self, fp = None):
        if fp is None:
            self._fp = z3.Fixedpoint()
            fp = self._fp

        for rel in self._rels_set:
            fp.register_relation(rel) ##SIMILAR thing!
        for r in self._rules:
            if r.has_formula():
                fp.add_rule(r.get_formula())
            else:
                fp.add_rule(r.mk_formula())

        return fp


class FolModel(object):
    def __init__(self):
        self._fn_interps = dict()

    def add_fn(self, name, lmbd):
        self._fn_interps[name] = lmbd

    def has_interp(self, name):
        return name in self._fn_interps.keys()

    def __setitem__(self, key, val):
        self.add_fn(key, val)

    def get_fn(self, name):
        return self._fn_interps[name]

    def eval(self, term):
        fn = self.get_fn(term.decl().name())
        # lambdas seem to be broken at the moment
        # this is a work around
        body = fn.body()
        body = z3.substitute_vars(body, *reversed(term.children()))
        return body


    def __str__(self):
        return str(self._fn_interps)
    def __repr__(self):
        return repr(self._fn_interps)

def load_horn_db_from_file(fname):
    fp = z3.Fixedpoint()
    queries = fp.parse_file(fname)
    db = HornClauseDb(fname)
    db.load_from_fp(fp, queries)
    #import pdb; pdb.set_trace()
    return db

def copy_horn_db_mk_pinit(origdb, newParList=[z3.Const('U', z3.RealSort())]):
    import copy
    db = copy.deepcopy(origdb)
    db._sealed = False
    db._rels_set = frozenset()
    db._rels = dict()
    db._fp = False

    for r in db._rules:
        r = replace_func(r, newParList)
        if is_rule_pre(r):
            if len(newParList) > 0:
                swapped = swap_const_U(r, copy.deepcopy(newParList[0]))
                if not swapped:
                    print("Could not swap in U.")
                    return
            
            pInit = z3.Function('pInit', *([p.sort() for p in newParList] + [z3.BoolSort()]))
            r._rels.append(pInit)
            r._body.append(pInit(*newParList))
            r._formula = r.mk_formula()
        
    firstRule = HornRule(z3.ForAll(newParList, \
        z3.Implies(z3.BoolVal(True), pInit(*newParList))))
    firstRule.mk_formula()
    db.add_rule(firstRule)
    db.seal()
    return db


def swap_const_U(rule, param):
    #flips first seen constant to U
    body = rule._body
    def is_num_val(val):
        if z3.is_const(val) \
            and (val.decl().kind() == z3.Z3_OP_ANUM or val.decl().kind() == z3.Z3_OP_AGNUM): #i.e. is fixed value!
            #Otherwise: "and val.decl().kind() != z3.Z3_OP_UNINTERPRETED:""
                return True
        if val.decl().kind() == z3.Z3_OP_TO_REAL or val.decl().kind() == z3.Z3_OP_TO_INT:
            return True
        return False

    for i in range(len(body)): #TODO: Remove Assumption: HACKY SPECIAL CASES
        e = body[i]
        if z3.is_expr(e) and e.decl().kind() == z3.Z3_OP_EQ:
            #for j in range(e.num_args()):
            val0 = param if is_num_val(e.arg(0)) else e.arg(0)
            val1 = param if is_num_val(e.arg(1)) else e.arg(1)
            body[i] = val0 == val1
            return True #success
        elif z3.is_expr(e) and e.decl().kind() == z3.Z3_OP_LE:
            val0 = param if is_num_val(e.arg(0)) else e.arg(0)
            val1 = param if is_num_val(e.arg(1)) else e.arg(1)
            body[i] = val0 <= val1
            return True
        elif z3.is_expr(e) and e.decl().kind() == z3.Z3_OP_GE:
            val0 = param if is_num_val(e.arg(0)) else e.arg(0)
            val1 = param if is_num_val(e.arg(1)) else e.arg(1)
            body[i] = val0 >= val1
            return True
        elif z3.is_expr(e) and e.decl().kind() == z3.Z3_OP_LT:
            val0 = param if is_num_val(e.arg(0)) else e.arg(0)
            val1 = param if is_num_val(e.arg(1)) else e.arg(1)
            body[i] = val0 < val1
            return True
        elif z3.is_expr(e) and e.decl().kind() == z3.Z3_OP_GT:
            val0 = param if is_num_val(e.arg(0)) else e.arg(0)
            val1 = param if is_num_val(e.arg(1)) else e.arg(1)
            body[i] = val0 > val1
            return True
    return False


def is_rule_pre(rule):
    body_uninterp = False
    body = rule._body
    for i in range(len(body)):
        f = body[i]
        if z3.is_app(f) and f.decl() in rule._rels:
            body_uninterp = True

    h = rule._head
    head_uninterp = z3.is_app(h) and h.decl() in rule._rels
    return not body_uninterp and head_uninterp

def replace_func(rule, Ulist):
    rule._formula = None
    rule._bound_constants.extend(Ulist)
    rels = list()

    body = rule._body
    for i in range(len(body)):
        f = body[i]
        if z3.is_app(f) and f.decl() in rule._rels:  # f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            #f is FUNCTION
            arglist = [f.arg(i) for i in range(f.num_args())]
            arglist.extend(Ulist) #add Ulist to arglist
            fNew = z3.Function(f.decl().name() + 'New', *([arg.sort() for arg in arglist] + [z3.BoolSort()]))
            rels.append(fNew)
            body[i] = fNew(*arglist)
    
    h = rule._head
    if z3.is_app(h) and h.decl() in rule._rels:
        arglist = [h.arg(i) for i in range(h.num_args())]
        arglist.extend(Ulist) #add Ulist to arglist
        hNew = z3.Function(h.decl().name() + 'New', *([arg.sort() for arg in arglist] + [z3.BoolSort()]))
        rels.append(hNew)
        rule._head = hNew(*arglist)
        #z3.substitute(h, (h.decl(), hdnew))

    rule._rels = rels #frozenset(rels)
    rule._formula = rule.mk_formula()
    return rule

#############################################################################


# wrapper to solve CHC constraints and extract result
def solve_horn(chc, pp=False, q3=False, max_unfold=10, verbosity=0, debug=False):
    z3.set_param(proof=True)
    z3.set_param(model=True)
    
    z3.set_param(verbose=verbosity)

    if debug:
        z3.set_option('fp.spacer.trace_file', 'spacer.log')
        z3.enable_trace('spacer_progress')
    else:
        z3.disable_trace('spacer_progress')

    s = z3.SolverFor('HORN')
    s.set('engine', 'spacer')
    s.set('spacer.order_children', 2)
    s.set('xform.subsumption_checker', False)  #is this okay?
    if not pp:
        s.set('xform.inline_eager', False)
        s.set('xform.inline_linear', False)
        s.set('xform.slice', False)

    if max_unfold > 0:
        s.set('spacer.max_level', max_unfold)

    if q3:
        # allow quantified variables in pobs
        s.set('spacer.ground_pobs', False)
        # enable quantified generalization
        s.set('spacer.q3.use_qgen', True)

    # add constraints to solver
    s.add(chc)
    if verbosity > 0:
        print(s.sexpr())
    # run solver
    res = s.check()
    # extract model or proof
    answer = None
    if res == z3.sat:
        answer = s.model()
    elif res == z3.unsat:
        answer = s.proof()
    #import pdb; pdb.set_trace()
    return res, answer

def print_chc_smt(horndb):
#print new CHCs in SMT2 format
    fp2 = z3.Fixedpoint()
    horndb.mk_fixedpoint(fp=fp2)
    fp2.set('print_fixedpoint_extensions', False)
    print("(set-option :produce-proofs true)")
    print(fp2.sexpr())
    print("(check-sat)\n(get-proof)\n(get-model)\n(exit)")

def main():
    db = load_horn_db_from_file(sys.argv[1])
    db2 = copy_horn_db_mk_pinit(db)
    #print(db2._rels)
    #modify_init_rule(db2)
    rules = [r.mk_formula() for r in db2.get_rules()]
    print_chc_smt(db2)

    #Modify pInit base here!
    res, answer = solve_horn(rules, verbosity=1, debug=True, max_unfold=1000)
    
    return 0

if __name__ == '__main__':
    sys.exit(main())
