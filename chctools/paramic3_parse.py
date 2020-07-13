import argparse
import sys

import z3
import pysmt
import pysmt.solvers.z3 as pyz3
import pysmt.typing as type

from pysmt.smtlib.parser import SmtLibParser

BASE_PATH = "/home/turingdreams/Desktop/fmcad2013/fmcad13/benchmarks/paramIC3/"
PARAM_SUF = "parameters.txt"
INIT_SUF = "init.smt2"
PROP_SUF = "property.smt2"
TR_SUF = "trans_partitioned.smt2"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-f', dest='filepath', type=str, default="csma_red_5", help ="name of folder")

    args = parser.parse_args()
    pathName = args.filepath

    FILE_BASE = BASE_PATH + pathName + '/'

    PARAMPATH = FILE_BASE + PARAM_SUF
    PROPPATH = FILE_BASE + PROP_SUF
    TRPATH = FILE_BASE + TR_SUF
    INITPATH = FILE_BASE + INIT_SUF

    env = pysmt.environment.get_env()
    mgr = env.formula_manager
    converter = pyz3.Z3Converter(env, z3.get_ctx(None))

    with open(PARAMPATH, "r") as f:
        param_lines = f.readlines()
        parnames = [param.strip() for param in param_lines]
        parsymbols = [mgr.Symbol(name, type.REAL) for name in parnames]
        parsymbols = [converter.convert(par) for par in parsymbols]
    

    def parse_formula(filePath):
        parser = SmtLibParser()
        with open(filePath, 'r') as f:
            script = parser.get_script(f)
            all_vars = script.get_declared_symbols()
            all_vars = [converter.convert(var) for var in all_vars]
            formula = converter.convert(script.get_last_formula())
        return (all_vars, formula)

    initvars, init = parse_formula(INITPATH)
    trvars, tr = parse_formula(TRPATH)
    propvars, prop = parse_formula(PROPPATH)

    allvar_names = set()
    allvars = []
    for var in initvars:
        if var.decl().name() not in allvar_names:
            allvar_names.add(var.decl().name())
            allvars.append(var)
    for var in trvars:
        if var.decl().name() not in allvar_names:
            allvar_names.add(var.decl().name())
            allvars.append(var)
    for var in propvars:
        if var.decl().name() not in allvar_names:
            allvar_names.add(var.decl().name())
            allvars.append(var)

    pre_post = {}
    prevars = []
    postvars = []
    for var in trvars:
        if var.decl().name().endswith(".next"):
            postname = var.decl().name()
            pre_post[var.decl().name()[:len(postname)-5]] = var
        else:
            prevars.append(var)

    for var in prevars:
        if var.decl().name() in pre_post:
            postvars.append(pre_post[var.decl().name()])
        else:
            postvars.append(var)

    #allvars.update(initvars); allvars.update(trvars); allvars.update(propvars)
    pinitDb = mk_pinit_db(allvars, prevars, postvars, init, tr, prop, param_list=parsymbols)

    from horn_hacking import main as do_blocking
    do_blocking(pinitDb)
    

def mk_pinit_db(allvars, prevars, postvars, init, tr, prop, name='initDb', param_list=[z3.Const('U', z3.RealSort())], pInitPre=z3.BoolVal(True)):
    from horn_hacking import HornClauseDb, HornRule
    db = HornClauseDb(name)
    #db.load_from_fp(fp, queries)
    db._sealed = False

    pInit = z3.Function('pInit', *([p.sort() for p in param_list] + [z3.IntSort()] + [z3.BoolSort()]))

    PInitForm0 = pInit(*(param_list + [0]))
    PInitForm1 = pInit(*(param_list + [1]))

    Inv = z3.Function('Inv', *([p.sort() for p in prevars] + [z3.BoolSort()]))
    InvPre = Inv(*prevars)
    InvPost = Inv(*postvars)

    ########################

    firstRule = HornRule(z3.ForAll(param_list, \
        z3.Implies(pInitPre, PInitForm0)))
    firstRule._update()
    firstRule.mk_formula()
    db.add_rule(firstRule)

    secondRule = HornRule(z3.ForAll(param_list, \
        z3.Implies(PInitForm0, PInitForm1)))
    secondRule._update()
    secondRule.mk_formula()
    db.add_rule(secondRule)

    thirdRule = HornRule(z3.ForAll(allvars, \
        z3.Implies(z3.And(PInitForm1, init), InvPre)))
    thirdRule._update()
    thirdRule.mk_formula()
    db.add_rule(thirdRule)

    fourRule = HornRule(z3.ForAll(allvars, \
        z3.Implies(z3.And(InvPre, tr), InvPost)))
    fourRule._update()
    fourRule.mk_formula()
    db.add_rule(fourRule)

    fifthRule = HornRule(z3.ForAll(allvars, \
        z3.Implies(z3.And(InvPre, z3.Not(prop)), z3.BoolVal(False))))
    fifthRule._update()
    fifthRule.mk_formula()
    db.add_rule(fifthRule)

    db.seal()
    #from horn_hacking import print_chc_smt
    #print_chc_smt(db)
    return db



if __name__=="__main__":
    sys.exit(main())

