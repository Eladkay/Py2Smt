import unittest

from z3 import Solver, Not, Implies, sat, unsat


class SmtTestCase(unittest.TestCase):
    def assertImplies(self, a, b):
        solver = Solver()
        solver.add(Not(Implies(a, b)))
        if solver.check() == sat:
            model = solver.model()
            decls = [d for d in model.decls() if not d.name().startswith("__")]
            result = {d: model[d] for d in decls}
            self.fail(f"{a} does not imply {b} (counterexample: {result})")

    def assertEquivalent(self, a, b):
        self.assertImplies(a, b)
        self.assertImplies(b, a)

    def assertSat(self, a):
        solver = Solver()
        solver.add(a)
        if solver.check() == unsat:
            self.fail(f"{a} is not satisfiable")

    def assertUnsat(self, a):
        solver = Solver()
        solver.add(a)
        if solver.check() == sat:
            self.fail(f"{a} is not unsatisfiable (model: {solver.model()})")

    def assertValid(self, a):
        self.assertUnsat(Not(a))

