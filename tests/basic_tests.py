import typing
import unittest

from py2smt import Py2Smt
from tests.smt_test_case import SmtTestCase
from z3 import *

# noinspection PyMethodMayBeStatic
class BasicTest:
    def simple_return(self) -> int:
        return 1

    def simple_assignment(self) -> int:
        x = 1
        return x

    def maybe_assignment(self, param: int) -> int:
        x = 1
        if param == 3:
            x = 2
        return x

    def ifelse(self, param: int) -> int:
        if param == 3:
            return 1
        else:
            return 2

    def while_loop(self, param: int) -> int:
        tmp = param
        i = 0
        while i < 5:
            tmp = 2 * tmp
            i += 1
        return tmp

    def binop(self, x: int, y: int) -> int:
        return x + y + 1

    def to_be_inlined(self) -> int:
        x = 2
        return 2

    def func_call(self) -> int:
        return self.to_be_inlined()

    def some_func_with_args(self, param: int) -> int:
        return param * 2

    def func_call_with_args(self) -> int:
        return self.some_func_with_args(2)

    def interfering_function(self):
        x = 1

    def interfered_function(self) -> int:
        x = 2
        self.interfering_function()
        return x

    def bools(self) -> bool:
        x = True
        y = False
        return x and y

    def breaking(self) -> int:
        x = 1
        while True:
            break
        return x

    def breaking2(self) -> int:
        x = 1
        while True:
            x = x + 1
            if x >= 5:
                break
        return x

    def arrays(self) -> int:
        arr: typing.List[int] = [1, 2, 3]
        return arr[1]

    def arrays_with_writing(self) -> int:
        arr: typing.List[int] = [1, 2, 3]
        arr[1] = 4
        return arr[1]

    def sets_and_dicts(self) -> bool:
        some_set: typing.Set[int] = {1, 2, 3}
        some_dict: typing.Dict[int, int] = {1: 2, 3: 4}
        return 1 in some_set and 2 in some_dict

    def strings(self) -> str:
        a = "a"
        b = "b"
        return a + b

    def list_in_a_dict(self) -> int:
        d: typing.Dict[int, typing.List[int]] = {1: [1, 2, 3]}
        return d[1][1]

    def raise_(self, param: int):
        if param == 1:
            raise ValueError()

    def assert_(self, param: int):
        assert param != 1


class Py2SmtBasicTests(SmtTestCase):

    def test_basic(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("simple_return")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertEquivalent(tr, state1.eval(entry.cfg.return_var) == 1)

    def test_assignment(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("simple_assignment")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertEquivalent(tr, And(state1["x"] == 1, state1.eval(entry.cfg.return_var) == 1))

    def test_maybe_assignment(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("maybe_assignment")
        self.assertEqual(entry.args, ["self", "param"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, Or(And(state1["x"] == 1, state1.eval(entry.cfg.return_var) == 1),
                                  And(state1["x"] == 2, state1.eval(entry.cfg.return_var) == 2)))

    def test_ifelse(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("ifelse")
        self.assertEqual(entry.args, ["self", "param"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, Or(state1.eval(entry.cfg.return_var) == 1, state1.eval(entry.cfg.return_var) == 2))

    def test_while_loop(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("while_loop")
        self.assertEqual(entry.args, ["self", "param"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation(50)(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, Implies(state0["param"] > 0, state1.eval(entry.cfg.return_var) == 32 * state0["param"]))

    def test_binop(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("binop")
        self.assertEqual(entry.args, ["self", "x", "y"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0["x"] + state0["y"] + 1)

    def test_func_call(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("func_call")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 2)

    def test_func_call_with_args(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("func_call_with_args")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 4)

    def test_interfering_variable_names(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("interfered_function")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 2)

    def test_booleans(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("bools")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == False)

    def test_break(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("breaking")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation(50)(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 1)

    def test_break2(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("breaking2")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation(50)(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) <= 10)

    def test_arrays(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("arrays")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 2)

    def test_arrays_with_writing(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("arrays_with_writing")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 4)

    def test_sets_and_dicts(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("sets_and_dicts")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == False)

    def test_strings(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("strings")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == "ab")

    def test_list_in_a_dict(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("list_in_a_dict")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 2)

    def test_raise_(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("raise_")
        self.assertEqual(entry.args, ["self", "param"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        error_condition = entry.cfg.get_error_condition()(state0, state1)
        self.assertImplies(tr, state0.eval("param") != 1)
        self.assertImplies(error_condition, state0.eval("param") == 1)

    def test_assert_(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("assert_")
        self.assertEqual(entry.args, ["self", "param"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        error_condition = entry.cfg.get_error_condition()(state0, state1)
        self.assertImplies(tr, state0.eval("param") != 1)
        self.assertImplies(error_condition, state0.eval("param") == 1)


if __name__ == '__main__':
    unittest.main()
