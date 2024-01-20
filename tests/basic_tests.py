import typing
import unittest

from py2smt import Py2Smt
from smt_helper import singleton_list
from stdlib import __assume__
from tests.smt_test_case import SmtTestCase
from z3 import *

# noinspection PyMethodMayBeStatic
class BasicTest:
    def simple_return(self):
        return 1

    def simple_assignment(self):
        x = 1
        return x

    def maybe_assignment(self, param: int):
        x = 1
        if param == 3:
            x = 2
        return x

    def ifelse(self, param: int):
        if param == 3:
            return 1
        else:
            return 2

    def while_loop(self, param: int):
        tmp = param
        i = 0
        while i < 5:
            tmp = 2 * tmp
            i += 1
        return tmp

    def binop(self, x: int, y: int):
        return x + y + 1

    def to_be_inlined(self):
        x = 2
        return 2

    def func_call(self):
        return self.to_be_inlined()

    def some_func_with_args(self, param: int):
        return param * 2

    def func_call_with_args(self):
        return self.some_func_with_args(2)

    def interfering_function(self):
        x = 1

    def interfered_function(self):
        x = 2
        self.interfering_function()
        return x

    def bools(self):
        x = True
        y = False
        return x and y

    def breaking(self):
        x = 1
        while True:
            break
        return x

    def breaking2(self):
        x = 1
        while True:
            x = x + 1
            if x >= 5:
                break
        return x

    def arrays(self):
        arr = [1, 2, 3]
        return arr[1]

    def arrays_with_writing(self):
        arr = [1, 2, 3]
        arr[1] = 4
        return arr[1]

    def sets_and_dicts(self):
        some_set = {1, 2, 3}
        some_dict = {1: 2, 3: 4}
        return 1 in some_set and 2 in some_dict

    def strings(self):
        a = "a"
        b = "b"
        return a + b

    def list_in_a_dict(self):
        d = {1: [1, 2, 3]}
        return d[1][1]

    def raise_(self, param: int):
        if param == 1:
            raise ValueError()

    def assert_(self, param: int):
        assert param != 1

    def for_range(self):
        x = 0
        for i in range(10):
            x += i
        return x

    def for_range_and_bmc(self):
        x = 0
        for i in range(10):
            x += i
        assert x == 45
        return x

    def assume_assert(self, param: int):
        __assume__(param > -1)
        assert param > -1

    def for_variable_range(self, param: int):
        __assume__(param > -1)
        x = 0
        for i in range(param + 1):
            x += i
        assert x == (param + 1) * (param + 2) / 2
        return x

    def a_lot_of_if(self, z: int):
        x = 1
        y = 2
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        if x > z:
            y = x * z
        else:
            x = y * z
        return x + y

    def list_for(self):
        x = [1, 2, 3]
        sum = 0
        for i in x:
            sum += i
        return sum

    def bitwise_ops(self, x: int, y: int) -> int:
        return (x | y) ^ (x & y)

    def floats(self, x: float, y: float, z: float) -> float:
        return x + y - 0.5*z

    def basic_list_append_and_extend(self, x: typing.List[int], y: typing.List[int]) -> typing.List[int]:
        x.append(1)
        x.extend(y)
        return x


class Py2SmtBasicTests(SmtTestCase):

    def test_basic(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("simple_return")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 1)

    def test_assignment(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("simple_assignment")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, And(state1["x"] == 1, state1.eval(entry.cfg.return_var) == 1))

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
        smt = Py2Smt([BasicTest], optimization_level=2)
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

    def test_for_range(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("for_range")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 45)

    def test_for_range_and_bmc(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("for_range_and_bmc")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 45)
        error_condition = entry.cfg.get_error_condition()(state0, state1)
        self.assertUnsat(error_condition)

    def test_assume_assert(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("assume_assert")
        self.assertEqual(entry.args, ["self", "param"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        error_condition = entry.cfg.get_error_condition()(state0, state1)
        self.assertUnsat(error_condition)

    def test_for_variable_range(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("for_variable_range")
        self.assertEqual(entry.args, ["self", "param"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        error_condition = entry.cfg.get_error_condition()(state0, state1)
        self.assertUnsat(error_condition)

    @unittest.skip
    def test_a_lot_of_if(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("a_lot_of_if")
        self.assertEqual(entry.args, ["self", "z"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)

    def test_list_for(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("list_for")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 6)

    def test_bitwise_ops(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("bitwise_ops")
        self.assertEqual(entry.args, ["self", "x", "y"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        x = Int2BV(state0.eval("x"), 64)
        y = Int2BV(state0.eval("y"), 64)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == BV2Int((x | y) ^ (x & y)))

    def test_floats(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("floats")
        self.assertEqual(entry.args, ["self", "x", "y", "z"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) ==
                           state0.eval("x") + state0.eval("y") - 0.5*state0.eval("z"))

    def test_basic_list_append_and_extend(self):
        smt = Py2Smt([BasicTest])
        entry = smt.get_entry_by_name("basic_list_append_and_extend")
        self.assertEqual(entry.args, ["self", "x", "y"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) ==
                           Concat(Concat(state0.eval("x"), singleton_list(1)), state0.eval("y")))


if __name__ == '__main__':
    unittest.main()
