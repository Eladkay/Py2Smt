import unittest
from typing import List

from py2smt import Py2Smt
from stdlib import __assume__
from tests.smt_test_case import SmtTestCase


class A:
    some_field: int
    some_array: List[int]

    def some_method(self):
        self.some_field += 1
        return self.some_field

    def field_of_other(self, a: 'A'):
        self.some_field += a.some_field
        return a.some_field

    def constructors(self):
        new_a = A()
        new_a.some_field = 1
        return new_a.some_field

    def method_call(self):
        return self.some_method()

    def list_test(self, idx: int):
        __assume__(0 <= idx < len(self.some_array))
        self.some_array[idx] += + 1
        return self.some_array[idx]


class RectangleTestClass:
    width: int
    height: int

    def get_area(self):
        return self.width * self.height

    def get_width(self):
        ret = self.width
        self.width = 0
        return ret


class Py2SmtClassTests(SmtTestCase):
    def test_basic_fields(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("some_method")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0.eval("A.some_field(self)") + 1)
        self.assertImplies(tr, state1.eval("A.some_field(self)") == state0.eval("A.some_field(self)") + 1)

    def test_field_of_other(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("field_of_other")
        self.assertEqual(entry.args, ["self", "a"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0.eval("A.some_field(a)"))
        self.assertImplies(tr, state1.eval("A.some_field(a)") == state0.eval("A.some_field(a)"))
        self.assertImplies(tr, state1.eval("A.some_field(self)") == state0.eval("A.some_field(self)")
                           + state0.eval("A.some_field(a)"))

    def test_list_attributes(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("list_test")
        self.assertEqual(entry.args, ["self", "idx"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state1.eval("A.some_array(self)[idx]"))
        self.assertImplies(tr, state1.eval("A.some_field(self)") == state0.eval("A.some_field(self)"))
        self.assertImplies(tr, state1.eval("A.some_array(self)[idx]") == 1 + state0.eval("A.some_array(self)[idx]"))

    def test_constructors(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("constructors")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 1)
        self.assertImplies(tr, state1.eval("A.some_field(new_a)") == 1)
        self.assertImplies(tr, state0.eval("self") == state1.eval("self"))

    def test_method_call(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("method_call")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0.eval("A.some_field(self)") + 1)
        self.assertImplies(tr, state1.eval("A.some_field(self)") == state0.eval("A.some_field(self)") + 1)

    def test_rectangle_area(self):
        smt = Py2Smt([RectangleTestClass])
        entry = smt.get_entry_by_name("get_area")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0.eval("RectangleTestClass.width(self)")
                           * state0.eval("RectangleTestClass.height(self)"))
        self.assertImplies(tr, state1.eval("RectangleTestClass.width(self)") ==
                           state0.eval("RectangleTestClass.width(self)"))
        self.assertImplies(tr, state1.eval("RectangleTestClass.height(self)") ==
                           state0.eval("RectangleTestClass.height(self)"))

    def test_rectangle_width(self):
        smt = Py2Smt([RectangleTestClass])
        entry = smt.get_entry_by_name("get_width")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0.eval("RectangleTestClass.width(self)"))


if __name__ == '__main__':
    unittest.main()
