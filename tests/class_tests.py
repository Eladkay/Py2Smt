import unittest
from typing import List

from z3 import Not, Concat

from py2smt import Py2Smt
from smt_helper import list_of, IntType, singleton_list
from stdlib import __assume__
from tests.smt_test_case import SmtTestCase


class A:
    some_field: int
    some_array: List[int]

    def some_method(self):
        self.some_field += 1
        return self.some_field

    def field_of_other(self, a: 'A'):
        assert self != a
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

    def list_append_and_extend(self):
        self.some_array.append(1)
        self.some_array.extend([1, 2, 3])

    def assign_to_list(self):
        self.some_array = [1, 2, 3]


class RectangleTestClass:
    width: int
    height: int

    def get_area(self):
        return self.width * self.height

    def get_width(self):
        ret = self.width
        self.width = 0
        return ret


class B:

    def self_none(self, param: A) -> bool:
        return self is None

    def param_none(self, param: A) -> bool:
        return param is None

    def self_param(self, param: A) -> bool:
        return self is param

    def hash_everything(self, hash_your_woman: int,
                        hash_your_man: str,
                        it_is_all_part_of_gods_plan: bool,
                        we_should_hash_all_that_we_can: A,
                        here_in_py2smt_land: List[int]):
        x: int = hash(hash_your_woman)
        x = hash(hash_your_man)
        x = hash(it_is_all_part_of_gods_plan)
        x = hash(we_should_hash_all_that_we_can)
        x = hash(here_in_py2smt_land)


class Py2SmtClassTests(SmtTestCase):
    def test_basic_fields(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("some_method")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0.eval("A.some_field(deref(self))") + 1)
        self.assertImplies(tr, state1.eval("A.some_field(deref(self))") == state0.eval("A.some_field(deref(self))") + 1)

    def test_field_of_other(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("field_of_other")
        self.assertEqual(entry.args, ["self", "a"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0.eval("A.some_field(deref(a))"))
        self.assertImplies(tr, state1.eval("A.some_field(deref(a))") == state0.eval("A.some_field(deref(a))"))
        self.assertImplies(tr, state1.eval("A.some_field(deref(self))") == state0.eval("A.some_field(deref(self))")
                           + state0.eval("A.some_field(deref(a))"))

    def test_list_attributes(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("list_test")
        self.assertEqual(entry.args, ["self", "idx"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state1.eval("A.some_array(deref(self))[idx]"))
        self.assertImplies(tr, state1.eval("A.some_field(deref(self))") == state0.eval("A.some_field(deref(self))"))
        self.assertImplies(tr, state1.eval("A.some_array(deref(self))[idx]") ==
                           1 + state0.eval("A.some_array(deref(self))[idx]"))

    def test_constructors(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("constructors")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == 1)
        self.assertImplies(tr, state1.eval("A.some_field(deref(new_a))") == 1)
        self.assertImplies(tr, state0.eval("deref(self)") == state1.eval("deref(self)"))

    def test_method_call(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("method_call")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0.eval("A.some_field(deref(self))") + 1)
        self.assertImplies(tr, state1.eval("A.some_field(deref(self))") == state0.eval("A.some_field(deref(self))") + 1)

    def test_rectangle_area(self):
        smt = Py2Smt([RectangleTestClass])
        entry = smt.get_entry_by_name("get_area")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var) == state0.eval("RectangleTestClass.width(deref(self))")
                           * state0.eval("RectangleTestClass.height(deref(self))"))
        self.assertImplies(tr, state1.eval("RectangleTestClass.width(deref(self))") ==
                           state0.eval("RectangleTestClass.width(deref(self))"))
        self.assertImplies(tr, state1.eval("RectangleTestClass.height(deref(self))") ==
                           state0.eval("RectangleTestClass.height(deref(self))"))

    def test_rectangle_width(self):
        smt = Py2Smt([RectangleTestClass])
        entry = smt.get_entry_by_name("get_width")
        self.assertEqual(entry.args, ["self"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(entry.cfg.return_var)
                           == state0.eval("RectangleTestClass.width(deref(self))"))

    def test_is(self):
        smt = Py2Smt([A, B])
        entries = smt.get_entry_by_name("self_none"), smt.get_entry_by_name("param_none"), \
            smt.get_entry_by_name("self_param")
        self.assertTupleEqual(tuple([entry.args for entry in entries]), (["self", "param"], ) * 3)

        self_none = entries[0]
        state0, state1 = self_none.make_state(), self_none.make_state("'")
        tr = self_none.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, Not(state1.eval(self_none.cfg.return_var)))

        param_none = entries[1]
        state0, state1 = param_none.make_state(), param_none.make_state("'")
        tr = param_none.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(param_none.cfg.return_var) == state0.eval(f"id(param) == 0"))

        self_param = entries[2]
        state0, state1 = self_param.make_state(), self_param.make_state("'")
        tr = self_param.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, Not(state1.eval(self_param.cfg.return_var)))

    def test_hash(self):
        smt = Py2Smt([A, B])
        entry = smt.get_entry_by_name("hash_everything")
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)

    def test_class_list_append_extend(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("list_append_and_extend")
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval("A.some_array(deref(self))")
                           == Concat(state0.eval("A.some_array(deref(self))"), list_of([1, 1, 2, 3], IntType)))

    def test_assign_to_list(self):
        smt = Py2Smt([A])
        entry = smt.get_entry_by_name("assign_to_list")
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval("A.some_array(deref(self))")
                           == list_of([1, 2, 3], IntType))


if __name__ == '__main__':
    unittest.main()
