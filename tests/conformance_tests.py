from py2smt import Py2Smt
from tests.smt_test_case import SmtTestCase


class A:
    some_field: int

    def __init__(self):
        self.some_field = 0

    def some_writing_method(self):
        self.some_field = 1
        return 2

    def some_reading_method(self):
        return self.some_field

    def some_reading_writing_method(self):
        self.some_field = 1
        return self.some_field

    def some_overridden_reading_writing_method(self):
        self.some_field += 1
        return self.some_field


class B(A):
    other_field: int
    object_field: A

    def other_new_method(self):
        x = self.some_reading_writing_method()  # x' = 1, some_field' = 1, other_field' = other_field
        self.other_field += 1  # x' = 1, some_field' = 1, other_field' = other_field + 1
        return x + self.other_field + self.some_field
        # returned' = 3 + other_field, some_field' = 1, other_field' = other_field + 1

    def some_overridden_reading_writing_method(self):
        self.some_writing_method()  # some_field' = 1, other_field' = other_field
        x = self.other_new_method()  # x' = 3 + other_field, some_field' = 1, other_field' = other_field + 1
        self.some_field += x  # x' = 3 + other_field, some_field' = 4 + other_field, other_field' = other_field + 1
        return self.some_reading_method()
        # returned' = 4 + other_field, some_field' = 3 + other_field, other_field' = other_field + 1

    def upcast(self) -> A:
        return self

    def object_field(self):
        self.object_field.some_writing_method()  # object_field.some_field' = 1
        return self.object_field.some_reading_method()  # returned' = 1, object_field.some_field' = 1

    def object_field2(self):
        self.object_field.some_field = 1
        return self.object_field.some_field

    def mutator(self, a: A):
        a.some_field = 1

    def check_pass_by_ref(self):
        a = A()
        self.mutator(a)
        return a.some_field

    def aliasing(self):
        a = A()
        b = a
        b.some_field = 1
        return a.some_field


class Py2SmtConformanceTests(SmtTestCase):
    system = Py2Smt([A, B])

    def test_correct_first_class(self):
        writing_method = self.system.get_entry_by_name("some_writing_method", A)
        state0, state1 = writing_method.make_state(), writing_method.make_state("'")
        tr = writing_method.cfg.get_transition_relation()(state0, state1)
        returned_var = state1[writing_method.cfg.return_var]
        self.assertSat(tr)
        self.assertImplies(tr, returned_var == 2)
        self.assertImplies(tr, state1.eval("A.some_field(deref(self))") == 1)

        reading_method = self.system.get_entry_by_name("some_reading_method", A)
        state0, state1 = reading_method.make_state(), reading_method.make_state("'")
        tr = reading_method.cfg.get_transition_relation()(state0, state1)
        returned_var = state1[reading_method.cfg.return_var]
        self.assertSat(tr)
        self.assertImplies(tr, returned_var == state0.eval("A.some_field(deref(self))"))

        reading_writing_method = self.system.get_entry_by_name("some_reading_writing_method", A)
        state0, state1 = reading_writing_method.make_state(), reading_writing_method.make_state("'")
        tr = reading_writing_method.cfg.get_transition_relation()(state0, state1)
        returned_var = state1[reading_writing_method.cfg.return_var]
        self.assertSat(tr)
        self.assertImplies(tr, returned_var == 1)
        self.assertImplies(tr, state1.eval("A.some_field(deref(self))") == 1)

        overridden_reading_writing_method = self.system.get_entry_by_name("some_overridden_reading_writing_method", A)
        state0, state1 = overridden_reading_writing_method.make_state(), \
            overridden_reading_writing_method.make_state("'")
        tr = overridden_reading_writing_method.cfg.get_transition_relation()(state0, state1)
        returned_var = state1[overridden_reading_writing_method.cfg.return_var]
        self.assertSat(tr)
        self.assertImplies(tr, returned_var == 1 + state0.eval("A.some_field(deref(self))"))
        self.assertImplies(tr, state1.eval("A.some_field(deref(self))") == 1 + state0.eval("A.some_field(deref(self))"))

    def test_conformance1(self):
        other_new_method = self.system.get_entry_by_name("other_new_method", B)
        state0, state1 = other_new_method.make_state(), other_new_method.make_state("'")
        tr = other_new_method.cfg.get_transition_relation()(state0, state1)
        returned_var = state1[other_new_method.cfg.return_var]
        self.assertSat(tr)
        self.assertImplies(tr, returned_var == 3 + state0.eval("B.other_field(deref(self))"))
        self.assertImplies(tr, state1.eval("B.some_field(deref(self))") == 1)
        self.assertImplies(tr, state1.eval("B.other_field(deref(self))") ==
                           state0.eval("B.other_field(deref(self))") + 1)

    def test_conformance2(self):
        # returned' = 3 + other_field, some_field' = 3 + other_field, other_field' = other_field + 1
        other_new_method = self.system.get_entry_by_name("some_overridden_reading_writing_method", B)
        state0, state1 = other_new_method.make_state(), other_new_method.make_state("'")
        tr = other_new_method.cfg.get_transition_relation()(state0, state1)
        returned_var = state1[other_new_method.cfg.return_var]
        self.assertSat(tr)
        self.assertImplies(tr, returned_var == 4 + state0.eval("B.other_field(deref(self))"))
        self.assertImplies(tr, state1.eval("B.some_field(deref(self))")
                           == 4 + state0.eval("B.other_field(deref(self))"))
        self.assertImplies(tr, state1.eval("B.other_field(deref(self))")
                           == state0.eval("B.other_field(deref(self))") + 1)

    def test_upcast(self):
        upcast = self.system.get_entry_by_name("upcast", B)
        state0, state1 = upcast.make_state(), upcast.make_state("'")
        tr = upcast.cfg.get_transition_relation()(state0, state1)
        returned_var = upcast.cfg.return_var
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(f"A.some_field(deref({returned_var}))")
                           == state0.eval("B.some_field(deref(self))"))

    def test_object_field(self):
        object_field = self.system.get_entry_by_name("object_field", B)
        state0, state1 = object_field.make_state(), object_field.make_state("'")
        tr = object_field.cfg.get_transition_relation()(state0, state1)
        returned_var = object_field.cfg.return_var
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(f"B.object_field(deref(self))")  # just the address
                           == state0.eval("B.object_field(deref(self))"))
        self.assertImplies(tr, state1.eval(f"A.some_field(deref(B.object_field(deref(self))))")
                           == state0.eval("A.some_field(deref(B.object_field(deref(self))))") + 1)
        self.assertImplies(tr, state1.eval(returned_var)
                           == state0.eval("A.some_field(deref(B.object_field(deref(self))))") + 1)

    def test_object_field2(self):
        object_field = self.system.get_entry_by_name("object_field2", B)
        state0, state1 = object_field.make_state(), object_field.make_state("'")
        tr = object_field.cfg.get_transition_relation()(state0, state1)
        returned_var = object_field.cfg.return_var
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(returned_var) == 1)

    def test_pass_by_ref(self):
        object_field = self.system.get_entry_by_name("check_pass_by_ref", B)
        state0, state1 = object_field.make_state(), object_field.make_state("'")
        tr = object_field.cfg.get_transition_relation()(state0, state1)
        returned_var = object_field.cfg.return_var
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(returned_var) == 1)

    def test_aliasing(self):
        object_field = self.system.get_entry_by_name("aliasing", B)
        state0, state1 = object_field.make_state(), object_field.make_state("'")
        tr = object_field.cfg.get_transition_relation()(state0, state1)
        returned_var = object_field.cfg.return_var
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval(returned_var) == 1)
