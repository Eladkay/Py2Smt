import unittest

from z3 import Implies, And

from cfg_actions import NoAction, AssignAction, AssumeAction, CompositeAction
from smt_helper import IntType
from symbolic_interp import State, Signature
from tests.smt_test_case import SmtTestCase


class ComponentTests(SmtTestCase):
    def test_no_action(self):
        state = State(Signature({'a': IntType}), None, {})
        new_state = NoAction.perform_action(state)
        self.assertEqual(state.locals, new_state.locals)

    def test_assign_action(self):
        state = State(Signature({'a': IntType}), None, {})
        new_state = AssignAction.of('a', 'a + 1').perform_action(state)
        # noinspection PyTypeChecker
        self.assertValid(new_state['a'] == 1 + state['a'])

    def test_assume_action(self):
        state = State(Signature({'a': IntType}), None, {})
        new_state = AssumeAction('a == 1').perform_action(state)
        # noinspection PyTypeChecker
        self.assertValid(Implies(And(*new_state.assumptions), new_state['a'] == 1))

    def test_composite_action(self):
        state = State(Signature({'a': IntType}), None, {})
        new_state = (CompositeAction.of(AssumeAction('a == 1'), AssignAction.of('a', 'a + 1'))
                     .perform_action(state))
        # noinspection PyTypeChecker
        self.assertValid(Implies(And(*new_state.assumptions), new_state['a'] == 2))

    def test_composite_action_simplify1(self):
        new_action = CompositeAction.of(AssignAction.of('b', 'b + 1'),
                                        AssignAction.of('a', 'a + 1')).simplify()
        self.assertEqual(new_action, AssignAction({'a': 'a + 1', 'b': 'b + 1'}))

    def test_composite_action_simplify2(self):
        action = CompositeAction.of(AssignAction.of('a', 'a + 1'),
                                    AssignAction.of('a', 'a + 1'))
        new_action = action.simplify()
        state = State(Signature({'a': IntType}), None, {})
        new_state1 = action.perform_action(state)
        new_state2 = new_action.perform_action(state)
        self.assertEqual(new_state1.locals, new_state2.locals)

    def test_composite_action_simplify3(self):
        action = CompositeAction.of(AssignAction.of('a', 'a + 1'), AssumeAction('a > 0'))
        new_action = action.simplify()
        self.assertEqual(new_action, action)

    def test_composite_action_simplify4(self):
        action = CompositeAction.of(AssumeAction('a <= 0'), AssumeAction('a > 0'))
        new_action = action.simplify()
        self.assertEqual(new_action, AssumeAction('And(a <= 0, a > 0)'))


if __name__ == '__main__':
    unittest.main()
