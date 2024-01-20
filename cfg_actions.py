import ast
import functools
from typing import override, List, Self

from common import syntactic_replace, generalized_syntactic_replace
from symbolic_interp import State


class Action:
    def _perform_action(self, s: State) -> State:
        raise NotImplementedError()

    def perform_action(self, s: State) -> State:
        new_state = self._perform_action(s)
        assert id(new_state) != id(s), "Action did not clone state"
        return new_state

    def simplify(self) -> 'Action':
        return self

    def __hash__(self):
        raise NotImplementedError()

    def _combine_actions(self, other: 'Action') -> 'Action':
        return CompositeAction.of(self, other)


class _NoAction(Action):

    @override
    def _perform_action(self, s: State) -> State:
        return s.clone()

    @override
    def __hash__(self):
        return hash("NoAction")

    def __eq__(self, other):
        return isinstance(other, _NoAction)

    @override
    def _combine_actions(self, other: Action) -> Action:
        return other

    @override
    def __str__(self):
        return "nop"


NoAction = _NoAction()


class AssignAction(Action):

    @staticmethod
    def of(var: str, value: str):
        assert isinstance(var, str) and isinstance(value, str)
        return AssignAction({var: value})

    def __init__(self, assignment: dict):
        self.assignment = assignment

    @override
    def _perform_action(self, s: State) -> State:
        return s.assign(self.assignment)

    @override
    def __hash__(self):
        return hash(f"AssignAction({self.assignment})")

    def __eq__(self, other):
        return isinstance(other, AssignAction) and self.assignment == other.assignment

    @override
    def _combine_actions(self, other: Action) -> Action:
        # Assignments are simultaneous, so combining them requires
        # incorporating relevant values from the first assignment into
        # the second assignment.
        # TODO: everything involving heaps doesn't work because there isn't a direct modification
        if isinstance(other, AssignAction) and all("deref" not in it for it in other.assignment.values()):
            assignment = {}
            for key in other.assignment:
                parsed_assignment = {assgn: ast.parse(value).body[0].value for assgn, value in self.assignment.items()}
                value = generalized_syntactic_replace(parsed_assignment, ast.parse(other.assignment[key]).body[0])
                assignment[key] = ast.unparse(value)
            for key in self.assignment:
                if key not in assignment:
                    assignment[key] = self.assignment[key]
            return AssignAction(assignment)
        if isinstance(other, CompositeAction):
            return CompositeAction.of(self, *other.actions)
        if other == NoAction:
            return self
        if isinstance(other, AssumeAction):
            # Try flipping the order of the actions
            parsed_assumption = ast.parse(other.expression).body[0].value
            parsed_assignment = {assgn: ast.parse(value).body[0].value for assgn, value in self.assignment.items()}
            value = generalized_syntactic_replace(parsed_assignment, parsed_assumption)
            return CompositeAction.of(AssumeAction(ast.unparse(value)), self)
        return super()._combine_actions(other)

    @override
    def __str__(self):
        return f"assign({str(self.assignment)})"


class AssumeAction(Action):
    def __init__(self, expression: str):
        self.expression = expression

    @override
    def _perform_action(self, s: State) -> State:
        return s.assume(self.expression)

    @override
    def __hash__(self):
        return hash(f"AssumeAction({self.expression})")

    def __eq__(self, other):
        return isinstance(other, AssumeAction) and self.expression == other.expression

    @override
    def __str__(self):
        return f"assume({self.expression})"

    @override
    def _combine_actions(self, other: Action) -> Action:
        if isinstance(other, CompositeAction):
            return CompositeAction.of(*other.actions, self)
        if other == NoAction:
            return self
        if isinstance(other, AssumeAction):
            return AssumeAction(f"And({self.expression}, {other.expression})")
        return super()._combine_actions(other)


class CompositeAction(Action):
    @staticmethod
    def of(*actions: Action):
        return CompositeAction(list(actions))

    def __init__(self, actions: List[Action]):
        self.actions = actions

    @override
    def _perform_action(self, s: State) -> State:
        for action in self.actions:
            s = action.perform_action(s)
        return s

    @override
    def __hash__(self):
        return hash(f"CompositeAction({self.actions})")

    @override
    def __str__(self):
        return f"[{', '.join(str(action) for action in self.actions)}]"

    def __eq__(self, other):
        return isinstance(other, CompositeAction) and self.actions == other.actions

    @override
    def _combine_actions(self, other: Action) -> 'Action':
        if isinstance(other, CompositeAction):
            return CompositeAction(self.actions + other.actions)
        if other == NoAction:
            return self
        return super()._combine_actions(other).simplify()

    def simplify(self) -> 'Action':
        def inline_composites(acts):
            while any(isinstance(action, CompositeAction) for action in acts):
                new_actions = []
                for action in acts:
                    if isinstance(action, CompositeAction):
                        new_actions.extend(action.actions)
                    else:
                        new_actions.append(action)
                acts = new_actions
            return acts
        actions = self.actions
        if len(actions) == 1:
            return actions[0].simplify()

        actions = [action.simplify() for action in actions if not action == NoAction]

        actions = inline_composites(actions)

        if len(actions) == 0:  # e.g. if all actions were empty composites or just nops
            return NoAction

        ret = functools.reduce(lambda x, y: x._combine_actions(y), actions)
        old_ret = None
        # todo: combining actions doesn't really work because if the first two actions
        # don't combine, the next ones won't either because now the first two are a composite
        while old_ret != ret:
            old_ret = ret
            ret = functools.reduce(lambda x, y: x._combine_actions(y), actions)

            if isinstance(ret, CompositeAction):
                inlined = inline_composites(ret.actions)
                if len(inlined) == 1:
                    ret = inlined[0]
                else:
                    ret = CompositeAction(inlined)
        if ret == self:
            return self
        return ret.simplify()
