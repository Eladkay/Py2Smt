import functools
from typing import override, List, Self

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

    def _combine_like_actions(self, other: Self) -> 'Action':
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
    def _combine_like_actions(self, other: Self) -> Action:
        return other


NoAction = _NoAction()


class AssignAction(Action):

    @staticmethod
    def of(var: str, value: str):
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
    def _combine_like_actions(self, other: Self) -> Action:
        # Assignments are simultaneous, so combining them requires
        # incorporating relevant values from the first assignment into
        # the second assignment.
        assignment = {}
        for key in other.assignment:
            value = other.assignment[key]
            for existing_assignment in self.assignment:
                value = value.replace(existing_assignment, f"({self.assignment[existing_assignment]})")
            assignment[key] = value
        for key in self.assignment:
            if key not in assignment:
                assignment[key] = self.assignment[key]
        return AssignAction(assignment)


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
    def _combine_like_actions(self, other: Self) -> Action:
        return AssumeAction(f"And({self.expression}, {other.expression})")


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

    def __eq__(self, other):
        return isinstance(other, CompositeAction) and self.actions == other.actions

    @override
    def _combine_like_actions(self, other: Self) -> 'Action':
        return CompositeAction(self.actions + other.actions)

    def simplify(self) -> 'Action':
        actions = self.actions
        if len(actions) == 1:
            return actions[0].simplify()

        actions = [action.simplify() for action in actions if not action == NoAction]

        if len(actions) == 0:  # e.g. if all actions were empty composites or just nops
            return NoAction

        partitions = []
        current_partition = [actions[0]]
        for action in actions[1:]:
            if isinstance(action, type(current_partition[0])):
                current_partition.append(action)
            else:
                partitions.append(current_partition)
                current_partition = [action]

        partitions.append(current_partition)
        assert all(len(it) > 0 for it in partitions)

        new_actions = [functools.reduce(lambda x, y: x._combine_like_actions(y), partition)
                       for partition in partitions]

        ret = CompositeAction(new_actions)
        if ret == self:
            return self
        return ret.simplify()
