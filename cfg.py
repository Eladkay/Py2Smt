import functools
import typing
from dataclasses import dataclass
from typing import Callable, Tuple, List, Any, Type

from z3 import *

from symbolic_interp import State, Signature


@dataclass
class ControlFlowNode:
    index: int
    label: str

    def __str__(self):
        return f"Node#{self.index}({self.label})"

    def __hash__(self):
        return hash(str(self))


@dataclass
class Label:
    index: int

    def __str__(self):
        return f"Label#{self.index}"

    def __hash__(self):
        return hash(str(self))


@dataclass
class ActionPlaceholder:
    index: int
    compute: Callable

    def __str__(self):
        return f"Action#{self.index}"

    def __hash__(self):
        return hash(str(self))


@dataclass
class ControlFlowEdge:
    source: typing.Union[Label, ControlFlowNode]
    target: typing.Union[Label, ControlFlowNode]
    action: typing.Union[str, ActionPlaceholder]

    def perform_action(self, s: State):
        return eval(self.action)  # uses s internally

    def __hash__(self):
        return hash(str(self))


class ControlFlowGraph:
    PASS = "pass"
    var_count: int = 0

    def __init__(self, system: 'Py2Smt', name: str, cls: typing.Union[Type, None]):
        self.system = system
        self.name = name
        self.cls = cls
        self.nodes = set()
        self.edges = set()
        self.labels = set()
        self.actions = set()

        self.start = self.add_node("start")

        self.end = self.add_node("end")
        self.end_label = self.next_bp_label()
        self.add_edge(self.end, self.end_label)

        self.break_label = None
        self.continue_label = None

        self.types = {}
        if isinstance(cls, Type):
            self.report_type("self", cls)

        self.return_var = None

    @staticmethod
    def get_place_of_default_value(ty: Any) -> Any:
        if isinstance(ty, ArraySortRef):
            return f"K({ControlFlowGraph.type_to_place_string(ty.domain())}, " \
                   f"{ControlFlowGraph.get_place_of_default_value(ty.range())})"
        elif isinstance(ty, ArithSortRef):
            return "0"
        elif isinstance(ty, BoolSortRef):
            return "False"
        elif isinstance(ty, SeqSortRef) and ty.is_string():
            return "\"\""
        elif ty.name().endswith("Option"):
            return f"{ty}.none"
        else:
            raise NotImplementedError(f"Cannot get default value for type {ty}")

    @staticmethod
    def get_literal_type(value: str):
        if value is None:
            return None
        try:
            int(value)
            return IntSort()
        except ValueError:
            pass
        if value in ["True", "False"]:
            return BoolSort()
        if (value.startswith('"') or value.startswith("\\\"")) and (value.endswith('"') or value.endswith("\\\"")):
            return StringSort()
        try:
            return eval(value).sort()
        except Exception:
            return None

    def get_type(self, value: str) -> Any:
        if value in self.types:
            return self.types[value]
        literal_type = ControlFlowGraph.get_literal_type(value)
        if literal_type is not None:
            return literal_type
        raise ValueError(f"Cannot find type for {value}")

    @staticmethod
    def type_to_place_string(ty: Any) -> str:
        if isinstance(ty, ArraySortRef):
            return f"ArraySort({ControlFlowGraph.type_to_place_string(ty.domain())}, " \
                   f"{ControlFlowGraph.type_to_place_string(ty.range())})"
        elif isinstance(ty, ArithSortRef):
            return "IntSort()"
        elif isinstance(ty, BoolSortRef):
            return "BoolSort()"
        elif isinstance(ty, SeqSortRef) and ty.is_string():
            return "StringSort()"
        else:
            raise NotImplementedError(f"Cannot get place string for type {ty}")

    def report_type(self, var: str, ty: Any):
        if ty is None:
            return
        if isinstance(ty, str):
            ty = eval(ty)
        new_type = self.system.class_types[ty] if isinstance(ty, typing.Hashable) and \
                                                  ty in self.system.class_types else ty
        if var in self.types:
            if self.types[var] != new_type:
                raise ValueError(f"Type redeclaration for {var}: {self.types[var]} vs {new_type}")
        assert isinstance(new_type, SortRef)
        self.types[var] = new_type

    def add_node(self, label: str) -> ControlFlowNode:
        node = ControlFlowNode(len(self.nodes), label)
        self.nodes.add(node)
        return node

    def add_all(self, other: 'ControlFlowGraph') -> Tuple[ControlFlowNode, Label]:
        new_nodes = {node: self.add_node(f"({node.label})_{other.name}") for node in other.nodes}
        new_end_label = self.next_bp_label()
        for edge in other.edges:
            self.add_edge(new_nodes[edge.source], new_nodes[edge.target], edge.action)
        self.add_edge(new_nodes[other.end], new_end_label)
        return new_nodes[other.start], new_end_label

    def add_edge(self, src: typing.Union[Label, ControlFlowNode], dst: typing.Union[Label, ControlFlowNode],
                 action: typing.Union[ActionPlaceholder, str] = "s"):
        edge = ControlFlowEdge(src, dst, action)
        self.edges.add(edge)
        return edge

    def add_action_placeholder(self, function: Callable) -> ActionPlaceholder:
        action = ActionPlaceholder(len(self.actions), function)
        self.actions.add(action)
        return action

    def next_bp_label(self):
        label = Label(len(self.labels))
        self.labels.add(label)
        return label

    def bp(self, label: Label, node: typing.Union[Label, ControlFlowNode]):
        to_remove = []
        to_add = []
        for edge in self.edges:
            if edge.source == label == edge.target:
                to_remove.append(edge)
                to_add.append(ControlFlowEdge(node, node, edge.action))
            elif edge.source == label:
                to_remove.append(edge)
                to_add.append(ControlFlowEdge(node, edge.target, edge.action))
            elif edge.target == label:
                to_remove.append(edge)
                to_add.append(ControlFlowEdge(edge.source, node, edge.action))
        for edge in to_remove:
            self.edges.remove(edge)
        for edge in to_add:
            self.edges.add(edge)

    def bp_list(self, lst: List[Tuple[Label, typing.Union[Label, ControlFlowNode]]]):
        for i in range(len(lst) - 1):
            _, end = lst[i]
            start, _ = lst[i + 1]
            self.bp(end, start)

    def _dfs(self, node: ControlFlowNode, depth_bound: int, end_node: ControlFlowNode, path: List[ControlFlowEdge]):
        if depth_bound == 0:
            return
        if node == end_node:
            yield path
        for edge in self.edges:
            if edge.source == node:
                yield from self._dfs(edge.target, depth_bound - 1, end_node, path + [edge])

    def dfs(self, depth_bound: int, end_node: ControlFlowNode = None):
        if end_node is None:
            end_node = self.end
        return list(self._dfs(self.start, depth_bound, end_node, []))

    def get_transition_relation_until(self, end_node: ControlFlowNode, depth_bound: int = 100) -> \
            Callable[[State, State], ExprRef]:
        edge_paths = self.dfs(depth_bound, end_node)
        lambdas = [functools.reduce(lambda f, g: lambda x: g(f(x)),
                                    [edge.perform_action for edge in edge_path], lambda x: x)
                   for edge_path in edge_paths]

        def tr(state0: State, state1: State) -> ExprRef:
            assert all(it in state0.sig.decls and it in state1.sig.decls for it in self.get_signature().decls)
            computation_paths = []
            for action in lambdas:
                new_state = action(state0)
                path = simplify(And(*[it for it in new_state.assumptions], state1 == new_state))
                if path is not False:
                    computation_paths.append(path)
            return simplify(Or(*computation_paths))

        return tr

    def get_transition_relation(self, depth_bound: int = 100) -> Callable[[State, State], ExprRef]:
        return self.get_transition_relation_until(self.end, depth_bound)

    def fresh_var(self, typ: typing.Any, prefix: str = "var") -> str:
        ControlFlowGraph.var_count += 1
        new_var = f"__{prefix}{ControlFlowGraph.var_count}__"
        self.report_type(new_var, typ)
        return new_var

    def clean_cfg(self):
        # remove unused labels
        to_remove = []
        for edge in self.edges:
            if isinstance(edge.source, Label) or isinstance(edge.target, Label):
                to_remove.append(edge)
        for edge in to_remove:
            self.edges.remove(edge)
        self.labels = []

        # remove unreachable nodes
        reachable = {self.start}
        to_visit = [self.start]
        while to_visit:
            node = to_visit.pop()
            for edge in self.edges:
                if edge.source == node:
                    if edge.target not in reachable:
                        reachable.add(edge.target)
                        to_visit.append(edge.target)
        self.nodes = list(reachable)

        # remove skip nodes
        for _ in self.nodes:
            self._clean_skip()
        self.nodes = list(filter(lambda x: x.label != ControlFlowGraph.PASS, self.nodes))

        # clean useless edges (must be done after skip removal)
        to_remove = []
        for edge in self.edges:
            if edge.source not in self.nodes or edge.target not in self.nodes:
                to_remove.append(edge)
        for edge in to_remove:
            self.edges.remove(edge)

    def export_to_dot(self):
        from graphviz import Digraph
        dot = Digraph()
        for node in self.nodes:
            dot.node(str(node), node.label)
        for label in self.labels:
            dot.node(str(label))
        for edge in self.edges:
            dot.edge(str(edge.source), str(edge.target), edge.action)
        return dot

    def _clean_skip(self):
        to_add = set()
        for edge1 in self.edges:
            if edge1.target.label == ControlFlowGraph.PASS:
                for edge2 in self.edges:
                    if edge2.source == edge1.target:
                        if edge1.action == "s":
                            action = edge2.action
                        elif edge2.action == "s":
                            action = edge1.action
                        else:
                            action = f"((lambda s: ({edge1.action}))({edge2.action}))"
                        to_add.add(ControlFlowEdge(edge1.source, edge2.target, action))
        self.edges.update(to_add)

    def get_signature(self):
        sig = Signature(self.types)
        sig.use({str(ty): ty for k, ty in self.system.class_types.items()})
        return sig

    def compute_actions(self):
        # BFS on the graph
        to_visit = [self.start]
        visited = set()
        while to_visit:
            node = to_visit.pop()
            if node in visited:
                continue
            visited.add(node)
            for edge in self.edges:
                if edge.source == node:
                    edge.action = ControlFlowGraph._compute_action(edge)
                    to_visit.append(edge.target)

    @staticmethod
    def _compute_action(edge: ControlFlowEdge) -> str:
        if isinstance(edge.action, str):
            return edge.action
        return edge.action.compute()

    def has_type(self, expr: Any) -> bool:
        return expr is not None and ControlFlowGraph.get_literal_type(expr) is not None or \
            expr in self.types

    @property
    def return_type(self):
        return self.types[self.return_var]
