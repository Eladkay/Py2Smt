import typing
from collections import OrderedDict
from typing import Any, Callable
import sys

from z3 import IntSort, ArithSortRef

from .cfg import ControlFlowGraph, ControlFlowNode
from .symbolic_interp import Signature


class Lattice:
    top: Any
    bottom: Any
    meet: Callable[[Any, Any], Any]
    join: Callable[[Any, Any], Any]

    def __init__(self, top: Any, bottom: Any, meet: Callable[[Any, Any], Any], join: Callable[[Any, Any], Any]):
        self.top = top
        self.bottom = bottom
        self.meet = meet
        self.join = join

    def join_all(self, values: list) -> Any:
        result = self.bottom
        for value in values:
            result = self.join(result, value)
        return result

    def meet_all(self, values: list) -> Any:
        result = self.top
        for value in values:
            result = self.meet(result, value)
        return result


class GraphFixedPointAnalysis:
    graph: ControlFlowGraph
    lattice: Lattice

    def __init__(self, graph: ControlFlowGraph, lattice: Lattice):
        self.graph = graph
        self.lattice = lattice
        self.results = {node: None for node in self.graph.nodes}

    def get_result(self) -> Any:
        return self.results

    def analysis_step(self, node: ControlFlowNode):
        pass

    def iterate(self, max_steps: int = 50) -> Any:
        worklist = list(self.graph.nodes)
        steps = 0
        while worklist and steps < max_steps:
            node = worklist.pop()
            old_result = self.results[node]
            self.analysis_step(node)
            if self.results[node] != old_result:
                worklist.append(node)
            steps += 1


class AbstractSignature:
    decls: OrderedDict[str, Lattice]

    def __init__(self, decls: typing.Union[dict, typing.List[typing.Tuple[str, Lattice]]]):
        self.decls = OrderedDict((name, ty for (name, ty) in decls.items()))


class AbstractState:
    sig: AbstractSignature

    def __init__(self, sig: AbstractSignature):
        self.sig = sig
        self.locals = {name: ty.top for (name, ty) in sig.decls.items()}
        self.assumptions = []

    def assign(self, var: str, abstract_val: Any):
        c = self.clone()
        c.locals[var] = abstract_val
        return c

    def eval(self, expr: Any) -> Any:
        if callable(expr):
            expr = expr(self)
        if isinstance(expr, str):
            try:
                expr = eval(expr)
            except Exception as exp:
                raise Exception("Failed to evaluate %s (%s)" % (expr, exp))
        return expr

    def assume(self, cond: Any):
        cond = self.eval(cond)
        cloned = self.clone()
        cloned.assumptions.append((cond.get_id(), cond))
        return cloned

    def clone(self):
        c = type(self)(self.sig)
        c.locals = self.locals.copy()
        c.assumptions = self.assumptions.copy()
        return c


class GraphIntervalAnalysis(GraphFixedPointAnalysis):
    MIN_INT = -100
    MAX_INT = 100

    class IntervalLattice(Lattice):
        def __init__(self):
            super().__init__((GraphIntervalAnalysis.MIN_INT, GraphIntervalAnalysis.MAX_INT),
                             (GraphIntervalAnalysis.MAX_INT, GraphIntervalAnalysis.MIN_INT),
                             lambda a, b: (max(a[0], b[0]), min(a[1], b[1])),
                             lambda a, b: (min(a[0], b[0]), max(a[1], b[1])))

    def __init__(self, graph: ControlFlowGraph):
        super().__init__(graph, GraphIntervalAnalysis.IntervalLattice())
        self.results = {node: {var: self.lattice.top
                               for var in graph.types
                               if isinstance(graph.types[var], ArithSortRef)}
                        for node in self.graph.nodes}

    def analysis_step(self, node: ControlFlowNode):
        pass
