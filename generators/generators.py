import ast
from _ast import AST, expr
from collections import defaultdict
from dataclasses import dataclass
from typing import Type, Union, List, NoReturn, Callable, Optional

from copy import deepcopy
from z3 import SortRef
from cfg import ControlFlowGraph, ControlFlowNode, Label
from common import Py2SmtException
from smt_helper import get_or_create_pointer

node_types = defaultdict(list)


def handles(typ: Union[Type, List[Type]]):
    def decorator(cls):
        global node_types
        if isinstance(typ, list):
            for t in typ:
                node_types[t].append(cls)
        else:
            node_types[typ].append(cls)
        return cls

    return decorator


@dataclass
class DecoratedAst:
    ty: str
    ast_node: AST


@dataclass
class DecoratedDataNode(DecoratedAst):
    start_node: ControlFlowNode
    end_label: Label
    place: str
    value_type: Optional[SortRef]


@dataclass
class DecoratedControlNode(DecoratedAst):
    start_node: ControlFlowNode
    end_label: Label


@dataclass
class DecoratedLeafNode(DecoratedAst):
    data: dict


# noinspection PyUnresolvedReferences
class CodeGenerationDispatcher:
    graph: ControlFlowGraph

    def __init__(self, graph: ControlFlowGraph):
        self.graph = graph
        self.generated = {}
        import generators.control_flow_generators
        import generators.expression_generators
        import generators.statement_generators
        import generators.misc_generators
        import generators.for_loop_generators
        self.generators = {k: [it(self) for it in v] for k, v in node_types.items()}

    def _postorder(self, tree: AST):
        for field, value in ast.iter_fields(tree):
            if field in ("annotation", "returns"):
                continue
            if isinstance(value, list):
                for item in value:
                    if isinstance(item, AST):
                        yield from self._postorder(item)
            elif isinstance(value, AST):
                yield from self._postorder(value)
        yield tree

    def process(self, root: AST) -> DecoratedAst:
        if root in self.generated:
            return self.generated[root]
        for node in self._postorder(root):
            if type(node) in self.generators:
                generators = self.generators[type(node)]
                for generator in generators:
                    if generator.is_applicable_on_node(node):
                        self.generated[node] = generator.process_node(node)
                        break
                else:
                    raise Py2SmtException(f"No generator for type {type(node)} "
                                          f"is suitable for node {ast.dump(node)}")
            else:
                raise NotImplementedError(f"Node type {type(node)} not implemented")
        return self.generated[root]

    def compute_graph(self, tree: AST):
        assert isinstance(tree, ast.Module)
        returns = tree.body[0].returns
        if self.graph.name == "__init__":
            self.graph.return_var = self.graph.fresh_var(get_or_create_pointer(self.graph.cls), "ret")
        elif returns is None:
            self.graph.return_var = None
        else:
            self.graph.return_var = self.graph.fresh_var(self.graph.system.get_type_from_annotation(returns), "ret")
        self.process(tree)
        if self.graph.break_label is not None or self.graph.continue_label is not None:
            raise Exception("Break or continue outside of loop")


class AbstractCodeGenerator:

    def __init__(self, disp: CodeGenerationDispatcher):
        self.dispatcher = disp

    @property
    def graph(self) -> ControlFlowGraph:
        return self.dispatcher.graph

    def is_applicable_on_node(self, node: AST) -> bool:
        return True

    def _process(self, node: AST) -> DecoratedAst:
        return self.dispatcher.process(node)

    def _process_expect_control(self, node: AST) -> DecoratedControlNode:
        res = self._process(node)
        assert res is not None, f"Node {ast.dump(node)} returned None"
        assert isinstance(res, DecoratedControlNode), f"Node {ast.dump(node)} returned {type(res)}"
        return res

    def _process_expect_data(self, node: AST) -> DecoratedDataNode:
        res = self._process(node)
        assert res is not None, f"Node {ast.dump(node)} returned None"
        assert isinstance(res, DecoratedDataNode), f"Node {ast.dump(node)} returned {type(res)}"
        return res

    def process_node(self, node: AST) -> Union[DecoratedAst, None]:
        return None

    def type_error(self, message: str) -> NoReturn:
        raise Py2SmtException(f"type error: {message}")


def syntactic_replace(name: str, value: expr, tree: AST, action: Callable = (lambda: 0)) -> AST:
    class SynReplace(ast.NodeTransformer):
        def visit_Name(self, node):
            if node.id == name:
                action()
                return value
            return node

    return SynReplace().visit(deepcopy(tree))
