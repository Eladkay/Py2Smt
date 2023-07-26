import ast
from _ast import AST
from dataclasses import dataclass
from typing import Type, Union, List, Any, NoReturn

from cfg import ControlFlowGraph, ControlFlowNode, Label
from common import Py2SmtException


node_types = {}


def handles(typ: Union[Type, List[Type]]):
    def decorator(cls):
        global node_types
        if isinstance(typ, list):
            for t in typ:
                node_types[t] = cls
        else:
            node_types[typ] = cls
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


@dataclass
class DecoratedControlNode(DecoratedAst):
    start_node: ControlFlowNode
    end_label: Label


@dataclass
class DecoratedLeafNode(DecoratedAst):
    data: dict


# noinspection PyUnresolvedReferences
class CodeGenerationDispatcher:
    def __init__(self, graph: ControlFlowGraph):
        self.graph = graph
        self.generated = {}
        import generators.control_flow_generators
        import generators.expression_generators
        import generators.statement_generators
        import generators.misc_generators
        self.generators = {k: v(self) for k, v in node_types.items()}

    def _postorder(self, tree: AST):
        for field, value in ast.iter_fields(tree):
            if field == "annotation" or field == "returns":
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
                generator = self.generators[type(node)]
                if not generator.is_applicable_on_node(node):
                    raise Py2SmtException(f"Assumptions for node type {type(node)} violated in node {ast.dump(node)}")
                    # todo?
                self.generated[node] = generator.process_node(node)
            else:
                raise NotImplementedError(f"Node type {type(node)} not implemented")
        return self.generated[root]

    def compute_graph(self, tree: AST):
        returns = tree.body[0].returns
        if returns is None:
            self.graph.return_var = None
        else:
            self.graph.return_var = self.graph.fresh_var(self.graph.system.get_type_from_annotation(returns), "ret")
        self.process(tree)
        if self.graph.break_label is not None or self.graph.continue_label is not None:
            raise Exception("Break or continue outside of loop")
        self.graph.compute_actions()


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
        if res is None:
            raise Py2SmtException(f"Node {ast.dump(node)} returned None")
        assert isinstance(res, DecoratedControlNode)
        return res

    def _process_expect_data(self, node: AST) -> DecoratedDataNode:
        res = self._process(node)
        if res is None:
            raise Py2SmtException(f"Node {ast.dump(node)} returned None")
        assert isinstance(res, DecoratedDataNode)
        return res

    def process_node(self, node: AST) -> Union[DecoratedAst, None]:
        return None

    def type_error(self, message: str) -> NoReturn:
        raise Py2SmtException(f"type error: {message}")


def checked_cast(ty: Type, value: Any) -> Any:
    assert isinstance(ty, value), f"Expected {ty}, got {type(value)}"
