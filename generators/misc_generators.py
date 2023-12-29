"""
This module contains various code generators for AST nodes that
do not fall under any other category, but are nonetheless supported.
"""

import _ast
import ast
import typing
from _ast import AST

from cfg import ControlFlowGraph
from generators.generators import AbstractCodeGenerator, DecoratedLeafNode, handles, \
    DecoratedControlNode, DecoratedDataNode
from smt_helper import get_or_create_pointer


# List of nodes that do not require any code generation.
nop = [ast.arguments, ast.Load, ast.Store, ast.FunctionDef, ast.Tuple]


@handles(nop)
class NopCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedLeafNode:
        return DecoratedLeafNode("nop", node, {"node": node})


@handles(_ast.arg)
class ArgCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedLeafNode:
        if node.annotation is not None:
            self.graph.report_type(node.arg,
                                   self.graph.system.get_type_from_annotation(node.annotation))
        elif node.arg == "self":
            self.graph.report_type("self", get_or_create_pointer(self.graph.system.class_types[self.graph.cls])
            if self.graph.cls is not None and
               isinstance(self.graph.cls, typing.Hashable) and
               self.graph.cls in self.graph.system.class_types else self.graph.cls)

        return DecoratedLeafNode("arg", node, {"arg": node.arg})


ops = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.Div: '/', ast.FloorDiv: "/", ast.Mod: '%',
       ast.Pow: '**', ast.LShift: '<<', ast.RShift: '>>', ast.Eq: "==",
       ast.NotEq: "!=", ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">=",
       ast.Is: "is", ast.IsNot: "is not", ast.In: "in", ast.NotIn: "not in"}
unaryops = {ast.Not: "not", ast.UAdd: "+", ast.USub: "-"}
boolops = [ast.And, ast.Or]


@handles(list(ops.keys()))
class BinOpCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedLeafNode:
        return DecoratedLeafNode("binop", node, {"op": ops[type(node)]})


@handles(list(unaryops.keys()))
class UnaryOpCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedLeafNode:
        return DecoratedLeafNode("unop", node, {"op": unaryops[type(node)]})


@handles(boolops)
class BoolOpCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedLeafNode:
        return DecoratedLeafNode("boolop", node, {"op": type(node).__name__})


@handles(_ast.Module)
class ModuleCodeGenerator(AbstractCodeGenerator):

    def is_applicable_on_node(self, node: AST) -> bool:
        return len(node.body) == 1

    def process_node(self, node: AST) -> DecoratedControlNode:
        function_body = node.body[0].body
        processed_statements = [self._process_expect_control(stmt) for stmt in function_body]
        self.graph.bp_list([(stmt.start_node, stmt.end_label) for stmt in processed_statements])
        self.graph.bp(self._process_expect_control(function_body[-1]).end_label, self.graph.end)
        self.graph.add_edge(self.graph.start,
                            self._process_expect_control(function_body[0]).start_node)
        return DecoratedControlNode("module", node, self.graph.start, self.graph.end)


@handles(_ast.Expr)
class ExprCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedControlNode:
        res = self._process(node.value)
        assert isinstance(res, (DecoratedControlNode, DecoratedDataNode))
        return DecoratedControlNode("expr", node, res.start_node, res.end_label)


@handles(_ast.Pass)
class PassCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedControlNode:
        idx = self.graph.add_node(ControlFlowGraph.PASS)
        label = self.graph.fresh_label()
        self.graph.add_edge(idx, label)
        return DecoratedControlNode("pass", node, idx, label)
