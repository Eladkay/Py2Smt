import _ast
import ast
import sys
from _ast import AST
from typing import Union, List

from z3 import ArraySortRef, SeqSortRef

import smt_helper
from cfg import ControlFlowGraph
from generators import misc_generators
from generators.generators import AbstractCodeGenerator, handles, \
    DecoratedDataNode, CodeGenerationDispatcher, syntactic_replace
from smt_helper import *
from symbolic_interp import Signature


@handles(_ast.Constant)
class ConstantCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedDataNode:
        new_node = self.graph.add_node(f"pass")
        new_label = self.graph.fresh_label()
        self.graph.add_edge(new_node, new_label)
        if isinstance(node.value, str):
            val = f"\\\"{node.value}\\\"" if isinstance(node.value, str) else node.value
        else:
            val = node.value
        return DecoratedDataNode("const", node, new_node, new_label, val)


@handles(_ast.Name)
class NameCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedDataNode:
        new_node = self.graph.add_node(f"pass")
        new_label = self.graph.fresh_label()
        self.graph.add_edge(new_node, new_label)
        return DecoratedDataNode("name", node, new_node, new_label, node.id)


op_return_types = {ast.Pow: IntType, ast.Sub: IntType, ast.Mult: IntType, ast.Div: IntType,
                   ast.FloorDiv: IntType, ast.Mod: IntType, ast.Eq: BoolType, ast.NotEq: BoolType,
                   ast.Lt: BoolType, ast.LtE: BoolType, ast.Gt: BoolType, ast.GtE: BoolType,
                   ast.Is: BoolType, ast.IsNot: BoolType, ast.In: BoolType, ast.NotIn: BoolType}


@handles(_ast.BinOp)
class BinOpCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedDataNode:
        left_decorated = self._process_expect_data(node.left)
        right_decorated = self._process_expect_data(node.right)
        start1, expr1, end1 = left_decorated.start_node, left_decorated.place, left_decorated.end_label
        start2, expr2, end2 = right_decorated.start_node, right_decorated.place, right_decorated.end_label
        if type(node.op) == ast.Add:
            new_var = self.graph.fresh_var(self.graph.types[expr1])
        else:
            new_var = self.graph.fresh_var(op_return_types[type(node.op)])
        op_string = misc_generators.ops[type(node.op)]
        new_node = self.graph.add_node(f"{new_var} = {expr1} {op_string} {expr2}")
        self.graph.bp(end1, start2)
        self.graph.bp(end2, new_node)
        new_label = self.graph.fresh_label()
        self.graph.add_edge(new_node, new_label, "s.assign({" + f"'{new_var}': '{expr1} {op_string} {expr2}'" + "})")
        return DecoratedDataNode("binop", node, start1, new_label, new_var)


@handles(_ast.Dict)
class DictCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> DecoratedDataNode:
        if len(node.keys) == 0:
            new_var = f"K(IntSort(), {Signature.get_or_create_optional_type(smt_helper.IntType)}.none)"
            new_node = self.graph.add_node(ControlFlowGraph.PASS)
            new_label = self.graph.fresh_label()
            self.graph.add_edge(new_node, new_label)  # note: can't infer sort of empty dicts!
            return DecoratedDataNode("dict", node, new_node, new_label, new_var)

        starts_keys, exprs_keys, ends_keys = zip(*[(item.start_node, item.place, item.end_label)
                                                   for item in [self._process_expect_data(it)
                                                                for it in node.keys]])
        starts_and_ends_keys = [(start, end) for start, end in zip(starts_keys, ends_keys)]

        starts_values, exprs_values, ends_values = zip(*[(item.start_node, item.place, item.end_label)
                                                         for item in [self._process_expect_data(it)
                                                                      for it in node.values]])
        starts_and_ends_values = [(start, end) for start, end in zip(starts_values, ends_values)]

        self.graph.bp_list(starts_and_ends_keys)
        self.graph.bp(ends_keys[-1], starts_values[0])
        self.graph.bp_list(starts_and_ends_values)
        key_type = self.graph.get_type(exprs_keys[0])
        value_type = self.graph.get_type(exprs_values[0])
        optional = Signature.get_or_create_optional_type(value_type)
        store = f"K({ControlFlowGraph.type_to_place_string(key_type)}, {optional}.none)"
        for k, v in zip(exprs_keys, exprs_values):
            store = f"Store({store}, {k}, {optional}.some({v}))"

        return DecoratedDataNode("dict", node, starts_keys[0], ends_values[-1], store)


@handles(ast.BoolOp)
class BoolOpCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> DecoratedDataNode:
        return self._process_expect_data(ast.Call(func=ast.Name(id=node.op.__class__.__name__), args=node.values))


@handles(ast.Compare)
class CompareCodeGenerator(AbstractCodeGenerator):
    def is_applicable_on_node(self, node: AST) -> bool:
        return len(node.ops) == 1 and len(node.comparators) == 1

    def process_node(self, node: AST) -> DecoratedDataNode:
        comparator = node.comparators[0]
        op = node.ops[0]
        if isinstance(op, ast.NotIn):
            start, var, label = self._process_expect_data(ast.Compare(left=node.left,
                                                                      ops=[ast.In()], comparators=[comparator]))
            return DecoratedDataNode("compare", node, start, label, f"Not({var})")
        elif isinstance(op, ast.In):
            left = self._process_expect_data(node.left)
            right = self._process_expect_data(comparator)
            start_left, var_left, end_left = left.start_node, left.place, left.end_label
            start_right, var_right, end_right = right.start_node, right.place, right.end_label
            self.graph.bp(end_left, start_right)
            right_type = self.graph.get_type(var_right)
            if isinstance(right_type, ArraySortRef) and right_type.range() == smt_helper.BoolType:
                return DecoratedDataNode("in", node, start_left, end_right, f"IsMember({var_left}, {var_right})")
            elif isinstance(right_type, ArraySortRef) and right_type.range().name().endswith("Option"):
                value_type = right_type.range()
                return DecoratedDataNode("in", node, start_left, end_right,
                                         f"Select({var_right}, {var_left}) != {value_type}.none")
            elif isinstance(self.graph.get_type(var_right), ArraySortRef):
                new_var = self.graph.fresh_var(smt_helper.BoolType)
                return DecoratedDataNode("in", node, start_left, end_right,
                                         f"Exists({new_var}, {var_right}[{new_var}] == {var_left})")
            else:
                raise NotImplementedError(f"Cannot handle inclusion checks for {type(self.graph.get_type(var_right))}")

        return self._process_expect_data(ast.BinOp(left=node.left, op=op, right=comparator))


@handles(ast.UnaryOp)
class UnaryOpCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> DecoratedDataNode:
        if isinstance(node.op, ast.Not):
            return self._process_expect_data(ast.Call(func=ast.Name(id="Not"), args=[node.operand]))
        operand = self._process_expect_data(node.operand)
        start, expr, end = operand.start_node, operand.place, operand.end_label
        new_var = self.graph.fresh_var(smt_helper.IntType)
        op_string = misc_generators.unaryops[type(node.op)]
        new_node = self.graph.add_node(f"{new_var} = {op_string} {expr}")
        self.graph.bp(end, new_node)
        new_label = self.graph.fresh_label()
        self.graph.add_edge(new_node, new_label, "s.assign({" + f"'{new_var}': '{op_string} {expr}'" + "})")
        return DecoratedDataNode("unaryop", node, start, new_label, new_var)


@handles(ast.Subscript)
class SubscriptCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> Union[DecoratedDataNode, None]:
        if isinstance(node.ctx, _ast.Store):
            return None
        value = self._process_expect_data(node.value)
        index = self._process_expect_data(node.slice)
        start1, expr1, end1 = value.start_node, value.place, value.end_label
        start2, expr2, end2 = index.start_node, index.place, index.end_label
        self.graph.bp(end1, start2)
        new_label = self.graph.fresh_label()
        value_type = self.graph.get_type(expr1)

        if isinstance(value_type, ArraySortRef) and value_type.range().name().endswith("Option"):
            value_sort = value_type.range()
            new_var = self.graph.fresh_var(value_sort.constructor(0).domain(0))
            new_node = self.graph.add_node(f"{new_var} = {expr1}[{expr2}]")
            self.graph.bp(end2, new_node)
            self.graph.add_edge(new_node, new_label,
                                "s.assign({" + f"'{new_var}': '{value_sort}.val({expr1}[{expr2}])'" + "})")
        elif isinstance(value_type, SeqSortRef):
            value_sort = smt_helper.StringType if value_type.is_string() else value_type.basis()
            new_var = self.graph.fresh_var(value_sort)
            new_node = self.graph.add_node(f"{new_var} = {expr1}[{expr2}]")
            self.graph.bp(end2, new_node)
            self.graph.add_edge(new_node, new_label,
                                "s.assign({" + f"'{new_var}': 'SubString({expr1}, {expr2}, 1)'" + "})")
        else:
            value_sort = value_type.range()
            new_var = self.graph.fresh_var(value_sort)
            new_node = self.graph.add_node(f"{new_var} = {expr1}[{expr2}]")
            self.graph.bp(end2, new_node)
            self.graph.add_edge(new_node, new_label, "s.assign({" + f"'{new_var}': '{expr1}[{expr2}]'" + "})")
        return DecoratedDataNode("subscript", node, start1, new_label, new_var)


@handles(ast.Set)
class SetCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> DecoratedDataNode:
        if len(node.elts) == 0:
            new_node = self.graph.add_node(ControlFlowGraph.PASS)
            new_label = self.graph.fresh_label()
            self.graph.add_edge(new_node, new_label)
            return DecoratedDataNode("set", node, new_node, new_label, "EmptySet(IntSort())")
        starts, exprs, ends = zip(*[(item.start_node, item.place, item.end_label)
                                    for item in [self._process_expect_data(it) for it in node.elts]])
        starts_and_ends = [(start, end) for start, end in zip(starts, ends)]
        self.graph.bp_list(starts_and_ends)
        store = f"EmptySet({ControlFlowGraph.type_to_place_string(self.graph.get_type(exprs[0]))})"
        for expr in exprs:
            store = f"Store({store}, {expr}, True)"
        return DecoratedDataNode("set", node, starts[0], ends[-1], store)


@handles(ast.Call)
class FunctionCallCodeGenerator(AbstractCodeGenerator):
    def is_applicable_on_node(self, node: AST) -> bool:
        if not isinstance(node.func, ast.Name) and not isinstance(node.func, ast.Attribute):
            return False
        return True

    @staticmethod
    def _syntactic_param_replace(transformed: AST, args: List[str], exprs: List[_ast.expr]) -> AST:
        for arg, expr in zip(args, exprs):
            transformed = syntactic_replace(arg, expr, transformed)
        return transformed

    @staticmethod
    def _syntactic_receiver_replace(transformed: AST, name: str, receiver: Union[None, str]) -> AST:
        def check_receiver():
            if receiver is None:
                raise ValueError(f"Called member function {name} without receiver.")
        return syntactic_replace(f"{name}_self", _ast.Name(receiver), transformed, check_receiver)

    def process_node(self, node: AST) -> DecoratedDataNode:
        name = node.func.id if isinstance(node.func, ast.Name) else node.func.attr
        receiver = self._process_expect_data(node.func.value).place if isinstance(node.func, ast.Attribute) else None
        args = [(arg.start_node, arg.place, arg.end_label)
                for arg in [self._process_expect_data(it) for it in node.args]]
        starts, exprs, ends = zip(*args) if len(args) > 0 else ([], [], [])
        starts_and_ends = [(start, end) for start, end in zip(starts, ends)]
        self.graph.bp_list(starts_and_ends)
        if not self.graph.system.has_entry(name, None if receiver is None else self.graph.get_type(receiver)) \
                and name in dir(z3):
            new_node = self.graph.add_node(ControlFlowGraph.PASS)
            new_label = self.graph.fresh_label()
            self.graph.add_edge(new_node, new_label)
            return DecoratedDataNode("z3_call", node, new_node, new_label, f"{name}({', '.join(map(str, exprs))})")

        called_function = self.graph.system.get_entry_by_name(name,
                                                              None if receiver is None
                                                              else self.graph.get_type(receiver))
        params = called_function.args

        if len(params) == len(exprs) + 1:
            assert params[0] == "self"
            params = params[1:]

        if called_function.name == "__literal__":
            if len(exprs) != 1:
                raise Exception("Literal expression should have exactly one argument")
            s = exprs[0]
            if not isinstance(s, _ast.Constant) or not isinstance(s.value, str):
                raise Exception("Literal expression should have a constant string argument")
            new_node = self.graph.add_node(f"return {s.value}")
            new_label = self.graph.fresh_label()
            self.graph.add_edge(new_node, new_label)
            self.graph.bp(ends[0], new_node)
            return DecoratedDataNode("literal_call", node, new_node, new_label, s.value)

        replaced_args = FunctionCallCodeGenerator._syntactic_param_replace(called_function.ast, params,
                                                                           [_ast.Name(it) for it in exprs])
        replaced_args.body[0].args = ast.arguments()

        local_vars = list(it for it in called_function.cfg.types.keys() if it not in params)
        tagged_local_vars = {it: _ast.Name(f"{name}_{it}") for it in local_vars}
        replaced_locals = FunctionCallCodeGenerator._syntactic_param_replace(replaced_args, local_vars,
                                                                             list(tagged_local_vars.values()))
        for k, v in tagged_local_vars.items():
            self.graph.report_type(v.id, called_function.cfg.types[k])

        replaced_receiver = FunctionCallCodeGenerator._syntactic_receiver_replace(replaced_locals, name, receiver) \
            if receiver is not None else replaced_locals

        new_cfg = ControlFlowGraph(self.graph.system, replaced_receiver.body[0].name, called_function.cls)
        new_cfg.types.update({f"{name}_{k}": v for k, v in called_function.cfg.types.items()})

        new_cfg.var_count = self.graph.var_count
        new_dispatcher = CodeGenerationDispatcher(new_cfg)
        new_dispatcher.compute_graph(replaced_receiver)

        self.graph.var_count = new_cfg.var_count

        new_cfg.clean_cfg()

        func_start, func_end = self.graph.add_all(new_cfg)
        if len(args) > 0:
            self.graph.bp(ends[-1], func_start)
        self.graph.types.update(new_cfg.types)
        new_label = self.graph.fresh_label()
        if new_cfg.return_var is not None:
            new_var = new_cfg.return_var
            new_node = self.graph.add_node(f"{new_var} = {name}({', '.join(map(str, exprs))})")
        else:
            new_var = "0"
            new_node = self.graph.add_node(f"{name}({', '.join(map(str, exprs))})")
        self.graph.add_edge(new_node, new_label)
        self.graph.bp(func_end, new_node)
        return DecoratedDataNode("regular_call", node, starts[0] if len(args) > 0 else func_start, new_label, new_var)


@handles(ast.Attribute)
class AttributeCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> Union[DecoratedDataNode, None]:
        if isinstance(node.ctx, _ast.Store) or (isinstance(node.value, _ast.Name) and node.value.id in sys.modules):
            return None
        value = self._process_expect_data(node.value)
        start, expr, end = value.start_node, value.place, value.end_label
        receiver_type = self.graph.get_type(expr)
        if not self.graph.system.is_field_of_class(receiver_type, node.attr):
            # try finding it as a method: if it's a method, no node needs to be created
            receiver_type = receiver_type.name()
            if (receiver_type, node.attr) in self.graph.system.methods:
                return None
            else:
                raise Exception(f"Cannot find field {node.attr} in {receiver_type}")
        field_type = self.graph.system.get_type_from_field(receiver_type, node.attr)
        new_var = self.graph.fresh_var(field_type)
        new_node = self.graph.add_node(f"{new_var} = {expr}.{node.attr}")
        self.graph.bp(end, new_node)
        new_label = self.graph.fresh_label()
        self.graph.add_edge(new_node, new_label,
                            "s.assign({" + f"'{new_var}': '{receiver_type}.{node.attr}({expr})'" + "})")
        return DecoratedDataNode("attribute", node, new_node, new_label, new_var)


@handles(ast.List)
class ListCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> DecoratedDataNode:
        if len(node.elts) == 0:
            new_node = self.graph.add_node(ControlFlowGraph.PASS)
            new_label = self.graph.fresh_label()
            self.graph.add_edge(new_node, new_label)
            return DecoratedDataNode("list", node, new_node, new_label, 'K(IntSort(), 0)')
        starts, exprs, ends = zip(*[(item.start_node, item.place, item.end_label)
                                    for item in [self._process_expect_data(it) for it in node.elts]])
        starts_and_ends = [(start, end) for start, end in zip(starts, ends)]
        self.graph.bp_list(starts_and_ends)
        list_type = self.graph.get_type(exprs[0])
        store = f"K(IntSort(), {ControlFlowGraph.get_place_of_default_value(list_type)})"
        for idx, expr in enumerate(exprs):
            store = f"Store({store}, {idx}, {expr})"
        return DecoratedDataNode("list", node, starts[0], ends[-1], store)