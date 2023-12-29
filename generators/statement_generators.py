import _ast
import ast
from _ast import AST

from z3 import ArraySortRef, SeqSortRef

from cfg import ControlFlowGraph, ControlFlowNode
from generators.generators import AbstractCodeGenerator, DecoratedAst, handles, \
    DecoratedControlNode, DecoratedDataNode
from smt_helper import IntType, get_heap_name, is_pointer_type


@handles(_ast.AugAssign)
class AugAssignCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> DecoratedAst:
        node.target.ctx = ast.Load()

        op = ast.BinOp(left=node.target, op=node.op, right=node.value)

        assign = ast.Assign(targets=[node.target], value=op)
        decorated = self._process(assign)
        return decorated


@handles(_ast.AnnAssign)
class AnnAssignCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> DecoratedAst:
        self.graph.report_type(node.target.id, self.graph.system.get_type_from_annotation(node.annotation))
        return self._process(ast.Assign(targets=[node.target], value=node.value))


def generate_code_for_subscript(array: DecoratedDataNode, index: DecoratedDataNode, value: DecoratedDataNode,
                                gen: AbstractCodeGenerator) -> (str,) * 4 + (ControlFlowNode,):
    graph = gen.graph
    if not graph.has_type(array.place):
        gen.type_error(f"Variable {array.place} does not exist!")
    arr_type, idx_type, value_type = graph.get_type(array.place), \
        graph.get_type(index.place), graph.get_type(value.place)
    if not isinstance(arr_type, ArraySortRef) and not isinstance(arr_type, SeqSortRef):
        gen.type_error(f"Variable {array.place} is not an array or dict!")

    domain = arr_type.domain() if isinstance(arr_type, ArraySortRef) else IntType
    rang = arr_type.range() if isinstance(arr_type, ArraySortRef) else arr_type.basis()
    if idx_type != domain:
        gen.type_error(f"{index.place} is not in the domain {domain} of {array.place}!")

    idx_start, idx_place, idx_end = index.start_node, index.place, index.end_label
    value_start, value_place, value_end = value.start_node, value.place, value.end_label
    arr_start, arr_place, arr_end = array.start_node, array.place, array.end_label

    if value_type != rang and not rang.name().endswith("Option") and \
            value_type.name() != rang.name()[:-len("Option")]:
        gen.type_error(f"Type of {value_place} does not match the stored type of {arr_place}! "
                       f"types: {value_type} != {rang}")

    if rang.name().endswith("Option"):
        value_type = arr_type.range()
        value_place = f"{value_type.name()}.some({value_place})"

    new_arr = f"Store({arr_place}, {idx_place}, {value_place})" if isinstance(arr_type, ArraySortRef) \
        else f"Concat(Concat(Extract({arr_place}, 0, {idx_place}), " \
             f"singleton_list({value_place})), " \
             f"Extract({arr_place}, {idx_place} + 1, Length({arr_place}) - {idx_place}))"
    if isinstance(array.ast_node, _ast.Name):
        graph.bp(arr_end, idx_start)
        graph.bp(idx_end, value_start)

        left_place = arr_place
        left_start = arr_start
        right_place = new_arr
        right_end = value_end
        new_node = graph.add_node(f"{arr_place}[{idx_place}] = {value_place}")

    elif isinstance(array.ast_node, _ast.Attribute):
        recv, attr = gen._process_expect_data(array.ast_node.value), array.ast_node.attr
        recv_place = recv.place
        recv_type = graph.get_type(recv_place)
        pointed_type = graph.system.get_pointed_type(recv_type)
        if not graph.system.is_field_of_class(pointed_type, attr):
            gen.type_error(f"Field {attr} is not declared! "
                           f"A type annotation is needed before use.")
        graph.bp(arr_end, idx_start)
        graph.bp(idx_end, value_start)
        recv_fields = graph.system.get_fields_from_class(pointed_type)
        accessors = [
            f"{pointed_type}.{field}(deref({recv_place}))"
            if field != attr else new_arr
            for field in recv_fields
        ]
        heap = get_heap_name(pointed_type)
        left_place = str(heap)
        right_place = (f"Store({heap}, {recv_type}.loc({recv_place}), "
                       f"{pointed_type}.mk_{pointed_type}({', '.join(map(str, accessors))}))")
        left_start = arr_start
        right_end = value_end
        new_node = graph.add_node(f"{recv_place}.{attr}[{idx_place}] = {value_place}")
    elif isinstance(array.ast_node, _ast.Subscript):
        raise Exception("Assigning to multi-dimensional arrays directly is unsupported")
    else:
        raise Exception(f"Invalid array write to object of type {type(array)}!")
    return left_place, left_start, right_place, right_end, new_node


@handles(_ast.Assign)
class AssignCodeGenerator(AbstractCodeGenerator):
    def is_applicable_on_node(self, node: AST) -> bool:
        if len(node.targets) != 1:
            return False
        target = node.targets[0]
        if isinstance(target, _ast.Subscript):
            target = target.value
        return isinstance(target, (_ast.Name,  _ast.Attribute))

    def process_node(self, node: AST) -> DecoratedAst:
        target = node.targets[0]
        value = self._process_expect_data(node.value)
        next_label = self.graph.fresh_label()
        if isinstance(target, _ast.Subscript):
            array, index = self._process_expect_data(target.value), self._process_expect_data(target.slice)
            left_place, left_start, right_place, right_end, new_node \
                = generate_code_for_subscript(array, index, value, self)
        elif isinstance(target, _ast.Attribute):
            recv, attr = self._process_expect_data(target.value), target.attr
            recv_start, recv_place, recv_end = recv.start_node, recv.place, recv.end_label
            value_start, value_place, value_end = value.start_node, value.place, value.end_label
            if not self.graph.has_type(recv_place):
                self.type_error(f"Variable {recv_place} is not typed! "
                                f"A type annotation is needed before use.")
            recv_type = self.graph.get_type(recv_place)

            if not is_pointer_type(recv_type):
                self.type_error(f"Variable {recv_place} is not a pointer!")
            pointed_type = self.graph.system.get_pointed_type(recv_type)

            if not self.graph.system.is_field_of_class(pointed_type, attr):
                self.type_error(f"Field {attr} is not declared! "
                                f"A type annotation is needed before use.")

            self.graph.bp(recv_end, value_start)
            recv_fields = self.graph.system.get_fields_from_class(pointed_type)
            heap = get_heap_name(pointed_type)
            accessors = [f"{pointed_type}.{field}(deref({recv_place}))" if field != attr else value.place
                         for field in recv_fields]
            left_place = str(heap)
            right_place = (f"Store({heap}, {recv_type}.loc({recv_place}), "
                           f"{pointed_type}.mk_{pointed_type}({', '.join(map(str, accessors))}))")
            left_start = recv_start
            right_end = value_end
            new_node = self.graph.add_node(f"{recv_place}.{attr} = {value_place}")
        elif isinstance(target, _ast.Name):
            name = target.id
            if not self.graph.has_type(name):
                if not self.graph.has_type(value.place):
                    literal_type = value.value_type
                    if literal_type is None:
                        self.type_error(f"Variable {name} is not typed! "
                                        f"A type annotation is needed before use.")
                    self.graph.report_type(name, literal_type)
                else:
                    self.graph.report_type(name, self.graph.get_type(value.place))

            left_place = name
            right_place = value.place
            left_start = value.start_node
            right_end = value.end_label
            new_node = self.graph.add_node(f"{left_place} = {right_place}")

        else:
            self.type_error(f"Unsupported assignment target {target}")
        self.graph.bp(right_end, new_node)
        self.graph.add_edge(new_node, next_label, "s.assign({\"" + left_place + "\": \"" + str(right_place) + "\"})")
        return DecoratedControlNode(f"{left_place} = {right_place}", node, left_start, next_label)


@handles(_ast.Return)
class ReturnCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> DecoratedAst:
        if self.graph.return_var is None and node.value is not None:
            value = self._process_expect_data(node.value)
            if value.value_type is not None:
                self.graph.return_var = self.graph.fresh_var(value.value_type)
            else:
                self.type_error(f"Function {self.graph.name} is not declared to return anything!")
        next_label = self.graph.fresh_label()
        if node.value is not None:
            value = self._process_expect_data(node.value)
            value_start, value_place, value_end = value.start_node, value.place, value.end_label
            new_node = self.graph.add_node(f"{self.graph.return_var} = {value_place}")
            self.graph.bp(value_end, new_node)
            self.graph.add_edge(new_node, next_label, "s.assign({\"" + self.graph.return_var +
                                "\": \"" + str(value_place) + "\"})")
            self.graph.bp(next_label, self.graph.end)
            return DecoratedControlNode(f"return {value_start}", node, value_start, next_label)

        new_node = self.graph.add_node(ControlFlowGraph.PASS)
        self.graph.add_edge(new_node, next_label)
        self.graph.bp(next_label, self.graph.end)
        return DecoratedControlNode("return", node, new_node, next_label)
