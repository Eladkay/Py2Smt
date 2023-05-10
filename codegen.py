import ast
import sys
from _ast import AST, expr, Subscript, Name, Store, Attribute, Constant
from typing import Tuple, Union, List, Type

from z3 import IntSort, DatatypeSortRef, BoolSort, ArraySortRef, StringSort, SeqSortRef, z3

from cfg import ControlFlowGraph, ControlFlowNode, Label
from symbolic_interp import Signature


ops = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.Div: '/', ast.FloorDiv: "/", ast.Mod: '%',
       ast.Pow: '**', ast.LShift: '<<', ast.RShift: '>>', ast.Eq: "==",
       ast.NotEq: "!=", ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">=",
       ast.Is: "is", ast.IsNot: "is not", ast.In: "in", ast.NotIn: "not in"}
unaryops = {ast.Not: "not", ast.UAdd: "+", ast.USub: "-"}
boolops = [ast.And, ast.Or]
nop = [ast.arguments, ast.Load, ast.Store, ast.FunctionDef]


def _syntactic_param_replace(transformed: AST, args: List[str], exprs: List[expr]) -> AST:
    class RewriteArgs(ast.NodeTransformer):
        def visit_Name(self, node):
            if node.id in args:
                return exprs[args.index(node.id)]
            return node

    return RewriteArgs().visit(transformed)


def _syntactic_receiver_replace(transformed: AST, name: str, receiver: Union[None, str]) -> AST:
    class RewriteReceiver(ast.NodeTransformer):
        def visit_Name(self, node):
            if isinstance(node.id, str) and node.id == f"{name}_self":
                if receiver is None:
                    raise ValueError(f"Called member function {name} without receiver.")
                return Name(receiver)
            return node

    return RewriteReceiver().visit(transformed)


def process(node: AST, graph: ControlFlowGraph):
    raise NotImplementedError("Should never be called!")  # forward declaration


# noinspection PyUnresolvedReferences
def _generate_control_for_call(node: ast.expr, graph: ControlFlowGraph) -> \
        Tuple[Union[Label, ControlFlowNode], str, Label]:
    assert isinstance(node.func, ast.Name) or isinstance(node.func, ast.Attribute)
    name = node.func.id if isinstance(node.func, ast.Name) else node.func.attr
    receiver = None if isinstance(node.func, ast.Name) else node.func.value.data['place']
    args = [(arg.data['start'], arg.data['place'], arg.data['end']) for arg in node.args]
    starts, exprs, ends = zip(*args) if len(args) > 0 else ([], [], [])
    starts_and_ends = [(start, end) for start, end in zip(starts, ends)]
    graph.bp_list(starts_and_ends)
    if not graph.system.has_entry(name, None if receiver is None else graph.get_type(receiver)) \
            and name in dir(z3):
        new_node = graph.add_node(ControlFlowGraph.PASS)
        new_label = graph.next_bp_label()
        graph.add_edge(new_node, new_label)
        return new_node, f"{name}({', '.join(map(str, exprs))})", new_label

    called_function = graph.system.get_entry_by_name(name, None if receiver is None else graph.get_type(receiver))
    params = called_function.args

    if len(params) == len(exprs) + 1:
        assert params[0] == "self"
        params = params[1:]

    if called_function.name == "__literal__":
        if len(exprs) != 1:
            raise Exception("Literal expression should have exactly one argument")
        s = exprs[0]
        if not isinstance(s, Constant) or not isinstance(s.value, str):
            raise Exception("Literal expression should have a constant string argument")
        new_node = graph.add_node(f"return {s.value}")
        new_label = graph.next_bp_label()
        graph.add_edge(new_node, new_label)
        graph.bp(ends[0], new_node)
        return new_node, s.value, new_label

    replaced_args = _syntactic_param_replace(called_function.ast, params, [Name(it) for it in exprs])
    replaced_args.body[0].args = ast.arguments()

    local_vars = list(it for it in called_function.cfg.types.keys() if it not in params)
    tagged_local_vars = {it: Name(f"{name}_{it}") for it in local_vars}
    replaced_locals = _syntactic_param_replace(replaced_args, local_vars, list(tagged_local_vars.values()))
    for k, v in tagged_local_vars.items():
        graph.report_type(v.id, called_function.cfg.types[k])

    replaced_receiver = _syntactic_receiver_replace(replaced_locals, name, receiver) if receiver is not None \
        else replaced_locals

    new_cfg = ControlFlowGraph(graph.system, replaced_receiver.body[0].name, called_function.cls)
    new_cfg.types.update({f"{name}_{k}": v for k, v in called_function.cfg.types.items()})

    new_cfg.var_count = graph.var_count
    process_all(replaced_receiver, new_cfg)
    graph.var_count = new_cfg.var_count

    new_cfg.clean_cfg()

    func_start, func_end = graph.add_all(new_cfg)
    if len(args) > 0:
        graph.bp(ends[-1], func_start)
    graph.types.update(new_cfg.types)
    new_label = graph.next_bp_label()
    if new_cfg.return_var is not None:
        new_var = new_cfg.return_var
        new_node = graph.add_node(f"{new_var} = {name}({', '.join(map(str, exprs))})")
    else:
        new_var = "0"
        new_node = graph.add_node(f"{name}({', '.join(map(str, exprs))})")
    graph.add_edge(new_node, new_label)
    graph.bp(func_end, new_node)
    return starts[0] if len(args) > 0 else func_start, new_var, new_label


# noinspection PyUnresolvedReferences
def _generate_control_for_expression(node: ast.expr, graph: ControlFlowGraph) -> \
        Tuple[Union[Label, ControlFlowNode], str, Label]:
    if isinstance(node, ast.Constant):
        new_node = graph.add_node(f"pass")
        new_label = graph.next_bp_label()
        graph.add_edge(new_node, new_label)
        val = f"\\\"{node.value}\\\"" if isinstance(node.value, str) else node.value
        return new_node, val, new_label
    elif isinstance(node, ast.Name):
        new_node = graph.add_node(f"pass")
        new_label = graph.next_bp_label()
        graph.add_edge(new_node, new_label)
        return new_node, f"{node.id}", new_label
    elif isinstance(node, ast.BinOp):
        start1, expr1, end1 = node.left.data["start"], node.left.data["place"], node.left.data["end"]
        start2, expr2, end2 = node.right.data["start"], node.right.data["place"], node.right.data["end"]
        types = {ast.Add: StringSort() if isinstance(graph.get_type(expr1), SeqSortRef) else IntSort(),
                 ast.Pow: IntSort(), ast.Sub: IntSort(), ast.Mult: IntSort(), ast.Div: IntSort(),
                 ast.FloorDiv: IntSort(), ast.Mod: IntSort(), ast.Eq: BoolSort(), ast.NotEq: BoolSort(),
                 ast.Lt: BoolSort(), ast.LtE: BoolSort(), ast.Gt: BoolSort(), ast.GtE: BoolSort(), ast.Is: BoolSort(),
                 ast.IsNot: BoolSort(), ast.In: BoolSort(), ast.NotIn: BoolSort()}
        new_var = graph.fresh_var(types[type(node.op)])
        op_string = ops[type(node.op)]
        new_node = graph.add_node(f"{new_var} = {expr1} {op_string} {expr2}")
        graph.bp(end1, start2)
        graph.bp(end2, new_node)
        new_label = graph.next_bp_label()
        graph.add_edge(new_node, new_label, "s.assign({" + f"'{new_var}': '{expr1} {op_string} {expr2}'" + "})")
        return start1, new_var, new_label
    elif isinstance(node, ast.BoolOp):
        return _generate_control_for_expression(ast.Call(func=ast.Name(id=node.op.__class__.__name__),
                                                         args=node.values), graph)
    elif isinstance(node, ast.Compare):
        assert len(node.ops) == 1
        assert len(node.comparators) == 1
        comparator = node.comparators[0]
        op = node.ops[0]
        if isinstance(op, ast.NotIn):
            start, var, label = _generate_control_for_expression(ast.Compare(left=node.left, ops=[ast.In()],
                                                                             comparators=[comparator]), graph)
            return start, f"Not({var})", label
        elif isinstance(op, ast.In):
            start_left, var_left, end_left = node.left.data["start"], node.left.data["place"], node.left.data["end"]
            start_right, var_right, end_right = comparator.data["start"], comparator.data["place"], comparator.data[
                "end"]
            graph.bp(end_left, start_right)
            right_type = graph.get_type(var_right)
            if isinstance(right_type, ArraySortRef) and right_type.range() == BoolSort():
                return start_left, f"IsMember({var_left}, {var_right})", end_right
            elif isinstance(right_type, ArraySortRef) and right_type.range().name().endswith("Option"):
                value_type = right_type.range()
                return start_left, f"Select({var_right}, {var_left}) != {value_type}.none", end_right
            elif isinstance(graph.get_type(var_right), ArraySortRef):
                newvar = graph.fresh_var(BoolSort())
                return start_left, f"Exists({newvar}, {var_right}[{newvar}] == {var_left})", end_right
            else:
                raise NotImplementedError(f"Cannot handle inclusion checks for {type(graph.get_type(var_right))}")

        return _generate_control_for_expression(ast.BinOp(left=node.left, op=op,
                                                          right=comparator), graph)
    elif isinstance(node, ast.UnaryOp):
        if isinstance(node.op, ast.Not):
            return _generate_control_for_expression(ast.Call(func=ast.Name(id="Not"),
                                                             args=[node.operand]), graph)
        start, expr, end = node.operand.data["start"], node.operand.data["place"], node.operand.data["end"]
        new_var = graph.fresh_var(IntSort())
        op_string = unaryops[type(node.op)]
        new_node = graph.add_node(f"{new_var} = {op_string} {expr}")
        graph.bp(end, new_node)
        new_label = graph.next_bp_label()
        graph.add_edge(new_node, new_label, "s.assign({" + f"'{new_var}': '{op_string} {expr}'" + "})")
        return start, new_var, new_label
    elif isinstance(node, ast.Subscript):
        if isinstance(node.ctx, Store):
            return None, None, None
        start1, expr1, end1 = node.value.data["start"], node.value.data["place"], node.value.data["end"]
        start2, expr2, end2 = node.slice.data["start"], node.slice.data["place"], node.slice.data["end"]
        graph.bp(end1, start2)
        new_label = graph.next_bp_label()
        value_type = graph.get_type(expr1)

        if isinstance(value_type, ArraySortRef) and value_type.range().name().endswith("Option"):
            value_sort = value_type.range()
            new_var = graph.fresh_var(value_sort.constructor(0).domain(0))
            new_node = graph.add_node(f"{new_var} = {expr1}[{expr2}]")
            graph.bp(end2, new_node)
            graph.add_edge(new_node, new_label,
                           "s.assign({" + f"'{new_var}': '{value_sort}.val({expr1}[{expr2}])'" + "})")
        elif isinstance(value_type, SeqSortRef):
            value_sort = StringSort() if value_type.is_string() else value_type.basis()
            new_var = graph.fresh_var(value_sort)
            new_node = graph.add_node(f"{new_var} = {expr1}[{expr2}]")
            graph.bp(end2, new_node)
            graph.add_edge(new_node, new_label,
                           "s.assign({" + f"'{new_var}': 'SubString({expr1}, {expr2}, 1)'" + "})")
        else:
            value_sort = value_type.range()
            new_var = graph.fresh_var(value_sort)
            new_node = graph.add_node(f"{new_var} = {expr1}[{expr2}]")
            graph.bp(end2, new_node)
            graph.add_edge(new_node, new_label, "s.assign({" + f"'{new_var}': '{expr1}[{expr2}]'" + "})")
        return start1, new_var, new_label
    elif isinstance(node, ast.Call):
        return _generate_control_for_call(node, graph)
    elif isinstance(node, ast.Attribute):
        if isinstance(node.ctx, Store) or (isinstance(node.value, Name) and node.value.id in sys.modules):
            return None, None, None
        start, expr, end = node.value.data["start"], node.value.data["place"], node.value.data["end"]
        receiver_type = graph.get_type(expr)
        if not graph.system.is_field_of_class(receiver_type, node.attr):
            if isinstance(receiver_type, DatatypeSortRef):
                receiver_type = receiver_type.name()
            if isinstance(receiver_type, Type):
                receiver_type = receiver_type.__name__
            elif not isinstance(receiver_type, str):
                raise Exception(f"Cannot find field {node.attr} in {receiver_type}")
            if (receiver_type, node.attr) in graph.system.methods:
                return None, None, None
            else:
                raise Exception(f"Cannot find field {node.attr} in {receiver_type}")
        field_type = graph.system.get_type_from_field(receiver_type, node.attr)
        new_var = graph.fresh_var(field_type)
        new_node = graph.add_node(f"{new_var} = {expr}.{node.attr}")
        graph.bp(end, new_node)
        new_label = graph.next_bp_label()
        graph.add_edge(new_node, new_label, "s.assign({" + f"'{new_var}': '{receiver_type}.{node.attr}({expr})'" + "})")
        return new_node, new_var, new_label
    elif isinstance(node, ast.List):
        if len(node.elts) == 0:
            new_node = graph.add_node(ControlFlowGraph.PASS)
            new_label = graph.next_bp_label()
            graph.add_edge(new_node, new_label)
            return new_node, 'K(IntSort(), 0)', new_label
        starts, exprs, ends = zip(*[(item.data['start'], item.data['place'], item.data['end']) for item in node.elts])
        starts_and_ends = [(start, end) for start, end in zip(starts, ends)]
        graph.bp_list(starts_and_ends)
        list_type = graph.get_type(exprs[0])
        store = f"K(IntSort(), {ControlFlowGraph.get_place_of_default_value(list_type)})"
        for idx, expr in enumerate(exprs):
            store = f"Store({store}, {idx}, {expr})"
        return starts[0], store, ends[-1]
    elif isinstance(node, ast.Set):
        if len(node.elts) == 0:
            new_node = graph.add_node(ControlFlowGraph.PASS)
            new_label = graph.next_bp_label()
            graph.add_edge(new_node, new_label)
            return new_node, "EmptySet(IntSort())", new_label
        starts, exprs, ends = zip(*[(item.data['start'], item.data['place'], item.data['end']) for item in node.elts])
        starts_and_ends = [(start, end) for start, end in zip(starts, ends)]
        graph.bp_list(starts_and_ends)
        store = f"EmptySet({ControlFlowGraph.type_to_place_string(graph.get_type(exprs[0]))})"
        for expr in exprs:
            store = f"Store({store}, {expr}, True)"
        return starts[0], store, ends[-1]
    elif isinstance(node, ast.Tuple):
        new_node = graph.add_node(ControlFlowGraph.PASS)
        new_label = graph.next_bp_label()
        graph.add_edge(new_node, new_label)
        return new_node, 'None', new_label
    elif isinstance(node, ast.Dict):
        if len(node.keys) == 0:
            new_var = f"K(IntSort(), {Signature.get_or_create_optional_type(IntSort())}.none)"
            new_node = graph.add_node(ControlFlowGraph.PASS)
            new_label = graph.next_bp_label()
            graph.add_edge(new_node, new_label)  # note: can't infer sort of empty dicts!
            return new_node, new_var, new_label
        starts_keys, exprs_keys, ends_keys = zip(*[(item.data['start'], item.data['place'], item.data['end'])
                                                   for item in node.keys])
        starts_and_ends_keys = [(start, end) for start, end in zip(starts_keys, ends_keys)]
        starts_values, exprs_values, ends_values = zip(*[(item.data['start'], item.data['place'], item.data['end'])
                                                         for item in node.values])
        starts_and_ends_values = [(start, end) for start, end in zip(starts_values, ends_values)]
        graph.bp_list(starts_and_ends_keys)
        graph.bp(ends_keys[-1], starts_values[0])
        graph.bp_list(starts_and_ends_values)
        key_type = graph.get_type(exprs_keys[0])
        value_type = graph.get_type(exprs_values[0])
        optional = Signature.get_or_create_optional_type(value_type)
        store = f"K({ControlFlowGraph.type_to_place_string(key_type)}, {optional}.none)"
        for k, v in zip(exprs_keys, exprs_values):
            store = f"Store({store}, {k}, {optional}.some({v}))"
        return starts_keys[0], store, ends_values[-1]
    else:
        raise NotImplementedError(f"Unknown node type: {node.__class__.__name__}")


# noinspection PyRedeclaration
def process(node: AST, graph: ControlFlowGraph) -> dict:
    if type(node) in nop:
        pass
    elif isinstance(node, ast.Module):
        assert len(node.body) == 1
        function_body = node.body[0].body
        graph.bp_list([(stmt.data["start"], stmt.data["end"]) for stmt in function_body])
        graph.bp(function_body[-1].data["end"], graph.end)
        graph.add_edge(graph.start, function_body[0].data["start"])
        return {"type": "start", "start": graph.start, "end": graph.end}
    elif isinstance(node, ast.arg):
        graph.report_type(node.arg, graph.system.get_type_from_annotation(node.annotation))
    elif type(node) in ops:
        return {"type": "binop", "op": ops[type(node)]}
    elif type(node) in unaryops:
        return {"type": "unaryop", "op": unaryops[type(node)]}
    elif type(node) in boolops:
        return {"type": "boolop", "op": type(node).__name__}
    elif isinstance(node, ast.expr):
        start, place, end = _generate_control_for_expression(node, graph)
        return {"type": "expr", "start": start, "end": end, "place": place}
    elif isinstance(node, ast.Return):
        if graph.return_var is None and node.value is not None:
            raise Exception(f"Function {graph.name} is not declared to return anything!")
        next_label = graph.next_bp_label()
        if node.value is not None:
            value_start, value_place, value_end = node.value.data["start"], node.value.data["place"], node.value.data[
                "end"]
            new_node = graph.add_node(f"{graph.return_var} = {value_place}")
            graph.bp(value_end, new_node)
            graph.add_edge(new_node, next_label, "s.assign({\"" + graph.return_var +
                           "\": \"" + str(value_place) + "\"})")
            graph.bp(next_label, graph.end)
            return {"type": "return", "start": value_start, "end": next_label}
        else:
            new_node = graph.add_node(ControlFlowGraph.PASS)
            graph.add_edge(new_node, next_label)
            graph.bp(next_label, graph.end)
            return {"type": "return", "start": new_node, "end": next_label}

    elif isinstance(node, ast.Assign):
        assert len(node.targets) == 1
        target = node.targets[0]
        value = node.value
        next_label = graph.next_bp_label()
        if isinstance(target, Subscript):
            array, slice = target.value, target.slice
            if array.data['place'] not in graph.types:
                raise Exception(f"Variable {array.data['place']} does not exist! A type annotation is needed before use.")
            if not isinstance(graph.get_type(array.data['place']), ArraySortRef):
                raise Exception(f"Variable {array.data['place']} is not an array!")
            domain = graph.get_type(array.data['place']).domain()
            if graph.get_type(slice.data['place']) != domain:
                raise Exception(f"{slice.data['place']} is not in the domain {domain} of {array.data['place']}!")
            idx_start, idx_place, idx_end = slice.data["start"], slice.data["place"], slice.data["end"]
            value_start, value_place, value_end = value.data["start"], value.data["place"], value.data["end"]
            arr_start, arr_place, arr_end = array.data["start"], array.data["place"], array.data["end"]
            if graph.get_type(value_place).name() != graph.get_type(arr_place).range().name()\
                    and not graph.get_type(arr_place).range().name().endswith("Option"):
                raise Exception(f"Type of {value_place} does not match the stored type of {arr_place}! "
                                f"types: {graph.get_type(value_place)} != {graph.get_type(arr_place).range()}")
            array_type = graph.get_type(arr_place)
            if isinstance(array_type, ArraySortRef) and array_type.range().name().endswith("Option"):
                value_type = array_type.range()
                value_place = f"{value_type}.some({value_place})"
            if isinstance(array, Name):
                graph.bp(arr_end, idx_start)
                graph.bp(idx_end, value_start)

                left_place = arr_place
                right_place = f"Store({arr_place}, {idx_place}, {value_place})"
                left_start = arr_start
                right_end = value_end
                new_node = graph.add_node(f"{arr_place}[{idx_place}] = {value_place}")
            elif isinstance(array, Attribute):
                recv, attr = array.value, array.attr
                if recv.data['place'] not in graph.types:
                    raise Exception(f"Variable {recv.data['place']} is not typed! "
                                    f"A type annotation is needed before use.")
                if not graph.system.is_field_of_class(graph.get_type(recv.data['place']), attr):
                    raise Exception(f"Field {attr.data['place']} is not declared! "
                                    f"A type annotation is needed before use.")
                recv_place = recv.data['place']
                graph.bp(arr_end, idx_start)
                graph.bp(idx_end, value_start)
                recv_type = graph.get_type(recv_place)
                recv_fields = graph.system.get_fields_from_class(recv_type)
                accessors = [
                    f"{recv_type}.{fieldname}({recv_place})"
                    if fieldname != attr else f"Store({arr_place}, {idx_place}, {value_place})"
                    for fieldname in recv_fields
                ]
                left_place = recv_place
                right_place = f"{recv_type}.mk_{recv_type}({', '.join(map(str, accessors))})"
                left_start = arr_start
                right_end = value_end
                new_node = graph.add_node(f"{recv_place}.{attr}[{idx_place}] = {value_place}")
            elif isinstance(array, Subscript):
                raise Exception("Assigning to multi-dimensional arrays directly is unsupported")
            else:
                raise Exception(f"Invalid array access to object of type {type(array)}!")
        elif isinstance(target, Attribute):
            recv, attr = target.value, target.attr
            if recv.data['place'] not in graph.types:
                raise Exception(f"Variable {recv.data['place']} is not typed! "
                                f"A type annotation is needed before use.")
            if not graph.system.is_field_of_class(graph.get_type(recv.data['place']), attr):
                raise Exception(f"Field {attr.data['place']} is not declared! "
                                f"A type annotation is needed before use.")
            recv_start, recv_place, recv_end = recv.data["start"], recv.data["place"], recv.data["end"]
            value_start, value_place, value_end = value.data["start"], value.data["place"], value.data["end"]
            graph.bp(recv_end, value_start)
            recv_type = graph.get_type(recv_place)
            recv_fields = graph.system.get_fields_from_class(recv_type)
            accessors = [f"{recv_type}.{fieldname}({recv_place})" if fieldname != attr else value.data['place']
                         for fieldname in recv_fields]
            left_place = recv_place
            right_place = f"{recv_type}.mk_{recv_type}({', '.join(map(str, accessors))})"
            left_start = recv_start
            right_end = value_end
            new_node = graph.add_node(f"{recv_place}.{attr} = {value_place}")
        elif isinstance(node.targets[0], Name):
            if target.data['place'] not in graph.types:
                if value.data['place'] not in graph.types:
                    literal_type = ControlFlowGraph.get_literal_type(value.data['place'])
                    if literal_type is None:
                        raise Exception(f"Variable {target.data['place']} is not typed! "
                                        f"A type annotation is needed before use.")
                    graph.report_type(target.data['place'], literal_type)
                else:
                    graph.report_type(target.data['place'], graph.get_type(value.data['place']))

            left_start, left_place, left_end = target.data["start"], target.data["place"], target.data["end"]
            right_start, right_place, right_end = value.data["start"], value.data["place"], value.data["end"]
            graph.bp(left_end, right_start)
            new_node = graph.add_node(f"{left_place} = {right_place}")
        else:
            raise Exception(f"Unsupported assignment target {target}")
        graph.bp(right_end, new_node)
        graph.add_edge(new_node, next_label, "s.assign({\"" + left_place + "\": \"" + str(right_place) + "\"})")
        return {"type": "assign", "start": left_start, "end": next_label}
    elif isinstance(node, ast.AnnAssign):
        graph.report_type(node.target.id, graph.system.get_type_from_annotation(node.annotation))
        return process(ast.Assign(targets=[node.target], value=node.value), graph)
    elif isinstance(node, ast.AugAssign):
        node.target.ctx = ast.Load()
        node.target.data = process(node.target, graph)  # reprocess with new context

        binop = ast.BinOp(left=node.target, op=node.op, right=node.value)
        binop.data = process(binop, graph)

        node.target.ctx = ast.Store()
        node.target.data = process(node.target, graph)  # reprocess with new context

        assign = ast.Assign(targets=[node.target], value=binop)
        assign.data = process(assign, graph)
        assign_start, assign_end = assign.data["start"], assign.data["end"]
        return {"type": "assign", "start": assign_start, "end": assign_end}
    elif isinstance(node, ast.If):
        test_start, test_end, test_place = node.test.data["start"], node.test.data["end"], node.test.data["place"]
        new_node = graph.add_node(f"if {test_place}")
        graph.bp(test_end, new_node)
        next_label = graph.next_bp_label()

        assume_node = graph.add_node(f"assume {test_place}")
        graph.add_edge(new_node, assume_node)
        if len(node.body) > 0:
            graph.add_edge(assume_node, node.body[0].data["start"], f"s.assume(\'{test_place}\')")
            graph.bp_list([(stmt.data["start"], stmt.data["end"]) for stmt in node.body])
            graph.bp(node.body[-1].data["end"], next_label)
        else:
            graph.add_edge(assume_node, next_label, f"s.assume(\'{test_place}\')")

        assume_not_node = graph.add_node(f"assume not {node.test.data['place']}")
        graph.add_edge(new_node, assume_not_node)
        if len(node.orelse) > 0:
            graph.add_edge(assume_not_node, node.orelse[0].data["start"], f"s.assume('Not({test_place}"f")')")
            graph.bp_list([(stmt.data["start"], stmt.data["end"]) for stmt in node.orelse])
            graph.bp(node.orelse[-1].data["end"], next_label)
        else:
            graph.add_edge(assume_not_node, next_label, f"s.assume('Not({test_place}"f")')")

        return {"type": "if", "start": test_start, "end": next_label}
    elif isinstance(node, ast.Pass):
        idx = graph.add_node(ControlFlowGraph.PASS)
        label = graph.next_bp_label()
        graph.add_edge(idx, label)
        return {"type": "pass", "start": idx, "end": label}
    elif isinstance(node, ast.While):
        test_start, test_end, test_place = node.test.data["start"], node.test.data["end"], node.test.data["place"]
        new_node = graph.add_node(f"while {node.test.data['place']}")
        graph.bp(test_end, new_node)
        next_label = graph.next_bp_label()

        assume_not_node = graph.add_node(f"assume not {test_place}")
        graph.add_edge(new_node, assume_not_node)
        graph.add_edge(assume_not_node, next_label, f"s.assume('Not({test_place})')")

        assume_idx = graph.add_node(f"assume {test_place}")
        graph.add_edge(new_node, assume_idx)
        graph.add_edge(assume_idx, node.body[0].data["start"], f"s.assume('{test_place}')")

        graph.bp_list([(stmt.data["start"], stmt.data["end"]) for stmt in node.body])
        graph.bp(node.body[-1].data["end"], test_start)
        if graph.break_label is not None:
            graph.bp(graph.break_label, next_label)
            graph.break_label = None
        if graph.continue_label is not None:
            graph.bp(graph.continue_label, test_start)
            graph.continue_label = None
        return {"type": "while", "start": test_start, "end": next_label}
    elif isinstance(node, ast.Raise):
        id = ast.Name(id=graph.return_var)
        id.data = process(id, graph)
        nondet_name = ast.Name(id="nondet")
        nondet_name.data = process(nondet_name, graph)
        call = ast.Call(func=nondet_name, args=[], keywords=[])
        call.data = process(call, graph)
        new_node = ast.Assign(targets=[id], value=call)
        new_node.data = process(new_node, graph)
        graph.bp(new_node.data["end"], graph.end)
        return {"type": "raise", "start": new_node.data["start"], "end": new_node.data["end"]}
    elif isinstance(node, ast.Expr):  # notice capital E
        return {"type": "expr", "start": node.value.data["start"], "end": node.value.data["end"]}
    elif isinstance(node, ast.Break):
        if graph.break_label is None:
            graph.break_label = graph.next_bp_label()
        node = graph.add_node("break")
        graph.add_edge(node, graph.break_label)
        return {"type": "break", "start": node, "end": None}
    elif isinstance(node, ast.Continue):
        if graph.continue_label is None:
            graph.continue_label = graph.next_bp_label()
        node = graph.add_node("continue")
        graph.add_edge(node, graph.continue_label)
        return {"type": "continue", "start": node, "end": None}
    else:
        raise Exception("Unknown rule", node.__class__.__name__)


def _postorder(tree: AST):
    for field, value in ast.iter_fields(tree):
        if field == "annotation" or field == "returns":
            continue
        if isinstance(value, list):
            for item in value:
                if isinstance(item, AST):
                    yield from _postorder(item)
        elif isinstance(value, AST):
            yield from _postorder(value)
    yield tree


def process_all(tree: AST, graph: ControlFlowGraph) -> ControlFlowGraph:
    returns = tree.body[0].returns
    if returns is None:
        graph.return_var = None
    else:
        graph.return_var = graph.fresh_var(graph.system.get_type_from_annotation(returns), "ret")
    for node in _postorder(tree):
        node.data = process(node, graph)
    if graph.break_label is not None or graph.continue_label is not None:
        raise Exception("Break or continue outside of loop")
    graph.compute_actions()
    return graph
