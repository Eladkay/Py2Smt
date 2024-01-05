import _ast
import ast
from typing import cast

from z3 import SeqSortRef

import smt_helper
from generators.generators import AbstractCodeGenerator, handles, DecoratedControlNode, syntactic_replace


@handles(ast.For)
class ConstRangeForLoopGenerator(AbstractCodeGenerator):
    def is_applicable_on_node(self, node: _ast.For) -> bool:
        return isinstance(node.iter, _ast.Call) and isinstance(node.iter.func, _ast.Name) \
            and node.iter.func.id == "range" and all(isinstance(it, _ast.Constant) for it in node.iter.args) \
            and isinstance(node.target, _ast.Name)

    def process_node(self, node: _ast.For) -> DecoratedControlNode:
        assert isinstance(node.target, _ast.Name) and isinstance(node.iter, _ast.Call)  # for the type checker
        var = node.target.id
        args = [cast(_ast.Constant, it).value for it in node.iter.args]
        body = node.body
        blocks = []
        for i in range(*args):
            processed_body = [self._process_expect_control(syntactic_replace(var, _ast.Constant(i), b)) for b in body]
            blocks.append((processed_body[0].start_node, processed_body[-1].end_label))
            self.graph.bp_list([(stmt.start_node, stmt.end_label) for stmt in processed_body])
        self.graph.bp_list(blocks)
        new_node = self.graph.add_node(f"for {var} in range({args})")
        label = self.graph.fresh_label()
        if blocks:
            self.graph.add_edge(new_node, blocks[0][0])
            self.graph.bp(blocks[-1][1], label)
        else:
            self.graph.add_edge(new_node, label)
        self.graph.report_type(var, smt_helper.IntType)
        return DecoratedControlNode(f"const_range_for", node, new_node, label)


@handles(ast.For)
class VariableRangeForLoopGenerator(AbstractCodeGenerator):
    def is_applicable_on_node(self, node: _ast.For) -> bool:
        return isinstance(node.iter, _ast.Call) and isinstance(node.iter.func, _ast.Name) \
            and node.iter.func.id == "range" and not all(isinstance(it, _ast.Constant) for it in node.iter.args) \
            and isinstance(node.target, _ast.Name)

    def process_node(self, tree: _ast.For) -> DecoratedControlNode:
        assert isinstance(tree.target, _ast.Name) and isinstance(tree.iter, _ast.Call)  # for the type checker
        var = tree.target.id
        args = [self._process_expect_data(it) for it in tree.iter.args]
        if len(args) == 1:
            start = 0
            stop = args[0].place
            step = 1
        elif len(args) == 2:
            start = args[0].place
            stop = args[1].place
            step = 1
        elif len(args) == 3:
            start = args[0].place
            stop = args[1].place
            step = args[2].place
        else:
            self.type_error(f"range() expected 1, 2 or 3 arguments, got {len(args)}")
        args_start = args[0].start_node

        backup_stop = self.graph.fresh_var(smt_helper.IntType)
        backup_step = self.graph.fresh_var(smt_helper.IntType)
        backup_stop_node = self.graph.add_node(f"{backup_stop} = {stop}")
        backup_step_node = self.graph.add_node(f"{backup_step} = {step}")
        fake_range_function = self._process_expect_data(tree.iter)
        self.graph.bp(fake_range_function.end_label, backup_stop_node)
        self.graph.add_edge(backup_stop_node, backup_step_node, "s.assign({" + f"'{backup_stop}': '{stop}'" + "})")

        self.graph.report_type(var, smt_helper.IntType)
        initialize_index_node = self.graph.add_node(f"{var} = {start}")
        self.graph.add_edge(backup_step_node, initialize_index_node, "s.assign({" + f"'{backup_step}': '{step}'" + "})")

        loop_node = self.graph.add_node(f"for {var} in range({', '.join([it.place for it in args])})")
        self.graph.add_edge(initialize_index_node, loop_node, "s.assign({" + f"'{var}': '{start}'" + "})")

        increment_node = self.graph.add_node(f"{var} = {var} + {backup_step}")
        self.graph.add_edge(loop_node, increment_node,
                            f"s.assume('Or(And({backup_step} > 0, {var} < {backup_stop}), "
                            f"And({backup_step} < 0, {var} > {backup_stop}))')")

        processed_body = [self._process_expect_control(b) for b in tree.body]
        self.graph.add_edge(increment_node, processed_body[0].start_node,
                            "s.assign({" + f"'{var}': '{var} + {backup_step}'" + "})")
        self.graph.bp_list([(stmt.start_node, stmt.end_label) for stmt in processed_body])

        label = self.graph.fresh_label()
        self.graph.bp(processed_body[-1].end_label, loop_node)
        self.graph.add_edge(loop_node, label, f"s.assume('Not(Or(And({backup_step} > 0, {var} < {backup_stop}), "
                                              f"And({backup_step} < 0, {var} > {backup_stop})))')")
        self.graph.report_type(var, smt_helper.IntType)
        return DecoratedControlNode(f"var_range_for", tree, args_start, label)


@handles(ast.For)
class ListForLoopGenerator(AbstractCodeGenerator):
    def is_applicable_on_node(self, node: _ast.For) -> bool:
        iterable = self._process_expect_data(node.iter)
        return isinstance(iterable.value_type, SeqSortRef) and isinstance(node.target, _ast.Name)

    def process_node(self, tree: _ast.For) -> DecoratedControlNode:
        assert isinstance(tree.target, _ast.Name)
        iterable = self._process_expect_data(tree.iter)
        assert isinstance(iterable.value_type, SeqSortRef)
        list_backup = self.graph.fresh_var(iterable.value_type)
        idx = self.graph.fresh_var(smt_helper.IntType)
        self.graph.report_type(tree.target.id, iterable.value_type.basis())

        backup_node = self.graph.add_node(f"{list_backup} = {iterable.place}")
        init_node = self.graph.add_node(f"{idx} = 0")
        for_node = self.graph.add_node(f"for {tree.target.id} in {iterable.place}")
        next_label = self.graph.fresh_label()
        increment = self.graph.add_node(f"{idx} = {idx} + 1")
        set_loopvar = self.graph.add_node(f"{tree.target.id} = {list_backup}[{idx}]")
        processed_body = [self._process_expect_control(b) for b in tree.body]

        self.graph.bp(iterable.end_label, backup_node)
        self.graph.add_edge(backup_node, init_node, "s.assign({" + f"'{list_backup}': '{iterable.place}'" + "})")
        self.graph.add_edge(init_node, for_node, "s.assign({" + f"'{idx}': '0'" + "})")
        self.graph.add_edge(for_node, next_label, f"s.assume('{idx} >= Length({list_backup})')")
        self.graph.add_edge(for_node, set_loopvar, f"s.assume('{idx} < Length({list_backup})')")
        self.graph.add_edge(set_loopvar, processed_body[0].start_node,
                            f"s.assign({{ '{tree.target.id}': '{list_backup}[{idx}]' }})")
        self.graph.bp_list([(stmt.start_node, stmt.end_label) for stmt in processed_body])
        self.graph.bp(processed_body[-1].end_label, increment)
        self.graph.add_edge(increment, for_node, "s.assign({" + f"'{idx}': '{idx} + 1'" + "})")

        return DecoratedControlNode(f"list_for", tree, iterable.start_node, next_label)
