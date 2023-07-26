import _ast
import ast
from typing import cast

import smt_helper
from generators.generators import AbstractCodeGenerator, handles, DecoratedControlNode, syntactic_replace


@handles(ast.For)
class ConstRangeForLoopGenerator(AbstractCodeGenerator):
    def is_applicable_on_node(self, node: _ast.For) -> bool:
        return isinstance(node.iter, _ast.Call) and isinstance(node.iter.func, _ast.Name) \
            and node.iter.func.id == "range" and all(isinstance(it, _ast.Constant) for it in node.iter.args) \
            and isinstance(node.target, _ast.Name)

    def process_node(self, tree: _ast.For) -> DecoratedControlNode:
        assert isinstance(tree.target, _ast.Name) and isinstance(tree.iter, _ast.Call)  # for the type checker
        var = tree.target.id
        args = [cast(_ast.Constant, it).value for it in tree.iter.args]
        body = tree.body
        blocks = []
        for i in range(*args):
            processed_body = [self._process_expect_control(syntactic_replace(var, _ast.Constant(i), b)) for b in body]
            blocks.append((processed_body[0].start_node, processed_body[-1].end_label))
            self.graph.bp_list([(stmt.start_node, stmt.end_label) for stmt in processed_body])
            pass
        self.graph.bp_list(blocks)
        node = self.graph.add_node(f"for {var} in range({args})")
        label = self.graph.fresh_label()
        if blocks:
            self.graph.add_edge(node, blocks[0][0])
            self.graph.bp(blocks[-1][1], label)
        else:
            self.graph.add_edge(node, label)
        return DecoratedControlNode(f"const_range_for", tree, node, label)


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
            raise Exception()
        # args should be computed already because range is a function

        backup_stop = self.graph.fresh_var(smt_helper.IntType)
        backup_step = self.graph.fresh_var(smt_helper.IntType)
        backup_stop_node = self.graph.add_node(f"{backup_stop} = {stop}")
        backup_step_node = self.graph.add_node(f"{backup_step} = {step}")
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
        return DecoratedControlNode(f"const_range_for", tree, backup_stop_node, label)
