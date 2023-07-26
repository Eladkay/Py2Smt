import _ast
from _ast import AST

from generators.generators import AbstractCodeGenerator, handles, \
    DecoratedControlNode


@handles([_ast.Break, _ast.Continue])
class BreakContinueCodeGenerator(AbstractCodeGenerator):

    def process_node(self, tree: AST) -> DecoratedControlNode:
        if isinstance(tree, _ast.Break):
            if self.graph.break_label is None:
                self.graph.break_label = label = self.graph.fresh_label()
            else:
                label = self.graph.break_label
        elif isinstance(tree, _ast.Continue):
            if self.graph.continue_label is None:
                self.graph.continue_label = label = self.graph.fresh_label()
            else:
                label = self.graph.continue_label
        else:
            raise Exception("Should not happen")

        name = {_ast.Break: "break", _ast.Continue: "continue"}[type(tree)]
        node = self.graph.add_node(name)
        self.graph.add_edge(node, label)
        # we need a fresh label here because otherwise it'd be connected to the next statement...
        return DecoratedControlNode(name, tree, node, self.graph.fresh_label())


# todo: I want to add an "exception state" node to the graph
# @handles(_ast.Raise)
# class RaiseCodeGenerator(AbstractCodeGenerator):
#
#     def process_node(self, tree: AST) -> DecoratedAst:
        # id = ast.Name(id=graph.return_var)
        # id.data = process(id, graph)
        # nondet_name = ast.Name(id="nondet")
        # nondet_name.data = process(nondet_name, graph)
        # call = ast.Call(func=nondet_name, args=[], keywords=[])
        # call.data = process(call, graph)
        # new_node = ast.Assign(targets=[id], value=call)
        # new_node.data = process(new_node, graph)
        # graph.bp(new_node.data["end"], graph.end)
        # return {"type": "raise", "start": new_node.data["start"], "end": new_node.data["end"]}
        # return NotImplemented  # todo


@handles(_ast.While)
class WhileCodeGenerator(AbstractCodeGenerator):

    def process_node(self, node: AST) -> DecoratedControlNode:
        test_decorated = self._process_expect_data(node.test)
        test_start, test_end, test_place = test_decorated.start_node, test_decorated.end_label, test_decorated.place
        new_node = self.graph.add_node(f"while {test_place}")
        self.graph.bp(test_end, new_node)

        next_label = self.graph.fresh_label()
        self.graph.add_edge(new_node, next_label, f"s.assume('Not({test_place})')")

        first_decorated = self._process_expect_control(node.body[0])
        self.graph.add_edge(new_node, first_decorated.start_node, f"s.assume('{test_place}')")

        self.graph.bp_list([(stmt.start_node, stmt.end_label)
                            for stmt in [self._process_expect_control(node) for node in node.body]])

        last_decorated = self._process_expect_control(node.body[-1])
        self.graph.bp(last_decorated.end_label, test_start)
        if self.graph.break_label is not None:  # todo: nested loop breaks and continues are not handled. need a stack
            self.graph.bp(self.graph.break_label, next_label)
            self.graph.break_label = None
        if self.graph.continue_label is not None:
            self.graph.bp(self.graph.continue_label, test_start)
            self.graph.continue_label = None
        return DecoratedControlNode(f"while {test_place}", node, test_start, next_label)


@handles(_ast.If)
class IfCodeGenerator(AbstractCodeGenerator):
    def process_node(self, node: AST) -> DecoratedControlNode:
        test_decorated = self._process_expect_data(node.test)
        test_start, test_end, test_place = test_decorated.start_node, test_decorated.end_label, test_decorated.place
        new_node = self.graph.add_node(f"if {test_place}")
        self.graph.bp(test_end, new_node)
        next_label = self.graph.fresh_label()

        if len(node.body) > 0:
            first_decorated = self._process_expect_control(node.body[0])
            self.graph.add_edge(new_node, first_decorated.start_node, f"s.assume(\'{test_place}\')")
            self.graph.bp_list([(stmt.start_node, stmt.end_label)
                                for stmt in [self._process_expect_control(node) for node in node.body]])
            last_decorated = self._process_expect_control(node.body[-1])
            self.graph.bp(last_decorated.end_label, next_label)
        else:
            self.graph.add_edge(new_node, next_label, f"s.assume(\'{test_place}\')")

        if len(node.orelse) > 0:
            first_decorated = self._process_expect_control(node.orelse[0])
            self.graph.add_edge(new_node, first_decorated.start_node, f"s.assume(\'Not({test_place})\')")
            self.graph.bp_list([(stmt.start_node, stmt.end_label)
                                for stmt in [self._process_expect_control(node) for node in node.orelse]])
            last_decorated = self._process_expect_control(node.orelse[-1])
            self.graph.bp(last_decorated.end_label, next_label)
        else:
            self.graph.add_edge(new_node, next_label, f"s.assume('Not({test_place}"f")')")

        return DecoratedControlNode(f"if {test_place}", node, new_node, next_label)