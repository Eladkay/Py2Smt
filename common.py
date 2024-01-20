import ast
from _ast import expr, AST
from copy import deepcopy
from typing import Callable


class Py2SmtException(Exception):
    def __init__(self, s: str):
        super().__init__(s)


def generalized_syntactic_replace(values: dict, tree: AST, action: Callable = (lambda: 0)) -> AST:
    class SynReplace(ast.NodeTransformer):
        def visit_Name(self, node):
            if node.id in values:
                action()
                return values[node.id]
            return node

    return SynReplace().visit(deepcopy(tree))


def syntactic_replace(name: str, value: expr, tree: AST, action: Callable = (lambda: 0)) -> AST:
    return generalized_syntactic_replace({name: value}, tree, action)
