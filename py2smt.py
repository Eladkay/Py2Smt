import ast
import inspect
import sys
from _ast import AST, expr, Constant
from textwrap import dedent
from typing import *

from z3 import z3, DatatypeSortRef, IntSort, BoolSort, StringSort, ArraySort, SetSort, SortRef

from generators.generators import CodeGenerationDispatcher
from symbolic_interp import Signature, State
import stdlib
from cfg import ControlFlowGraph


class MethodObject:

    @staticmethod
    def get_from_method(method: Callable, system: 'Py2Smt', cls: Type = None) -> 'MethodObject':
        return MethodObject(method.__name__,
                            ast.parse(dedent(inspect.getsource(method))),
                            inspect.getfullargspec(method).args,
                            cls if cls else vars(sys.modules[method.__module__])[method.__qualname__.split('.')[0]],
                            system)

    def __init__(self, name: str, tree: AST, args: List[str], cls: Type, system: 'Py2Smt'):
        self.system = system
        self.name = name
        self.ast = tree
        self.args = args
        self.cls = cls
        self._sig = None
        self._cfg = None
        self._dispatcher = None

    @property
    def sig(self) -> Signature:
        if self._sig is None:
            self._sig = self.cfg.get_signature()
        return self._sig

    @property
    def cfg(self) -> ControlFlowGraph:
        if self._cfg is None:
            self._cfg = ControlFlowGraph(self.system, self.ast.body[0].name, self.cls)
            self._dispatcher = CodeGenerationDispatcher(self.cfg)
            self._dispatcher.compute_graph(self.ast)
            self._cfg.clean_cfg()

        return self._cfg

    def make_state(self, tag=""):
        return State(self.sig, tag)

    @staticmethod
    def create_empty_constructor(system: 'Py2Smt', ty: Type, fields: Dict[str, SortRef]) -> 'MethodObject':
        body = "return self" if not fields else \
            '\n\t'.join([f'self.{f} = {ControlFlowGraph.get_place_of_default_value(ty)}' for f, ty in fields.items()])\
            + "\n\treturn self"
        empty_constructor = f"""def __init__(self) -> {ty.__name__}:\n\t{body}"""
        return MethodObject("__init__", ast.parse(empty_constructor), [], ty, system)


class Py2Smt:
    def __init__(self, classes: List[Type], depth_bound: int = 20):
        self.classes = classes
        self.class_fields = {}
        self.class_types = {}
        self.depth_bound = depth_bound

        self._abstract_types = {}
        self._get_class_fields()

        # methods from the classes
        self.methods = {(cls.__name__, method):
                        MethodObject.get_from_method(getattr(cls, method), self, cls)
                        for cls in classes
                        for method in set(dir(cls)) - set(dir(object))
                        if (not method.startswith("__") and isinstance(getattr(cls, method), Callable))}

        # constructors from the classes
        self.methods.update({(cls.__name__, f"__init__"):
                             MethodObject.create_empty_constructor(self, cls, self.class_fields[cls])
                             for cls in classes
                             if getattr(cls, "__init__") is object.__init__})
        self.methods.update({(cls.__name__, f"__init__"):
                             MethodObject.get_from_method(getattr(cls, "__init__"), self, cls)
                             for cls in classes
                             if getattr(cls, "__init__") is not object.__init__})

        # methods from the stdlib
        self.methods.update({("", method): MethodObject.get_from_method(getattr(stdlib, method), self)
                             for method in set(dir(stdlib)) - set(dir(object))
                             if (not method.startswith("__")) and isinstance(getattr(stdlib, method), Callable) and
                             getattr(stdlib, method).__module__ == stdlib.__name__})

    def add_abstract_type(self, concrete: Type, abstract: z3.SortRef):
        self._abstract_types[str(concrete)] = abstract

    def get_abstract_type_from_concrete(self, concrete: Type) -> Union[Type, z3.SortRef]:
        if str(concrete) not in self._abstract_types:
            return concrete
        return self._abstract_types[str(concrete)]

    def get_transition_relation_for_method(self, cls: Type, method: Callable) -> Callable[[State, State], z3.ExprRef]:
        if (cls, method.__name__) not in self.methods:
            raise ValueError("Method not represented")

        cfg = self.methods[method].cfg
        return cfg.get_transition_relation(self.depth_bound)

    def get_entry_by_name(self, name: str, typ: Union[Type, DatatypeSortRef, str, None] = None) -> MethodObject:
        if isinstance(typ, DatatypeSortRef):
            typ = [it for it in self.classes if it.__name__ == typ.name()][0]
        if isinstance(typ, Type):
            typ = typ.__name__
        for cls, method in self.methods:
            if method == name and (typ is None or typ == cls):
                return self.methods[(cls, method)]
        if name in [cls.__name__ for cls in self.classes]:
            return self.methods[(name, f"__init__")]
        raise ValueError(f"Method {f'{typ}.' if type is not None else ''}{name} not represented")

    def has_entry(self, name: str, typ: Union[Type, DatatypeSortRef, str, None] = None) -> bool:
        try:
            self.get_entry_by_name(name, typ)
            return True
        except ValueError:
            return False

    def get_or_add_entry_by_name(self, name: str, cls: Type) -> MethodObject:
        if self.has_entry(name, cls):
            return self.get_entry_by_name(name, cls)
        else:
            ret = MethodObject.get_from_method(getattr(cls, name), self, cls)
            self.methods[(cls, name)] = ret
            return ret

    def _get_class_fields(self):
        for cls in self.classes:
            node = ast.parse(dedent(inspect.getsource(cls)))
            annotations = [it for it in node.body[0].body if isinstance(it, ast.AnnAssign)]
            self.class_fields[cls] = {it.target.id: self.get_type_from_annotation(it.annotation) for it in annotations}

        for cls in self.classes:
            superclasses = []
            queue = list(cls.__bases__)
            while queue:
                superclass = queue[0]
                queue = queue[1:]
                superclasses.append(superclass)
                queue.extend(superclass.__bases__)
            superclasses.remove(object)  # trivial
            self.class_fields[cls].update({field: self.class_fields[superclass][field]
                                           for superclass in superclasses for field in self.class_fields[superclass]})

            self.class_types[cls] = z3.Datatype(f"{cls.__name__}"), \
                [(field, Signature.parse_type(self.get_abstract_type_from_concrete(typ)))
                 for field, typ in self.class_fields[cls].items()]
        for cls in self.classes:
            datatype, fields = self.class_types[cls]
            fields = [(k, (self.class_types[v] if v in self.class_types else v)) for k, v in fields]
            datatype.declare(f"mk_{cls.__name__}", *fields)
            self.class_types[cls] = datatype.create()

    def _get_type_from_string(self, typename: str) -> Type:
        base_types = {"int": IntSort(), "bool": BoolSort(), "str": StringSort()}
        if typename in base_types:
            return base_types[typename]
        elif typename in [cls.__name__ for cls in self.classes]:
            return [cls for cls in self.classes if cls.__name__ == typename][0]
        else:
            raise ValueError("Unknown type")

    def get_type_from_annotation(self, annotation: expr) -> Any:
        if annotation is None:
            return None
        if isinstance(annotation, ast.Subscript):
            assert isinstance(annotation.slice, ast.Name) or isinstance(annotation.slice, ast.Tuple)
            if (isinstance(annotation.value, ast.Name) and annotation.value.id == "List") \
                    or (isinstance(annotation.value, ast.Attribute) and annotation.value.attr == "List"):
                return ArraySort(IntSort(), self.get_type_from_annotation(annotation.slice))
            elif (isinstance(annotation.value, ast.Name) and annotation.value.id == "Dict") \
                    or (isinstance(annotation.value, ast.Attribute) and annotation.value.attr == "Dict"):
                return ArraySort(self.get_type_from_annotation(annotation.slice.elts[0]),
                                 Signature.get_or_create_optional_type(
                                     self.get_type_from_annotation(annotation.slice.elts[1])))
            elif (isinstance(annotation.value, ast.Name) and annotation.value.id == "Set") \
                    or (isinstance(annotation.value, ast.Attribute) and annotation.value.attr == "Set"):
                return SetSort(self.get_type_from_annotation(annotation.slice))

            raise AssertionError("Unknown subscript type")
        elif isinstance(annotation, ast.List):
            assert len(annotation.elts) == 1
            ret = ArraySort(IntSort(), self.get_type_from_annotation(*annotation.elts))
        elif isinstance(annotation, Constant):
            ret = self._get_type_from_string(str(annotation.value))
        elif isinstance(annotation, ast.Dict):
            assert len(annotation.keys) == len(annotation.values) == 1
            ret = ArraySort(self.get_type_from_annotation(*annotation.keys),
                            Signature.get_or_create_optional_type(self.get_type_from_annotation(*annotation.values)))
        elif isinstance(annotation, ast.Set):
            assert len(annotation.elts) == 1
            ret = SetSort(self.get_type_from_annotation(*annotation.elts))
        else:
            assert isinstance(annotation, ast.Name)
            ret = self._get_type_from_string(annotation.id)
        return self.get_abstract_type_from_concrete(ret)

    def is_field_of_class(self, cls: Type, field: str) -> bool:
        if isinstance(cls, DatatypeSortRef):
            cls = [it for it in self.classes if it.__name__ == cls.name()][0]
        return field in self.class_fields[cls]

    def get_type_from_field(self, cls: Type, field: str) -> Any:
        if isinstance(cls, DatatypeSortRef):
            cls = [it for it in self.classes if it.__name__ == cls.name()][0]
        return self.class_fields[cls][field]

    def get_fields_from_class(self, cls: Type) -> dict[str, DatatypeSortRef]:
        if isinstance(cls, DatatypeSortRef):
            cls = [it for it in self.classes if it.__name__ == cls.name()][0]
        return {field: Signature.parse_type(self.get_abstract_type_from_concrete(typ))
                for field, typ in self.class_fields[cls].items()}
