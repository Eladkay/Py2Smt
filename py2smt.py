import ast
import inspect
import sys
import typing
from _ast import AST, expr, Constant
from textwrap import dedent
from typing import List, Union, Type, Callable, Any, Dict

from z3 import (z3, DatatypeSortRef, IntSort, ArraySort, SetSort, SortRef, SeqSort)

from generators.generators import CodeGenerationDispatcher
from smt_helper import get_or_create_optional_type, IntType, BoolType, StringType, get_heap_pointer_name, get_heap_name, \
    is_pointer_type, get_or_create_pointer_by_name, get_pointed_type, HELPER_SMT_FUNCTIONS, FloatType, NoneType
from symbolic_interp import Signature, State
import stdlib
from cfg import ControlFlowGraph


class MethodObject:

    @staticmethod
    def get_from_method(method: Callable, system: 'Py2Smt',
                        cls: Union[Type, None] = None, optimization_level: int = 1) -> 'MethodObject':
        cls = cls if cls else vars(sys.modules[method.__module__])[method.__qualname__.split('.')[0]]
        if not isinstance(cls, Type):
            cls = None
        return MethodObject(method.__name__,
                            ast.parse(dedent(inspect.getsource(method))),
                            inspect.getfullargspec(method).args,
                            cls,
                            system,
                            optimization_level)

    def __init__(self, name: str, tree: AST, args: List[str],
                 cls: Union[Type, None], system: 'Py2Smt', optimzation_level: int = 1):
        self.system = system
        self.name = name
        self.ast = tree
        if name == "__init__":
            self.args = args[1:]
        else:
            self.args = args
        self.cls = cls
        self._sig = None
        self._cfg = None
        self._dispatcher = None
        self.optimization_level = optimzation_level

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
            self._cfg.optimize_graph(self.optimization_level)

        return self._cfg

    def make_state(self, tag=""):
        return State(self.sig, HELPER_SMT_FUNCTIONS, self.system.class_types, tag)

    @staticmethod
    def create_empty_constructor(system: 'Py2Smt', ty: Type,
                                 fields: Dict[str, SortRef]) -> 'MethodObject':
        body = "pass" if not fields else \
            '\n\t'.join([f'self.{f} = {ControlFlowGraph.get_place_of_default_value(ty)}'
                         for f, ty in fields.items()])
        empty_constructor = f"""def __init__(self):\n\t{body}"""
        return MethodObject("__init__", ast.parse(empty_constructor), ['self'], ty, system)


class Py2Smt:
    def __init__(self, classes: List[Type], *, depth_bound: int = 20, optimization_level: int = 1):
        self.classes = classes
        self.class_fields = {}
        self.class_types = {}
        self.depth_bound = depth_bound
        self.optimization_level = optimization_level

        self._abstract_types = {}
        self._discover_class_generic_vars()
        self._discover_class_fields()

        # methods from the classes
        self.methods = {(cls.__name__, method):
                            MethodObject.get_from_method(getattr(cls, method), self, cls, self.optimization_level)
                        for cls in classes
                        for method in set(dir(cls)) - set(dir(object))
                        if (not method.startswith("__") and isinstance(getattr(cls, method), Callable))}

        # constructors for the classes
        self.methods.update({(cls.__name__, "__init__"):
                                 MethodObject.create_empty_constructor(self, cls, self.class_fields[cls])
                             for cls in classes
                             if getattr(cls, "__init__") is object.__init__})
        self.methods.update({(cls.__name__, "__init__"):
                                 MethodObject.get_from_method(getattr(cls, "__init__"), self, cls)
                             for cls in classes
                             if getattr(cls, "__init__") is not object.__init__})

        # methods from the stdlib
        self.methods.update({("", method): MethodObject.get_from_method(getattr(stdlib, method), self)
                             for method in set(dir(stdlib)) - set(dir(object))
                             if isinstance(getattr(stdlib, method), Callable) and
                             getattr(stdlib, method).__module__ == stdlib.__name__})

    def add_abstract_type(self, concrete: Type, abstract: z3.SortRef):
        self._abstract_types[str(concrete)] = abstract

    def get_abstract_type_from_concrete(self, concrete: Type) -> Union[Type, z3.SortRef]:
        if str(concrete) not in self._abstract_types:
            return concrete
        return self._abstract_types[str(concrete)]

    def get_transition_relation_for_method(self, cls: Type, method: Callable) \
            -> Callable[[State, State], z3.ExprRef]:
        if (cls, method.__name__) not in self.methods:
            raise ValueError("Method not represented")

        cfg = self.methods[method].cfg
        return cfg.get_transition_relation(self.depth_bound)

    def get_entry_by_name(self, name: str,
                          typ: Union[Type, DatatypeSortRef, str, None] = None) -> MethodObject:
        if isinstance(typ, DatatypeSortRef):
            if is_pointer_type(typ):
                typ = get_pointed_type(typ)
            types = [it for it in self.classes if it.__name__ == typ.name()]
            if len(types) == 0:
                raise ValueError(f"Method {f'{typ}.' if typ is not None else ''}{name} not represented")
            typ = types[0]
        if isinstance(typ, Type):
            typ = typ.__name__
        for cls, method in self.methods:
            if method == name and (typ is None or typ == cls):
                return self.methods[(cls, method)]
        if name in [cls.__name__ for cls in self.classes]:
            return self.methods[(name, "__init__")]
        raise ValueError(f"Method {f'{typ}.' if typ is not None else ''}{name} not represented")

    def has_method_entry(self, name: str, typ: Union[Type, DatatypeSortRef, str, None] = None) -> bool:
        try:
            self.get_entry_by_name(name, typ)
            return True
        except ValueError:
            return False

    def get_or_add_entry_by_name(self, name: str, cls: Type) -> MethodObject:
        if self.has_method_entry(name, cls):
            return self.get_entry_by_name(name, cls)

        ret = MethodObject.get_from_method(getattr(cls, name), self, cls)
        self.methods[(cls, name)] = ret
        return ret

    def _discover_class_fields(self):
        for cls in self.classes:
            node = ast.parse(dedent(inspect.getsource(cls)))
            annotations = [it for it in node.body[0].body if isinstance(it, ast.AnnAssign)]
            self.class_fields[cls] = {it.target.id: self.get_type_from_annotation(it.annotation)
                                      for it in annotations}

        for cls in self.classes:
            superclasses = set()
            queue = list(cls.__bases__)
            while queue:
                superclass = queue[0]
                queue = queue[1:]
                superclasses.add(superclass)
                queue.extend(superclass.__bases__)
            superclasses = superclasses - {object, typing.Generic}  # trivial
            superclasses = [it for it in superclasses if it.__module__ != typing.__name__]
            self.class_fields[cls].update({field: self.class_fields[superclass][field]
                                           for superclass in superclasses
                                           for field in self.class_fields[superclass]})

            self.class_types[cls] = z3.Datatype(f"{cls.__name__}"), \
                [(field, self.get_abstract_type_from_concrete(typ))
                 for field, typ in self.class_fields[cls].items()]
        for cls in self.classes:
            datatype, fields = self.class_types[cls]
            fields = [(k, (self.class_types[v] if v in self.class_types else v)) for k, v in fields]
            datatype.declare(f"mk_{cls.__name__}", *fields)
            self.class_types[cls] = datatype.create()

    def _get_type_from_string(self, typename: str) -> SortRef:
        base_types = {"int": IntType, "bool": BoolType, "str": StringType, "float": FloatType}
        if typename in base_types:
            return base_types[typename]
        if typename == NoneType.name():  # this is *not* NoneTypeName
            return NoneType
        if typename in [cls.__name__ for cls in self.classes]:
            return get_or_create_pointer_by_name(typename)
        if typename in self.generic_vars:  # todo: generic vars are global, also what about instantiation?
            return z3.DeclareSort(typename)  # todo cache this?
        raise ValueError(f"Unknown type {typename}")

    def get_type_from_annotation(self, annotation: expr) -> Any:
        if annotation is None:
            return None
        if isinstance(annotation, ast.Subscript):
            assert isinstance(annotation.slice, (ast.Name, ast.Tuple))
            val = annotation.value
            val_name = val.id if isinstance(val, ast.Name) else None
            val_attr = val.attr if isinstance(val, ast.Attribute) else None
            if val_name == "List" or val_attr == "List":
                return SeqSort(self.get_type_from_annotation(annotation.slice))
            if val_name == "Dict" or val_attr == "Dict":
                return ArraySort(self.get_type_from_annotation(annotation.slice.elts[0]),
                                 get_or_create_optional_type(self.get_type_from_annotation(annotation.slice.elts[1])))
            if val_name == "Set" or val_attr == "Set":
                return SetSort(self.get_type_from_annotation(annotation.slice))

            raise AssertionError("Unknown subscript type")
        if isinstance(annotation, ast.List):
            assert len(annotation.elts) == 1
            ret = ArraySort(IntSort(), self.get_type_from_annotation(*annotation.elts))
        elif isinstance(annotation, Constant):
            ret = self._get_type_from_string(str(annotation.value))
        elif isinstance(annotation, ast.Dict):
            assert len(annotation.keys) == len(annotation.values) == 1
            ret = ArraySort(self.get_type_from_annotation(*annotation.keys),
                            get_or_create_optional_type(self.get_type_from_annotation(*annotation.values)))
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
        return {field: self.get_abstract_type_from_concrete(typ)
                for field, typ in self.class_fields[cls].items()}

    def is_heap_pointer_name(self, name: str) -> bool:
        return any(name == get_heap_pointer_name(cls) for cls in self.class_types)

    def is_heap_name(self, ty: SortRef) -> bool:
        return any(ty == get_heap_name(cls) for cls in self.class_types)

    def _discover_class_generic_vars(self):
        self.generic_vars = set()
        for cls in self.classes:
            node = ast.parse(dedent(inspect.getsource(cls)))
            cls = node.body[0]
            if not hasattr(cls, "type_params"):
                continue
            # noinspection PyUnresolvedReferences
            for param in cls.type_params:
                self.generic_vars.add(param.name)
