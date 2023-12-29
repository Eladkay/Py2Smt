from typing import Any, Union

import z3
from z3 import (ExprRef, ArithSortRef, SortRef, BoolSortRef,
                DatatypeSortRef, If, Datatype, SeqRef, StringVal)


IntType = z3.IntSort()
StringType = z3.StringSort()
BoolType = z3.BoolSort()


def upcast_expr(var1: ExprRef, target_sort: SortRef) -> ExprRef:
    # todo: essentially, the problem here is that var1 can be a pointer and the upcast
    # just changes the pointer type, but not the underlying type. What we actually need is to allocate
    # new memory in the target sort heap and copy the value there. But that's a bit of a problem.
    # Potential solution: change the caller to also expect new heaps and HPs.
    real_type = var1.sort()
    if isinstance(real_type, ArithSortRef) and isinstance(target_sort, BoolSortRef):
        return var1 != 0
    if isinstance(real_type, BoolSortRef) and isinstance(target_sort, ArithSortRef):
        return If(var1, 1, 0)
    if not isinstance(var1.sort(), DatatypeSortRef) or not isinstance(target_sort, DatatypeSortRef):
        raise ValueError(f"Cannot cast sort {var1.sort()} to "
                         f"{target_sort} (one of the sorts is not a class)")
    fields_real = [real_type.accessor(0, i) for i in range(real_type.constructor(0).arity())]
    fields_target = [target_sort.accessor(0, i) for i in range(target_sort.constructor(0).arity())]
    field_names_real = [it.name() for it in fields_real]
    field_names_target = [it.name() for it in fields_target]
    missing = set(field_names_target) - set(field_names_real)
    if len(missing) != 0:
        raise ValueError(f"Cannot cast {var1.sort()} to "
                         f"{target_sort} (the sorts are not comparable)")
    return target_sort.constructor(0)(*[[itt for itt in fields_real
                                         if itt.name() == it.name()][0](var1)
                                        for it in fields_target])


OPTIONAL_TYPES = {}

POINTER_TYPES = {}


def _cleanup_type_name(ty: str) -> str:
    ty = ty.replace(" ", "")
    ty = ty.replace("(", "_")
    ty = ty.replace(")", "_")
    ty = ty.replace(",", "_")
    return ty


def get_or_create_optional_type(ty: SortRef) -> DatatypeSortRef:
    if ty in OPTIONAL_TYPES:
        return OPTIONAL_TYPES[ty]
    option = Datatype(f"{_cleanup_type_name(str(ty))}Option")
    option.declare('some', ('val', ty))
    option.declare("none")

    option = option.create()
    OPTIONAL_TYPES[ty] = option
    return option


def get_or_create_pointer(ty: Union[type, DatatypeSortRef]) -> SortRef:
    type_name = ty.name() if isinstance(ty, DatatypeSortRef) else ty.__name__
    ptr = get_or_create_pointer_by_name(type_name)
    return ptr


def get_heap_pointer_name(ty: Union[type, SortRef]) -> str:
    type_name = ty.name() if isinstance(ty, SortRef) else ty.__name__
    return f"__heapptr_{type_name}__"


def get_heap_name(ty: Union[type, SortRef]) -> str:
    type_name = ty.name() if isinstance(ty, SortRef) else ty.__name__
    return f"__heap_{type_name}__"


def get_or_create_pointer_by_name(type_name: str) -> DatatypeSortRef:
    if type_name in POINTER_TYPES:
        return POINTER_TYPES[type_name]
    option = Datatype(f"__{type_name}Pointer__")
    option.declare(f'ptr', ('loc', IntType))

    option = option.create()
    POINTER_TYPES[type_name] = option
    return option


def singleton_list(t: Any) -> SeqRef:
    if isinstance(t, str):
        t = StringVal(t)
    if isinstance(t, int):
        t = z3.IntVal(t)
    if isinstance(t, bool):
        t = z3.BoolVal(t)
    return z3.Unit(t)


def is_pointer_type(ty: SortRef) -> bool:
    return ty in POINTER_TYPES.values()
