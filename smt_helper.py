import functools
from typing import Any, Union, Dict, Optional, List

import z3
from z3 import (ExprRef, ArithSortRef, SortRef, BoolSortRef,
                DatatypeSortRef, If, Datatype, SeqRef, StringVal, DatatypeRef, ArrayRef, BoolVal, And, ToInt, Store,
                ToReal, SeqSort)


IntType = z3.IntSort()
StringType = z3.StringSort()
BoolType = z3.BoolSort()
FloatType = z3.RealSort()
NoneTypeName = "NoneType"  # todo: compute the type itself only once


def upcast_pointer(ptr1: DatatypeRef, target_pointer_sort: DatatypeSortRef, source_heap: ArrayRef) -> ExprRef:
    loc = ptr1.sort().accessor(0, 0)(ptr1)
    expr = source_heap[loc]
    pointed_sort = get_pointed_type(target_pointer_sort)
    return upcast_expr(expr, pointed_sort)


def upcast_expr(var1: ExprRef, target_sort: SortRef) -> ExprRef:
    real_type = var1.sort()
    if isinstance(real_type, ArithSortRef) and isinstance(target_sort, BoolSortRef):
        return var1 != 0
    if isinstance(real_type, BoolSortRef) and isinstance(target_sort, ArithSortRef):
        return If(var1, 1, 0)
    if isinstance(real_type, ArithSortRef) and isinstance(target_sort, ArithSortRef):
        if target_sort.is_int():
            return ToInt(var1)
        else:
            return ToReal(var1)
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

CONCRETE_TO_PTR = {}


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


def get_or_create_pointer(ty: DatatypeSortRef) -> SortRef:
    if ty in CONCRETE_TO_PTR:
        return CONCRETE_TO_PTR[ty]
    type_name = ty.name()
    ptr = get_or_create_pointer_by_name(type_name)
    CONCRETE_TO_PTR[ty] = ptr
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


def list_of(l: List[Any], sort: SortRef) -> SeqRef:
    if len(l) == 0:
        return z3.Empty(SeqSort(sort))
    return z3.Concat(singleton_list(l[0]), list_of(l[1:], sort))


def is_pointer_type(ty: SortRef) -> bool:
    return ty in POINTER_TYPES.values()


def get_pointed_type(ptr: DatatypeSortRef, fallback: Optional[Dict] = None) -> SortRef:
    ptr_to_concrete = {v: k for k, v in CONCRETE_TO_PTR.items()}
    if ptr in ptr_to_concrete:
        return ptr_to_concrete[ptr]
    if fallback is not None and ptr in fallback:
        return fallback[ptr]
    raise ValueError(f"Could not find pointed type for {ptr}!")


def try_upcast(locals: dict, new_values: dict, class_types: dict,
               computed_value: ExprRef, target_sort: SortRef) -> ExprRef:
    if is_pointer_type(target_sort):
        assert is_pointer_type(computed_value.sort()) and isinstance(computed_value, DatatypeRef)
        assert isinstance(target_sort, DatatypeSortRef)
        # latter is for type checker, actually implied by the first one

        if computed_value.sort() == get_or_create_pointer_by_name(NoneTypeName):
            upcast_value = target_sort.constructor(0)(0)
        else:
            fb = {get_or_create_pointer(ty): ty for ty in class_types.values()}
            source_pointed_sort = get_pointed_type(computed_value.sort(), fb)
            target_pointed_sort = get_pointed_type(target_sort, fb)

            upcast_value = upcast_pointer(computed_value, target_sort,
                                          locals[get_heap_name(source_pointed_sort)])
            assert get_heap_name(target_pointed_sort) not in new_values
            assert get_heap_pointer_name(target_pointed_sort) not in new_values
            target_heap = locals[get_heap_name(target_pointed_sort)]
            target_hp = locals[get_heap_pointer_name(target_pointed_sort)]
            new_values[get_heap_name(target_pointed_sort)] = \
                Store(target_heap, target_hp, upcast_value)
            new_values[get_heap_pointer_name(target_pointed_sort)] = \
                target_hp + 1
            upcast_value = target_sort.constructor(0)(target_hp)
    else:
        upcast_value = upcast_expr(computed_value, target_sort)
    return upcast_value


# Helper SMT functions - functions that should be accessible from the generated
# code but are not implementable in the code itself, usually because they need
# sort information

def dereference_pointer(locals, ctx, ptr: DatatypeRef) -> ExprRef:
    ptr_sort = ptr.sort()
    pointed_sort_name = [k for k, v in POINTER_TYPES.items() if v == ptr_sort][0]
    pointed_sort = ctx[pointed_sort_name]
    return locals[get_heap_name(pointed_sort)][ptr_sort.accessor(0, 0)(ptr)]


def get_pointer_from_loc(locals, ctx, loc: ExprRef, cls_name: str) -> DatatypeRef:
    ptr_sort = get_or_create_pointer_by_name(cls_name)
    return ptr_sort.constructor(0)(loc)


def get_loc_from_pointer(locals, ctx, ptr: DatatypeRef) -> ExprRef:
    ptr_sort = ptr.sort()
    return ptr_sort.accessor(0, 0)(ptr)


def is_pointer_memory_valid(locals, ctx, ptr: DatatypeRef) -> ExprRef:
    if not isinstance(ptr, DatatypeRef):
        return BoolVal(True)
    ptr_sort = ptr.sort()
    pointed_sort_name = [k for k, v in POINTER_TYPES.items() if v == ptr_sort][0]
    pointed_sort = ctx[pointed_sort_name]
    loc = get_loc_from_pointer(locals, ctx, ptr)
    return And(0 <= loc, loc < locals[get_heap_pointer_name(pointed_sort)])


def is_valid_not_none(locals, ctx, ptr: DatatypeRef) -> ExprRef:
    return And(is_pointer_memory_valid(locals, ctx, ptr), get_loc_from_pointer(locals, ctx, ptr) != 0)


def cast_to_int(locals, ctx, flt: ArithSortRef) -> ExprRef:
    return ToInt(flt)


HELPER_SMT_FUNCTIONS = lambda locals, ctx: {k: functools.partial(v, locals, ctx)
                                            for k, v in {"deref": dereference_pointer, "ref": get_pointer_from_loc,
                                                         "id": get_loc_from_pointer,
                                                         "is_valid": is_pointer_memory_valid,
                                                         "is_valid_not_none": is_valid_not_none,
                                                         "int": cast_to_int,
                                                         "singleton_list": lambda locals, ctx, *args:
                                                                           singleton_list(*args),
                                                         "list_of": lambda locals, ctx, *args:
                                                         list_of(*args)}.items()}
