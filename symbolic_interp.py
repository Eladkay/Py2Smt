import typing
from typing import List, Tuple, Any
from collections import OrderedDict
from z3 import *  # pylint: disable=unused-wildcard-import,wildcard-import

# we need singleton_list
# noinspection PyUnresolvedReferences
# pylint: disable=unused-import
from smt_helper import upcast_expr, OPTIONAL_TYPES, singleton_list, POINTER_TYPES, get_heap_name, \
    get_or_create_pointer_by_name, get_heap_pointer_name, is_pointer_type, get_pointed_type, upcast_pointer, \
    get_or_create_pointer, try_upcast


class Signature:
    def __init__(self, decls: typing.Union[dict, List[Tuple[str, Any]]]):
        self.decls = OrderedDict(decls)
        self.middleware = []

    def variable_names(self) -> List[str]:
        return list(self.decls.keys())

    def type_of(self, varname: str) -> Any:
        return self.decls[varname]

    def intersect(self, var_names: List[str]) -> 'Signature':
        return type(self)([(name, ty) for (name, ty) in self.decls.items() if name in var_names])

    def __repr__(self) -> str:
        return "; ".join(f"{name}: {ty}" for name, ty in self.decls.items())

    def use(self, middleware: dict) -> 'Signature':
        if isinstance(middleware, dict):
            middleware = [middleware]
        self.middleware += middleware
        return self

    def __or__(self, other):
        assert isinstance(other, Signature)
        sig = Signature(self.decls | other.decls)
        sig.middleware = self.middleware + other.middleware
        return sig


class State:
    def __init__(self, sig: Signature, helpers: typing.Callable[[dict, dict], dict] | None, class_types: dict,
                 suffix: str = ''):
        self.locals = {}
        self.path_constraint = []
        self.class_types = class_types
        self.tag = suffix
        self.sig = sig
        self.locals = {name: Const(name + suffix, ty) for (name, ty) in sig.decls.items()}
        self.middleware = sig.middleware
        self.helpers = helpers

    def assign(self, values: dict) -> 'State':
        """simultaneous assignment"""
        cloned = self.clone()
        try:
            new_values = {}
            for target, value in values.items():
                target_value = new_values[target] if target in new_values else cloned.locals[target]
                computed_value = self.eval(value)
                if isinstance(target_value, ExprRef) and isinstance(computed_value, ExprRef) and \
                        target_value.sort() != computed_value.sort():
                    computed_value = try_upcast(self.locals, new_values, self.class_types, computed_value,
                                                target_value.sort())
                new_values[target] = computed_value
            cloned.locals.update(new_values)
        except Exception as exp:
            raise type(exp)(f"Failed to assign {values}") from exp
        return cloned

    def assume(self, cond: typing.Union[ExprRef, bool, str]) -> 'State':
        cond = self.eval(cond)
        if isinstance(cond, bool):
            cond = BoolVal(cond)
        cloned = self.clone()
        cloned.path_constraint.append((cond.get_id(), cond))
        return cloned

    def eval(self, expr: Any) -> Any:
        if callable(expr):
            expr = expr(self)
        if isinstance(expr, str):
            try:
                ctx = {'_': self}
                for mw in self.middleware:
                    ctx.update(mw)
                if self.helpers is not None:
                    ctx.update(self.helpers(self.locals, ctx))
                ctx.update(self.locals)
                ctx.update({str(ty): ty for k, ty in OPTIONAL_TYPES.items()})
                ctx.update({str(ty): ty for k, ty in POINTER_TYPES.items()})

                expr = eval(expr, globals(), ctx)
            except Exception as exp:
                raise type(exp)(f"Failed to evaluate {expr} ({exp})") from exp
        return expr

    def clone(self) -> 'State':
        c = type(self)(self.sig, self.helpers, self.class_types, self.tag)
        c.locals = self.locals.copy()
        c.path_constraint = self.path_constraint.copy()
        c.middleware = self.middleware
        return c

    @property
    def assumptions(self) -> List[ExprRef]:
        return [value for _, value in self.path_constraint]

    def make_concrete(self, model: ModelRef) -> 'State':
        c = type(self)(self.sig, self.helpers, self.class_types, self.tag)
        c.locals = {name: self.make_val_concrete(model, var) for name, var in self.locals.items()}
        return c

    @staticmethod
    def make_val_concrete(model: ModelRef, expr: ExprRef) -> Any:
        if isinstance(expr, AstRef):
            val = model.eval(expr)
            if z3.is_array(val):
                array_rep = {}
                while z3.is_store(val):
                    idx = val.arg(1)
                    val = val.arg(2)
                    array_rep[idx.as_long()] = val
                    val = val.arg(0)

                k = val.arg(0) if z3.is_const_array(val) else '???'

                alen = max(array_rep.keys()) + 1 if array_rep else 0
                ret = [k] * alen
                for i, val in array_rep.items():
                    ret[i] = val
                if not (ret and ret[-1] == k):
                    ret.append(k)
                ret.append("...")
                return ret
            return val
        return expr

    def make_var_concrete(self, model: ModelRef, varname: str) -> Any:
        return self.make_val_concrete(model, self.locals[varname])

    def _equate_vars(self, other: 'State') -> ExprRef:
        conj = []
        for (var, val) in self.locals.items():
            if var in other.locals:
                oval = other.locals[var]
                try:
                    conj.append(val == oval)
                except Z3Exception as exp:
                    raise Z3Exception(f"Could not compare {val} and {oval} of "
                                      f"sorts {val.sort()}, {oval.sort()}") from exp
        return And(*conj)

    def __getitem__(self, varname: str) -> ExprRef:
        return self.locals[varname]

    def __eq__(self, other: 'State') -> ExprRef:
        assert isinstance(other, State)
        return self._equate_vars(other)

    def __call__(self, model: ModelRef) -> 'State':
        assert isinstance(model, ModelRef)
        return self.make_concrete(model)

    def __repr__(self) -> str:
        return str(self.locals)
