import typing
from typing import List, Tuple, Any
from z3 import *
from collections import OrderedDict

# we need singleton_list
# noinspection PyUnresolvedReferences
from smt_helper import upcast_expr, OPTIONAL_TYPES, singleton_list


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
        return "; ".join("%s: %s" % (name, ty) for name, ty in self.decls.items())

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
    def __init__(self, sig: Signature, suffix: str = ''):
        self.locals = {}
        self.path_constraint = []
        self.tag = suffix
        self.sig = sig
        self.locals = {name: Const(name + suffix, ty) for (name, ty) in sig.decls.items()}
        self.middleware = sig.middleware

    def assign(self, values: dict) -> 'State':
        """simultaneous assignment"""
        cloned = self.clone()
        try:
            new_values = {}
            for target, value in values.items():
                target_value = new_values[target] if target in new_values else cloned.locals[target]
                computed_value = self.eval(value)
                if isinstance(target_value, ExprRef) and isinstance(computed_value, ExprRef) and \
                        isinstance(target_value.sort(), DatatypeSortRef) and  \
                        isinstance(computed_value.sort(), DatatypeSortRef) and  \
                        target_value.sort() != computed_value.sort():
                    computed_value = upcast_expr(computed_value, target_value.sort())
                new_values[target] = computed_value
            cloned.locals.update(new_values)
        except Exception:
            raise Exception("Failed to assign %s" % values)
        return cloned

    def assume(self, cond: typing.Union[ExprRef, bool]) -> 'State':
        cond = self.eval(cond)
        if cond is True:
            cond = BoolVal(True)
        elif cond is False:
            cond = BoolVal(False)
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
                ctx.update(self.locals)
                ctx.update({str(ty): ty for k, ty in OPTIONAL_TYPES.items()})
                expr = eval(expr, globals(), ctx)
            except Exception as exp:
                raise Exception("Failed to evaluate %s (%s)" % (expr, exp))
        return expr

    def clone(self) -> 'State':
        c = type(self)(self.sig)
        c.locals = self.locals.copy()
        c.path_constraint = self.path_constraint.copy()
        c.middleware = self.middleware
        return c

    @property
    def assumptions(self) -> List[ExprRef]:
        return [value for _, value in self.path_constraint]

    def make_concrete(self, model: ModelRef) -> 'State':
        c = type(self)(self.sig)
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
        else:
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
                except Z3Exception:
                    raise Z3Exception("Could not compare %s and %s of sorts %s, %s" % (val, oval,
                                                                                       val.sort(), oval.sort()))
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
