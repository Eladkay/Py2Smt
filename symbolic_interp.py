import typing
from typing import List, Tuple, Any
from z3 import *
from collections import OrderedDict


class Signature:
    def __init__(self, decls: typing.Union[dict, List[Tuple[str, Any]]]):
        self.decls = OrderedDict((name, self.parse_type(ty))
                                 for (name, ty) in decls.items())
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

    @classmethod
    def parse_type(cls, ty: Any) -> SortRef:
        if isinstance(ty, list):
            assert len(ty) == 1
            return ArraySort(IntSort(), cls.parse_type(ty[0]))
        if isinstance(ty, dict):
            assert len(ty) == 1
            key, value = list(ty.items())[0]
            key_type = cls.parse_type(key)
            value_type = cls.parse_type(value)
            option = cls.get_or_create_optional_type(value_type)
            return ArraySort(key_type, option)
        if isinstance(ty, set):
            assert len(ty) == 1
            return SetSort(cls.parse_type(list(ty)[0]))
        if isinstance(ty, tuple):
            types = [cls.parse_type(t) for t in ty]
            return TupleSort(f"{ty}", types)[0]
        else:
            ty = cls.TYPE_ALIASES.get(ty, ty)
            if isinstance(ty, str) and ty in [it.__name__ for it in cls.TYPE_ALIASES.keys()]:
                return cls.TYPE_ALIASES[eval(ty)]
            return ty

    @staticmethod
    def _cleanup_type_name(ty: str) -> str:
        ty = ty.replace(" ", "")
        ty = ty.replace("(", "_")
        ty = ty.replace(")", "_")
        ty = ty.replace(",", "_")
        return ty

    @classmethod
    def get_or_create_optional_type(cls, ty: Any) -> DatatypeSortRef:
        if isinstance(ty, str):
            ty = eval(ty)
        if isinstance(ty, typing.Hashable) and ty in cls.OPTIONAL_TYPES:
            return cls.OPTIONAL_TYPES[ty]
        option = Datatype(f"{Signature._cleanup_type_name(str(ty))}Option")
        option.declare('some', ('val', ty))
        option.declare("none")

        option = option.create()
        option.__optional__ = True
        cls.OPTIONAL_TYPES[ty] = option
        return option

    def __or__(self, other):
        assert isinstance(other, Signature)
        sig = Signature(self.decls | other.decls)
        sig.middleware = self.middleware + other.middleware
        return sig

    TYPE_ALIASES = {
        int: IntSort(), Int: IntSort(),
        bool: BoolSort(), Bool: BoolSort(),
        str: StringSort(), String: StringSort()
    }

    OPTIONAL_TYPES = {}


class State:
    def __init__(self, sig: Signature, suffix: str = ''):
        self.locals = {}
        self.path_constraint = []
        self.tag = suffix
        self.sig = sig
        self.locals = {name: Const(name + suffix, ty) for (name, ty) in sig.decls.items()}
        self.middleware = sig.middleware

    @staticmethod
    def _upcast_expr(var1: ExprRef, target_sort: SortRef) -> ExprRef:
        real_type = var1.sort()
        if isinstance(real_type, ArithSortRef) and isinstance(target_sort, BoolSortRef):
            return var1 != 0
        if isinstance(real_type, BoolSortRef) and isinstance(target_sort, ArithSortRef):
            return If(var1, 1, 0)
        if not isinstance(var1.sort(), DatatypeSortRef) or not isinstance(target_sort, DatatypeSortRef):
            raise Exception(f"Cannot cast sort {var1.sort()} to {target_sort} (one of the sorts is not a class)")
        fields_real = [real_type.accessor(0, i) for i in range(real_type.constructor(0).arity())]
        fields_target = [target_sort.accessor(0, i) for i in range(target_sort.constructor(0).arity())]
        field_names_real = [it.name() for it in fields_real]
        field_names_target = [it.name() for it in fields_target]
        missing = set(field_names_target) - set(field_names_real)
        if len(missing) != 0:
            raise Exception(f"Cannot cast {var1.sort()} to {target_sort} (the sorts are not comparable)")
        return target_sort.constructor(0)(*[[itt for itt in fields_real if itt.name() == it.name()][0](var1)
                                            for it in fields_target])

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
                    computed_value = State._upcast_expr(computed_value, target_value.sort())
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
                expr = eval(expr, globals(), self._eval_context())
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

    def _eval_context(self) -> dict:
        ctx = {'_': self}
        for mw in self.middleware:
            ctx.update(mw)
        ctx.update(self.locals)
        ctx.update({str(ty): ty for k, ty in Signature.OPTIONAL_TYPES.items()})
        return ctx

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
