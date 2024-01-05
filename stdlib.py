from z3 import Length, Replace


# noinspection PyPep8Naming
def And(x: bool, y: bool) -> bool:
    if x:
        return y
    return False


# noinspection PyPep8Naming
def Or(x: bool, y: bool) -> bool:
    if x:
        return True
    return y


# noinspection PyPep8Naming
def Not(x: bool) -> bool:
    if x:
        return False
    return True


# noinspection PyShadowingBuiltins
def hash(x: int) -> int:
    return x


# noinspection PyShadowingBuiltins
def len(s: str) -> int:
    # noinspection PyTypeChecker
    return Length(s)


def str_replace(s: str, old: str, new: str) -> str:
    # noinspection PyTypeChecker
    return Replace(s, old, new)


def ValueError():
    pass


def TypeError():
    pass


def Exception():
    pass


def range(n: int):
    pass


def __assume__(s):
    pass


def __literal__(s):
    pass


def is_valid(s):
    pass


def id(s):
    pass

def int(num: float) -> int:
    pass

def singleton_list(s):
    pass

def list_of(l, sort):
    pass
