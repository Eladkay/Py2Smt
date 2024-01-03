from typing import Optional, List, Set

from z3 import Or, z3, And

from py2smt import Py2Smt
from stdlib import __assume__
from tests.smt_test_case import SmtTestCase


class Node[E]:
    next: 'Node[E]'
    value: E


class CacheEntry[E]:
    idx: int
    value: E

    def __init__(self, idx: int, value: E):
        self.idx = idx
        self.value = value


class CachedLinkedList[E]:
    cache: Optional[CacheEntry[E]]
    head: Optional[Node[E]]

    def __init__(self):
        self.cache = None
        self.head = None

    def add(self, value: E):
        node = Node()
        node.value = value
        node.next = self.head
        self.head = node

    def index_of(self, value: E) -> int:
        if self.cache is not None and self.cache.value == value:
            return self.cache.idx
        idx = 0
        node = self.head
        while node is not None:
            if node.value == value:
                self.cache = CacheEntry(idx, value)
                return idx
            idx += 1
            node = node.next
        return -1

    def __getitem__(self, idx: int) -> E:
        node = self.head
        while idx > 0:
            node = node.next
            idx -= 1
        return node.value


class GenericList[T]:
    backing: List[T]
    cache_idx: int
    cache_value: T

    def set(self, idx: int, value: T):
        __assume__(0 <= idx < len(self.backing))
        self.backing[idx] = value
        self.cache_idx = idx
        self.cache_value = value

    def get(self, idx: int) -> T:
        __assume__(0 <= idx < len(self.backing))
        if self.cache_idx == idx:
            return self.cache_value
        self.cache_idx = idx
        self.cache_value = self.backing[idx]
        return self.cache_value


# Constrictor DS benchmarks - START
class ImmutableSet[T]:
    delegate: Set[T]
    hash_code: int

    def __init__(self, delegate: Set[T]):
        self.delegate = delegate
        self.hash_code = 0

    def contains(self, value: T) -> bool:
        return value in self.delegate

    def __hash__(self) -> int:
        if self.hash_code == 0:
            self.hash_code = hash(self.delegate)
        return self.hash_code


# Constrictor DS benchmarks - FIN


class Py2SmtDataStructureTests(SmtTestCase):
    def test_generic_list_set(self):
        smt = Py2Smt([GenericList])
        entry = smt.get_entry_by_name("set")
        self.assertEqual(entry.args, ["self", "idx", "value"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        self.assertImplies(tr, state1.eval("GenericList.backing(deref(self))[idx]") == state0.eval("value"))
        self.assertImplies(tr, state1.eval("GenericList.cache_idx(deref(self))") == state0.eval("idx"))
        self.assertImplies(tr, state1.eval("GenericList.cache_value(deref(self))") == state0.eval("value"))
        i = z3.Int("_i")
        self.assertImplies(And(tr, i != state0.eval("idx"), 0 < i,
                               i < state1.eval("Length(GenericList.backing(deref(self)))")),
                           state1.eval("GenericList.backing(deref(self))")[i]
                           == state0.eval("GenericList.backing(deref(self))")[i])

    def test_generic_list_get(self):
        smt = Py2Smt([GenericList])
        entry = smt.get_entry_by_name("get")
        self.assertEqual(entry.args, ["self", "idx"])
        state0, state1 = entry.make_state(), entry.make_state("'")
        tr = entry.cfg.get_transition_relation()(state0, state1)
        self.assertSat(tr)
        retvar = entry.cfg.return_var
        self.assertImplies(tr, Or(state1.eval(retvar) == state0.eval("GenericList.backing(deref(self))[idx]"),
                                  state1.eval(retvar) == state0.eval("GenericList.cache_value(deref(self))")))
        self.assertImplies(tr, state1.eval("GenericList.cache_idx(deref(self))") == state0.eval("idx"))
        self.assertImplies(tr, Or(state1.eval("GenericList.cache_value(deref(self))")
                                  == state0.eval("GenericList.backing(deref(self))[idx]"),
                                  state1.eval("GenericList.cache_value(deref(self))")
                                  == state0.eval("GenericList.cache_value(deref(self))")))
