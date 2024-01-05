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


class HashEntry[K, V]:
    next: 'HashEntry[K, V]'
    hash_code: int
    key: K
    value: V

    def __init__(self, next: Optional['HashEntry[K, V]'], hash_code: int, key: K, value: V):
        self.next = next
        self.hash_code = hash_code
        self.key = key
        self.value = value

    def get_key(self) -> K:
        return self.key

    def get_value(self) -> V:
        return self.value

    def set_value(self, value: V):
        self.value = value


class LinkEntry[K, V](HashEntry):
    before: 'LinkEntry[K, V]'
    after: 'LinkEntry[K, V]'

    def __init__(self, next: 'HashEntry[K, V]', hash_code: int, key: K, value: V):
        self.next = next
        self.hash_code = hash_code
        self.key = key
        self.value = value
        self.before = None
        self.after = None


class LRUMap[K, V]:
    max_size: int
    mod_count: int
    size: int
    load_factor: float
    threshold: int
    header: LinkEntry
    data: List[LinkEntry]

    def __init__(self):
        self.max_size = 16
        self.mod_count = 0
        self.size = 0
        self.load_factor = 0.75
        self.threshold = int(self.max_size * self.load_factor)
        self.header = LinkEntry(None, -1, None, None)
        self.header.before = self.header
        self.header.after = self.header
        self.data = [None]
        for i in range(self.max_size - 1):
            self.data.append(None)

    def get(self, key: K) -> V:
        entry = self._get_entry(key)
        if entry is None:
            return None
        self._move_to_mru(entry)
        return entry.get_value()

    def _move_to_mru(self, entry: LinkEntry):
        if entry.after != self.header:
            self.mod_count += 1
            assert entry.before is not None
            entry.before.after = entry.after
            entry.after.before = entry.before
            entry.after = self.header
            entry.before = self.header.before
            self.header.before.after = entry
            self.header.before = entry
        else:
            assert entry != self.header

    def put(self, key: K, value: V) -> V:
        hash_code = hash(key)
        index = self.hash_index(hash_code, len(self.data))
        entry = self.data[index]
        while entry is not None:
            if entry.hash_code == hash_code and entry.key == key:
                old_value = entry.get_value()
                entry.set_value(value)
                return old_value
            entry = entry.next
        self.add_mapping(index, hash_code, key, value)
        return None

    def add_mapping(self, index: int, hash_code: int, key: K, value: V):
        if self.is_full():
            reuse = self.header.after
            assert reuse is not None
            self.reuse_mapping(reuse, index, hash_code, key, value)
        else:
            self._add_mapping(index, hash_code, key, value)

    def reuse_mapping(self, entry: LinkEntry, hash_index: int, hash_code: int, key: K, value: V):
        remove_index = self.hash_index(entry.hash_code, len(self.data))
        tmp: List[HashEntry] = self.data
        loop = tmp[remove_index]
        previous = None
        while loop != entry and loop is not None:
            previous = loop
            loop = loop.next
        assert loop is not None
        self.mod_count += 1
        self.remove_entry(entry, remove_index, previous)
        self.reuse_entry(entry, hash_index, hash_code, key, value)
        self.data[hash_index] = entry

    def hash_index(self, hash_code: int, length: int) -> int:
        return hash_code & (length - 1)

    def is_full(self) -> bool:
        return self.size >= self.max_size

    def _add_mapping(self, index: int, hash_code: int, key: K, value: V):
        self.mod_count += 1
        entry = self.create_entry(self.data[index], hash_code, key, value)
        self.data[index] = entry
        self.size += 1
        self.check_capacity()

    def remove_entry(self, entry: HashEntry, index: int, previous: HashEntry):
        if previous is None:
            self.data[index] = entry.next
        else:
            previous.next = entry.next

    def reuse_entry(self, entry: HashEntry, hash_index: int, hash_code: int, key: K, value: V):
        entry.next = self.data[hash_index]
        entry.hash_code = hash_code
        entry.key = key
        entry.value = value

    def create_entry(self, next: HashEntry, hash_code: int, key: K, value: V) -> HashEntry:
        return HashEntry(next, hash_code, key, value)

    def _get_entry(self, key: K) -> LinkEntry:
        hash_code = hash(key)
        entry = self.data[self.hash_index(hash_code, len(self.data))]
        while entry is not None:
            if entry.hash_code == hash_code and entry.key == key:
                return entry
            entry = entry.next
        return None

    def check_capacity(self):
        if self.size > self.threshold:
            self.ensure_capacity(len(self.data) * 2)

    def ensure_capacity(self, new_capacity: int):
        old_capacity = len(self.data)
        if new_capacity <= old_capacity:
            return
        if self.size == 0:
            self.threshold = int(new_capacity * self.load_factor)
            self.data = [None]
            for i in range(new_capacity - 1):
                self.data.append(None)
            return
        old_entries = self.data
        new_entries = [None] * new_capacity
        self.mod_count += 1
        for i in range(0, old_capacity):
            entry = old_entries[i]
            if entry is not None:
                old_entries[i] = None
                while entry is not None:
                    next = entry.next
                    index = self.hash_index(entry.hash_code, new_capacity)
                    entry.next = new_entries[index]
                    new_entries[index] = entry
                    entry = next
        self.threshold = int(new_capacity * self.load_factor)
        self.data = new_entries


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
