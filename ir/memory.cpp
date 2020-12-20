// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "ir/memory.h"
#include "ir/globals.h"
#include "ir/state.h"
#include "ir/value.h"
#include "smt/solver.h"
#include "util/compiler.h"
#include <array>
#include <numeric>
#include <string>


// FIXME: remove; for DEBUG
#include <iostream>


using namespace IR;
using namespace smt;
using namespace std;
using namespace util;

  // Non-local block ids (assuming that no block is optimized out):
  // 1. null block: 0
  // 2. global vars in source: 1 ~ num_globals_src
  // 3. ptr args, fn call returned ptrs, ptr loads
  // 4. global vars in target only:
  //      num_nonlocals_src ~ num_nonlocals - 1

static unsigned next_local_bid;
static unsigned next_global_bid;
static unsigned next_fn_memblock;

static bool byte_has_ptr_bit() {
  return does_int_mem_access && does_ptr_mem_access;
}

static unsigned bits_ptr_byte_offset() {
  assert(!does_ptr_mem_access || bits_byte <= bits_program_pointer);
  return bits_byte < bits_program_pointer ? 3 : 0;
}

static unsigned padding_ptr_byte() {
  return Byte::bitsByte() - does_int_mem_access - 1 - Pointer::totalBits()
                          - bits_ptr_byte_offset();
}

static unsigned padding_nonptr_byte() {
  return
    Byte::bitsByte() - does_ptr_mem_access - bits_byte - bits_poison_per_byte;
}

static expr concat_if(const expr &ifvalid, expr &&e) {
  return ifvalid.isValid() ? ifvalid.concat(e) : move(e);
}

static expr prepend_if(const expr &pre, expr &&e, bool prepend) {
  return prepend ? pre.concat(e) : move(e);
}

static string local_name(const State *s, const char *name) {
  return string(name) + (s->isSource() ? "_src" : "_tgt");
}

// Assumes that both begin + len don't overflow
static expr disjoint(const expr &begin1, const expr &len1, const expr &begin2,
                     const expr &len2) {
  return begin1.uge(begin2 + len2) || begin2.uge(begin1 + len1);
}

static expr load_bv(const expr &var, const expr &idx0) {
  auto bw = var.bits();
  if (!bw)
    return {};
  if (var.isAllOnes())
    return true;
  auto idx = idx0.zextOrTrunc(bw);
  return var.lshr(idx).extract(0, 0) == 1;
}

static void store_bv(Pointer &p, const expr &val, expr &local,
                     expr &non_local, bool assume_local = false) {
  auto bid0 = p.getShortBid();

  auto set = [&](const expr &var) {
    auto bw = var.bits();
    if (!bw)
      return expr();
    auto bid = bid0.zextOrTrunc(bw);
    auto one = expr::mkUInt(1, bw) << bid;
    auto full = expr::mkInt(-1, bid);
    auto mask = (full << (bid + expr::mkUInt(1, bw))) |
                full.lshr(expr::mkUInt(bw, bw) - bid);
    return expr::mkIf(val, var | one, var & mask);
  };

  auto is_local = p.isLocal() || assume_local;
  local = expr::mkIf(is_local, set(local), local);
  non_local = expr::mkIf(!is_local, set(non_local), non_local);
}

namespace IR {

Byte::Byte(const Memory &m, expr &&byterepr) : m(m), p(move(byterepr)) {
  assert(!p.isValid() || p.bits() == bitsByte());
}

Byte::Byte(const Pointer &ptr, unsigned i, const expr &non_poison)
  : m(ptr.getMemory()) {
  // TODO: support pointers larger than 64 bits.
  assert(bits_program_pointer <= 64 && bits_program_pointer % 8 == 0);
  assert(i == 0 || bits_ptr_byte_offset() > 0);

  if (!does_ptr_mem_access) {
    p = expr::mkUInt(0, bitsByte());
    return;
  }

  if (byte_has_ptr_bit())
    p = expr::mkUInt(1, 1);
  p = concat_if(p,
                expr::mkIf(non_poison, expr::mkUInt(0, 1), expr::mkUInt(1, 1)))
      .concat(ptr());
  if (bits_ptr_byte_offset())
    p = p.concat(expr::mkUInt(i, bits_ptr_byte_offset()));
  p = p.concat_zeros(padding_ptr_byte());
  assert(!p.isValid() || p.bits() == bitsByte());
}

Byte::Byte(const Memory &m, const expr &data, const expr &non_poison) : m(m) {
  assert(!data.isValid() || data.bits() == bits_byte);
  assert(!non_poison.isValid() || non_poison.bits() == bits_poison_per_byte);

  if (!does_int_mem_access) {
    p = expr::mkUInt(0, bitsByte());
    return;
  }

  if (byte_has_ptr_bit())
    p = expr::mkUInt(0, 1);
  p = concat_if(p, non_poison.concat(data).concat_zeros(padding_nonptr_byte()));
  assert(!p.isValid() || p.bits() == bitsByte());
}

expr Byte::isPtr() const {
  if (!does_ptr_mem_access)
    return false;
  if (!does_int_mem_access)
    return true;
  auto bit = p.bits() - 1;
  return p.extract(bit, bit) == 1;
}

expr Byte::ptrNonpoison() const {
  if (!does_ptr_mem_access)
    return true;
  auto bit = p.bits() - 1 - byte_has_ptr_bit();
  return p.extract(bit, bit) == 0;
}

Pointer Byte::ptr() const {
  return { m, ptrValue() };
}

expr Byte::ptrValue() const {
  if (!does_ptr_mem_access)
    return expr::mkUInt(0, Pointer::totalBits());

  auto start = bits_ptr_byte_offset() + padding_ptr_byte();
  return p.extract(Pointer::totalBits() + start - 1, start);
}

expr Byte::ptrByteoffset() const {
  if (!does_ptr_mem_access)
    return expr::mkUInt(0, bits_ptr_byte_offset());
  if (bits_ptr_byte_offset() == 0)
    return expr::mkUInt(0, 1);

  unsigned start = padding_ptr_byte();
  return p.extract(bits_ptr_byte_offset() + start - 1, start);
}

expr Byte::nonptrNonpoison() const {
  if (!does_int_mem_access)
    return expr::mkUInt(0, bits_poison_per_byte);
  unsigned start = padding_nonptr_byte() + bits_byte;
  return p.extract(start + bits_poison_per_byte - 1, start);
}

expr Byte::nonptrValue() const {
  if (!does_int_mem_access)
    return expr::mkUInt(0, bits_byte);
  unsigned start = padding_nonptr_byte();
  return p.extract(start + bits_byte - 1, start);
}

expr Byte::isPoison(bool fullbit) const {
  expr np = nonptrNonpoison();
  if (byte_has_ptr_bit() && bits_poison_per_byte == 1) {
    assert(!np.isValid() || ptrNonpoison().eq(np == 0));
    return np == 1;
  }
  return expr::mkIf(isPtr(), !ptrNonpoison(),
                              fullbit ? np == -1ull : np != 0);
}

expr Byte::isZero() const {
  return expr::mkIf(isPtr(), ptr().isNull(), nonptrValue() == 0);
}

unsigned Byte::bitsByte() {
  unsigned ptr_bits = does_ptr_mem_access *
                        (1 + Pointer::totalBits() + bits_ptr_byte_offset());
  unsigned int_bits = does_int_mem_access * (bits_byte + bits_poison_per_byte);
  // allow at least 1 bit if there's no memory access
  return max(1u, byte_has_ptr_bit() + max(ptr_bits, int_bits));
}

Byte Byte::mkPtrByte(const Memory &m, const expr &val) {
  assert(does_ptr_mem_access);
  expr byte;
  if (byte_has_ptr_bit())
    byte = expr::mkUInt(1, 1);
  return { m, concat_if(byte, expr(val))
                .concat_zeros(bits_for_ptrattrs + padding_ptr_byte()) };
}

Byte Byte::mkNonPtrByte(const Memory &m, const expr &val) {
  if (!does_int_mem_access)
    return { m, expr::mkUInt(0, bitsByte()) };
  expr byte;
  if (byte_has_ptr_bit())
    byte = expr::mkUInt(0, 1);
  return { m, concat_if(byte, expr(val)).concat_zeros(padding_nonptr_byte()) };
}

Byte Byte::mkPoisonByte(const Memory &m) {
  IntType ty("", bits_byte);
  auto v = ty.toBV(ty.getDummyValue(false));
  return { m, v.value, v.non_poison };
}

ostream& operator<<(ostream &os, const Byte &byte) {
  if (byte.isPoison().isTrue())
    return os << "poison";

  if (byte.isPtr().isTrue()) {
    os << byte.ptr() << ", byte offset=";
    byte.ptrByteoffset().printSigned(os);
  } else {
    auto np = byte.nonptrNonpoison();
    auto val = byte.nonptrValue();
    if (np.isZero()) {
      val.printHexadecimal(os);
    } else {
      os << "#b";
      for (unsigned i = 0; i < bits_poison_per_byte; ++i) {
        unsigned idx = bits_poison_per_byte - i - 1;
        auto is_poison = (np.extract(idx, idx) == 1).isTrue();
        auto v = (val.extract(idx, idx) == 1).isTrue();
        os << (is_poison ? 'p' : (v ? '1' : '0'));
      }
    }
  }
  return os;
}

bool Memory::isInitialMemBlock(const expr &e) {
  string name;
  expr blk;
  unsigned hi, lo;
  if (e.isExtract(blk, hi, lo))
    name = blk.fn_name();
  else
    name = e.fn_name();
  return name == "init_mem";
}

Memory::AliasSet::AliasSet(const Memory &m)
  : local(m.numLocals(), false), non_local(m.numNonlocals(), false) {}

size_t Memory::AliasSet::size(bool islocal) const {
  return (islocal ? local : non_local).size();
}

int Memory::AliasSet::isFullUpToAlias(bool islocal) const {
  auto &v = islocal ? local : non_local;
  unsigned i = 0;
  for (unsigned e = v.size(); i != e; ++i) {
    if (!v[i])
      break;
  }
  for (unsigned i2 = i, e = v.size(); i2 != e; ++i2) {
    if (v[i])
      return -1;
  }
  return i - 1;
}

expr Memory::AliasSet::mayAlias(bool islocal, const expr &bid) const {
  int upto = isFullUpToAlias(islocal);
  if (upto >= 0)
    return bid.ule(upto);

  expr ret(false);
  for (unsigned i = 0, e = size(islocal); i < e; ++i) {
    if (mayAlias(islocal, i))
      ret |= bid == i;
  }
  return ret;
}

bool Memory::AliasSet::mayAlias(bool islocal, unsigned bid) const {
  return (islocal ? local : non_local)[bid];
}

unsigned Memory::AliasSet::numMayAlias(bool islocal) const {
  auto &v = islocal ? local : non_local;
  return count(v.begin(), v.end(), true);
}

bool Memory::AliasSet::intersects(const AliasSet &other) const {
  for (auto [v, v2] : { make_pair(&local, &other.local),
                        make_pair(&non_local, &other.non_local) }) {
    for (size_t i = 0, e = v->size(); i != e; ++i) {
      if ((*v)[i] && (*v2)[i])
        return true;
    }
  }
  return false;
}

void Memory::AliasSet::setMayAlias(bool islocal, unsigned bid) {
  (islocal ? local : non_local)[bid] = true;
}

void Memory::AliasSet::setMayAliasUpTo(bool local, unsigned limit,
                                       unsigned start) {
  for (unsigned i = start; i <= limit; ++i) {
    setMayAlias(local, i);
  }
}

void Memory::AliasSet::setFullAlias(bool islocal) {
  auto &v = (islocal ? local : non_local);
  auto sz = v.size();
  v.clear();
  v.resize(sz, true);
}

void Memory::AliasSet::setNoAlias(bool islocal, unsigned bid) {
  (islocal ? local : non_local)[bid] = false;
}

void Memory::AliasSet::intersectWith(const AliasSet &other) {
  auto intersect = [](auto &a, const auto &b) {
    auto I2 = b.begin();
    for (auto I = a.begin(), E = a.end(); I != E; ++I, ++I2) {
      *I = *I && *I2;
    }
  };
  intersect(local, other.local);
  intersect(non_local, other.non_local);
}

void Memory::AliasSet::unionWith(const AliasSet &other) {
  auto unionfn = [](auto &a, const auto &b) {
    auto I2 = b.begin();
    for (auto I = a.begin(), E = a.end(); I != E; ++I, ++I2) {
      *I = *I || *I2;
    }
  };
  unionfn(local, other.local);
  unionfn(non_local, other.non_local);
}

static const array<uint64_t, 5> alias_buckets_vals = { 1, 2, 3, 5, 10 };
static array<uint64_t, 6> alias_buckets_hits = { 0 };
static uint64_t only_local = 0, only_nonlocal = 0;

void Memory::AliasSet::computeAccessStats() const {
  auto nlocal = numMayAlias(true);
  auto nnonlocal = numMayAlias(false);

  if (nlocal > 0 && nnonlocal == 0)
    ++only_local;
  else if (nlocal == 0 && nnonlocal > 0)
    ++only_nonlocal;

  auto alias = nlocal + nnonlocal;
  for (unsigned i = 0; i < alias_buckets_vals.size(); ++i) {
    if (alias <= alias_buckets_vals[i]) {
      ++alias_buckets_hits[i];
      return;
    }
  }
  ++alias_buckets_hits.back();
}

void Memory::AliasSet::printStats(ostream &os) {
  double total
    = accumulate(alias_buckets_hits.begin(), alias_buckets_hits.end(), 0);

  if (!total)
    return;

  total /= 100.0;
  os.precision(1);
  os << fixed;

  os << "\n\nAlias sets statistics\n=====================\n"
        "Only local:     " << (only_local / total)
     << "%\nOnly non-local: " << (only_nonlocal / total)
     << "%\n\nBuckets:\n";

  for (unsigned i = 0; i < alias_buckets_vals.size(); ++i) {
    os << "\u2264 " << alias_buckets_vals[i] << ": "
       << (alias_buckets_hits[i] / total) << "%\n";
  }
  os << "> " << alias_buckets_vals.back() << ": "
     << (alias_buckets_hits.back() / total) << "%\n";
}

void Memory::AliasSet::print(ostream &os) const {
  auto print = [&](const char *str, const auto &v) {
    os << str;
    for (auto bit : v) {
      os << bit;
    }
  };

  bool has_local = false;
  if (numMayAlias(true) > 0) {
    print("local: ", local);
    has_local = true;
  }
  if (numMayAlias(false) > 0) {
    if (has_local) os << " / ";
    print("non-local: ", non_local);
  } else if (!has_local)
    os << "(empty)";
}


set<Memory::MemStore> Memory::mem_store_holder;

Memory::MemStore::MemStore(const Pointer &src, const expr *size,
                           unsigned align_src)
  : type(COPY), ptr_src(src), alias(src.getMemory()) {
  uint64_t st_size = 1;
  if (size)
    size->isUInt(st_size);
  src_alias = const_cast<Memory&>(src.getMemory())
                 .computeAliasing(src, st_size, align_src, false);
}

const Memory::MemStore*
Memory::MemStore::mkIf(const expr &cond, const MemStore *then,
                       const MemStore *els) {
  if (then == els)
    return then;

  MemStore st(COND);
  st.size.emplace(cond);
  st.next = then;
  st.els = els;
  st.alias = then ? then->alias : els->alias;
  st.alias.setFullAlias(false);
  st.alias.setFullAlias(true);
  return &*mem_store_holder.emplace(move(st)).first;
}

bool Memory::MemStore::isInitBlock() const {
  return uf_name == "init_mem";
}

void Memory::MemStore::print(std::ostream &os) const {
  auto type_str = [](const auto st) {
    switch (st->type) {
      case INT_VAL: return "INT VAL";
      case PTR_VAL: return "PTR VAL";
      case CONST:   return "CONST";
      case COPY:    return "COPY";
      case FN:      return "FN";
      case COND:    return "COND";
    }
    UNREACHABLE();
  };

  unsigned next_block_id = 0;
  map<const MemStore*, unsigned> block_id;
  auto get_id = [&](const auto st) {
    auto [I, inserted] = block_id.try_emplace(st, 0);
    if (inserted)
      I->second = next_block_id++;
    return I->second;
  };

  vector<const MemStore*> todo = { this };
  set<const MemStore*> printed;
  do {
    auto st = todo.back();
    todo.pop_back();
    if (!printed.emplace(st).second)
      continue;

    os << "Store #" << get_id(st) << "  Type: " << type_str(st)
       << "  Align: " << st->align;
    if (st->ptr)
      os << "\nPointer: " << *st->ptr;
    if (st->size)
      os << "\nSize: " << *st->size;
    os << "\nAlias: ";
    st->alias.print(os);

    switch (st->type) {
      case INT_VAL:
      case PTR_VAL:
      case CONST:
        os << "\nValue: " << st->value;
        break;
      case FN:
        os << "\nFN: " << st->uf_name;
        break;
      case COPY:
        os << "\nSRC PTR: " << *st->ptr_src;
        os << "\nSRC ALIAS: ";
        st->src_alias.print(os);
        break;
      case COND:
        break;
    }

    if (st->next)
      os << "\nSuccessor: #" << get_id(st->next);
    if (st->els) {
      todo.push_back(st->els);
      os << "\nElse: #" << get_id(st->els);
    }
    if (st->next)
      todo.push_back(st->next);
    os << "\n\n-----------------------------------------------------------\n";
  } while (!todo.empty());
}


static set<Pointer> all_leaf_ptrs(Memory &m, const expr &ptr) {
  set<Pointer> ptrs;
  for (auto &ptr_val : ptr.leafs()) {
    Pointer p(m, ptr_val);
    auto offset = p.getOffset();
    for (auto &bid : p.getBid().leafs()) {
      ptrs.emplace(m, bid, offset);
    }
  }
  return ptrs;
}

static set<expr> extract_possible_local_bids(Memory &m, const expr &eptr) {
  set<expr> ret;
  for (auto &ptr : all_leaf_ptrs(m, eptr)) {
    if (!ptr.isLocal().isFalse())
      ret.emplace(ptr.getShortBid());
  }
  return ret;
}

unsigned Memory::numLocals() const {
  return state->isSource() ? num_locals_src : num_locals_tgt;
}

unsigned Memory::numNonlocals() const {
  return state->isSource() ? num_nonlocals_src : num_nonlocals;
}

expr Memory::isBlockAlive(const expr &bid, bool local) const {
  return
    load_bv(local ? local_block_liveness : non_local_block_liveness, bid) &&
      (!local && has_null_block ? bid != 0 : true);
}

bool Memory::mayalias(bool local, unsigned bid0, const expr &offset0,
                      unsigned bytes, unsigned align, bool write) const {
  if (local && bid0 >= next_local_bid)
    return false;
  if (!local && (bid0 >= (write ? num_nonlocals_src : numNonlocals()) ||
                 bid0 < has_null_block + write * num_consts_src))
    return false;

  int64_t offset = 0;
  bool const_offset = offset0.isInt(offset);

  if (offset < 0)
    return false;

  assert(!isUndef(offset0));

  expr bid = expr::mkUInt(bid0, Pointer::bitsShortBid());
  if (auto algn = (local ? local_blk_align : non_local_blk_align).lookup(bid)) {
    uint64_t blk_align;
    ENSURE(algn->isUInt(blk_align));
    if (align > (1ull << blk_align) && (!observesAddresses() || const_offset))
      return false;
  }

  if (auto sz = (local ? local_blk_size : non_local_blk_size).lookup(bid)) {
    uint64_t blk_size;
    if (sz->isUInt(blk_size)) {
      if ((uint64_t)offset >= blk_size || bytes > (blk_size - offset))
        return false;
    }
  } else if (local) // allocated in another branch
    return false;

  // globals are always live
  if (local || (bid0 >= num_globals_src && bid0 < num_nonlocals_src)) {
    if ((local ? local_block_liveness : non_local_block_liveness)
          .extract(bid0, bid0).isZero())
      return false;
  }

  return true;
}

Memory::AliasSet Memory::computeAliasing(const Pointer &ptr, unsigned bytes,
                                         unsigned align, bool write) {
  assert(bytes % (bits_byte/8) == 0);

  AliasSet aliasing(*this);
  auto sz_local = aliasing.size(true);
  auto sz_nonlocal = aliasing.size(false);

  auto check_alias = [&](AliasSet &alias, bool local, unsigned bid,
                         const expr &offset) {
    if (!alias.mayAlias(local, bid) &&
        mayalias(local, bid, offset, bytes, align, write))
      alias.setMayAlias(local, bid);
  };

  // collect over-approximation of possible touched bids
  for (auto &p : all_leaf_ptrs(*this, ptr())) {
    if (has_readnone && p.isReadnone().isTrue())
      continue;
    if (has_readonly && write && p.isReadonly().isTrue())
      continue;

    AliasSet this_alias = aliasing;
    auto is_local = p.isLocal();
    auto shortbid = p.getShortBid();
    expr offset = p.getOffset();
    uint64_t bid;
    if (shortbid.isUInt(bid)) {
      if (!is_local.isFalse() && bid < sz_local)
        check_alias(this_alias, true, bid, offset);
      if (!is_local.isTrue() && bid < sz_nonlocal)
        check_alias(this_alias, false, bid, offset);
      goto end;
    }

    for (auto local : { true, false }) {
      if ((local && is_local.isFalse()) || (!local && is_local.isTrue()))
        continue;

      unsigned i = 0;
      if (!local)
        i = has_null_block + write * num_consts_src;

      for (unsigned e = local ? sz_local : sz_nonlocal; i < e; ++i) {
        check_alias(this_alias, local, i, offset);
      }
    }

end:
    // intersect computed aliasing with known aliasing
    auto I = ptr_alias.find(p.getBid());
    if (I != ptr_alias.end())
      this_alias.intersectWith(I->second);
    aliasing.unionWith(this_alias);
  }

  // intersect computed aliasing with known aliasing
  // We can't store the result since our cache is per Bid expression only
  // and doesn't take byte size, etc into account.
  auto I = ptr_alias.find(ptr.getBid());
  if (I != ptr_alias.end())
    aliasing.intersectWith(I->second);

  alias_info.computeAccessStats();
  return alias_info;
}

StateValue Memory::load(const Pointer &ptr, unsigned bytes, set<expr> &undef,
                        unsigned align, DataType type) {
  if (bytes == 0)
    return {};

  auto alias = computeAliasing(ptr, bytes, align, false);

  // TODO: optimize alignment for realloc COPY nodes
  // TODO: skip consideration of type punning yielding poison nodes
  unsigned bytes_per_load = gcd(align, bytes);
  {
    vector<const MemStore*> todo = { store_seq_head };
    set<const MemStore*> seen;
    while (bytes_per_load > 1 && !todo.empty()) {
      auto st = todo.back();
      todo.pop_back();
      if (!seen.insert(st).second)
        continue;

      if (st->alias.intersects(alias)) {
        bytes_per_load = gcd(bytes_per_load, st->align);
        if (st->size) {
          uint64_t size = 1;
          st->size->isUInt(size);
          bytes_per_load = gcd(bytes_per_load, size);
        }
      }

      if (st->next) todo.push_back(st->next);
      if (st->els)  todo.push_back(st->els);
    }
  }

  unsigned num_loads = bytes / bytes_per_load;
  assert((bytes % bytes_per_load) == 0);
  assert((bytes_per_load % (bits_byte / 8)) == 0);

  map<tuple<const MemStore*, const Pointer*, const AliasSet*>,
      vector<StateValue>> vals;
  vector<tuple<const MemStore*, const Pointer*, const AliasSet*>> todo
    = { { store_seq_head, &ptr, &alias } };
  set<tuple<const MemStore*, const Pointer*, const AliasSet*>> seen;

  do {
    auto key = todo.back();
    auto &st = *get<0>(key);
    auto &ptr = *get<1>(key);
    auto &alias = *get<2>(key);

    // TODO: don't process children if store matches perfectly or full write
    bool has_all_deps = true;
    if (st.next && !vals.count({st.next, &ptr, &alias})) {
      todo.emplace_back(st.next, &ptr, &alias);
      has_all_deps = false;
    }
    if (st.els && !vals.count({st.els, &ptr, &alias})) {
      todo.emplace_back(st.els, &ptr, &alias);
      has_all_deps = false;
    }
    if (st.ptr_src && !vals.count({st.next, &*st.ptr_src, &st.src_alias})) {
      assert(st.next);
      todo.emplace_back(st.next, &*st.ptr_src, &st.src_alias);
      has_all_deps = false;
    }

    if (!has_all_deps)
      continue;
    todo.pop_back();

    auto [I, inserted] = vals.try_emplace(key);
    auto &val = I->second;
    if (!inserted)
      continue;

    const vector<StateValue> *v1 = nullptr;
    if (st.next) {
      auto I = vals.find({st.next, &ptr, &alias});
      v1 = &I->second;
    }

    StateValue poison_byte(expr::mkUInt(0, bytes_per_load * 8), false);
    bool added_undef_vars = false;

    if (!st.alias.intersects(alias)) {
      for (unsigned i = 0; i < num_loads; ++i) {
        val.emplace_back(v1 ? (*v1)[i] : poison_byte);
      }
      continue;
    }

    // TODO: optimize full stores to GC unreachable nodes?
    auto store = [&](unsigned i, const StateValue &v, unsigned total_size) {
      assert(st.ptr);
      expr cond;
      if (bytes*8 != total_size || st.align < bytes || align < bytes) {
        assert(st.size);
        cond = ptr.getBid() == st.ptr->getBid();
        expr load_offset = (ptr + i).getShortOffset();
        expr store_offset = st.ptr->getShortOffset();

        if (!ptr.getShortOffset().eq(store_offset))
          cond &= load_offset.uge(store_offset);

        // skip upperbound conditions if loading from the same ptr as store
        // and there's space left to read
        uint64_t store_size;
        if (!(load_offset.eq(store_offset) && st.size->isUInt(store_size) &&
              store_size >= bytes_per_load)) {
          auto upper_bound
            = (*st.ptr + *st.size + expr::mkInt(-i, bits_for_offset));
          cond &= load_offset.ult(upper_bound.getShortOffset());
        }
      } else {
        cond = (ptr + i) == *st.ptr;
      }

      if (!added_undef_vars && !cond.isFalse()) {
        // TODO: benchmark skipping undef vars of v1 if cond == true
        undef.insert(st.undef.begin(), st.undef.end());
        added_undef_vars = true;
      }

      assert(!v.value.isValid() || v.value.bits() == bytes_per_load*8);
      assert(!v.non_poison.isValid() ||
             v.non_poison.bits() == bytes_per_load*8);

      if (v1) {
        auto &v1_sv = (*v1)[i / bytes_per_load];
        val.emplace_back(StateValue::mkIf(cond, v, v1_sv));
      } else
        val.emplace_back(cond.isFalse() ? poison_byte : v);
    };

    auto store_ptr = [&](const StateValue &ptr) {
      if (num_loads == 1) {
        store(0, ptr, bits_program_pointer);
        return;
      }
      // FIXME i is wrong for unaligned load/stores
      for (unsigned i = 0; i < bytes; i += bytes_per_load) {
        store(i, { ptr.value.concat(expr::mkUInt(i, 3)),
                   expr(ptr.non_poison) }, bits_program_pointer);
      }
    };

    auto combine_np = [](const expr &np, const expr &cond) {
      return np | expr::mkIf(cond, expr::mkUInt(0, np), expr::mkInt(-1, np));
    };

    switch (st.type) {
      case MemStore::INT_VAL: {
        assert(st.ptr);
        auto bits = st.value.bits();

        for (unsigned i = 0; i < bytes; i += bytes_per_load) {
          StateValue value;
          if (bits == bytes_per_load*8) {
            value = st.value;
          }
          else if (bytes*8 == bits && st.align >= bytes && align >= bytes) {
            unsigned high = little_endian
                              ? (i+1) * bytes_per_load * 8 - 1
                              : (num_loads - i) * bytes_per_load * 8 - 1;
            unsigned low = little_endian
                             ? i * bytes_per_load * 8
                             : (num_loads - i - 1) * bytes_per_load * 8;
            value = st.value.extract(high, low);
          }
          else {
            // TODO: optimize loads from small stores to avoid shifts
            auto diff = (ptr + i).getOffset() - st.ptr->getOffset();
            diff = (diff * expr::mkUInt(8 * bytes_per_load, diff))
                    .zextOrTrunc(bits);

            if (little_endian) {
              value.value = st.value.value.lshr(diff)
                              .extract(bytes_per_load * 8 - 1, 0);
              value.non_poison = st.value.non_poison.lshr(diff)
                                   .extract(bytes_per_load * 8 - 1, 0);
            } else {
              value.value = (st.value.value << diff)
                              .extract(bits - 1, bits - bytes_per_load * 8);
              value.non_poison = (st.value.non_poison << diff)
                                 .extract(bits - 1, bits - bytes_per_load * 8);
            }

            // optimization: if all ones, output is guaranteed to be false
            // regardless of which byte is read
            if (value.non_poison.isAllOnes())
              value.non_poison = expr::mkInt(-1, bytes_per_load * 8);
          }

          assert(!st.value.isValid() || !(*st.ptr)().isValid() ||
                 value.bits() == bytes_per_load * 8);

          // allow zero -> null type punning
          if (type == DATA_PTR) {
            store_ptr({ Pointer::mkNullPointer(*this).release(),
                        combine_np(value.non_poison, value.value == 0) });
          } else {
            store(i, value, bits);
          }
        }
        break;
      }

      case MemStore::PTR_VAL:
        // ptr -> int: type punning is poison
        if (type == DATA_INT) {
          for (unsigned i = 0; i < bytes; i += bytes_per_load) {
            store(i, poison_byte, bits_program_pointer);
          }
        } else {
          store_ptr(st.value);
        }
        break;

      case MemStore::CONST: {
        // allow zero -> null type punning
        if (type == DATA_PTR) {
          store_ptr({ Pointer::mkNullPointer(*this).release(),
                      combine_np(st.value.non_poison, st.value.value == 0) });
          break;
        }

        auto elem = st.value;
        for (unsigned i = 1; i < bytes_per_load; ++i) {
          elem = elem.concat(st.value);
        }
        for (unsigned i = 0; i < bytes; i += bytes_per_load) {
          store(i, elem, 0);
        }
        break;
      }

      case MemStore::COPY: {
        auto &v2 = vals.at({st.next, &*st.ptr_src, &st.src_alias});
        for (unsigned i = 0; i < bytes; i += bytes_per_load) {
          store(i, v2[i/bytes_per_load], 0);
        }
        break;
      }

      case MemStore::FN: {
        assert(!st.size);
        auto range = expr::mkUInt(0, Byte::bitsByte());
        for (unsigned i = 0; i < bytes; i += bytes_per_load) {
          StateValue widesv;
          for (unsigned j = 0; j < bytes_per_load; j += bits_byte/8) {
            auto ptr_uf = (ptr + i).shortPtr(st.isInitBlock());
            Byte byte(*this, expr::mkUF(st.uf_name, { ptr_uf }, range));
            StateValue sv;
            if (type == DATA_INT) {
              sv.value      = byte.nonptrValue();
              sv.non_poison = combine_np(byte.nonptrNonpoison(), !byte.isPtr());
            } else {
              assert(type == DATA_PTR);
              sv.value      = expr::mkIf(byte.isPtr(),
                                         byte.ptrValue(),
                                         Pointer::mkNullPointer(*this)());
              sv.non_poison = expr::mkIf(byte.isPtr(),
                                         byte.ptrNonpoison() &&
                                           byte.ptrByteoffset() == i + j,
                                         // allow zero -> null type punning
                                         byte.nonptrNonpoison() == 0 &&
                                           byte.nonptrValue() == 0);

              auto npbits = bytes_per_load * bits_poison_per_byte;
              sv.non_poison = expr::mkIf(sv.non_poison, expr::mkUInt(0, npbits),
                                         expr::mkInt(-1, npbits));
            }
            widesv = j == 0 ? move(sv) : widesv.concat(sv);
          }
          if (num_loads > 1 && type == DATA_PTR)
            widesv.value = widesv.value.concat(expr::mkUInt(i, 3));

          // function call havoc
          if (st.ptr) {
            assert(st.next);
            widesv = StateValue::mkIf(ptr.getBid() == st.ptr->getBid(), widesv,
                                      (*v1)[i / bytes_per_load]);
          } else { // initial memory value
            assert(!st.next);
            assert(st.alias.numMayAlias(true) == 0);
            widesv = StateValue::mkIf(ptr.isLocal(), poison_byte, widesv);
          }
          val.emplace_back(move(widesv));
        }
        break;
      }

      case MemStore::COND: {
        assert(st.size && st.els);
        auto &v2 = vals.at({st.els, &ptr, &alias});
        for (unsigned i = 0; i < num_loads; ++i) {
          val.emplace_back(StateValue::mkIf(*st.size, (*v1)[i], v2[i]));
        }
        break;
      }
    }
  } while (!todo.empty());

  auto &val = vals.at({ store_seq_head, &ptr, &alias });
  if (num_loads == 1)
    return val[0];

  if (type == DATA_INT) {
    auto ret = move(val[little_endian ? num_loads-1 : 0]);
    for (unsigned i = 1; i < num_loads; ++i) {
      ret = ret.concat(val[little_endian ? num_loads-1 - i : i]);
    }
    assert(!ret.isValid() || ret.bits() == bytes * 8);
    return ret;
  }

  assert(type == DATA_PTR);
  auto bits = Pointer::totalBits();
  Pointer ret_ptr(*this, val[0].value.extract(bits+2, 3));
  expr np = true;
  for (unsigned i = 0; i < bytes; i += bytes_per_load) {
    np &= val[i].non_poison;
    np &= val[i].value.extract(bits+2, 3) == ret_ptr();
    np &= val[i].value.extract(2, 0) == i;
  }
  return { ret_ptr.release(), move(np) };
}

void Memory::store(optional<Pointer> ptr, const expr *bytes, unsigned align,
                   MemStore &&data) {
  if (data.type == MemStore::PTR_VAL && !data.value.non_poison.isFalse())
    escapeLocalPtr(data.value.value);

  uint64_t st_size = 1;
  if (bytes) {
    bytes->isUInt(st_size);
    data.size = *bytes;
    if (st_size == 0)
      return;
  }

  if (ptr) {
    data.alias = computeAliasing(*ptr, st_size, align, true);
    data.ptr.emplace(move(*ptr));
    if (data.alias.numMayAlias(false) == 0 &&
        data.alias.numMayAlias(true) == 0)
      return;
  }

  data.align = align;
  data.next = store_seq_head;
  store_seq_head = &*mem_store_holder.emplace(move(data)).first;
}

void Memory::store(optional<Pointer> ptr, unsigned bytes, unsigned align,
                   MemStore &&data) {
  if (bytes != 0) {
    auto sz = expr::mkUInt(bytes, bits_size_t);
    store(move(ptr), &sz, align, move(data));
  }
}

static bool memory_unused() {
  return num_locals_src == 0 && num_locals_tgt == 0 && num_nonlocals == 0;
}

static expr mk_liveness_array() {
  if (!num_nonlocals)
    return {};

  // consider all non_locals are initially alive
  // block size can still be 0 to invalidate accesses
  return expr::mkInt(-1, num_nonlocals);
}

void Memory::mk_init_mem_val_axioms(const char *uf_name, bool allow_local,
                                    bool short_bid) {
  if (!does_ptr_mem_access)
    return;

  expr ptr
    = expr::mkFreshVar("#ptr",
                       expr::mkUInt(0, Pointer::totalBitsShort(short_bid)));
  Byte byte(*this,
            expr::mkUF(uf_name, {ptr}, expr::mkUInt(0, Byte::bitsByte())));

  Pointer loadedptr = byte.ptr();
  expr bid = loadedptr.getShortBid();
  expr islocal = loadedptr.isLocal(false);
  expr constr = bid.ule(numNonlocals()-1);

  if (allow_local && escaped_local_blks.numMayAlias(true) > 0) {
    expr local = escaped_local_blks.mayAlias(true, bid);
    constr = expr::mkIf(islocal, local, constr);
  } else {
    constr = !islocal && constr;
  }

  state->addAxiom(
    expr::mkForAll({ ptr },
      byte.isPtr().implies(constr && !loadedptr.isNocapture(false))));
}

Memory::Memory(State &state) : state(&state), escaped_local_blks(*this) {
  if (memory_unused())
    return;

  if (numNonlocals() > 0) {
    MemStore st(*this, "init_mem");
    st.alias.setMayAliasUpTo(false, num_nonlocals_src - 1,
                             has_null_block + num_consts_src);
    store(nullopt, nullptr, 1u << 31, move(st));

    non_local_block_liveness = mk_liveness_array();

    // Non-local blocks cannot initially contain pointers to local blocks
    // and no-capture pointers.
    mk_init_mem_val_axioms("init_mem", false, true);
  }

  if (numLocals() > 0) {
    // all local blocks as automatically initialized as non-pointer poison value
    // This is okay because loading a pointer as non-pointer is also poison.

    // all local blocks are dead in the beginning
    local_block_liveness = expr::mkUInt(0, numLocals());
  }

  // Initialize a memory block for null pointer.
  if (has_null_block)
    alloc(expr::mkUInt(0, bits_size_t), bits_byte / 8, GLOBAL, false, false, 0);

  assert(bits_for_offset <= bits_size_t);
}

void Memory::mkAxioms(const Memory &tgt) const {
  assert(state->isSource() && !tgt.state->isSource());
  if (memory_unused())
    return;

  // transformation can increase alignment
  unsigned align = ilog2(heap_block_alignment);
  for (unsigned bid = has_null_block; bid < num_nonlocals; ++bid) {
    Pointer p(*this, bid, false);
    Pointer q(tgt, bid, false);
    auto p_align = p.blockAlignment();
    auto q_align = q.blockAlignment();
    state->addAxiom(
      p.isHeapAllocated().implies(p_align == align && q_align == align));
    if (!p_align.isConst() || !q_align.isConst())
      state->addAxiom(p_align.ule(q_align));
  }

  if (!observesAddresses())
    return;

  if (has_null_block)
    state->addAxiom(Pointer::mkNullPointer(*this).getAddress(false) == 0);

  // Non-local blocks are disjoint.
  // Ignore null pointer block
  for (unsigned bid = has_null_block; bid < num_nonlocals; ++bid) {
    Pointer p1(*this, bid, false);
    auto addr = p1.getAddress();
    auto sz = p1.blockSize();

    state->addAxiom(addr != 0);

    // Ensure block doesn't spill to local memory
    auto bit = bits_size_t - 1;
    expr disj = (addr + sz).extract(bit, bit) == 0;

    // disjointness constraint
    for (unsigned bid2 = bid + 1; bid2 < num_nonlocals; ++bid2) {
      Pointer p2(*this, bid2, false);
      disj &= p2.isBlockAlive()
                .implies(disjoint(addr, sz, p2.getAddress(), p2.blockSize()));
    }
    state->addAxiom(p1.isBlockAlive().implies(disj));
  }
}

void Memory::cleanGlobals() {
  mem_store_holder.clear();
}

void Memory::resetGlobals() {
  Pointer::resetGlobals();
  next_global_bid = has_null_block;
  next_local_bid = 0;
  next_fn_memblock = 0;
}

void Memory::syncWithSrc(const Memory &src) {
  assert(src.state->isSource() && !state->isSource());
  Pointer::resetGlobals();
  next_local_bid = 0;
  // The bid of tgt global starts with num_nonlocals_src
  next_global_bid = num_nonlocals_src;
}

void Memory::markByVal(unsigned bid) {
  assert(bid < has_null_block + num_globals_src);
  byval_blks.emplace_back(bid);
}

expr Memory::mkInput(const char *name, const ParamAttrs &attrs) {
  Pointer p(*this, name, false, false, false, attrs);
  auto bid = p.getShortBid();

  state->addAxiom(bid.ule(num_nonlocals_src-1));

  if (!byval_blks.empty()) {
    AliasSet alias(*this);
    alias.setFullAlias(false);

    // FIXME: doesn't take future markByVal() into account
    for (auto byval_bid : byval_blks) {
      state->addAxiom(bid != byval_bid);
      alias.setNoAlias(false, byval_bid);
    }
    ptr_alias.emplace(p.getBid(), move(alias));
  }

  return p.release();
}

pair<expr, expr> Memory::mkUndefInput(const ParamAttrs &attrs) const {
  bool nonnull = attrs.has(ParamAttrs::NonNull);
  unsigned log_offset = ilog2_ceil(bits_for_offset, false);
  unsigned bits_undef = bits_for_offset + nonnull * log_offset;
  expr undef = expr::mkFreshVar("undef", expr::mkUInt(0, bits_undef));
  expr offset = undef;

  if (nonnull) {
    expr var = undef.extract(log_offset - 1, 0);
    expr one = expr::mkUInt(1, bits_for_offset);
    expr shl = expr::mkIf(var.ugt(bits_for_offset-1),
                          one,
                          one << var.zextOrTrunc(bits_for_offset));
    offset = undef.extract(bits_undef - 1, log_offset) | shl;
  }
  Pointer p(*this, expr::mkUInt(0, bits_for_bid), offset, attrs);
  return { p.release(), move(undef) };
}

expr Memory::PtrInput::operator==(const PtrInput &rhs) const {
  if (byval != rhs.byval || nocapture != rhs.nocapture)
    return false;
  return val == rhs.val;
}

expr Memory::mkFnRet(const char *name, const vector<PtrInput> &ptr_inputs) {
  bool has_local = escaped_local_blks.numMayAlias(true);

  unsigned bits_bid = has_local ? bits_for_bid : Pointer::bitsShortBid();
  expr var
    = expr::mkFreshVar(name, expr::mkUInt(0, bits_bid + bits_for_offset));
  auto p_bid = var.extract(bits_bid + bits_for_offset - 1, bits_for_offset);
  if (!has_local && Pointer::hasLocalBit())
    p_bid = expr::mkUInt(0, 1).concat(p_bid);
  Pointer p(*this, p_bid, var.extract(bits_for_offset-1, 0));

  auto bid = p.getShortBid();
  expr local = escaped_local_blks.mayAlias(true, bid);

  expr nonlocal = bid.ule(numNonlocals());
  auto alias = escaped_local_blks;
  alias.setFullAlias(false);

  for (auto byval_bid : byval_blks) {
    nonlocal &= bid != byval_bid;
    alias.setNoAlias(false, byval_bid);
  }
  ptr_alias.emplace(p.getBid(), move(alias));

  expr input = false;
  for (auto &ptr_in : ptr_inputs) {
    input |= ptr_in.val.non_poison &&
             p.getBid() == Pointer(*this, ptr_in.val.value).getBid();
    }

  state->addAxiom(input || expr::mkIf(p.isLocal(), local, nonlocal));
  return p.release();
}

Memory::CallState Memory::CallState::mkIf(const expr &cond,
                                          const CallState &then,
                                          const CallState &els) {
  CallState ret;
#if 0
FIXME
  for (unsigned i = 0, e = then.non_local_block_val.size(); i != e; ++i) {
    ret.non_local_block_val.emplace_back(
      expr::mkIf(cond, then.non_local_block_val[i],
                 els.non_local_block_val[i]));
  }
  ret.non_local_block_liveness
    = expr::mkIf(cond, then.non_local_block_liveness,
                 els.non_local_block_liveness);
#endif
  return ret;
}

expr Memory::CallState::operator==(const CallState &rhs) const {
  if (empty != rhs.empty)
    return false;
  if (empty)
    return true;

  expr ret(true);
#if 0
  for (unsigned i = 0, e = non_local_block_val.size(); i != e; ++i) {
    ret &= non_local_block_val[i] == rhs.non_local_block_val[i];
  }
  if (non_local_liveness_var.isValid() && st.non_local_liveness_var.isValid())
    ret &= non_local_liveness_var == st.non_local_liveness_var;
#endif
  return ret;
}

Memory::CallState
Memory::mkCallState(const string &fnname, const vector<PtrInput> *ptr_inputs,
                    bool nofree) {
  CallState st;
  st.empty = false;

  {
    st.uf_name = fnname + "#mem#" + to_string(next_fn_memblock++);
    AliasSet full_alias(*this);

    if (ptr_inputs) {
      for (auto &ptr_in : *ptr_inputs) {
        if (!ptr_in.val.non_poison.isFalse()) {
          Pointer ptr(*this, ptr_in.val.value);
          MemStore mem(*this, st.uf_name.c_str());
          mem.alias = computeAliasing(ptr, 1, 1, true);
          full_alias.unionWith(mem.alias);
          store(ptr, nullptr, 1u << 31, move(mem));
        }
      }
    } else {
      MemStore mem(*this, st.uf_name.c_str());
      mem.alias = escaped_local_blks;
      mem.alias.setMayAliasUpTo(false, numNonlocals() - 1,
                                has_null_block + num_consts_src);
      full_alias = mem.alias;
      store(nullopt, nullptr, 1u << 31, move(mem));
    }
    mk_init_mem_val_axioms(st.uf_name.c_str(), true, false);
  }
  st.store_seq_head = store_seq_head;

  if (num_nonlocals_src && !nofree) {
    expr one  = expr::mkUInt(1, num_nonlocals);
    expr zero = expr::mkUInt(0, num_nonlocals);
    expr mask = has_null_block ? one : zero;
    for (unsigned bid = has_null_block; bid < num_nonlocals; ++bid) {
      expr may_free = true;
      if (ptr_inputs) {
        may_free = false;
        for (auto &ptr_in : *ptr_inputs) {
          if (!ptr_in.byval && bid < num_nonlocals_src)
            may_free |= Pointer(*this, ptr_in.val.value).getBid() == bid;
        }
      }
      expr heap = Pointer(*this, bid, false).isHeapAllocated();
      mask = mask | expr::mkIf(heap && may_free,
                               zero,
                               one << expr::mkUInt(bid, num_nonlocals));
    }

    if (mask.isAllOnes()) {
      st.non_local_block_liveness = non_local_block_liveness;
    } else {
      st.non_local_liveness_var
        = expr::mkFreshVar("blk_liveness", mk_liveness_array());
      // functions can free an object, but cannot bring a dead one back to live
      st.non_local_block_liveness
        = non_local_block_liveness & (st.non_local_liveness_var | mask);
    }
  } else {
    st.non_local_block_liveness = non_local_block_liveness;
  }

  if (numLocals() && !nofree) {
    // TODO: local liveness
  }

  return st;
}

void Memory::setState(const Memory::CallState &st) {
  store_seq_head = st.store_seq_head;
  non_local_block_liveness = st.non_local_block_liveness;
  /* TODO: needs program alignment when reusing fn calls across src/tgt?
  if (st.local_liveness_var.isValid())
    local_block_liveness = local_block_liveness & st.local_block_liveness;
  */
}

static expr disjoint_local_blocks(const Memory &m, const expr &addr,
                                  const expr &sz, FunctionExpr &blk_addr) {
  expr disj = true;

  // Disjointness of block's address range with other local blocks
  auto one = expr::mkUInt(1, 1);
  auto zero = expr::mkUInt(0, bits_for_offset);
  for (auto &[sbid, addr0] : blk_addr) {
    Pointer p2(m, prepend_if(one, expr(sbid), Pointer::hasLocalBit()), zero);
    disj &= p2.isBlockAlive()
              .implies(disjoint(addr, sz, p2.getAddress(), p2.blockSize()));
  }
  return disj;
}

pair<expr, expr>
Memory::alloc(const expr &size, unsigned align, BlockKind blockKind,
              const expr &precond, const expr &nonnull,
              optional<unsigned> bidopt, unsigned *bid_out) {
  assert(!memory_unused());

  // Produce a local block if blockKind is heap or stack.
  bool is_local = blockKind != GLOBAL && blockKind != CONSTGLOBAL;

  auto &last_bid = is_local ? next_local_bid : next_global_bid;
  unsigned bid = bidopt ? *bidopt : last_bid;
  assert((is_local && bid < numLocals()) ||
         (!is_local && bid < numNonlocals()));
  if (!bidopt)
    ++last_bid;
  assert(bid < last_bid);

  if (bid_out)
    *bid_out = bid;

  expr size_zext = size.zextOrTrunc(bits_size_t);
  expr nooverflow = size_zext.extract(bits_size_t - 1, bits_size_t - 1) == 0;

  expr allocated = precond && nooverflow;
  state->addPre(nonnull.implies(allocated));
  allocated |= nonnull;

  Pointer p(*this, bid, is_local);
  auto short_bid = p.getShortBid();
  // TODO: If address space is not 0, the address can be 0.
  // TODO: add support for C++ allocs
  unsigned alloc_ty = 0;
  switch (blockKind) {
  case MALLOC:      alloc_ty = Pointer::MALLOC; break;
  case CXX_NEW:     alloc_ty = Pointer::CXX_NEW; break;
  case STACK:       alloc_ty = Pointer::STACK; break;
  case GLOBAL:
  case CONSTGLOBAL: alloc_ty = Pointer::GLOBAL; break;
  }

  assert(align != 0);
  auto align_bits = ilog2(align);

  if (is_local) {
    if (observesAddresses()) {
      // MSB of local block area's address is 1.
      auto addr_var
        = expr::mkFreshVar("local_addr",
                           expr::mkUInt(0, bits_size_t - align_bits - 1));
      state->addQuantVar(addr_var);

      expr blk_addr = addr_var.concat_zeros(align_bits);
      auto full_addr = expr::mkUInt(1, 1).concat(blk_addr);

      // addr + size does not overflow
      if (!size.uge(align).isFalse())
        state->addPre(allocated.implies(full_addr.add_no_uoverflow(size_zext)));

      // Disjointness of block's address range with other local blocks
      state->addPre(
        allocated.implies(disjoint_local_blocks(*this, full_addr, size_zext,
                                                local_blk_addr)));

      local_blk_addr.add(short_bid, move(blk_addr));
    }
  } else {
    state->addAxiom(p.blockSize() == size_zext);
    state->addAxiom(p.isBlockAligned(align, true));
    if (!has_null_block || bid != 0) {
      state->addAxiom(p.getAllocType() == alloc_ty);
    }

    if (align_bits && observesAddresses())
      state->addAxiom(p.getAddress().extract(align_bits - 1, 0) == 0);

    bool cond = (has_null_block && bid == 0) ||
                (bid >= has_null_block + num_consts_src &&
                 bid < num_nonlocals_src + num_extra_nonconst_tgt);
    if (blockKind == CONSTGLOBAL) assert(!cond); else assert(cond);
    (void)cond;
  }

  store_bv(p, allocated, local_block_liveness, non_local_block_liveness);
  (is_local ? local_blk_size : non_local_blk_size)
    .add(short_bid, size_zext.trunc(bits_size_t - 1));
  (is_local ? local_blk_align : non_local_blk_align)
    .add(short_bid, expr::mkUInt(align_bits, 6));
  (is_local ? local_blk_kind : non_local_blk_kind)
    .add(short_bid, expr::mkUInt(alloc_ty, 2));

  if (nonnull.isTrue())
    return { p.release(), move(allocated) };

  expr nondet_nonnull = expr::mkFreshVar("#alloc_nondet_nonnull", true);
  state->addQuantVar(nondet_nonnull);
  allocated = precond && (nonnull || (nooverflow && nondet_nonnull));
  return { expr::mkIf(allocated, p(), Pointer::mkNullPointer(*this)()),
           move(allocated) };
}

void Memory::startLifetime(const expr &ptr_local) {
  assert(!memory_unused());
  Pointer p(*this, ptr_local);
  state->addUB(p.isLocal());

  if (observesAddresses())
    state->addPre(disjoint_local_blocks(*this, p.getAddress(), p.blockSize(),
                  local_blk_addr));

  store_bv(p, true, local_block_liveness, non_local_block_liveness, true);
}

void Memory::free(const expr &ptr, bool unconstrained) {
  assert(!memory_unused() && (has_free || has_dead_allocas));
  Pointer p(*this, ptr);
  if (!unconstrained)
    state->addUB(p.isNull() || (p.getOffset() == 0 &&
                                p.isBlockAlive() &&
                                p.getAllocType() == Pointer::MALLOC));
  store_bv(p, false, local_block_liveness, non_local_block_liveness);
}

unsigned Memory::getStoreByteSize(const Type &ty) {
  assert(bits_program_pointer != 0);

  if (ty.isPtrType())
    return divide_up(bits_program_pointer, 8);

  auto aty = ty.getAsAggregateType();
  if (aty && !isNonPtrVector(ty)) {
    unsigned sz = 0;
    for (unsigned i = 0, e = aty->numElementsConst(); i < e; ++i)
      sz += getStoreByteSize(aty->getChild(i));
    return sz;
  }
  return divide_up(ty.bits(), 8);
}

void Memory::store(const Pointer &ptr, unsigned offset, StateValue &&v,
                   const Type &type, unsigned align,
                   const set<expr> &undef_vars) {
  auto aty = type.getAsAggregateType();
  if (aty && !isNonPtrVector(type)) {
    unsigned byteofs = 0;
    for (unsigned i = 0, e = aty->numElementsConst(); i < e; ++i) {
      auto &child = aty->getChild(i);
      if (child.bits() == 0)
        continue;
      store(ptr, offset + byteofs, aty->extract(v, i), child,
            gcd(align, offset + byteofs), undef_vars);
      byteofs += getStoreByteSize(child);
    }
    assert(byteofs == getStoreByteSize(type));

  } else if (type.isPtrType()) {
    store(ptr + offset, bits_program_pointer / 8, align,
          MemStore(MemStore::PTR_VAL, move(v), undef_vars));

  } else {
    unsigned bits = round_up(v.bits(), 8);
    auto val = v.zextOrTrunc(bits);
    store(ptr + offset, bits / 8, align,
          MemStore(MemStore::INT_VAL, type.toInt(*state, move(val)),
                   undef_vars));
  }
}

void Memory::store(const expr &p, const StateValue &v, const Type &type,
                   unsigned align, const set<expr> &undef_vars) {
  assert(!memory_unused());
  Pointer ptr(*this, p);

  // initializer stores are ok by construction
  if (!state->isInitializationPhase())
    state->addUB(ptr.isDereferenceable(getStoreByteSize(type), align, true));

  store(ptr, 0, StateValue(v), type, align, undef_vars);
}

StateValue Memory::load(const Pointer &ptr, const Type &type, set<expr> &undef,
                        unsigned align) {
  unsigned bytecount = getStoreByteSize(type);

  auto aty = type.getAsAggregateType();
  if (aty && !isNonPtrVector(type)) {
    vector<StateValue> member_vals;
    unsigned byteofs = 0;
    for (unsigned i = 0, e = aty->numElementsConst(); i < e; ++i) {
      // Padding is filled with poison.
      if (aty->isPadding(i)) {
        byteofs += getStoreByteSize(aty->getChild(i));
        continue;
      }

      auto ptr_i = ptr + byteofs;
      auto align_i = gcd(align, byteofs % align);
      member_vals.emplace_back(load(ptr_i, aty->getChild(i), undef, align_i));
      byteofs += getStoreByteSize(aty->getChild(i));
    }
    assert(byteofs == bytecount);
    return aty->aggregateVals(member_vals);
  }

  bool is_ptr = type.isPtrType();
  return type.fromInt(load(ptr, bytecount, undef, align,
                               is_ptr ? DATA_PTR : DATA_INT)
                        .trunc(type.bits(), type.np_bits()));
}

pair<StateValue, AndExpr>
Memory::load(const expr &p, const Type &type, unsigned align) {
  assert(!memory_unused());

  Pointer ptr(*this, p);
  auto ubs = ptr.isDereferenceable(getStoreByteSize(type), align, false);
  set<expr> undef_vars;
  auto ret = load(ptr, type, undef_vars, align);
  return { state->rewriteUndef(move(ret), undef_vars), move(ubs) };
}

Byte Memory::load(const Pointer &p, set<expr> &undef, unsigned align) {
  //return move(load(p, bits_byte / 8, undef, align)[0]);
  // TODO
  return { *this, expr() };
}

void Memory::memset(const expr &p, const StateValue &val, const expr &bytesize,
                    unsigned align, const set<expr> &undef_vars,
                    bool deref_check) {
  assert(!memory_unused());
  assert(!val.isValid() || val.bits() == 8);

  Pointer ptr(*this, p);
  if (deref_check)
    state->addUB(ptr.isDereferenceable(bytesize, align, true));

  store(ptr, &bytesize, align,
        MemStore(MemStore::CONST, StateValue(val), undef_vars));
}

void Memory::memcpy(const expr &d, const expr &s, const expr &bytesize,
                    unsigned align_dst, unsigned align_src, bool is_move) {
  assert(!memory_unused());

  Pointer dst(*this, d), src(*this, s);
  state->addUB(dst.isDereferenceable(bytesize, align_dst, true));
  state->addUB(src.isDereferenceable(bytesize, align_src, false));
  if (!is_move)
    src.isDisjointOrEqual(bytesize, dst, bytesize);

  // copy to itself
  if ((src == dst).isTrue())
    return;

  store(dst, &bytesize, align_dst, MemStore(src, &bytesize, align_src));
}

void Memory::copy(const Pointer &src, const Pointer &dst) {
  store(dst, nullptr, 1, MemStore(src, nullptr, 1));
}

expr Memory::ptr2int(const expr &ptr) const {
  assert(!memory_unused());
  return Pointer(*this, ptr).getAddress();
}

expr Memory::int2ptr(const expr &val) const {
  assert(!memory_unused());
  // TODO
  return {};
}

expr Memory::blockValRefined(const Memory &other, unsigned bid, bool local,
                             const expr &offset, set<expr> &undef) const {
  assert(!local);
  // TODO
  //auto &mem1 = non_local_block_val[bid];
  //auto &mem2 = other.non_local_block_val[bid].val;

  //Byte val(*this, mem1.val.load(offset));
  //Byte val2(other, mem2.load(offset));
  Byte val(*this, expr()), val2(*this, expr());

  if (val.eq(val2))
    return true;

  //undef.insert(mem1.undef.begin(), mem1.undef.end());

  // refinement if offset had non-ptr value
  expr v1 = val.nonptrValue();
  expr v2 = val2.nonptrValue();
  expr np1 = val.nonptrNonpoison();
  expr np2 = val2.nonptrNonpoison();

  expr int_cnstr;
  if (bits_poison_per_byte == bits_byte) {
    int_cnstr = (np2 | np1) == np1 && (v1 | np1) == (v2 | np1);
  }
  else if (bits_poison_per_byte > 1) {
    assert((bits_byte % bits_poison_per_byte) == 0);
    unsigned bits_val = bits_byte / bits_poison_per_byte;
    int_cnstr = true;
    for (unsigned i = 0; i < bits_poison_per_byte; ++i) {
      expr ev1 = v1.extract((i+1) * bits_val - 1, i * bits_val);
      expr ev2 = v2.extract((i+1) * bits_val - 1, i * bits_val);
      expr enp1 = np1.extract(i, i);
      expr enp2 = np2.extract(i, i);
      int_cnstr
        &= enp1 == 1 || ((enp1.eq(enp2) ? true : enp2 == 0) && ev1 == ev2);
    }
  } else {
    int_cnstr = np1 == 1 || ((np1.eq(np2) ? true : np2 == 0) && v1 == v2);
  }

  // fast path: if we didn't do any ptr store, then all ptrs in memory were
  // already there and don't need checking
  expr is_ptr = val.isPtr();
  expr is_ptr2 = val2.isPtr();
  expr ptr_cnstr;
  if (!does_ptr_store || is_ptr.isFalse() || is_ptr2.isFalse()) {
    ptr_cnstr = val == val2;
  } else {
    ptr_cnstr = !val.ptrNonpoison() ||
                  (val2.ptrNonpoison() &&
                   val.ptrByteoffset() == val2.ptrByteoffset() &&
                   val.ptr().refined(val2.ptr()));
  }
  return expr::mkIf(is_ptr == is_ptr2,
                    expr::mkIf(is_ptr, ptr_cnstr, int_cnstr),
                    // allow null ptr <-> zero
                    val.isPoison() ||
                      (val.isZero() && !val2.isPoison() && val2.isZero()));
}

expr Memory::blockRefined(const Pointer &src, const Pointer &tgt, unsigned bid,
                          set<expr> &undef) const {
  unsigned bytes_per_byte = bits_byte / 8;

  expr blk_size = src.blockSize();
  expr ptr_offset = src.getShortOffset();
  expr val_refines;

  uint64_t bytes;
  if (blk_size.isUInt(bytes) && (bytes / bytes_per_byte) <= 8) {
    val_refines = true;
    for (unsigned off = 0; off < (bytes / bytes_per_byte); ++off) {
      expr off_expr = expr::mkUInt(off, Pointer::bitsShortOffset());
      val_refines
        &= (ptr_offset == off_expr).implies(
             blockValRefined(tgt.getMemory(), bid, false, off_expr, undef));
    }
  } else {
    val_refines
      = src.getOffsetSizet().ult(blk_size).implies(
          blockValRefined(tgt.getMemory(), bid, false, ptr_offset, undef));
  }

  assert(src.isWritable().eq(tgt.isWritable()));

  expr aligned(true);
  expr src_align = src.blockAlignment();
  expr tgt_align = tgt.blockAlignment();
  // if they are both non-const, then the condition holds per the precondition
  if (src_align.isConst() || tgt_align.isConst())
    aligned = src_align.ule(tgt_align);

  expr alive = src.isBlockAlive();
  return alive == tgt.isBlockAlive() &&
         blk_size == tgt.blockSize() &&
         src.getAllocType() == tgt.getAllocType() &&
         aligned &&
         alive.implies(val_refines);
}

tuple<expr, Pointer, set<expr>>
Memory::refined(const Memory &other, bool fncall,
                const vector<PtrInput> *set_ptrs,
                const vector<PtrInput> *set_ptrs_other) const {
  // TODO: needs to consider local escaped blocks
  if (num_nonlocals <= has_null_block)
    return { true, Pointer(*this, expr()), {} };

  assert(!memory_unused());
  assert(!set_ptrs || fncall);
  assert(((set_ptrs != 0) ^ (set_ptrs_other != 0)) == 0);

  Pointer ptr(*this, "#idx_refinement", false);
  expr ptr_bid = ptr.getBid();
  expr offset = ptr.getOffset();
  expr ret(true);
  set<expr> undef_vars;

  auto relevant = [&](const Memory &m, const MemStore *st) {
    if (!st->ptr)
      return false;

    if (set_ptrs) {
      auto bid = st->ptr->getBid();
      for (auto &p : *((&m == this) ? set_ptrs : set_ptrs_other)) {
        if (!(Pointer(m, p.val.value).getBid() == bid).isFalse())
          return true;
      }
      return false;
    } else {
      // TODO: check local escaped blocks
      return st->alias.numMayAlias(false) > 0;
    }
  };

  // 1) Check that set of tgt written locs is in set of src written locs
  // i.e., we can remove stores but can't introduce stores to new locations
  if (other.store_seq_head) {
    auto collect_stores = [&](const Memory &m) {
      // bid -> (path, offset, size)*
      map<expr, vector<tuple<expr, expr, expr>>> stores;
      vector<pair<const MemStore*, expr>> todo = { {m.store_seq_head, true} };
      do {
        auto [st, path] = todo.back();
        todo.pop_back();

        if (st->type == MemStore::COND) {
          todo.emplace_back(st->next, path && *st->size);
          todo.emplace_back(st->els,  path && !*st->size);
          continue;
        }

        if (st->type != MemStore::FN && relevant(m, st)) {
          assert(st->size);
          stores[st->ptr->getBid()]
            .emplace_back(path, st->ptr->getShortOffset(), *st->size);
        }

        if (st->next) {
          todo.emplace_back(st->next, move(path));
        }
      } while (!todo.empty());

      return stores;
    };

    // bid -> (path, offset, size)*
    auto src_stores = collect_stores(*this);
    auto tgt_stores = collect_stores(other);
    vector<tuple<expr, expr, expr>> empty_vector;

    for (auto &[bid, tgt_list] : tgt_stores) {
      auto src_I = src_stores.find(bid);
      auto &src_list = src_I == src_stores.end() ? empty_vector : src_I->second;

      for (auto &[tgt_path, tgt_offset, tgt_size] : tgt_list) {
        OrExpr src_domain;
        // fast path: stores match and tgt domain -> src domain
        for (auto &[src_path, src_offset, src_size] : src_list) {
          if (tgt_offset.eq(src_offset) && tgt_size.ule(src_size).isTrue())
            src_domain.add(src_path);
        }

        if (src_domain.contains(tgt_path))
          continue;

        // slow path
        // TODO
        cout << "[MEMREF] SLOW PATH: " << bid << " / tgt_path=" << tgt_path
             << "\nsrc_domain=" << src_domain << "\noffset=" << tgt_offset
             << " size=" << tgt_size << endl;
      }
    }
  }

  if (!store_seq_head)
    return { move(ret), move(ptr), move(undef_vars) };

  // check that written locs in src are refined by tgt
  AliasSet full_alias(*this);
  if (fncall) {

  } else {
    full_alias.setFullAlias(false);
  }
  map<tuple<const MemStore*, const Pointer*, const AliasSet*>,
      vector<StateValue>> vals;
  vector<tuple<const MemStore*, const Pointer*, const AliasSet*>> todo
    = { { store_seq_head, &ptr, &full_alias } };
  set<tuple<const MemStore*, const Pointer*, const AliasSet*>> seen;

  do {
    auto key = todo.back();
    auto &st = *get<0>(key);
    auto &ptr = *get<1>(key);
    auto &alias = *get<2>(key);

    // TODO: don't process children if store matches perfectly or full write
    bool has_all_deps = true;
    if (st.next && !vals.count({st.next, &ptr, &alias})) {
      todo.emplace_back(st.next, &ptr, &alias);
      has_all_deps = false;
    }
    if (st.els && !vals.count({st.els, &ptr, &alias})) {
      todo.emplace_back(st.els, &ptr, &alias);
      has_all_deps = false;
    }
    if (st.ptr_src && !vals.count({st.next, &*st.ptr_src, &st.src_alias})) {
      assert(st.next);
      todo.emplace_back(st.next, &*st.ptr_src, &st.src_alias);
      has_all_deps = false;
    }

    if (!has_all_deps)
      continue;
    todo.pop_back();

    auto [I, inserted] = vals.try_emplace(key);
    ////auto &val = I->second;
    if (!inserted)
      continue;

    // TODO: traverse tgt stores

  } while (!todo.empty());

#if 0
  unsigned bid = has_null_block + skip_constants * num_consts_src;
  for (; bid < num_nonlocals_src; ++bid) {
    expr bid_expr = expr::mkUInt(bid, bits_for_bid);
    Pointer p(*this, bid_expr, offset);
    Pointer q(other, p());
    if (p.isByval().isTrue() && q.isByval().isTrue())
      continue;
    ret &= (ptr_bid == bid_expr).implies(blockRefined(p, q, bid, undef_vars));
  }

  // restrict refinement check to set of request blocks
  if (set_ptrs) {
    expr c(false);
    for (auto &itm: *set_ptrs) {
      // TODO: deal with the byval arg case (itm.second)
      auto &ptr = itm.val;
      c |= ptr.non_poison && Pointer(*this, ptr.value).getBid() == ptr_bid;
    }
    ret = c.implies(ret);
  }
#endif

  return { move(ret), move(ptr), move(undef_vars) };
}

expr Memory::checkNocapture() const {
  if (!does_ptr_store || !has_nocapture || !store_seq_head)
    return true;

  auto name = local_name(state, "#ptr_nocapture");
  auto ptr_var = expr::mkVar(name.c_str(), Pointer::totalBitsShort());
  Pointer ptr(*this, ptr_var.concat_zeros(bits_for_ptrattrs));

  vector<pair<const MemStore*, expr>> todo = { { store_seq_head, true } };
  map<StateValue, expr> ptr_reach;

  // traverse the mem store as a *tree* to gather block reachability
  do {
    auto &[st, cond] = todo.back();
    todo.pop_back();

    switch (st->type) {
    case MemStore::COND:
      todo.emplace_back(st->next, cond && *st->size);
      todo.emplace_back(st->els,  cond && !*st->size);
      break;

    case MemStore::PTR_VAL: {
      auto store_cond = cond && ptr == *st->ptr;
      auto [I, inserted] = ptr_reach.try_emplace(st->value, move(store_cond));
      if (!inserted)
        I->second |= store_cond;
    }
    [[fallthrough]];

    default:
      if (st->ptr) {
        //cond &= TODO;
      } else {
        assert(st->type == MemStore::FN);
        // TODO
      }
      break;
    }

    if (st->type != MemStore::COND && st->next)
      todo.emplace_back(st->next, move(cond));
  } while (!todo.empty());

  expr res(true);
  for (auto &[ptr_e, cond] : ptr_reach) {
    Pointer ptr(*this, ptr_e.value);
    res &= (ptr.isBlockAlive() && ptr_e.non_poison).implies(!ptr.isNocapture());
  }

  if (!res.isTrue())
    state->addQuantVar(ptr_var);
  return res;
}

void Memory::escapeLocalPtr(const expr &ptr) {
  if (next_local_bid == 0)
    return;

  uint64_t bid;
  for (const auto &bid_expr : extract_possible_local_bids(*this, ptr)) {
    if (bid_expr.isUInt(bid)) {
      if (bid < next_local_bid)
        escaped_local_blks.setMayAlias(true, bid);
    } else if (isInitialMemBlock(bid_expr)) {
      // initial non local block bytes don't contain local pointers.
      continue;
    } else {
      // may escape a local ptr, but we don't know which one
      escaped_local_blks.setMayAliasUpTo(true, next_local_bid-1);
      break;
    }
  }
}

Memory Memory::mkIf(const expr &cond, const Memory &then, const Memory &els) {
  assert(then.state == els.state);
  Memory ret(then);
  ret.store_seq_head
    = MemStore::mkIf(cond, then.store_seq_head, els.store_seq_head);
  ret.non_local_block_liveness = expr::mkIf(cond, then.non_local_block_liveness,
                                            els.non_local_block_liveness);
  ret.local_block_liveness     = expr::mkIf(cond, then.local_block_liveness,
                                            els.local_block_liveness);
  ret.local_blk_addr.add(els.local_blk_addr);
  ret.local_blk_size.add(els.local_blk_size);
  ret.local_blk_align.add(els.local_blk_align);
  ret.local_blk_kind.add(els.local_blk_kind);
  ret.non_local_blk_size.add(els.non_local_blk_size);
  ret.non_local_blk_align.add(els.non_local_blk_align);
  ret.non_local_blk_kind.add(els.non_local_blk_kind);
  assert(then.byval_blks == els.byval_blks);
  ret.escaped_local_blks.unionWith(els.escaped_local_blks);

  ret.ptr_alias.clear();
  for (const auto &[expr, alias] : then.ptr_alias) {
    auto I = els.ptr_alias.find(expr);
    if (I != els.ptr_alias.end())
      ret.ptr_alias.emplace(expr, alias)
         .first->second.unionWith(I->second);
  }
  return ret;
}

#define P(name, expr) do {      \
  auto v = m.eval(expr, false); \
  uint64_t n;                   \
  if (v.isUInt(n))              \
    os << "\t" name ": " << n;  \
  else if (v.isConst())         \
    os << "\t" name ": " << v;  \
  } while(0)

void Memory::print(ostream &os, const Model &m) const {
  if (memory_unused())
    return;

  auto print = [&](bool local, unsigned num_bids) {
    for (unsigned bid = 0; bid < num_bids; ++bid) {
      Pointer p(*this, bid, local);
      uint64_t n;
      ENSURE(p.getBid().isUInt(n));
      os << "Block " << n << " >";
      P("size", p.blockSize());
      P("align", expr::mkInt(1, 64) << p.blockAlignment().zextOrTrunc(64));
      P("alloc type", p.getAllocType());
      if (observesAddresses())
        P("address", p.getAddress());
      os << '\n';
    }
  };

  bool did_header = false;
  auto header = [&](const char *msg) {
    if (!did_header) {
      os << (state->isSource() ? "\nSOURCE" : "\nTARGET")
         << " MEMORY STATE\n===================\n";
    } else
      os << '\n';
    os << msg;
    did_header = true;
  };

  if (state->isSource() && num_nonlocals) {
    header("NON-LOCAL BLOCKS:\n");
    print(false, num_nonlocals);
  }

  if (numLocals()) {
    header("LOCAL BLOCKS:\n");
    print(true, numLocals());
  }
}
#undef P

#define P(msg, local, nonlocal)                                                \
  os << msg "\n";                                                              \
  if (m.numLocals() > 0) os << "Local: " << m.local.simplify() << '\n';        \
  if (m.numNonlocals() > 0)                                                    \
    os << "Non-local: " << m.nonlocal.simplify() << "\n\n"

ostream& operator<<(ostream &os, const Memory &m) {
  if (memory_unused())
    return os;
  os << "\n\nMEMORY\n======\n";
  if (m.store_seq_head) {
    os << "STORE SEQUENCE:\n";
    m.store_seq_head->print(os);
  }
  P("BLOCK LIVENESS:", local_block_liveness, non_local_block_liveness);
  P("BLOCK SIZE:", local_blk_size, non_local_blk_size);
  P("BLOCK ALIGN:", local_blk_align, non_local_blk_align);
  P("BLOCK KIND:", local_blk_kind, non_local_blk_kind);
  if (m.escaped_local_blks.numMayAlias(true) > 0) {
    m.escaped_local_blks.print(os << "ESCAPED LOCAL BLOCKS: ");
  }
  if (!m.local_blk_addr.empty()) {
    os << "\nLOCAL BLOCK ADDR: " << m.local_blk_addr << '\n';
  }
  if (!m.ptr_alias.empty()) {
    os << "\nALIAS SETS:\n";
    for (auto &[bid, alias] : m.ptr_alias) {
      os << bid << ": ";
      alias.print(os);
      os << '\n';
    }
  }
  return os;
}

}
