// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "ir/state.h"
#include "ir/function.h"
#include "smt/smt.h"
#include "util/errors.h"
#include <cassert>
#include <sstream>
#include <string_view>

using namespace smt;
using namespace util;
using namespace std;

namespace IR {

State::State(const Function &f, bool source)
  : f(f), source(source), memory(*this),
    return_val(f.getType().getDummyValue(false)), return_memory(memory) {}

void State::resetGlobals() {
  Memory::resetGlobalData();
}

const StateValue& State::exec(const Value &v) {
  assert(undef_vars.empty());
  auto val = v.toSMT(*this);
  ENSURE(values_map.try_emplace(&v, (unsigned)values.size()).second);
  values.emplace_back(&v, ValTy(move(val), move(undef_vars)), false);

  // cleanup potentially used temporary values due to undef rewriting
  while (i_tmp_values > 0) {
    tmp_values[--i_tmp_values] = StateValue();
  }

  return get<1>(values.back()).first;
}

const StateValue& State::operator[](const Value &val) {
  auto &[var, val_uvars, used] = values[values_map.at(&val)];
  auto &[sval, uvars] = val_uvars;
  (void)var;

  if (uvars.empty() || !used || disable_undef_rewrite) {
    used = true;
    undef_vars.insert(uvars.begin(), uvars.end());
    return sval;
  }

  vector<pair<expr, expr>> repls;
  for (auto &u : uvars) {
    repls.emplace_back(u, expr::mkFreshVar("undef", u));
  }

  if (hit_half_memory_limit())
    throw AliveException("Out of memory; skipping function.", false);

  auto sval_new = sval.subst(repls);
  if (sval_new.eq(sval)) {
    uvars.clear();
    return sval;
  }

  for (auto &p : repls) {
    undef_vars.emplace(move(p.second));
  }

  return tmp_values[i_tmp_values++] = move(sval_new);
}

const State::ValTy& State::at(const Value &val) const {
  return get<1>(values[values_map.at(&val)]);
}

const expr* State::jumpCondFrom(const BasicBlock &bb) const {
  auto &pres = predecessor_data.at(current_bb);
  auto I = pres.find(&bb);
  return I == pres.end() ? nullptr : &I->second.first.first;
}

bool State::startBB(const BasicBlock &bb) {
  assert(undef_vars.empty());
  ENSURE(seen_bbs.emplace(&bb).second);
  current_bb = &bb;

  if (&f.getFirstBB() == &bb) {
    domain.first = true;
    return true;
  }

  auto I = predecessor_data.find(&bb);
  if (I == predecessor_data.end())
    return false;

  domain.first = false;
  domain.second.clear();

  DisjointExpr<Memory> in_memory;

  for (auto &[src, data] : I->second) {
    (void)src;
    auto &[dom, mem] = data;
    auto &[cond, vars] = dom;
    domain.first |= cond;
    domain.second.insert(vars.begin(), vars.end());
    in_memory.add(mem, cond);
  }

  if (domain.first.isFalse())
    return false;

  memory = *in_memory();

  return true;
}

void State::addJump(const BasicBlock &dst, expr &&cond) {
  if (seen_bbs.count(&dst))
    throw AliveException("Loops are not supported yet! Skipping function.",
                         false);

  cond &= domain.first;
  auto p = predecessor_data[&dst].try_emplace(current_bb, DomainTy({}, {}),
                                              memory);
  if (!p.second) {
    p.first->second.second = Memory::mkIf(cond, memory, p.first->second.second);
    p.first->second.first.first |= move(cond);
    p.first->second.first.second.insert(undef_vars.begin(), undef_vars.end());
  } else {
    p.first->second.first.first  = move(cond);
    p.first->second.first.second = undef_vars;
  }
  p.first->second.first.second.insert(domain.second.begin(),
                                      domain.second.end());
}

void State::addJump(const BasicBlock &dst) {
  addJump(dst, true);
  domain.first = false;
}

void State::addJump(StateValue &&cond, const BasicBlock &dst) {
  addJump(dst, move(cond.value) && move(cond.non_poison));
}

void State::addCondJump(const StateValue &cond, const BasicBlock &dst_true,
                        const BasicBlock &dst_false) {
  addJump(dst_true,  cond.value == 1 && cond.non_poison);
  addJump(dst_false, cond.value == 0 && cond.non_poison);
  domain.first = false;
}

void State::addReturn(const StateValue &val) {
  return_val.add(val, domain.first);
  return_memory.add(memory, domain.first);
  return_domain.add(move(domain.first));
  return_undef_vars.insert(undef_vars.begin(), undef_vars.end());
  return_undef_vars.insert(domain.second.begin(), domain.second.end());
  undef_vars.clear();
  domain.first = false;
}

void State::addUB(expr &&ub) {
  domain.first &= move(ub);
  domain.second.insert(undef_vars.begin(), undef_vars.end());
}

void State::addUB(const expr &ub) {
  domain.first &= ub;
  domain.second.insert(undef_vars.begin(), undef_vars.end());
}

const vector<StateValue>
State::addFnCall(const string &name, vector<StateValue> &&inputs,
                 vector<StateValue> &&ptr_inputs,
                 const vector<Type*> &out_types) {
  // TODO: handle changes to memory due to fn call
  expr all_args_np(true);
  for (auto &v : inputs) {
    all_args_np &= v.non_poison;
  }
  for (auto &v : ptr_inputs) {
    all_args_np &= v.non_poison;
  }

  auto [I, inserted]
    = fn_call_data[name].try_emplace({move(inputs), move(ptr_inputs), memory});

  if (inserted) {
    vector<StateValue> values;
    string valname = name + "#val";
    string npname = name + "#np";
    for (auto t : out_types) {
      values.emplace_back(
        expr::mkFreshVar(valname.c_str(), t->getDummyValue(false).value),
        expr::mkFreshVar(npname.c_str(), false));
    }

    string ub_name = string(name) + "#ub";
    I->second = { move(values), expr::mkFreshVar(ub_name.c_str(), false) };
  }

  addUB(I->second.second);
  if (all_args_np.isTrue())
    return I->second.first;

  // if any of the arguments is poison, yield an arbitrary value, such that
  // f(poison) -> f(42) works
  vector<StateValue> ret;
  auto var_name = name + "#pval";
  for (auto &[v, np] : I->second.first) {
    auto var = expr::mkFreshVar(var_name.c_str(), v);
    ret.emplace_back(expr::mkIf(all_args_np, v, var), expr(np));
    addQuantVar(var);
  }
  return ret;
}

void State::addQuantVar(const expr &var) {
  quantified_vars.emplace(var);
}

void State::addUndefVar(expr &&var) {
  undef_vars.emplace(move(var));
}

void State::resetUndefVars() {
  quantified_vars.insert(undef_vars.begin(), undef_vars.end());
  undef_vars.clear();
}

static void collectUndefVars(State &s, set<expr> &undef_vars,
                             vector<pair<expr,expr>> &repls, const expr &val) {
  for (auto &var : val.vars()) {
    ostringstream ss;
    ss << var;
    auto name = ss.str();
    if (string_view(name).substr(0, 6) == "undef!" &&
        undef_vars.emplace(var).second) {
      auto newvar = expr::mkFreshVar("undef", var);
      repls.emplace_back(var, newvar);
      s.addUndefVar(move(newvar));
    }
  }
}

StateValue State::rewriteUndef(StateValue &&val) {
  set<expr> undef_vars;
  vector<pair<expr, expr>> repls;
  collectUndefVars(*this, undef_vars, repls, val.value);
  collectUndefVars(*this, undef_vars, repls, val.non_poison);
  if (undef_vars.empty())
    return move(val);
  if (hit_half_memory_limit())
    throw AliveException("Out of memory; skipping function.", false);
  return { val.value.subst(repls), val.non_poison.subst(repls) };
}

void State::addGlobalVarBid(const string &glbvar, unsigned bid) {
  ENSURE(glbvar_bids.emplace(glbvar, make_pair(bid, true)).second);
}

bool State::hasGlobalVarBid(const string &glbvar, unsigned &bid,
                            bool &allocated) const {
  auto itr = glbvar_bids.find(glbvar);
  bool found = itr != glbvar_bids.end();
  if (found) {
    bid = itr->second.first;
    allocated = itr->second.second;
  }
  return found;
}

void State::markGlobalAsAllocated(const string &glbvar) {
  auto itr = glbvar_bids.find(glbvar);
  assert(itr != glbvar_bids.end());
  itr->second.second = true;
}

void State::syncSEdataWithSrc(const State &src) {
  assert(glbvar_bids.empty());
  assert(src.isSource() && !isSource());
  glbvar_bids = src.glbvar_bids;
  for (auto &itm : glbvar_bids)
    itm.second.second = false;

  fn_call_data = src.fn_call_data;

  Memory::resetLocalBids();
}

void State::mkAxioms(State &tgt) {
  assert(isSource() && !tgt.isSource());
  memory.mkAxioms();

  // axioms for function calls
  for (auto &[fn, data] : tgt.fn_call_data) {
    (void)fn;
    for (auto I = data.begin(), E = data.end(); I != E; ++I) {
      auto &[ins, ptr_ins, mem] = I->first;
      auto &[rets, ub] = I->second;

      for (auto I2 = data.begin(); I2 != E; ++I2) {
        auto &[ins2, ptr_ins2, mem2] = I2->first;
        auto &[rets2, ub2] = I2->second;

        expr refines(true), is_val_eq(true);
        for (unsigned i = 0, e = ins.size(); i != e; ++i) {
          expr eq_val = ins[i].value == ins2[i].value;
          is_val_eq &= eq_val;
          refines &= !ins[i].non_poison || (eq_val && ins2[i].non_poison);
        }

        for (unsigned i = 0, e = ptr_ins.size(); i != e; ++i) {
          expr eq_val = Pointer(memory, ptr_ins[i].value)
                          .refined(Pointer(memory, ptr_ins2[i].value));
          is_val_eq &= eq_val;
          refines &= ptr_ins[i].non_poison
                       .implies(eq_val && ptr_ins2[i].non_poison);
        }

        {
          expr mem_refined = mem.refined(mem2).first;
          is_val_eq &= mem_refined;
          refines &= mem_refined;
        }

        expr ref_expr(true), eq_expr(true);
        for (unsigned i = 0, e = rets.size(); i != e; ++i) {
          eq_expr &= rets[i].value == rets2[i].value;
          ref_expr &= rets[i].non_poison.implies(rets2[i].non_poison);
        }
        tgt.addPre(is_val_eq.implies(eq_expr));
        tgt.addPre(refines.implies(ref_expr && ub.implies(ub2)));
      }
    }
  }
}

}
