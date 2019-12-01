// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "smt/exprs.h"
#include "util/compiler.h"

using namespace std;

namespace smt {

void FunctionExpr::add(const expr &key, expr &&val) {
  ENSURE(fn.emplace(key, move(val)).second);
}

void FunctionExpr::add(const FunctionExpr &other) {
  fn.insert(other.fn.begin(), other.fn.end());
}

void FunctionExpr::del(const expr &key) {
  fn.erase(key);
}

expr FunctionExpr::operator()(const expr &key) const {
  DisjointExpr disj(default_val);
  for (auto &[k, v] : fn) {
    disj.add(v, k == key);
  }
  return disj();
}

const expr* FunctionExpr::lookup(const expr &key) const {
  auto I = fn.find(key);
  return I != fn.end() ? &I->second : nullptr;
}

bool FunctionExpr::operator<(const FunctionExpr &rhs) const {
  return tie(fn, default_val) < tie(rhs.fn, rhs.default_val);
}

}
