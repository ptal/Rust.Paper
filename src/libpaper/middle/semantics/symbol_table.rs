// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at

//     http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::collections::HashMap;
use std::ops::Index;

pub struct SymbolTable
{
  sym_to_id: HashMap<String, Vec<u32>>,
  uid: u32,
  names_used_now: usize
}

impl SymbolTable
{
  pub fn new() -> SymbolTable
  {
    SymbolTable {
      sym_to_id: HashMap::new(),
      uid: 0,
      names_used_now: 0
    }
  }

  pub fn get<'a>(&'a self, name: &str) -> Option<&'a u32>
  {
    match self.sym_to_id.get(name) {
      None => None,
      Some(v) =>
        if v.is_empty() { None }
        else { Some(&v[v.len()-1]) }
    }
  }

  pub fn expect<'a>(&'a self, name: &str, err_msg: &str) -> &'a u32
  {
    match self.get(name) {
      None => panic!("{}", err_msg),
      Some(id) => id
    }
  }

  pub fn shadow(&mut self, name: String) -> u32
  {
    if self.sym_to_id.contains_key(&name) {
      self.sym_to_id[name].push(self.uid);
    } else {
      self.sym_to_id.insert(name, vec![self.uid]);
    }
    self.names_used_now += 1;
    self.inc_uid()
  }

  pub fn unshadow(&mut self, name: String)
  {
    assert!(self.sym_to_id.contains_key(&name),
      "Cannot unshadow a name not currently in scope.");
    self.sym_to_id[name].pop();
    if self.sym_to_id[name].is_empty() {
      self.sym_to_id.remove(&name);
    }
    self.names_used_now -= 1;
  }

  pub fn names_in_scope_len(&self) -> usize
  {
    self.sym_to_id.len()
  }

  pub fn names_currently_used_len(&self) -> usize
  {
    self.names_used_now
  }

  fn inc_uid(&mut self) -> u32
  {
    self.uid += 1;
    self.uid - 1
  }
}

impl Index<str> for SymbolTable {
    type Output = u32;

    #[inline]
    fn index<'a>(&'a self, index: &str) -> &'a u32 {
        self.expect(index, format!("{} is not in scope.", index).as_slice())
    }
}


#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn shadow_test()
  {
    let mut sym_table = SymbolTable::new();
    let mut v = vec![1,2];
    assert_eq!(v[0], 1);
    assert_eq!(sym_table.get("a"), None);
    assert_eq!(sym_table.shadow(name("a")), 0);
    assert_eq!(sym_table.get("a"), Some(&0));
    assert_eq!(sym_table.shadow(name("a")), 1);
    assert_eq!(sym_table[*"a"], 1);
    assert_eq!(sym_table.shadow(name("b")), 2);
    assert_eq!(sym_table[*"b"], 2);
    assert_eq!(sym_table.get("c"), None);

    assert_eq!(sym_table.names_in_scope_len(), 2);
    assert_eq!(sym_table.names_currently_used_len(), 3);
  }

  #[test]
  fn unshadow_test()
  {
    let mut sym_table = SymbolTable::new();
    sym_table.shadow(name("a"));
    sym_table.shadow(name("a"));
    sym_table.shadow(name("b"));

    assert_eq!(sym_table.names_in_scope_len(), 2);
    assert_eq!(sym_table.names_currently_used_len(), 3);

    assert_eq!(sym_table[*"a"], 1);
    sym_table.unshadow(name("a"));
    assert_eq!(sym_table[*"a"], 0);
    assert_eq!(sym_table.names_in_scope_len(), 2);
    assert_eq!(sym_table.names_currently_used_len(), 2);

    sym_table.unshadow(name("a"));
    assert_eq!(sym_table.get("a"), None);
    assert_eq!(sym_table.names_in_scope_len(), 1);
    assert_eq!(sym_table.names_currently_used_len(), 1);

    sym_table.unshadow(name("b"));
    assert_eq!(sym_table.get("b"), None);
    assert_eq!(sym_table.names_in_scope_len(), 0);
    assert_eq!(sym_table.names_currently_used_len(), 0);
  }

  #[should_fail]
  #[test]
  fn bad_unshadowing_test()
  {
    let mut sym_table = SymbolTable::new();
    sym_table.unshadow(name("a"));
  }

  #[should_fail]
  #[test]
  fn bad_unshadowing_test2()
  {
    let mut sym_table = SymbolTable::new();
    sym_table.shadow(name("a"));
    sym_table.unshadow(name("a"));
    sym_table.unshadow(name("a"));
  }

  #[should_fail]
  #[test]
  fn index_expect_test()
  {
    let mut sym_table = SymbolTable::new();
    sym_table[*"a"];
  }

  fn name(v: &str) -> String { String::from_str(v) }
}
