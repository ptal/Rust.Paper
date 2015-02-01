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

use front::constraint_ast::Constraint;
use middle::semantics::symbol_table::SymbolTable;

trait AlphaConversion
{
  type TargetAST;
  fn convert(self, symbols: &SymbolTable) -> Self::TargetAST;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AConstraint {
  XEqualY(u32, u32),
  XEqualC(u32, i32),
  XNotEqualY(u32, u32),
  XLessThanY(u32, u32),
}

impl AlphaConversion for Constraint
{
  type TargetAST = AConstraint;

  fn convert(self, symbols: &SymbolTable) -> AConstraint {
    match self {
      Constraint::XEqualY(x, y) => AConstraint::XEqualY(symbols[x], symbols[y]),
      Constraint::XEqualC(x, c) => AConstraint::XEqualC(symbols[x], c),
      Constraint::XNotEqualY(x, y) => AConstraint::XNotEqualY(symbols[x], symbols[y]),
      Constraint::XLessThanY(x, y) => AConstraint::XLessThanY(symbols[x], symbols[y])
    }
  }
}
