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

use front::ast::{Program, Expr};
use front::constraint_ast::Constraint;
use middle::semantics::symbol_table::SymbolTable;

trait AlphaConversion
{
  type TargetAST;
  fn rename(self, symbols: &SymbolTable) -> Self::TargetAST;
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

  fn rename(self, symbols: &SymbolTable) -> AConstraint {
    match self {
      Constraint::XEqualY(x, y) => AConstraint::XEqualY(symbols[x], symbols[y]),
      Constraint::XEqualC(x, c) => AConstraint::XEqualC(symbols[x], c),
      Constraint::XNotEqualY(x, y) => AConstraint::XNotEqualY(symbols[x], symbols[y]),
      Constraint::XLessThanY(x, y) => AConstraint::XLessThanY(symbols[x], symbols[y])
    }
  }
}

pub struct AProgram<C, D>
{
  pub args: Vec<u32>,
  pub def: AExpr<C, D>
}

pub enum AExpr<C, D>
{
  ReactiveSum(Vec<AExpr<C, D>>),
  Parallel(Vec<AExpr<C, D>>),
  Replicate(Box<AExpr<C, D>>),
  When(C, Box<AExpr<C, D>>),
  Unless(C, Box<AExpr<C, D>>),
  Tell(C),
  Next(Box<AExpr<C, D>>),
  Async(Box<AExpr<C, D>>),
  LetIn(u32, D, Box<AExpr<C, D>>)
}

fn alpha_conversion<C, D>(program: Program<C,D>)
  -> AProgram<<C as AlphaConversion>::TargetAST, D>
  where C: AlphaConversion
{
  let mut symbol_table = SymbolTable::new();
  AProgram {
    args: program.args.into_iter()
      .map(|arg| symbol_table.shadow(arg))
      .collect(),
    def: alpha_expr(&mut symbol_table, program.def)
  }
}

fn alpha_expr<C, D>(symbol_table: &mut SymbolTable, expr: Expr<C,D>)
  -> AExpr<<C as AlphaConversion>::TargetAST, D>
  where C: AlphaConversion
{
  match expr {
    Expr::ReactiveSum(exprs) => {
      AExpr::ReactiveSum(exprs.into_iter()
        .map(|expr| alpha_expr(symbol_table, expr))
        .collect())
    }
    Expr::Parallel(exprs) => {
      AExpr::Parallel(exprs.into_iter()
        .map(|expr| alpha_expr(symbol_table, expr))
        .collect())
    }
    Expr::Replicate(expr) => {
      AExpr::Replicate(box alpha_expr(symbol_table, *expr))
    }
    Expr::When(c, expr) => {
      AExpr::When(
        c.rename(symbol_table),
        box alpha_expr(symbol_table, *expr)
      )
    }
    Expr::Unless(c, expr) => {
      AExpr::Unless(
        c.rename(symbol_table),
        box alpha_expr(symbol_table, *expr)
      )
    },
    Expr::Tell(c) => {
      AExpr::Tell(c.rename(symbol_table))
    }
    Expr::Next(expr) => {
      AExpr::Next(box alpha_expr(symbol_table, *expr))
    }
    Expr::Async(expr) => {
      AExpr::Async(box alpha_expr(symbol_table, *expr))
    }
    Expr::LetIn(name, dom, expr) => {
      let uid = symbol_table.shadow(name.clone());
      let expr = box alpha_expr(symbol_table, *expr);
      symbol_table.unshadow(name);
      AExpr::LetIn(uid, dom, expr)
    }
  }
}
