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

// Temporal flow graph (TFG)

// TODO: two types to distinguish vertex and edge indexes.

use front::ast::*;
use front::ast::Expr::*;

pub struct Graph<C, D> {
  vertices: Vec<Vertex<C,D>>,
  edges: Vec<Edge<C,D>>,
  args: Vec<String>,
  entry: usize
}

impl<C,D> Graph<C,D> {
  fn add_empty_vertex(&mut self) -> usize {
    self.vertices.push(Vertex::new_empty());
    self.vertices.len() - 1
  }

  fn add_delay_on(&mut self, source: usize, target: usize, delay: u32) -> usize {
    match self.find_edge(source, target) {
      None => self.add_edge(source, target, vec![delay]),
      Some(edge_id) => {
        self.edges[edge_id].delays.push(delay);
        edge_id
      }
    }
  }

  fn find_edge(&self, source: usize, target: usize) -> Option<usize> {
    for &edge_id in self.vertices[source].next.iter() {
      if self.edges[edge_id].target == target {
        return Some(edge_id);
      }
    }
    None
  }

  fn add_edge(&mut self, source: usize, target: usize, delays: Vec<u32>) -> usize {
    let edge = Edge::new(target, delays);
    self.edges.push(edge);
    let edge_id = self.edges.len() - 1;
    self.vertices[source].next.push(edge_id);
    edge_id
  }

  fn add_seq_edge(&mut self, target: usize) -> usize {
    let edge = Edge::new(target, vec![0]);
    self.edges.push(edge);
    self.edges.len() - 1
  }
}

pub struct Vertex<C, D> {
  sums: Vec<Vec<ConstraintDependentEdge<C>>>,
  unless: Vec<ConstraintDependentEdge<C>>,
  tell: Vec<C>,
  locals: Vec<(String, D)>,
  next: Vec<usize> // there should only be sequential edge here (after the 'compact' step)
}

impl<C,D> Vertex<C, D> {
  fn new_empty() -> Vertex<C,D> {
    Vertex {
      sums: vec![],
      unless: vec![],
      tell: vec![],
      locals: vec![],
      next: vec![]
    }
  }
}

pub struct Edge<C,D> {
  target: usize,
  delays: Vec<u32>
}

impl<C,D> Edge<C,D> {
  fn new(target: usize, delays: Vec<u32>) -> Edge<C,D> {
    Edge {
      target: target,
      delays: delays
    }
  }
}

pub struct ConstraintDependentEdge<C> {
  c: C,
  edge: usize
}

impl<C> ConstraintDependentEdge<C> {
  pub fn new(c: C, edge: usize) -> ConstraintDependentEdge<C> {
    ConstraintDependentEdge {
      c: c,
      edge: edge
    }
  }
}

pub fn compile_program<D,C>(program: Program<C,D>) -> Graph<C,D>
{
  let mut graph: Graph<C,D> = Graph {
    vertices: vec![],
    edges: vec![],
    args: program.args,
    entry: 0
  };
  let current_vertex_id = graph.add_empty_vertex();
  graph.entry = compile_expr(&mut graph, program.def, current_vertex_id);
  graph
}

// Returns the vertex id we just compiled expr into.
pub fn compile_expr<C,D>(graph: &mut Graph<C,D>, expr: Expr<C,D>, current: usize) -> usize
{
  match expr {
    Tell(c) => compile_tell(graph, c, current),
    Parallel(exprs) => compile_par(graph, exprs, current),
    when@When(_,_) => compile_reactive_sum(graph, vec![when], current),
    ReactiveSum(whens) => compile_reactive_sum(graph, whens, current),
    LetIn(v, dom, expr) => compile_let_in(graph, v, dom, *expr, current),
    Next(expr) => compile_next(graph, *expr, 1, current),
    _ => panic!("unimplemented")
    // Replicate(Box<Expr<C, D>>),
    // Unless(C, Box<Expr<C, D>>),
    // Next(Box<Expr<C, D>>),
    // Async(Box<Expr<C, D>>),
  }
}

fn compile_tell<C,D>(graph: &mut Graph<C,D>, c: C, current: usize) -> usize
{
  graph.vertices[current].tell.push(c);
  current
}

fn compile_par<C,D>(graph: &mut Graph<C,D>, exprs: Vec<Expr<C,D>>, current: usize) -> usize
{
  for expr in exprs.into_iter() {
    compile_expr(graph, expr, current);
  }
  current
}

fn compile_reactive_sum<C,D>(graph: &mut Graph<C,D>, whens: Vec<Expr<C,D>>, current: usize) -> usize
{
  let mut sum = vec![];
  for when in whens.into_iter() {
    match when {
      When(c, expr) => {
        let empty_vertex = graph.add_empty_vertex();
        let cexpr = compile_expr(graph, *expr, empty_vertex);
        let seq_edge_id = graph.add_seq_edge(cexpr);
        sum.push(ConstraintDependentEdge::new(c, seq_edge_id));
      }
      _ => panic!("The sugar P + P' instead of when true -> P + when true -> P' is not yet supported.")
    }
  }
  graph.vertices[current].sums.push(sum);
  current
}

// Note: it must has previously been alpha-renamed, so two occurrences of the name v
// inside a node is impossible.
fn compile_let_in<C,D>(graph: &mut Graph<C,D>, v: String, dom: D, expr: Expr<C,D>, current: usize) -> usize
{
  graph.vertices[current].locals.push((v, dom));
  compile_expr(graph, expr, current);
  current
}

fn compile_next<C,D>(graph: &mut Graph<C,D>, expr: Expr<C,D>, delay: u32, current: usize) -> usize
{
  match expr {
    Next(expr) => {
      compile_next(graph, *expr, delay+1, current)
    }
    expr => {
      let empty_vertex = graph.add_empty_vertex();
      let target_id = compile_expr(graph, expr, empty_vertex);
      graph.add_delay_on(current, target_id, delay);
      current
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use front::constraint_ast::*;
  use front::constraint_ast::Domain::*;
  use front::constraint_ast::Constraint::*;
  use front::ast::*;
  use front::ast::Expr::*;

  #[test]
  fn tell_test() {
    let p: Program<Constraint, Domain> = Program {
      args: vec![],
      def: Tell(make_x_eq_y())
    };
    let g = compile_program(p);
    assert_eq!(g.vertices.len(), 1);
    assert_eq!(g.edges.len(), 0);
    assert_eq!(g.vertices[0].tell.len(), 1);
    assert_eq!(g.vertices[0].tell[0], make_x_eq_y());
  }

  #[test]
  fn par_tell_test() {
    let p: Program<Constraint, Domain> = Program {
      args: vec![],
      def: Parallel(vec![
            Tell(make_x_eq_y()),
            Tell(make_x_neq_z())])
    };
    let g = compile_program(p);
    assert_eq!(g.vertices.len(), 1);
    assert_eq!(g.edges.len(), 0);
    assert_eq!(g.vertices[0].tell.len(), 2);
    assert_eq!(g.vertices[0].tell[0], make_x_eq_y());
    assert_eq!(g.vertices[0].tell[1], make_x_neq_z());
  }

  #[test]
  fn when_tell_test() {
    let p: Program<Constraint, Domain> = Program {
      args: vec![],
      def: ReactiveSum(vec![
            When(make_x_eq_0(), box Tell(make_x_eq_y())),
            When(make_x_eq_1(), box Tell(make_x_neq_z()))])
    };
    let g = compile_program(p);
    assert_eq!(g.vertices.len(), 3);
    assert_eq!(g.vertices[0].tell.len(), 0);
    assert_eq!(g.vertices[1].tell.len(), 1);
    assert_eq!(g.vertices[2].tell.len(), 1);
    assert_eq!(g.vertices[1].tell[0], make_x_eq_y());
    assert_eq!(g.vertices[2].tell[0], make_x_neq_z());

    assert_eq!(g.vertices[0].sums.len(), 1);
    assert_eq!(g.vertices[0].sums[0].len(), 2);
    assert_eq!(g.vertices[0].sums[0][0].c, make_x_eq_0());
    assert_eq!(g.vertices[0].sums[0][1].c, make_x_eq_1());

    assert_eq!(g.edges.len(), 2);
    assert_eq!(g.edges[0].delays, vec![0]);
    assert_eq!(g.edges[0].target, 1);
    assert_eq!(g.edges[1].target, 2);
  }

  #[test]
  fn par_when_test() {
    let e =
      Parallel(vec![
        ReactiveSum(vec![
          When(make_x_eq_0(), box Tell(make_x_eq_y())),
          When(make_x_eq_1(), box Tell(make_x_neq_z()))]),
        When(make_x_eq_y(), box Tell(make_x_neq_z())),
        When(make_x_neq_z(), box Tell(make_x_eq_y()))]);

    let p: Program<Constraint, Domain> = Program {
      args: vec![],
      def: e
    };
    let g = compile_program(p);
    assert_eq!(g.vertices.len(), 5);
    assert_eq!(g.vertices[0].sums.len(), 3);
    assert_eq!(g.vertices[0].sums[0].len(), 2);
    assert_eq!(g.vertices[0].sums[1].len(), 1);
    assert_eq!(g.vertices[0].sums[2].len(), 1);

    assert_eq!(g.edges.len(), 4);
    assert_eq!(g.edges[0].target, 1);
    // test the When alone.
    assert_eq!(g.edges[3].target, 4);
    assert_eq!(g.edges[3].delays, vec![0]);
  }

  fn nested_par_equiv(expr: Expr<Constraint, Domain>) {
    let p: Program<Constraint, Domain> = Program {
      args: vec![],
      def: expr
    };
    let g = compile_program(p);
    assert_eq!(g.vertices.len(), 3);
    assert_eq!(g.edges.len(), 2);
    assert_eq!(g.vertices[0].sums.len(), 2);
    assert_eq!(g.vertices[0].tell.len(), 2);
    assert_eq!(g.edges[0].target, 1);
    assert_eq!(g.edges[1].target, 2);
  }

  #[test]
  fn nested_par_test_1() {
    let e =
      Parallel(vec![
        When(make_x_eq_0(), box Tell(make_x_neq_z())),
        When(make_x_eq_1(), box Tell(make_x_eq_y())),
        Tell(make_x_eq_0()),
        Tell(make_x_eq_1())]);

    nested_par_equiv(e);
  }

  #[test]
  fn nested_par_test_2() {
    let e =
      Parallel(vec![
        Parallel(vec![
          When(make_x_eq_0(), box Tell(make_x_neq_z())),
          When(make_x_eq_1(), box Tell(make_x_eq_y()))]),
        Tell(make_x_eq_0()),
        Tell(make_x_eq_1())]);

    nested_par_equiv(e);
  }

  #[test]
  fn nested_par_test_3() {
    let e =
      Parallel(vec![
        Parallel(vec![
          When(make_x_eq_0(), box Tell(make_x_neq_z())),
          When(make_x_eq_1(), box Tell(make_x_eq_y()))]),
        Parallel(vec![
          Tell(make_x_eq_0()),
          Tell(make_x_eq_1())])]);

    nested_par_equiv(e);
  }

  #[test]
  fn nested_par_test_4() {
    let e =
      Parallel(vec![
        Parallel(vec![
          When(make_x_eq_0(), box Tell(make_x_neq_z())),
          When(make_x_eq_1(), box Tell(make_x_eq_y()))]),
        Parallel(vec![
          Parallel(vec![Tell(make_x_eq_0())]),
          Parallel(vec![Tell(make_x_eq_1())])])]);

    nested_par_equiv(e);
  }

  #[test]
  fn nested_par_when_test_5() {
    let e =
      Parallel(vec![
        ReactiveSum(vec![When(make_x_eq_0(), box Tell(make_x_neq_z()))]),
        ReactiveSum(vec![When(make_x_eq_1(), box Tell(make_x_eq_y()))]),
        Tell(make_x_eq_0()),
        Tell(make_x_eq_1())]);
    nested_par_equiv(e);
  }

  fn nested_letin_equiv(expr: Expr<Constraint, Domain>) {
    let p: Program<Constraint, Domain> = Program {
      args: vec![],
      def: expr
    };
    let g = compile_program(p);
    assert_eq!(g.vertices.len(), 2);
    assert_eq!(g.vertices[0].locals.len(), 2);
    assert_eq!(g.vertices[0].locals[0], (x_name(), Singleton(1)));
    assert_eq!(g.vertices[0].locals[1], (y_name(), Singleton(1)));
    assert_eq!(g.vertices[0].tell.len(), 0);
    assert_eq!(g.vertices[1].locals.len(), 1);
    assert_eq!(g.vertices[1].locals[0], (z_name(), Interval(1,2)));
    assert_eq!(g.vertices[1].tell.len(), 1);
    assert_eq!(g.edges.len(), 1);
    assert_eq!(g.edges[0].target, 1);
  }

  #[test]
  fn letin_test_1() {
    let e =
      LetIn(x_name(), Singleton(1), box
      LetIn(y_name(), Singleton(1), box
      When(make_x_eq_y(), box
        LetIn(z_name(), Interval(1, 2), box
        Tell(make_x_neq_z())))));

    nested_letin_equiv(e);
  }

  /*
     when {x = 0} -> next {x != z}
  || when {x = 1} -> {x = y}
  || next next next {x = 0}
  || {x = 1} || next {x = 1}
  */
  // TODO: the edge between `when {x = 0}` and `next {x != z}` is
  //   compacted, an empty vertex is created.
  #[test]
  fn next_test() {
    let e =
      Parallel(vec![
        When(make_x_eq_0(), box Next(box Tell(make_x_neq_z()))),
        When(make_x_eq_1(), box Tell(make_x_eq_y())),
        Next(box Next(box Next(box Tell(make_x_eq_0())))),
        Parallel(vec![
          Tell(make_x_eq_1()),
          Next(box Tell(make_x_eq_1()))])]);
    let p: Program<Constraint, Domain> = Program {
      args: vec![],
      def: e
    };
    let g = compile_program(p);

    assert_eq!(g.vertices.len(), 6);
    for i in range(0, 6) {
      if i != 1 { // empty node generated by the when.
        assert_eq!(g.vertices[i].tell.len(), 1);
      }
    }
    assert_eq!(g.vertices[2].tell[0], make_x_neq_z());
    assert_eq!(g.vertices[4].tell[0], make_x_eq_0()); // in next^3 {x=0}

    assert_eq!(g.vertices[0].sums.len(), 2);

    assert_eq!(g.edges.len(), 5);
    // when {x = 0} -> next {x != z}
    assert_eq!(g.edges[0].delays, vec![1]);
    assert_eq!(g.edges[0].target, 2);
    assert_eq!(g.edges[1].delays, vec![0]);
    assert_eq!(g.edges[1].target, 1);
    // when {x = 1} -> {x = y}
    assert_eq!(g.edges[2].delays, vec![0]);
    assert_eq!(g.edges[2].target, 3);
    // next next next {x = 0}
    assert_eq!(g.edges[3].delays, vec![3]);
    assert_eq!(g.edges[3].target, 4);
    // next {x = 1}
    assert_eq!(g.edges[4].delays, vec![1]);
    assert_eq!(g.edges[4].target, 5);
  }

  fn make_x_eq_y() -> Constraint {
    XEqualY(x_name(), y_name())
  }

  fn make_x_neq_z() -> Constraint {
    XLessThanY(x_name(), z_name())
  }

  fn make_x_eq_0() -> Constraint {
    XEqualC(x_name(), 0)
  }

  fn make_x_eq_1() -> Constraint {
    XEqualC(x_name(), 1)
  }

  fn x_name() -> String { String::from_str("x") }
  fn y_name() -> String { String::from_str("y") }
  fn z_name() -> String { String::from_str("z") }
}