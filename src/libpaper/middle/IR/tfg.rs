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

use front::ast::*;
use front::ast::Expr::*;

struct Graph<C, D> {
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

struct Vertex<C, D> {
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

struct Edge<C,D> {
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

struct ConstraintDependentEdge<C> {
  c: C,
  edge: usize
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
    _ => panic!("unimplemented")
  }
}

fn compile_tell<C,D>(graph: &mut Graph<C,D>, c: C, current: usize) -> usize
{
  graph.vertices[current].tell.push(c);
  current
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
    assert_eq!(g.vertices[0].tell[0], make_x_eq_y());
  }

  fn make_x_eq_y() -> Constraint {
    XEqualY(String::from_str("x"), String::from_str("y"))
  }
}