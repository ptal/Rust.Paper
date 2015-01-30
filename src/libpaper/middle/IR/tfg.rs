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
}

struct Vertex<C, D> {
  sums: Vec<Vec<ConstraintDependentEdge<C>>>,
  unless: Vec<ConstraintDependentEdge<C>>,
  tell: Vec<C>,
  locals: Vec<(String, D)>,
  next: Vec<usize>
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
