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

struct Program<C, D>
{
  args: Vec<String>,
  def: Expr<C, D>
}

enum Expr<C, D>
{
  ReactiveSum(Vec<Expr<C, D>>),
  Parallel(Vec<Expr<C, D>>),
  Replicate(Box<Expr<C, D>>),
  When(C, Box<Expr<C, D>>),
  Unless(C, Box<Expr<C, D>>),
  Tell(C),
  Next(Box<Expr<C, D>>),
  Async(Box<Expr<C, D>>),
  LetIn(String, D, Box<Expr<C, D>>)
}
