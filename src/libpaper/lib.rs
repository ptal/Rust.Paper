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

#![crate_name = "paper"]
#![experimental]
#![crate_type = "dylib"]

#![feature(plugin_registrar, quote, box_syntax)]
#![allow(unstable)]

extern crate syntax;
extern crate rustc;

use rustc::plugin::Registry;
use syntax::ext::base::{ExtCtxt,DummyResult,MacResult};
use syntax::codemap::{DUMMY_SP,Span};
use syntax::ast::TokenTree;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry)
{
  reg.register_macro("paper", expand)
}

fn expand<'cx>(cx: &'cx mut ExtCtxt, _sp: Span, tts: &[TokenTree]) -> Box<MacResult + 'cx>
{
  parse(cx, tts)
}

fn parse<'cx>(cx: &'cx mut ExtCtxt, tts: &[TokenTree]) -> Box<MacResult + 'cx>
{
  DummyResult::any(DUMMY_SP)
}