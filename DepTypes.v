Require Import Bool Arith Vector LibTactics.
Require Import Maps.

Inductive Abs : Type := Ab (x:exp) (t:Type) (e:exp)
with  exp : Type := Var (d:id)
                  | Univ {n:nat}
                  | Pi (Abs : Type)
                  | Lam (Abs : Type)
                  | App (exp : Type) (exp : Type).





type expr =
| Var of variable
| Universe of int
| Pi of abstraction
| Lambda of abstraction
| App of expr * expr
                  