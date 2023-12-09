(** The type of binary operators. *)
type bop = 
  | Add
  | Mult
  | Leq
  | Power
  | Addf
  | Multf
  | Powerf

(** The type of the abstract syntax tree (AST). *)
type expr =
  | Var of string
  | Int of int
  | Bool of bool 
  | Float of float
  | Binop of bop * expr * expr
  | Let of string * expr * expr
  | If of expr * expr * expr
