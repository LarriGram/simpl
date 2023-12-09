
(* The type of tokens. *)

type token = 
  | VAR of (string)
  | TRUE
  | TIMESF
  | TIMES
  | THEN
  | RPAREN
  | POWERF
  | POWER
  | PLUSF
  | PLUS
  | LPAREN
  | LET
  | LEQF
  | LEQ
  | INT of (int)
  | IN
  | IF
  | FLOAT of (float)
  | FALSE
  | EQUALS
  | EOF
  | ELSE

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
