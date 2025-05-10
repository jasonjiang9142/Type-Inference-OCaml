
(* The type of tokens. *)

type token = 
  | WITH
  | VAR of (string)
  | TVAR of (string)
  | TUNIT
  | TRUE
  | TOPTION
  | TLIST
  | TINT
  | THEN
  | TFLOAT
  | TBOOL
  | SUBF
  | SUB
  | STAR
  | SOME
  | SEMICOLON
  | RPAREN
  | REC
  | RBRACKET
  | POW
  | OR
  | NONE
  | NEQ
  | MULF
  | MOD
  | MATCH
  | LTE
  | LT
  | LPAREN
  | LET
  | LBRACKET
  | INT of (int)
  | IN
  | IF
  | GTE
  | GT
  | FUN
  | FLOAT of (float)
  | FALSE
  | EQ
  | EOF
  | ELSE
  | DIVF
  | DIV
  | CONS
  | COMMA
  | COLON
  | ASSERT
  | ARROW
  | AND
  | ALT
  | ADDF
  | ADD

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Utils.prog)
