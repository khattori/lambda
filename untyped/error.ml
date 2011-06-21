(** エラー情報の出力 *)

open Printf
open Lexing

(** エラー情報を出力する *)
let report pos e = (
  match e with
    | Lexer.Illegal_character c ->
        fprintf stderr "Illegal character (%s)\n" (Char.escaped c)
    | Lexer.Illegal_escape s ->
        fprintf stderr "Illegal escape: %s\n" s
    | Lexer.Unterminated_string ->
        fprintf stderr "Unterminated string: at line %d in file '%s'\n"
          pos.pos_lnum pos.pos_fname
    | Absyn.Parse_error ->
        fprintf stderr "Syntax error: at line %d in file '%s'\n"
          pos.pos_lnum pos.pos_fname
    | Absyn.Multiple_labels l ->
        fprintf stderr "Multiple labels defined: %s\n" l
    | Context.Multiple_names s ->
        fprintf stderr "Multiple names defined: %s\n" s
    | Context.Unbound_name s ->
        fprintf stderr "Unbound name: %s\n" s
    | Failure s ->
        fprintf stderr "Runtime error: %s\n" s
    | exn -> raise exn );
  flush stderr
