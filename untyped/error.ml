(** エラー情報の出力 *)

open Printf
open Lexing

(* 位置情報の出力 *)
let print_position pos =
  if pos.pos_fname = "" then
    fprintf stderr "\n"
  else
    fprintf stderr ": at line %d in file '%s'\n" pos.pos_lnum pos.pos_fname

(** エラー情報を出力する *)
let report pos e = (
  match e with
    | Lexer.Illegal_character c ->
        fprintf stderr "Illegal character (%s)" (Char.escaped c);
        print_position pos
    | Lexer.Illegal_escape s ->
        fprintf stderr "Illegal escape: %s" s;
        print_position pos
    | Lexer.Unterminated_string ->
        fprintf stderr "Unterminated string";
        print_position pos
    | Absyn.Parse_error ->
        fprintf stderr "Syntax error";
        print_position pos
    | Absyn.Multiple_labels l ->
        fprintf stderr "Multiple labels defined: '%s'" l;
        print_position pos
    | Context.Multiple_names s ->
        fprintf stderr "Multiple names defined: '%s'" s;
        print_position pos
    | Context.Unbound_name s ->
        fprintf stderr "Unbound name: '%s'" s;
        print_position pos
    | Failure s ->
        fprintf stderr "Runtime error: %s\n" s
    | exn -> raise exn );
  flush stderr
