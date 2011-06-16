open Printf

(* エラーレポート *)
let report e = (
  match e with
    | Lexer.Illegal_character c ->
        fprintf stderr "Illegal character (%s)\n" (Char.escaped c)
    | Lexer.Illegal_escape s ->
        fprintf stderr "Illegal escape: %s\n" s
    | Lexer.Unterminated_string ->
        fprintf stderr "Unterminated string\n"
    | Absyn.Parse_error ->
        fprintf stderr "Syntax error\n"
    | Context.Multiple_names s ->
        fprintf stderr "Multiple name defined (%s)\n" s
    | Failure s ->
        fprintf stderr "Runtime error: %s\n" s
    | exn -> raise exn );
  flush stderr
