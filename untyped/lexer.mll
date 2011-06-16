(*
  lexer.mll: 字句定義
*)
{
  open Parser
  open Lexing

  exception Illegal_character of char

  let keyword_table = [
    ( "in",    IN    );
    ( "let",   LET   );
    ( "def",   DEF   );
    ( "and",   AND   );
  ]
}

let space = [' ' '\t']
let blank = space | ['\011'(* \v *) '\012'(* \f *)]
let cr = '\r'
let lf = '\n'
let newline = cr | lf | cr lf

let alpha = ['a'-'z' 'A'-'Z']
let nonzero_digit = ['1'-'9']
let digit = '0' | nonzero_digit
let num = nonzero_digit digit* | '0'

let ident_char_head = alpha | '_'
let ident_char  = ident_char_head | digit | ['\'' '?' '!']
let operator_char =
  ['!' '$' '%' '&' '*' '+' '-' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']

rule token = parse
  | blank+
      { token lexbuf }
  | newline
      { token lexbuf }
  | ident_char_head ident_char*
      {
        let s = lexeme lexbuf in
          if List.mem_assoc s keyword_table then
            List.assoc s keyword_table
          else if List.mem s Prims.symbols then
            CONST(Const.CSym s)
          else
            IDENT s
      }
  | "=" { EQ }
  | "::=" { COLONCOLONEQ }
  | operator_char+
      {
        let s = lexeme lexbuf in
          if List.mem s Prims.symbols then
            CONST(Const.CSym s)
          else
            IDENT s
      }
  | num { CONST(Const.CInt(int_of_string(lexeme lexbuf))) }
  | "\\" { BACKSLASH }
  (* セパレータ *)
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "." { DOT }
  | ";" { SEMI }
  | eof
      { EOF }
  | _ as c
      { raise (Illegal_character c) }
