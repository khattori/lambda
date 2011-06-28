(*
  lexer.mll: 字句定義
*)
{
  open Parser
  open Lexing
  open Absyn

  exception Illegal_character of char
  exception Illegal_escape of string
  exception Unterminated_string

  let keyword_table = [
    ( "def",   DEF   );
    ( "use",   USE   );
    ( "let",   LET   );
    ( "in",    IN    );
  ]

  let init lexbuf fname =
    lexbuf.lex_curr_p <- {
      pos_fname = fname;
      pos_lnum = 1;
      pos_bol = 0;
      pos_cnum = 0;
    }
}

let space = [' ' '\t']
let blank = space | ['\011'(* \v *) '\012'(* \f *)]
let cr = '\r'
let lf = '\n'
let newline = cr | lf | cr lf
let nonnl = [^ '\r' '\n']

let alpha = ['a'-'z' 'A'-'Z']
let nonzero_digit = ['1'-'9']
let sign  = ['+' '-']
let digit = '0' | nonzero_digit
let hexdg = ['0'-'9' 'a'-'f' 'A'-'F']
let octdg = ['0'-'7']
let num = nonzero_digit digit* | '0'
let float_literal = digit+ '.' digit+ (['e' 'E'] sign? digit+)*

let ident_char_head = alpha | '_'
let ident_char  = ident_char_head | digit | ['\'' '?' '!']
let operator_char =
  ['!' '$' '%' '&' '*' '+' '-' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']

rule token = parse
  | blank+  { token lexbuf }
  | newline { new_line lexbuf; token lexbuf }
  | "_"     { WILDCARD }
  | ident_char_head ident_char*
      {
        let s = lexeme lexbuf in
          if List.mem_assoc s keyword_table then
            List.assoc s keyword_table
          else
            IDENT s
      }
  | "="    { EQ }
  | "#" nonnl* newline
           { new_line lexbuf; token lexbuf }
  | operator_char+
           { IDENT(lexeme lexbuf) }
  | num    { CONST(CnInt(int_of_string(lexeme lexbuf))) }
  | "\\"   { BACKSLASH }
  (* セパレータ *)
  | "("    { LPAREN }
  | ")"    { RPAREN }
  | "."    { DOT }
  | float_literal
           { CONST(CnRea(float_of_string(lexeme lexbuf))) }
  | ";"    { SEMI }
  | '"'    { CONST(CnStr(string (Buffer.create 0) lexbuf)) }
  | eof    { EOF }
  | _ as c { raise (Illegal_character c) }
(* 文字列リテラルの処理 *)
and string strbuf = parse
  | '"'
      { Buffer.contents strbuf }
  | '\\'
      { Buffer.add_char strbuf (escaped lexbuf); string strbuf lexbuf }
  | '\\' newline
      { new_line lexbuf; string strbuf lexbuf }
  | newline
      { Buffer.add_char strbuf '\n'; new_line lexbuf; string strbuf lexbuf }
  | eof
      { raise Unterminated_string }
  | _ as c
      { Buffer.add_char strbuf c; string strbuf lexbuf }
(* エスケープ文字の処理 *)
and escaped = parse
  | 'a'  { '\007' }
  | 'b'  { '\b' }
  | 'f'  { '\012' }
  | 'n'  { '\n' }
  | 'r'  { '\r' }
  | 't'  { '\t' }
  | 'v'  { '\011' }
  | '"'  { '"' }
  | '\'' { '\'' }
  | '\\' { '\\' }
  | octdg octdg? octdg? as od
      {
        try
          Char.chr (int_of_string ("0o" ^ od))
        with Invalid_argument _ ->
          raise (Illegal_escape ("'\\" ^ od))
      }
  | 'x' hexdg hexdg? as hd
      { Char.chr (int_of_string ("0" ^ hd)) }
  | _ as c
      { raise (Illegal_escape ("'\\" ^ String.make 1 c)) }
