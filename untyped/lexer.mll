(*
  lexer.mll: �����`
*)
{
  open Parser
  open Lexing

  exception Illegal_character of char
  exception Illegal_escape of string
  exception Unterminated_string

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
let sign  = ['+' '-']
let digit = '0' | nonzero_digit
let hexdg = ['0'-'9' 'a'-'f' 'A'-'F']
let octdg = ['0'-'7']
let num = nonzero_digit digit* | '0'
let float_literal = digit* '.' digit* (['e' 'E'] sign? digit+)*

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
  | float_literal
      { CONST(Const.CReal(float_of_string(lexeme lexbuf))) }
  | "\\" { BACKSLASH }
  (* �Z�p���[�^ *)
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "." { DOT }
  | ";" { SEMI }
  | '"'
      { CONST(Const.CStr(string (Buffer.create 0) lexbuf)) }
  | eof
      { EOF }
  | _ as c
      { raise (Illegal_character c) }
(* �����񃊃e�����̏��� *)
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
(* �G�X�P�[�v�����̏��� *)
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
