/* parser.mly: 構文定義 */
%{
  open Absyn
  open Context
%}

/* トークン */
%token EOF
/* キーワードトークン */
%token IN
%token LET
%token DEF
%token AND
%token DATA
%token CASE
%token OF
%token RARROW
%token DDDOT
%token DOT
%token VBAR
%token SEMI
%token BACKSLASH
%token LPAREN
%token RPAREN
%token EQ
%token COLONCOLONEQ
%token <string>  IDENT
%token <Const.t> CONST

%start toplevel
%type <Absyn.term Context.t -> Absyn.command> toplevel
%%

/* トップレベル */
toplevel
  : command SEMI { $1 }
  | error SEMI { raise Absyn.Parse_error }
  | EOF { raise End_of_file }
;

command
  : expression
      { fun ctx -> Eval($1 ctx) }
  | DEF bind_list {
      fun ctx ->
        let binds = $2 ctx in
        let names = List.map (fun (_,x,_) -> x) binds in
        let _ = Context.add_names ctx names in
          Defn binds
      }
  | DATA IDENT
      { fun ctx -> Data($2,0) }
  | DATA IDENT LPAREN CONST RPAREN
      { fun ctx ->
          match $4 with
              Const.CInt(n) -> Data($2,n)
            | _ -> raise Absyn.Parse_error
      }

  | /* empty */
      { fun ctx -> Noop }
;

bind_list
  : bind { fun ctx -> [$1 ctx] }
  | bind AND bind_list { fun ctx -> $1 ctx::$3 ctx }
;

bind
  : IDENT EQ expression
      { fun ctx -> (Eager, $1, $3 ctx) }
  | IDENT COLONCOLONEQ expression
      { fun ctx -> (Lazy, $1, $3 ctx) }
;

expression
  : apply_expression { $1 }
  | LET bind_list IN expression {
      fun ctx ->
        let binds = $2 ctx in
        let names = List.map (fun (_,x,_) -> x) binds in
          TmLet(binds, $4 (Context.add_names ctx names))
    }
  | BACKSLASH IDENT DOT expression {
      fun ctx -> TmAbs(Eager, $2, $4 (Context.add_name ctx $2))
    }
  | BACKSLASH LPAREN IDENT RPAREN DOT expression {
      fun ctx -> TmAbs(Lazy, $3, $6 (Context.add_name ctx $3))
    }
  | CASE expression OF pattern_list {
      fun ctx -> let patns,default = $4 ctx in TmCas($2 ctx,patns,default)
    }
;

pattern_list
  : pattern { fun ctx -> [$1 ctx],None }
  | pattern VBAR pattern_list {
      fun ctx -> let patns,default = $3 ctx in ($1 ctx::patns),default
    }
  | DDDOT RARROW atomic_expression {
      fun ctx -> [],Some($3 ctx)
    }
;

pattern
  : CONST RARROW atomic_expression { fun ctx -> $1,$3 ctx }
;

apply_expression
  : atomic_expression { $1 }
  | apply_expression atomic_expression {
      fun ctx -> TmApp($1 ctx, $2 ctx)
    }
;

atomic_expression
  : IDENT {
      fun ctx ->
        let i = Context.name2index ctx $1 in
          TmVar i
    }
  | CONST { fun ctx -> TmCon($1) }
  | LPAREN expression RPAREN { $2 }
;
