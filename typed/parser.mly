/* parser.mly: 構文定義 */
%{
  open Absyn
  open Context
  open Command
%}

/* トークン */
%token EOF
/* キーワードトークン */
%token DATA
%token DEF
%token USE

%token LET
%token IN
%token CASE
%token OF
%token QUOTE
%token UNQUO
%token RARROW
%token DDDOT
%token DOT
%token COMMA
%token VBAR
%token SEMI
%token BACKSLASH
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
%token EQ
%token WILDCARD
%token <string>        IDENT
%token <Absyn.const>   CONST
%token <int>           ARITY

%nonassoc IN
%nonassoc LET
%nonassoc OF
%nonassoc below_VBAR
%left     VBAR
%nonassoc below_COMMA
%left     COMMA
%right    RARROW
%nonassoc DOT


%start main toplevel
%type <Absyn.term Context.t -> Command.t list> main
%type <Absyn.term Context.t -> Command.t> toplevel
%%

/* バッチモード時のメイン */
main
  : command_list EOF { fun ctx ->
                         let cmds,_= $1 ctx in
                           List.rev cmds           }
  | error            { raise Absyn.Parse_error     }
;

/* 対話モード時のトップレベル */
toplevel
  : command SEMI { fun ctx -> fst($1 ctx)  }
  | error SEMI   { raise Absyn.Parse_error }
  | EOF          { raise End_of_file       }
;

command
  : expression                    { fun ctx -> Eval($1 ctx),ctx        }
  | DEF binder_list EQ expression { fun ctx ->
                                      let bs,ctx' = $2 ctx in
                                        Defn(bs,$4 ctx),ctx'           }
  | DATA IDENT arity_option       { fun ctx ->
                                      let c,arity = $2,$3 in
                                        Const.add_ctor c arity;
                                        Data(c,arity),ctx              }
  | USE IDENT                     { fun ctx ->
                                      let ctx' =
                                        Command.use_module $2 in
                                        ( Use($2,ctx'),
                                          Context.join ctx' ctx )      }
  | /* empty */                   { fun ctx -> Noop,ctx                }
;
command_list
  : command                       { fun ctx ->
                                      let cmd,ctx' = $1 ctx in
                                        [cmd],ctx'               }
  | command_list SEMI command     { fun ctx ->
                                      let cmds,ctx' = $1 ctx in
                                      let cmd,ctx'' = $3 ctx' in
                                        cmd::cmds,ctx''          }
;

arity_option
  : /* empty */  { 0 }
  | ARITY        { $1 }
;
binder_list
  : binder_comma_list {
      fun ctx ->
        let bs = List.rev ($1 ctx) in
          bs, Context.add_binds ctx bs
    }
;
binder_comma_list
  : binder                         { fun ctx -> [$1] }
  | binder_comma_list COMMA binder { fun ctx -> $3::$1 ctx }
;
binder
  : WILDCARD        { Wild }
  | IDENT           { Eager $1 }
  | BACKSLASH IDENT { Lazy  $2 }
;

expression
  : apply_expression { $1 }
  | expression_comma_list %prec below_COMMA {
      fun ctx -> TmTpl(List.rev($1 ctx))
    }
  | LET binder_list EQ expression IN expression {
      fun ctx ->
        let bs,ctx' = $2 ctx in
          TmLet(bs, $4 ctx, $6 ctx')
    }
  | BACKSLASH binder_list DOT expression {
      fun ctx ->
        let bs,ctx' = $2 ctx in
          TmAbs(bs, $4 ctx')
    }
  | CASE expression OF case_list {
      fun ctx -> TmCas($2 ctx, $4 ctx)
    }
  | QUOTE atomic_expression {
      fun ctx -> TmQuo($2 ctx)
    }
  | UNQUO atomic_expression {
      fun ctx -> TmUnq($2 ctx)
    }
;

case_list
  : pattern_case %prec below_VBAR { fun ctx -> [$1 ctx]       }
  | default_case %prec below_VBAR { fun ctx -> [$1 ctx]       }
  | pattern_case VBAR case_list   { fun ctx -> $1 ctx::$3 ctx }
;
pattern_case
  : CONST RARROW expression { fun ctx -> PatnCase($1,$3 ctx) }
  | IDENT RARROW expression { fun ctx ->
                                let s = $1 in
                                  if Const.is_symbol s then
                                    PatnCase(CnSym s,$3 ctx)
                                  else
                                    raise Parse_error        }
;
default_case
  : DDDOT RARROW expression { fun ctx -> DeflCase($3 ctx)    }
;

apply_expression
  : atomic_expression                  { $1 }
  | apply_expression atomic_expression { fun ctx -> TmApp($1 ctx, $2 ctx) }
;

atomic_expression
  : IDENT                       { fun ctx ->
                                    let s = $1 in
                                      if Const.is_symbol s then
                                        TmCon(CnSym s,[])
                                      else
                                        TmVar(Context.name2index ctx s) }
  | CONST                       { fun ctx -> TmCon($1,[]) }
  | atomic_expression DOT IDENT { fun ctx -> TmLbl($1 ctx, $3) }
  | LPAREN expression RPAREN    { $2 }
  | LPAREN RPAREN               { fun ctx -> Prims.nil }
  | LBRACE record RBRACE        { fun ctx -> TmRcd(check_record($2 ctx)) }
  | LBRACE RBRACE               { fun ctx -> Prims.nil }
  | LBRACKET list RBRACKET      { fun ctx -> $2 ctx }
  | LBRACKET RBRACKET           { fun ctx -> Prims.nil }
;
record
  : binder EQ expression             { fun ctx -> [$1,$3 ctx] }
  | binder EQ expression SEMI record { fun ctx -> ($1,$3 ctx)::$5 ctx}
;
list
  : expression_semi_list { fun ctx -> Prims.list(List.rev($1 ctx)) }
;
expression_semi_list
  : expression                           { fun ctx -> [$1 ctx] }
  | expression_semi_list SEMI expression { fun ctx -> $3 ctx::$1 ctx }
;
expression_comma_list
  : expression COMMA expression            { fun ctx -> [$3 ctx; $1 ctx] }
  | expression_comma_list COMMA expression { fun ctx -> $3 ctx::$1 ctx }
;
