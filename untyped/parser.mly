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
%token DATA
%token CASE
%token OF
%token RARROW
%token DDDOT
%token DOT
%token COMMA
%token VBAR
%token SEMI
%token BACKSLASH
%token LPAREN
%token RPAREN
%token EQ
%token WILDCARD
%token <string>  IDENT
%token <Const.t> CONST
%token <int>     ARITY

%nonassoc IN
%nonassoc LET
%nonassoc OF
%nonassoc below_VBAR
%left     VBAR
%nonassoc below_COMMA
%left     COMMA
%right    RARROW
%nonassoc DOT


%start toplevel
%type <Absyn.term Context.t -> Absyn.command> toplevel
%%

/* トップレベル */
toplevel
  : command SEMI { $1 }
  | error SEMI   { raise Absyn.Parse_error }
  | EOF          { raise End_of_file }
;
command
  : expression                     { fun ctx -> Eval($1 ctx) }
  | DEF binder_list EQ expression  { fun ctx ->
                                       let bs,_ = $2 ctx in
                                         Defn(bs,$4 ctx)     }
  | DATA IDENT arity_option        { fun ctx -> Data($2,$3)  }
  | /* empty */                    { fun ctx -> Noop         }
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
  : binder                         { fun ctx -> [$1 ctx] }
  | binder_comma_list COMMA binder { fun ctx -> $3 ctx::$1 ctx }
;
binder
  : WILDCARD        { fun ctx -> Wild }
  | IDENT           { fun ctx -> Eager $1 }
  | BACKSLASH IDENT { fun ctx -> Lazy  $2 }
;

expression_comma_list
  : expression COMMA expression            { fun ctx -> [$3 ctx; $1 ctx] }
  | expression_comma_list COMMA expression { fun ctx -> $3 ctx::$1 ctx }
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
;

case_list
  : pattern_case %prec below_VBAR { fun ctx -> [$1 ctx]       }
  | default_case %prec below_VBAR { fun ctx -> [$1 ctx]       }
  | pattern_case VBAR case_list   { fun ctx -> $1 ctx::$3 ctx }
;
pattern_case : CONST RARROW expression { fun ctx -> PatnCase($1,$3 ctx) };
default_case : DDDOT RARROW expression { fun ctx -> DeflCase($3 ctx)    };

apply_expression
  : atomic_expression                  { $1 }
  | apply_expression atomic_expression { fun ctx -> TmApp($1 ctx, $2 ctx) }
;

atomic_expression
  : IDENT                    { fun ctx -> TmVar(Context.name2index ctx $1) }
  | CONST                    { fun ctx -> TmCon $1 }
  | LPAREN expression RPAREN { $2 }
  | LPAREN RPAREN            { fun ctx -> Prims.nil }
;
