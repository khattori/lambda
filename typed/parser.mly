%{
  open Absyn
  open Context
  open Command
%}

%token EOF
%token DATA
%token DEF
%token USE

%token LET
%token IN
%token CASE
%token OF
%token OVER
%token DOT
%token RARROW
%token DDDOT
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
%token <Type.tyc>      TCONST

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
%type <(Absyn.term, Type.typ) Context.t -> Command.t> toplevel
%%

toplevel
  : command SEMI  { fun ctx -> $1 ctx       }
  | error SEMI    { raise Absyn.Parse_error }
  | EOF           { raise End_of_file       }
;

command
  : expression                    { fun ctx -> Eval($1 ctx)            }
  | DEF binder_list EQ expression { fun ctx -> Defn($2,$4 ctx)         }
  | DATA IDENT ident_list EQ ctor_def_list
      {
        fun ctx ->
          let xs = List.rev $3 in
          let ctx' = Context.add_names ctx xs in
          Data($2,$3,$5 ctx')
      }
  | USE IDENT                     { fun ctx -> Use $2                  }
  | /* empty */                   { fun ctx -> Noop                    }
;

ident_list
  : /* empty */      { []     }
  | ident_list IDENT { $2::$1 }
;
ctor_def_list
  : ctor_def                    { fun ctx -> [$1 ctx]   }
  | ctor_def_list VBAR ctor_def { fun ctx -> $3 ctx::$1 ctx}
;
ctor_def
  : IDENT type_expression_list { fun ctx -> $1,List.rev($2 ctx) }
;
type_expression_list
  : /* empty */                                 { []     }
  | type_expression_list atomic_type_expression { $2::$1 }
;
type_expression
  : atomic_type_expression { $1 }
  | atomic_type_expression RARROW type_expression
      { fun ctx -> TyCon(TyCArr,[$1 ctx;$3 ct]) }
  | TCONST type_expression_list
      { fun ctx -> TyCon($1,List.rev($2 ctx)) }
;

atomic_type_expression
  : IDENT { fun ctx -> TyVar(Context.name2index $1) }
  | LPAREN type_expression RPAREN { $2 }
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
        let ctx' = Context.add_bind ctx $2 in
          TmLet($2,None,$4 ctx,$6 ctx')
    }
  | BACKSLASH binder_list DOT expression {
      fun ctx ->
        let ctx' = Context.add_bind ctx $2 in
          TmAbs($2,None,$4 ctx')
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
pattern_case
  : CONST RARROW expression { fun ctx -> PatnCase($1,$3 ctx) }
  | IDENT RARROW expression { fun ctx ->
                                let s = $1 in
                                  PatnCase(CnSym s,$3 ctx)   }
;
default_case
  : DDDOT RARROW expression { fun ctx -> DeflCase($3 ctx)    }
;

apply_expression
  : atomic_expression                  { $1 }
  | apply_expression atomic_expression { fun ctx -> TmApp($1 ctx, $2 ctx) }
;

atomic_expression
  : IDENT                       { fun ctx -> TmVar(Context.name2index ctx $1) }
  | CONST                       { fun ctx -> TmCon($1,[]) }
  | LPAREN expression RPAREN    { $2 }
  | LBRACE record RBRACE        { fun ctx -> TmRcd(check_record($2 ctx)) }
  | LBRACE list RBRACE          { fun ctx -> $2 ctx }
  | LBRACE RBRACE               { fun ctx -> Prims.nil }
  | LPAREN RPAREN               { fun ctx -> Prims.tm_unit }
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
