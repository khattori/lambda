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
%token FIX
%token CASE
%token OF
%token OVER
%token DOT
%token RARROW
%token DDDOT
%token COMMA
%token COLON
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
%token <int>           NTH
%token <string>        SEL
%token <string>        IDENT
%token <Const.t>       CONST
%token <Type.tyc>      TCONST

%nonassoc IN
%nonassoc LET
%nonassoc OF
%nonassoc below_VBAR
%left     VBAR
%nonassoc below_COMMA
%left     COMMA
%right    FIX
%right    RARROW
%nonassoc DOT

%start toplevel
%type <(Absyn.term, Type.t) Context.t -> Command.t> toplevel
%%

toplevel
  : command SEMI  { fun ctx -> $1 ctx       }
  | error SEMI    { raise Absyn.Parse_error }
  | EOF           { raise End_of_file       }
;

command
  : expression                    { fun ctx -> Eval($1 ctx 0)       }
  | DEF binder EQ expression      { fun ctx -> Defn($2,$4 ctx 0)    }
  | DATA IDENT ident_list EQ ctor_def_list
      {
        fun ctx ->
          let xs = List.rev $3 in
          let ctx' = Context.add_names ctx xs in
          Data($2,xs,List.rev($5 ctx'))
      }
  | USE IDENT                     { fun ctx -> Use $2                  }
  | /* empty */                   { fun ctx -> Noop                    }
;

ident_list
  : /* empty */      { []     }
  | ident_list IDENT { $2::$1 }
;
ctor_def_list
  : ctor_def                    { fun ctx -> [$1 ctx]       }
  | ctor_def_list VBAR ctor_def { fun ctx -> $3 ctx::$1 ctx }
;
ctor_def
  : IDENT type_expression_list
      { fun ctx -> $1,List.rev($2 ctx None) }
  | IDENT
      { fun ctx -> $1,[]                    }
;
type_expression_list
  : atomic_type_expression
      { fun ctx ropt -> [$1 ctx ropt] }
  | type_expression_list atomic_type_expression
      { fun ctx ropt -> $2 ctx ropt::$1 ctx ropt }
;
type_expression
  : atomic_type_expression { $1 }
  | atomic_type_expression RARROW type_expression
      { fun ctx ropt -> Type.TyCon(Type.TyCArr,[$1 ctx ropt;$3 ctx ropt]) }
  | type_expression_comma_list %prec below_COMMA
      {
        fun ctx ropt ->
          let ts = List.rev($1 ctx ropt) in
            Type.TyCon(Type.TyCTpl(List.length ts),ts)
      }
  | TCONST type_expression_list
      { fun ctx ropt -> Type.TyCon($1,List.rev($2 ctx ropt)) }
;

atomic_type_expression
  : IDENT  { fun ctx ropt -> match ropt with
               | None -> Type.TyVar(Context.name2index ctx $1)
               | Some(rank,tytbl_ref) ->
                   if List.mem_assoc $1 !tytbl_ref then
                     List.assoc $1 !tytbl_ref
                   else
                     let ty = Type.fresh_mvar rank in
                       tytbl_ref := ($1,ty)::!tytbl_ref;
                       ty
           }
  | TCONST { fun ctx ropt -> Type.TyCon($1,[]) }
  | LPAREN type_expression RPAREN { $2 }
  | LBRACE type_record RBRACE {
      fun ctx ropt ->
        let ls,tys = List.split($2 ctx ropt) in
          Type.TyCon(Type.TyCRcd ls,tys)
    }
;

type_expression_comma_list
  : type_expression COMMA type_expression
      { fun ctx ropt -> [$3 ctx ropt; $1 ctx ropt] }
  | type_expression_comma_list COMMA type_expression
      { fun ctx ropt -> $3 ctx ropt::$1 ctx ropt }
;

type_record
  : IDENT COLON type_expression
      { fun ctx ropt -> [$1,$3 ctx ropt]              }
  | IDENT COLON type_expression SEMI type_record
      { fun ctx ropt -> ($1,$3 ctx ropt)::$5 ctx ropt }
;

binder
  : WILDCARD        { Wild }
  | IDENT           { Eager $1 }
  | BACKSLASH IDENT { Lazy  $2 }
;

expression
  : apply_expression { $1 }
  | expression_comma_list %prec below_COMMA {
      fun ctx rank -> tm_tuple(List.rev($1 ctx rank))
    }
  | LET binder EQ expression IN expression {
      fun ctx rank ->
        let ctx' = Context.add_bind ctx $2 in
          TmLet(($2,None),$4 ctx (rank + 1),$6 ctx' rank)
    }
  | BACKSLASH binder DOT expression {
      fun ctx rank ->
        let ctx' = Context.add_bind ctx $2 in
          TmAbs(($2,None),$4 ctx' rank)
    }
  | FIX expression {
      fun ctx rank -> TmFix($2 ctx rank)
    }
  | CASE expression OF case_list {
      fun ctx rank -> TmCas($2 ctx rank, $4 ctx rank)
    }
  | OVER type_expression OF expression_vbar_list {
      fun ctx rank ->
        let tytbl_ref = ref [] in
          TmOvr($2 ctx (Some(rank,tytbl_ref)),List.rev($4 ctx rank))
    }
;

case_list
  : pattern_case %prec below_VBAR { fun ctx rank -> [$1 ctx rank]            }
  | default_case %prec below_VBAR { fun ctx rank -> [$1 ctx rank]            }
  | pattern_case VBAR case_list   { fun ctx rank -> $1 ctx rank::$3 ctx rank }
;
pattern_case
  : const_expression RARROW expression
      { fun ctx rank -> CsPat($1,$3 ctx rank) }
;
default_case
  : DDDOT RARROW expression { fun ctx rank -> CsDef($3 ctx rank)             }
;
const_expression
  : CONST const_expression_list { Const($1,List.rev $2) }
;
const_expression_list
  : /* empty */                 { [] }
  | const_expression_list CONST { Const($2,[])::$1 }
;

apply_expression
  : atomic_expression                  { $1 }
  | apply_expression atomic_expression
      { fun ctx rank -> TmApp($1 ctx rank,$2 ctx rank) }
;

atomic_expression
  : IDENT
      { fun ctx rank -> TmVar(Context.name2index ctx $1) }
  | CONST
      { fun ctx rank -> TmCon($1,[]) }
  | NTH
      { fun ctx rank -> TmCon(Const.CnNth $1,[]) }
  | SEL
      { fun ctx rank -> TmCon(Const.CnSel $1,[]) }
  | LPAREN expression RPAREN
      { $2 }
  | LBRACE record RBRACE
      { fun ctx rank -> tm_record($2 ctx rank) }
  | LBRACE expression_semi_list RBRACE
      { fun ctx rank -> Prims.list(List.rev($2 ctx rank)) }
  | LBRACE RBRACE
      { fun ctx rank -> Prims.nil  }
  | LPAREN RPAREN
      { fun ctx rank -> Prims.unit }
;
record
  : IDENT EQ expression
      { fun ctx rank -> [$1,$3 ctx rank] }
  | IDENT EQ expression SEMI record
      { fun ctx rank -> ($1,$3 ctx rank)::$5 ctx rank}
;
expression_semi_list
  : expression
      { fun ctx rank -> [$1 ctx rank] }
  | expression_semi_list SEMI expression
      { fun ctx rank -> $3 ctx rank::$1 ctx rank }
;
expression_comma_list
  : expression COMMA expression
      { fun ctx rank -> [$3 ctx rank; $1 ctx rank] }
  | expression_comma_list COMMA expression
      { fun ctx rank -> $3 ctx rank::$1 ctx rank }
;
expression_vbar_list
  : expression %prec below_VBAR
      { fun ctx rank -> [None,$1 ctx rank] }
  | expression_vbar_list VBAR expression
      { fun ctx rank -> (None,$3 ctx rank)::$1 ctx rank }
;
