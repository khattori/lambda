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
%token DOT
%token SEMI
%token BACKSLASH
%token LPAREN
%token RPAREN
%token EQ
%token WILDCARD
%token <string>        IDENT
%token <Absyn.const>   CONST

%nonassoc IN
%nonassoc LET
%nonassoc DOT

%start main toplevel
%type <(Absyn.term, Absyn.typ) Context.t -> Command.t list> main
%type <(Absyn.term, Absyn.typ) Context.t -> Command.t> toplevel
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
  | DEF binder EQ expression      { fun ctx ->
                                      let ctx' = Context.add_bind ctx $2 in
                                        Defn($2,$4 ctx),ctx'            }
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

binder
  : WILDCARD        { Wild }
  | IDENT           { Eager $1 }
  | BACKSLASH IDENT { Lazy  $2 }
;

expression
  : apply_expression { $1 }
  | LET binder EQ expression IN expression {
      fun ctx ->
        let ctx' = Context.add_bind ctx $2 in
          TmLet($2,None,$4 ctx,$6 ctx')
    }
  | BACKSLASH binder DOT expression {
      fun ctx ->
        let ctx' = Context.add_bind ctx $2 in
          TmAbs($2,None,$4 ctx')
    }
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
  | LPAREN expression RPAREN    { $2 }
  | LPAREN RPAREN               { fun ctx -> Prims.tm_unit }
;
