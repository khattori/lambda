(** メタプログラミングのための処理 *)

open Absyn
open Const
open Context
open Prims

exception Ctor_parse of string

(* 抽象構文木のデータ定義 *)
let _absyn_table = [
  (* 構文木 *)
  (* type tm =      *)
  ( "tm_var", 1); (* | TmVar of int *)
  ( "tm_con", 2); (* | TmCon of const * term list *)
  ( "tm_mem", 1); (* | TmMem of int    *)
  ( "tm_abs", 2); (* | TmAbs of binder list * term *)
  ( "tm_app", 2); (* | TmApp of term * term *)
  ( "tm_let", 3); (* | TmLet of binder list * term * term *)
  ( "tm_cas", 2); (* | TmCas of term * case list *)
  ( "tm_tpl", 1); (* | TmTpl of term list *)
  ( "tm_rcd", 1); (* | TmRcd of (binder * term) list *)
  ( "tm_lbl", 2); (* | TmLbl of term * string *)
  ( "tm_quo", 1); (* | TmQuo of term *)
  ( "tm_unq", 1); (* | TmUnq of term *)
  (* and case = PatnCase of Const.t * term | DeflCase of term *)
  ( "ca_pat", 2);
  ( "ca_dfl", 1);
  (* 定数            type t =          *)
  ( "cn_int", 1); (* | CnInt of int    *)
  ( "cn_rea", 1); (* | CnRea of float  *)
  ( "cn_str", 1); (* | CnStr of string *)
  ( "cn_sym", 1); (* | CnSym of string *)
  ( "bn_wild",  0);
  ( "bn_eager", 1);
  ( "bn_lazy",  1);
]

let _ =
  List.iter (fun (s,arity) -> Const.add_ctor s arity) _absyn_table

(* 変数束縛のデータ表現の定義 *)
let bn_wild    = tm_sym "bn_wild" []
let bn_eager x = tm_sym "bn_eager" [tm_str x]
let bn_lazy  x = tm_sym "bn_lazy"  [tm_str x]
(* 定数項のデータ表現の定義 *)
let cn_int n   = tm_sym "cn_int" [tm_int n]
let cn_rea r   = tm_sym "cn_rea" [tm_rea r]
let cn_str s   = tm_sym "cn_str" [tm_str s]
let cn_sym s   = tm_sym "cn_sym" [tm_str s]
(* 項のデータ表現の定義 *)
let tm_var x        = tm_sym "tm_var" [tm_str x]
let tm_con c vs     = tm_sym "tm_con" [c;vs]
let tm_mem m        = tm_sym "cn_mem" [tm_int m]
let tm_abs bs t     = tm_sym "tm_abs" [bs;t]
let tm_app t1 t2    = tm_sym "tm_app" [t1;t2]
let tm_let bs t1 t2 = tm_sym "tm_let" [bs;t1;t2]
let tm_cas t cs     = tm_sym "tm_cas" [t;cs]
let tm_tpl ts       = tm_sym "tm_tpl" [ts]
let tm_rcd rs       = tm_sym "tm_rcd" [rs]
let tm_lbl t l      = tm_sym "tm_lbl" [t;tm_str l]
let tm_quo t        = tm_sym "tm_quo" [t]
let tm_unq t        = tm_sym "tm_unq" [t]
(* case節のデータ表現の定義 *)
let ca_pat c t = tm_sym "ca_pat" [c;t]
let ca_dfl t   = tm_sym "ca_dfl" [t]


(* 変数束縛からデータ表現を生成 *)
let bind_to_ctor b = match b with
  | Wild    -> bn_wild
  | Eager x -> bn_eager x
  | Lazy x  -> bn_lazy  x
let binds_to_ctor bs = match bs with
  | [b] -> bind_to_ctor b
  | bs  -> TmTpl(List.map (fun b -> bind_to_ctor b) bs)
(* 定数項からデータ表現を生成 *)
let con_to_ctor c = match c with
  | CnInt n -> cn_int n
  | CnRea r -> cn_rea r
  | CnStr s -> cn_str s
  | CnSym s -> cn_sym s

(** 項をプログラムで扱えるデータ構造に変換 *)
let rec term_to_ctor ctx = function
  | TmVar x        -> tm_var (Context.index2name ctx x)
  | TmCon(c,vs)    -> tm_con (con_to_ctor c) (terms_to_ctor ctx vs)
  | TmMem m        -> tm_mem m
  | TmAbs(bs,tm)   ->
      let ctx' = Context.add_binds ctx bs in
        tm_abs (binds_to_ctor bs) (term_to_ctor ctx' tm)
  | TmApp(tm1,tm2) -> tm_app (term_to_ctor ctx tm1) (term_to_ctor ctx tm2)
  | TmLet(bs,tm1,tm2) ->
      let ctx' = Context.add_binds ctx bs in
        tm_let
          (binds_to_ctor bs) (term_to_ctor ctx tm1) (term_to_ctor ctx' tm2)
  | TmCas(tm1,cs)  -> tm_cas (term_to_ctor ctx tm1) (cases_to_ctor ctx cs)
  | TmTpl tms      -> tm_tpl (terms_to_ctor ctx tms)
  | TmRcd rs       -> tm_rcd (bdtms_to_ctor ctx rs)
  | TmLbl(tm,l)    -> tm_lbl (term_to_ctor ctx tm) l
  | TmQuo tm       -> tm_quo (term_to_ctor ctx tm)
  | TmUnq tm       -> tm_unq (term_to_ctor ctx tm)
and terms_to_ctor ctx = function
  | [tm] -> term_to_ctor ctx tm
  | tms -> TmTpl(List.map (term_to_ctor ctx) tms)
and cases_to_ctor ctx = function
  | [c] -> case_to_ctor ctx c
  | cs -> TmTpl(List.map (case_to_ctor ctx) cs)
and case_to_ctor ctx = function
  | PatnCase(c,t) -> ca_pat (con_to_ctor c) (term_to_ctor ctx t)
  | DeflCase t    -> ca_dfl (term_to_ctor ctx t)
and bdtm_to_ctor ctx (b,t) =
  TmTpl[bind_to_ctor b;term_to_ctor ctx t]
and bdtms_to_ctor ctx = function
  | [bt] -> bdtm_to_ctor ctx bt
  | bdtms -> TmTpl(List.map (bdtm_to_ctor ctx) bdtms)

(* データ表現から定数項への変換 *)
let ctor_to_con c = match c with
  | TmCon(CnSym "cn_int",[TmCon(CnInt _ as n,_)]) -> n
  | TmCon(CnSym "cn_rea",[TmCon(CnRea _ as r,_)]) -> r
  | TmCon(CnSym "cn_str",[TmCon(CnStr _ as s,_)]) -> s
  | TmCon(CnSym "cn_sym",[TmCon(CnStr s,     _)]) -> CnSym s
  | _ -> raise(Ctor_parse "ctor_to_con")
let ctor_to_bind b = match b with
  | TmCon(CnSym "bn_wild", [])                 -> Wild
  | TmCon(CnSym "bn_eager",[TmCon(CnStr x,_)]) -> Eager x
  | TmCon(CnSym "bn_lazy", [TmCon(CnStr x,_)]) -> Lazy x
  | _ -> raise(Ctor_parse "ctor_to_bind")
let ctor_to_binds bs = match bs with
  | TmTpl bs -> List.map ctor_to_bind bs
  | b        -> [ctor_to_bind b]

(** データ構造を項に変換 *)
let rec ctor_to_term ctx = function
  | TmCon(CnSym "tm_var",[TmCon(CnStr x,[])]) ->
      TmVar(Context.name2index ctx x)
  | TmCon(CnSym "tm_con",[c;vs]) ->
      TmCon(ctor_to_con c,ctor_to_terms ctx vs)
  | TmCon(CnSym "tm_mem",[TmCon(CnInt m,[])]) ->
      TmMem m
  | TmCon(CnSym "tm_abs",[bs;t]) ->
      let bs' = ctor_to_binds bs in
      let ctx' = Context.add_binds ctx bs' in
        TmAbs(bs',ctor_to_term ctx' t)
  | TmCon(CnSym "tm_app",[t1;t2]) ->
      TmApp(ctor_to_term ctx t1,ctor_to_term ctx t2)
  | TmCon(CnSym "tm_let",[bs;t1;t2]) ->
      let bs' = ctor_to_binds bs in
      let ctx' = Context.add_binds ctx bs' in
        TmLet(bs',ctor_to_term ctx t1,ctor_to_term ctx' t2)
  | TmCon(CnSym "tm_cas",[t;cs]) ->
      TmCas(ctor_to_term ctx t,ctor_to_cases ctx cs)
  | TmCon(CnSym "tm_tpl",[ts]) ->
      TmTpl(ctor_to_terms ctx ts)
  | TmCon(CnSym "tm_rcd",[rs]) ->
      TmRcd(ctor_to_bdtms ctx rs)
  | TmCon(CnSym "tm_lbl",[t;TmCon(CnStr l,[])]) ->
      TmLbl(ctor_to_term ctx t,l)
  | TmCon(CnSym "tm_quo",[t]) ->
      TmQuo(ctor_to_term ctx t)
  | TmCon(CnSym "tm_unq",[t]) ->
      TmUnq(ctor_to_term ctx t)
  | _ -> Prims.tm_error "*** ctor_to_term ***"
and ctor_to_terms ctx = function
  | TmTpl ts -> List.map (ctor_to_term ctx) ts
  | tm -> [ctor_to_term ctx tm]
and ctor_to_case ctx = function
  | TmCon(CnSym "ca_pat",[c;t]) ->
      PatnCase(ctor_to_con c,ctor_to_term ctx t)
  | TmCon(CnSym "ca_dfl",[t]) ->
      DeflCase(ctor_to_term ctx t)
  | _ -> raise(Ctor_parse "ctor_to_case")
and ctor_to_cases ctx = function
  | TmTpl cs -> List.map (ctor_to_case ctx) cs
  | c -> [ctor_to_case ctx c]
and ctor_to_bdtm ctx = function
  | TmTpl[b;t] -> ctor_to_bind b,ctor_to_term ctx t
  | _ -> raise(Ctor_parse "ctor_to_bdtm")
and ctor_to_bdtms ctx = function
  | TmTpl((TmTpl[b;t]::_) as bts) -> List.map (ctor_to_bdtm ctx) bts
  | bdtm -> [ctor_to_bdtm ctx bdtm]
