(** メタプログラミングのための処理 *)

open Absyn
open Const
open Context
open Prims

exception Ctor_parse of string

let bind_to_ctor b = match b with
  | Wild -> bn_wild
  | Eager x -> bn_eager x
  | Lazy x -> bn_lazy x
let binds_to_ctor bs = match bs with
  | [b] -> bind_to_ctor b
  | bs -> TmTpl(List.map (fun b -> bind_to_ctor b) bs)
let con_to_ctor c = match c with
  | CnInt n -> cn_int n
  | CnRea r -> cn_rea r
  | CnStr s -> cn_str s
  | CnSym s -> cn_sym s

(** 項をプログラムで扱えるデータ構造に変換 *)
let rec term_to_ctor ctx tm = match tm with
  | TmVar x        -> tm_var (Context.index2name ctx x)
  | TmCon c        -> tm_con (con_to_ctor c)
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
  | TmTpl tms      -> tm_tpl (TmTpl(List.map (term_to_ctor ctx) tms))
  | TmRcd rs       -> tm_rcd (bdtms_to_ctor ctx rs)
  | TmLbl(tm,l)    -> tm_lbl (term_to_ctor ctx tm) l
  | TmQuo tm       -> tm_quo (term_to_ctor ctx tm)
  | TmUnq tm       -> tm_unq (term_to_ctor ctx tm)
and cases_to_ctor ctx cs  = match cs with
  | [c] -> case_to_ctor ctx c
  | cs -> TmTpl(List.map (case_to_ctor ctx) cs)
and case_to_ctor ctx case = match case with
  | PatnCase(c,t) -> ca_pat (con_to_ctor c) (term_to_ctor ctx t)
  | DeflCase t    -> ca_dfl (term_to_ctor ctx t)
and bdtm_to_ctor ctx (b,t) = TmTpl[bind_to_ctor b;term_to_ctor ctx t]
and bdtms_to_ctor ctx rcd = match rcd with
  | [bt] -> bdtm_to_ctor ctx bt
  | bdtms -> TmTpl(List.map (bdtm_to_ctor ctx) bdtms)

let ctor_to_con c = match c with
  | TmApp(TmCon(CnSym "cn_int"),TmCon(CnInt _ as n)) -> n
  | TmApp(TmCon(CnSym "cn_rea"),TmCon(CnRea _ as r)) -> r
  | TmApp(TmCon(CnSym "cn_str"),TmCon(CnStr _ as s)) -> s
  | TmApp(TmCon(CnSym "cn_sym"),TmCon(CnSym _ as s)) -> s
  | _ -> raise(Ctor_parse "ctor_to_con")
let ctor_to_bind b = match b with
  | TmCon(CnSym "bn_wild") -> Wild
  | TmApp(TmCon(CnSym "bn_eager"),TmCon(CnStr x)) -> Eager x
  | TmApp(TmCon(CnSym "bn_lazy"),TmCon(CnStr x)) -> Lazy x
  | _ -> raise(Ctor_parse "ctor_to_bind")
let ctor_to_binds bs = match bs with
  | TmTpl bs -> List.map ctor_to_bind bs
  | b -> [ctor_to_bind b]

(** データ構造を項に変換 *)
let rec ctor_to_term ctx tm = match tm with
  | TmApp(TmCon(CnSym "tm_var"),TmCon(CnStr x)) ->
      TmVar(Context.name2index ctx x)
  | TmApp(TmCon(CnSym "tm_con"),c) -> TmCon(ctor_to_con c)
  | TmApp(TmCon(CnSym "tm_mem"),TmCon(CnInt m)) -> TmMem m
  | TmApp(TmCon(CnSym "tm_abs"),TmTpl[bs;t]) ->
      let bs' = ctor_to_binds bs in
      let ctx' = Context.add_binds ctx bs' in
        TmAbs(bs',ctor_to_term ctx' t)
  | TmApp(TmCon(CnSym "tm_app"),TmTpl[t1;t2]) ->
      TmApp(ctor_to_term ctx t1,ctor_to_term ctx t2)
  | TmApp(TmCon(CnSym "tm_let"),TmTpl[bs;t1;t2]) ->
      let bs' = ctor_to_binds bs in
      let ctx' = Context.add_binds ctx bs' in
        TmLet(bs',ctor_to_term ctx t1,ctor_to_term ctx' t2)
  | TmApp(TmCon(CnSym "tm_cas"),TmTpl[t;cs]) ->
      TmCas(ctor_to_term ctx t,ctor_to_cases ctx cs)
  | TmApp(TmCon(CnSym "tm_tpl"),TmTpl ts) ->
      TmTpl(List.map (ctor_to_term ctx) ts)
  | TmApp(TmCon(CnSym "tm_rcd"),rs) ->
      TmRcd(ctor_to_bdtms ctx rs)
  | TmApp(TmCon(CnSym "tm_lbl"),TmTpl[t;TmCon(CnStr l)]) ->
      TmLbl(ctor_to_term ctx t,l)
  | TmApp(TmCon(CnSym "tm_quo"),t) ->
      TmQuo(ctor_to_term ctx t)
  | TmApp(TmCon(CnSym "tm_unq"),t) ->
      TmUnq(ctor_to_term ctx t)
  | _ -> Prims.tm_error "*** ctor_to_term ***"
and ctor_to_case ctx case = match case with
  | TmApp(TmApp(TmCon(CnSym "ca_pat"),c),t) ->
      PatnCase(ctor_to_con c,ctor_to_term ctx t)
  | TmApp(TmCon(CnSym "ca_dfl"),t) ->
      DeflCase(ctor_to_term ctx t)
  | _ -> raise(Ctor_parse "ctor_to_case")
and ctor_to_cases ctx cs = match cs with
  | TmTpl cs -> List.map (ctor_to_case ctx) cs
  | c -> [ctor_to_case ctx c]
and ctor_to_bdtm ctx bt = match bt with
  | TmTpl[b;t] -> ctor_to_bind b,ctor_to_term ctx t
  | _ -> raise(Ctor_parse "ctor_to_bdtm")
and ctor_to_bdtms ctx bdtms = match bdtms with
  | TmTpl((TmTpl[b;t]::_) as bts) -> List.map (ctor_to_bdtm ctx) bts
  | TmTpl[b;t] -> [ctor_to_bdtm ctx bdtms]
  | _ -> raise(Ctor_parse "ctor_to_bdtms")
