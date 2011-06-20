(** lambda評価器 *)
open Absyn
open Const
open Context
open Prims

exception Return_term of term
exception Ctor_parse of string
(*
 * (...((C t1) t2) ... tn)を
 *    C,[t1;t2;...;tn]の形にする
 *)
let flatten tm =
  let rec iter tm args = match tm with
    | TmCon c -> c,args
    | TmApp(tm1,tm2) -> iter tm1 (tm2::args)
    | _ -> assert false
  in
    iter tm []
(* flattenと逆 *)
let rec apply tm tms =
  match tms with
    | [] -> tm
    | tm'::tms' -> apply (TmApp(tm,tm')) tms'

(*
 * delta_reduc: δ簡約
 *)
let delta_reduc store tm =
  let d,args = flatten tm in
  let f = get_dtor_fun d in
    f store args

(*
 * case_reduc: case簡約
 * 
 * case c v1…vn of c1 -> t1 | c2 -> t2 | … | cm -> tm | ... -> t
 * →
 * - ti v1…vn    --- if c = c2
 * - t (c v1…vn) --- else
 *)
let case_reduc v cs =
  try
    let c,vs = flatten v in
      List.iter (
        function
          | PatnCase(c',tm) when c = c' -> raise (Return_term(apply tm vs))
          | DeflCase tm -> raise (Return_term(TmApp(tm,v)))
          | _ -> ()
      ) cs;
      (tm_error "*** no match case ***")
  with Return_term tm -> tm

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

let rec term_to_ctor ctx tm = match tm with
  | TmVar x        -> tm_var x
  | TmCon c        -> tm_con (con_to_ctor c)
  | TmMem m        -> tm_mem m
  | TmAbs(bs,tm)   -> tm_abs (binds_to_ctor bs) (term_to_ctor ctx tm)
  | TmApp(tm1,tm2) -> tm_app (term_to_ctor ctx tm1) (term_to_ctor ctx tm2)
  | TmLet(bs,tm1,tm2) ->
      tm_let (binds_to_ctor bs) (term_to_ctor ctx tm1) (term_to_ctor ctx tm2)
  | TmCas(tm1,cs)  -> tm_cas (term_to_ctor ctx tm1) (cases_to_ctor ctx cs)
  | TmTpl tms      -> tm_tpl (terms_to_ctor ctx tms)
  | TmRcd rs       -> tm_rcd (bdtms_to_ctor ctx rs)
  | TmLbl(tm,l)    -> tm_lbl (term_to_ctor ctx tm) l
  | TmQuo tm       -> tm_quo (term_to_ctor ctx tm)
and terms_to_ctor ctx tms = TmTpl(List.map (term_to_ctor ctx) tms)
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

let rec ctor_to_case case = match case with
  | TmApp(TmApp(TmCon(CnSym "ca_pat"),c),t) ->
      PatnCase(ctor_to_con c,ctor_to_term t)
  | TmApp(TmCon(CnSym "ca_dfl"),t) ->
      DeflCase(ctor_to_term t)
  | _ -> raise(Ctor_parse "ctor_to_case")
and ctor_to_cases cs = match cs with
  | TmTpl cs -> List.map ctor_to_case cs
  | c -> [ctor_to_case c]
and ctor_to_bdtm bt = match bt with
  | TmTpl[b;t] -> ctor_to_bind b,ctor_to_term t
  | _ -> raise(Ctor_parse "ctor_to_bdtm")
and ctor_to_bdtms bdtms = match bdtms with
  | TmTpl((TmTpl[b;t]::_) as bts) -> List.map ctor_to_bdtm bts
  | TmTpl[b;t] -> [ctor_to_bdtm bdtms]
  | _ -> raise(Ctor_parse "ctor_to_bdtms")
and ctor_to_term tm = match tm with
  | TmApp(TmCon(CnSym "tm_var"),TmCon(CnInt x)) -> TmVar x
  | TmApp(TmCon(CnSym "tm_con"),c) -> TmCon(ctor_to_con c)
  | TmApp(TmCon(CnSym "tm_mem"),TmCon(CnInt m)) -> TmMem m
  | TmApp(TmCon(CnSym "tm_abs"),TmTpl[bs;t]) ->
      TmAbs(ctor_to_binds bs,ctor_to_term tm)
  | TmApp(TmCon(CnSym "tm_app"),TmTpl[t1;t2]) ->
      TmApp(ctor_to_term t1,ctor_to_term t2)
  | TmApp(TmCon(CnSym "tm_let"),TmTpl[bs;t1;t2]) ->
      TmLet(ctor_to_binds bs,ctor_to_term t1,ctor_to_term t2)
  | TmApp(TmCon(CnSym "tm_cas"),TmTpl[t;cs]) ->
      TmCas(ctor_to_term t,ctor_to_cases cs)
  | TmApp(TmCon(CnSym "tm_tpl"),TmTpl ts) ->
      TmTpl(List.map ctor_to_term ts)
  | TmApp(TmCon(CnSym "tm_rcd"),rs) ->
      TmRcd(ctor_to_bdtms rs)
  | TmApp(TmCon(CnSym "tm_lbl"),TmTpl[t;TmCon(CnStr l)]) ->
      TmLbl(ctor_to_term t,l)
  | TmApp(TmCon(CnSym "tm_quo"),t) ->
      TmQuo(ctor_to_term t)
  | _ -> Prims.tm_error "*** ctor_to_term ***"

let _ = Prims.ctor_to_term_ref := ctor_to_term

(** 1ステップの評価を行う *)
(*
 * [構文]
 * 
 * v ::= x | m | \b1,…,bn.t | c v1…vn | v1,…,vn
 * t ::= t1 t 2
 *     | let b1,…,bn = t1 in t2
 *     | case t of c1 -> t1 | … | ... -> t
 *     | t1,…,tn
 * b ::= x | \x | _
 * E ::= []
 *     | E t | (\x.t) E | (\_.t) E | (\bs.t) T
 *     | case E of c1 -> t1 | … | ... -> t
 *     | (v1,…,Ei,…,tn)
 * T ::= []
 *     | E t | (\x.t) E | (\_.t) E | (\bs.t) T
 *     | case E of c1 -> t1 | … | ... -> t
 * 
 * [letの変換]
 * let b1,…,bn = t1 in t2 ⇒ (\b1,…,bn.t2) t1
 * 
 * [tuple適用の変換]
 * (\b1,…,bn.t) (t1,…,tn) ⇒ ((…(((\b1.(\b2.(….(\bn.t)…))) t1) t2)…) tn)
 * 
 * [β簡約規則]
 * (\_.t) v → v
 * (\x.t) v → t[x:=v]
 * (\\x.t) t' → t[x:=t']
 * 
 *)
let rec eval_step ctx store tm = match tm with
  | tm when is_value tm -> Prims.tm_error "*** no eval rule ***"
  | TmLet(bs,tm1,tm2) ->
      TmApp(TmAbs(bs,tm2),tm1)
  | TmApp(TmAbs([(Eager _|Wild) as b],tm2),tm1) ->
      if is_value tm1 then
        term_subst_top tm2 tm1
      else
        TmApp(TmAbs([b],tm2),eval_step ctx store tm1)
  | TmApp(TmAbs([Lazy _],tm2),tm1) ->
      term_subst_top tm2 tm1
  | TmApp(TmAbs(bs,tm2),TmTpl(tms)) ->
      if List.length bs == List.length tms then
        List.fold_left (fun tm tm' -> TmApp(tm,tm'))
          (List.fold_right (fun b tm -> TmAbs([b],tm)) bs tm2)
          tms
      else
        Prims.tm_error "*** tuple mismatch ***"
  | TmApp(TmAbs(bs,tm2),tm1) ->
      TmApp(TmAbs(bs,tm2),eval_step ctx store tm1)
  | tm when is_dtor_value tm ->
      delta_reduc store tm
  | TmApp(tm1,tm2) ->
      if is_value tm1 then
        TmApp(tm1,eval_step ctx store tm2)
      else
        TmApp(eval_step ctx store tm1,tm2)
  | TmVar x ->
      let tm',o = Context.get_term ctx x in
        term_shift (x + o) tm'
  | TmCas(tm1,cs) when is_ctor_value tm1 ->
      case_reduc tm1 cs
  | TmCas(tm1,cs) ->
      TmCas(eval_step ctx store tm1,cs)
  | TmTpl tms ->
      TmTpl(List.map
              (fun tm -> if is_value tm then tm else eval_step ctx store tm)
              tms)
  | TmRcd rcd ->
      TmRcd(List.map
              (fun (b,t) ->
                 match b with
                   | (Wild | Eager _) when is_value t -> b,t
                   | Lazy _ -> b,t
                   | _ -> b,eval_step ctx store t) rcd)
  | TmLbl(TmRcd rcd,l) -> (
      try
        snd(List.find
              (fun (b,t) ->
                 match b with
                   | (Eager x | Lazy x) when x = l -> true
                   | _ -> false) rcd)
      with Not_found -> tm_error "*** label not found ***"
    )
  | TmLbl(t1,l) ->
      TmLbl(eval_step ctx store t1,l)
  | TmQuo(t1) -> term_to_ctor ctx t1
  | _ -> tm_error "*** no eval rule ***"

(** 項が組になるまで評価を行う *)
let eval_tuple ctx store tm =
  let rec iter tm = match tm with
    | TmTpl _ -> tm
    | tm when is_value tm -> tm
    | _ -> iter (eval_step ctx store tm)
  in
    iter tm

(** 項が値になるまで評価を行う *)
let eval ctx store tm =
  let rec iter tm =
    if is_value tm then
      tm
    else
      iter (eval_step ctx store tm)
  in
    iter tm
