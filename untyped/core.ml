(** lambda評価器 *)
open Absyn
open Const
open Context
open Prims

exception Return_term of term
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
    dtor_apply d store args

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
let binds_to_ctor bs =
  TmTpl(List.map (fun b -> bind_to_ctor b) bs)

let con_to_ctor c = match c with
  | CInt n  -> cn_int n
  | CReal r -> cn_rea r
  | CStr s  -> cn_str s
  | CSym s  -> cn_sym s
  | CMem m  -> cn_mem m

let rec term_to_ctor ctx tm = match tm with
  | TmVar x -> tm_var x
  | TmCon c -> tm_con(con_to_ctor c)
  | TmAbs(bs,tm) ->
      tm_abs (binds_to_ctor bs) (term_to_ctor ctx tm)
  | TmApp(tm1,tm2) ->
      tm_app (term_to_ctor ctx tm1) (term_to_ctor ctx tm2)
  | TmLet(bs,tm1,tm2) ->
      tm_let (binds_to_ctor bs) (term_to_ctor ctx tm1) (term_to_ctor ctx tm2)
  | TmCas(tm1,cs) ->
      tm_cas (term_to_ctor ctx tm1) (cases_to_ctor ctx cs)
  | TmTpl tms -> tm_tpl (terms_to_ctor ctx tms)
  | TmRcd rs -> tm_rcd (record_to_ctor ctx rs)
  | TmLbl(tm,l) -> tm_lbl (term_to_ctor ctx tm) l
  | TmQuo tm -> tm_quo (term_to_ctor ctx tm)
and terms_to_ctor ctx tms =
  TmTpl(List.map (term_to_ctor ctx) tms)
and cases_to_ctor ctx cs =
  TmTpl(List.map (case_to_ctor ctx) cs)
and case_to_ctor ctx case = match case with
  | PatnCase(c,t) -> ca_pat (con_to_ctor c) (term_to_ctor ctx t)
  | DeflCase t -> ca_dfl (term_to_ctor ctx t)
and record_to_ctor ctx rcd =
  TmTpl(List.map (fun (b,t) -> TmTpl([bind_to_ctor b;term_to_ctor ctx t])) rcd)

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
  | TmLet(bs,tm1,tm2) ->
      TmApp(TmAbs(bs,tm2),tm1)
  | TmApp(TmAbs(bs,tm2),TmTpl(tms)) ->
      if List.length bs == List.length tms then
        List.fold_left (fun tm tm' -> TmApp(tm,tm'))
          (List.fold_right (fun b tm -> TmAbs([b],tm)) bs tm2)
          tms
      else
        Prims.tm_error "*** tuple mismatch ***"
  | TmApp(TmAbs([(Eager _|Wild) as b],tm2),tm1) ->
      if is_value tm1 then
        term_subst_top tm2 tm1
      else
        TmApp(TmAbs([b],tm2),eval_step ctx store tm1)
  | TmApp(TmAbs([Lazy _],tm2),tm1) ->
      term_subst_top tm2 tm1
  | TmApp(TmAbs(bs,tm2),tm1) ->
      TmApp(TmAbs(bs,tm2),eval_step ctx store tm1)
  | tm when is_dtor_value tm ->
      delta_reduc store tm
  | TmApp(tm1,tm2) when not (is_ctor_value tm1) ->
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

let eval_tuple ctx store tm =
  let rec iter tm = match tm with
    | TmTpl _ -> tm
    | tm when is_value tm -> tm
    | _ -> iter (eval_step ctx store tm)
  in
    iter tm

let eval ctx store tm =
  let rec iter tm =
    if is_value tm then
      tm
    else
      iter (eval_step ctx store tm)
  in
    iter tm
