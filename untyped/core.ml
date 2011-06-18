(** lambda�]���� *)

open Absyn
open Const
open Context


exception Return_term of term
(*
 * (...((C t1) t2) ... tn)��
 *    C,[t1;t2;...;tn]�̌`�ɂ���
 *)
let flatten tm =
  let rec iter tm args = match tm with
    | TmCon c -> c,args
    | TmApp(tm1,tm2) -> iter tm1 (tm2::args)
    | _ -> assert false
  in
    iter tm []
(* flatten�Ƌt *)
let rec apply tm tms =
  match tms with
    | [] -> tm
    | tm'::tms' -> apply (TmApp(tm,tm')) tms'

(*
 * delta_reduc: �Ȗ�
 *)
let delta_reduc store tm =
  let d,args = flatten tm in
    Prims.dstr_apply d store args

(*
 * case_reduc: case�Ȗ�
 * 
 * case c v1�cvn of c1 -> t1 | c2 -> t2 | �c | cm -> tm | ... -> t
 * ��
 * - ti v1�cvn    --- if c = c2
 * - t (c v1�cvn) --- else
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
      (Prims.tm_error "*** no match case ***")
  with Return_term tm -> tm

(*
 * [�\��]
 * 
 * v ::= x | m | \b1,�c,bn.t | c v1�cvn | v1,�c,vn
 * t ::= t1 t 2
 *     | let b1,�c,bn = t1 in t2
 *     | case t of c1 -> t1 | �c | ... -> t
 *     | t1,�c,tn
 * b ::= x | \x | _
 * E ::= []
 *     | E t | (\x.t) E | (\_.t) E | (\bs.t) T
 *     | case E of c1 -> t1 | �c | ... -> t
 *     | (v1,�c,Ei,�c,tn)
 * T ::= []
 *     | E t | (\x.t) E | (\_.t) E | (\bs.t) T
 *     | case E of c1 -> t1 | �c | ... -> t
 * 
 * [let�̕ϊ�]
 * let b1,�c,bn = t1 in t2 �� (\b1,�c,bn.t2) t1
 * 
 * [tuple�K�p�̕ϊ�]
 * (\b1,�c,bn.t) (t1,�c,tn) �� ((�c(((\b1.(\b2.(�c.(\bn.t)�c))) t1) t2)�c) tn)
 * 
 * [���Ȗ�K��]
 * (\_.t) v �� v
 * (\x.t) v �� t[x:=v]
 * (\\x.t) t' �� t[x:=t']
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
  | tm when is_dstr_value tm ->
      delta_reduc store tm
  | TmApp(tm1,tm2) when not (is_cstr_value tm1) ->
      if is_value tm1 then
        TmApp(tm1,eval_step ctx store tm2)
      else
        TmApp(eval_step ctx store tm1,tm2)
  | TmVar x ->
      let tm',o = Context.get_term ctx x in
        term_shift (x + o) tm'
  | TmCas(tm1,cs) when is_cstr_value tm1 ->
      case_reduc tm1 cs
  | TmCas(tm1,cs) ->
      TmCas(eval_step ctx store tm1,cs)
  | TmTpl tms ->
      TmTpl(List.map
              (fun tm -> if is_value tm then tm else eval_step ctx store tm)
              tms)
  | _ -> Prims.tm_error "*** no eval rule ***"

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
