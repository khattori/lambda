(** lambda評価器 *)
open Absyn
open Const
open Context
open Prims

exception Return_term of term


(* 
 * make_apps: 入れ子になったλ適用の項を作る
 * 
 * E E1...En を ((...((E E1) E2) ...) En)に変換
 * 
 *)
let rec make_apps tm tms =
  match tms with
    | [] -> tm
    | tm'::tms' -> make_apps (TmApp(tm,tm')) tms'

(*
 * delta_reduc: δ簡約
 *)
let delta_reduc store d vs =
  (get_dtor_fun d) store vs

(*
 * case_reduc: case簡約
 * 
 * case c v1…vn of c1 -> t1 | c2 -> t2 | … | cm -> tm | ... -> t
 * →
 * - ti v1…vn    --- if c = c2
 * - t (c v1…vn) --- else
 *)
let case_reduc v cs =
  let find_case c vs =
    try
      List.iter (
        function
          | PatnCase(c',tm) when c = c' -> raise (Return_term(make_apps tm vs))
          | DeflCase tm -> raise (Return_term(TmApp(tm,v)))
          | _ -> ()
      ) cs;
      (tm_error "*** no match case ***")
    with Return_term tm -> tm
  in
    match v with
      | TmCon(c,vs) when Const.arity c == List.length vs -> find_case c vs
      | _ -> Prims.tm_error "*** invalid case value ***"

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
let rec eval_step ctx store tm =
  match tm with
  | tm when is_value tm ->
      Prims.tm_error "*** no eval rule ***"
  | TmCon(CnSym d,vs) ->
      delta_reduc store d vs
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
  | TmApp(TmCon(c,vs),tm1) when is_value tm1 ->
      if Const.arity c > List.length vs then
        TmCon(c,vs@[tm1])
      else
        Prims.tm_error "*** no eval rule ***"
  | TmApp(tm1,tm2) ->
      if is_value tm1 then
        TmApp(tm1,eval_step ctx store tm2)
      else
        TmApp(eval_step ctx store tm1,tm2)
  | TmVar x ->
      let tm',o = Context.get_term ctx x in
        term_shift (x + o) tm'
  | TmCas(tm1,cs) when is_value tm1 ->
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
  | TmQuo(t1) ->
      Meta.term_to_ctor ctx t1
  | TmUnq(t1) when is_value t1 ->
      Meta.ctor_to_term ctx t1
  | TmUnq(t1) ->
      TmUnq(eval_step ctx store t1)
  | _ -> Prims.tm_error "*** no eval rule ***"

(** 項が組になるまで評価を行う *)
let eval_tuple ctx store tm =
  let rec iter tm =
(*    Printf.printf "---> %s\n" (Absyn.to_string ctx tm); *)
    match tm with
      | TmTpl _ -> tm
      | tm ->
          if is_value tm then
            tm
          else
            iter (eval_step ctx store tm)
  in
    iter tm

(** 項が値になるまで評価を行う *)
let eval ctx store tm =
  let rec iter tm =
(*    Printf.printf "---> %s\n" (Absyn.to_string ctx tm); *)
    if is_value tm then
      tm
    else
      iter (eval_step ctx store tm)
  in
    iter tm
