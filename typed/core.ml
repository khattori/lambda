(** lambda評価器 *)
open Absyn
open Const
open Context
open Prims

(*
 * delta_reduc: δ簡約
 *)
let delta_reduc store d vs =
  (get_dtor_fun d) store vs

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
  | TmLet(b,topt,tm1,tm2) ->
      TmApp(TmAbs(b,topt,tm2),tm1)
  | TmApp(TmAbs((Eager _|Wild) as b,topt,tm2),tm1) ->
      if is_value tm1 then
        term_subst_top tm2 tm1
      else
        TmApp(TmAbs(b,topt,tm2),eval_step ctx store tm1)
  | TmApp(TmAbs(Lazy _,_,tm2),tm1) ->
      term_subst_top tm2 tm1
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
  | _ -> Prims.tm_error "*** no eval rule ***"

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
