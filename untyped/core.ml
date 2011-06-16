(** lambda�]���� *)

open Absyn
open Const
open Context

(*
 * delta_reduc: �Ȗ�
 *
 *)
let delta_reduc store tm =
  let rec flatten tm args = match tm with
    | TmCon(CSym d)  -> d,args
    | TmApp(tm1,tm2) -> flatten tm1 (tm2::args)
    | _ -> failwith "delta_reduc:flatten"
  in
  let d,args = flatten tm [] in
    Prims.dstr_apply d store args

(*
  v ::= z | m | \z.t | c v1 ... vk

  E ::= []
      | E t
      | v E
      | let z1 = v1 and z2 = v2 and ... and zi = Ei and ... zn = En in t

  (\z.t) v �� [z/v]t
  (\(z).t') t �� [z/t']t
  let z ::= t1 in t2 �� [z/t1]t2
  let z1 = v1 and z2 = t2 and ... zn = tn in t2 ��
      let z2 = t2 and ... zn = tn in [z/v]t2
*)
let rec eval_step ctx store tm =
  match tm with
    | TmApp(TmAbs(Eager,x,tm1),tm2) when is_value tm2 ->
        term_subst_top tm1 tm2         (* ��-reduc *)
    | TmApp(TmAbs(Lazy,x,tm1),tm2) ->
        term_subst_top tm1 tm2         (* ��-reduc *)
    | tm when is_dstr_value tm ->
        delta_reduc store tm      (* ��-reduc *)
    | TmApp(tm1,tm2) when is_value tm1 ->
        let tm2' = eval_step ctx store tm2 in
          TmApp(tm1, tm2')
    | TmApp(tm1,tm2) ->
        let tm1' = eval_step ctx store tm1 in
          TmApp(tm1', tm2)
    | TmLet(binds,tm2) ->
        trans_binds binds tm2
    | TmVar x ->
        let tm',o = Context.get_term ctx x in
          term_shift (x + o) tm'
    | _ -> failwith "stuck"
(*
  let x,y,z = 2,3,4
  let x1 = E1 and x2 = E2 and ... xn = En
    where y1 = E1 and and y2 = E2 and ... ym = Em
  in E'
  ===>
  ((...((\x1.\x2...\xn.E') E1) E2) ...) En)
*)
and trans_binds binds tm =
  List.fold_left (fun tm (_,_,tm') -> TmApp(tm,tm'))
    (List.fold_right (fun (s,x,_) tm -> TmAbs(s,x,tm)) binds tm)
    binds

let eval ctx store tm =
  let rec iter tm =
    if is_value tm then tm else iter (eval_step ctx store tm)
  in
    iter tm
