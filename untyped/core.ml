(** lambda•]‰¿Ší *)

open Absyn
open Const
open Context

(*
 * (...((C t1) t2) ... tn)‚ğ
 *    C,[t1;t2;...;tn]‚ÌŒ`‚É‚·‚é
 *)
let flatten tm =
  let rec iter tm args = match tm with
    | TmCon c -> c,args
    | TmApp(tm1,tm2) -> iter tm1 (tm2::args)
    | _ -> assert false
  in
    iter tm []
(* flatten‚Æ‹t *)
let rec apply tm tms =
  match tms with
    | [] -> tm
    | tm'::tms' -> apply (TmApp(tm,tm')) tms'

(*
 * delta_reduc: ƒÂŠÈ–ñ
 *
 *)
let delta_reduc store tm =
  let d,args = flatten tm in
    Prims.dstr_apply d store args

(*
  v ::= z | m | \z.t | c v1 ... vk

  E ::= []
      | E t
      | v E
      | let z1 = v1 and z2 = v2 and ... and zi = Ei and ... zn = En in t

  (\z.t) v ¨ [z/v]t
  (\(z).t') t ¨ [z/t']t
  let z ::= t1 in t2 ¨ [z/t1]t2
  let z1 = v1 and z2 = t2 and ... zn = tn in t2 ¨
      let z2 = t2 and ... zn = tn in [z/v]t2
*)
let rec eval_step ctx store tm =
  match tm with
    | TmApp(TmAbs(Eager,x,tm1),tm2) when is_value tm2 ->
        term_subst_top tm1 tm2         (* ƒÀ-reduc *)
    | TmApp(TmAbs(Lazy,x,tm1),tm2) ->
        term_subst_top tm1 tm2         (* ƒÀ-reduc *)
    | tm when is_dstr_value tm ->
        delta_reduc store tm      (* ƒÂ-reduc *)
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
    | TmCas(tm1,cs,tm2opt) when is_cstr_value tm1 ->
        let c,vs = flatten tm1 in (
            try
              let tm' = List.assoc c cs in
                apply tm' vs
            with
                Not_found -> (
                  match tm2opt with
                    | Some tm' -> TmApp(tm',tm1)
                    | None -> Prims.tm_error "*** no match case ***"
                )
          )
    | TmCas(tm1,cs,tm2opt) ->
        TmCas(eval_step ctx store tm1,cs,tm2opt)
    | _ ->
        Prims.tm_error "*** no eval rule ***"
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
