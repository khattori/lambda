(** lambda評価器 *)
open Absyn
open Const
open Context
open Prims

exception Unify_fail of link ref list
exception Occur_check of link ref list

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
  | TmApp(TmAbs((Eager _|Wild) as b,topt,tm1),tm2) ->
      if is_value tm2 then
        term_subst_top tm2 tm1
      else
        TmApp(TmAbs(b,topt,tm1),eval_step ctx store tm2)
  | TmApp(TmAbs(Lazy _,_,tm1),tm2) ->
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
  | TmTpp(TmTbs(x,tm1),ty2) ->
      tytm_subst_top ty2 tm1
  | TmTpp(tm1,ty2) ->
      TmTpp(eval_step ctx store tm1,ty2)
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

let typ_of_const c vs =
  match c with
    | CnInt _ -> tint
    | CnRea _ -> treal
    | CnStr _ -> tstring
    | CnSym s -> Prims.get_const_type s

let generalize rank tm ty =
  let id_ref = ref 0 in
  let ts_ref = ref [] in
  let rec walk = function
    | TyMva({contents=NoLink(r,_)} as link) when r >= rank ->
        let id = !id_ref in
        let ty = TyVar id in
          ts_ref := Printf.sprintf "t%d" id::!ts_ref;
          link := link_to ty r;
          incr id_ref;
          ty
    | TyMva{contents=LinkTo{typ=ty}} -> walk ty
    | TyCon(tc,tys) -> TyCon(tc,List.map walk tys)
    | ty -> ty
  in
  let ty' = walk ty in (
      List.fold_right (fun t tm -> TmTbs(t,tm)) !ts_ref tm,
      List.fold_right (fun t ty -> TyAll(t,ty)) !ts_ref ty'
    )

let instanciate rank tm ty =
  let tm_ref = ref tm in
  let rec walk ty = match ty with
    | TyMva{contents=NoLink _} -> ty
    | TyMva{contents=LinkTo{typ=ty}} -> walk ty
    | TyCon(tc,ts) -> TyCon(tc,List.map walk ts)
    | TyAll(x,ty) ->
        let mvar = fresh_mvar rank in
          tm_ref := TmTpp(!tm_ref,mvar);
          walk (typ_subst_top mvar ty)
    | _ -> assert false (* 自由なTyVarが出現した *)
  in
    !tm_ref,walk ty

let unify lrefs ty1 ty2 =
  let rec walk ty1 ty2 =
    let ty1 = repr ty1 and ty2 = repr ty2 in
      if ty1 == ty2 then () else
        match ty1,ty2 with
          | TyMva({contents=NoLink(r1,_)} as l1),
            TyMva({contents=NoLink(r2,_)} as l2) ->
              if r1 > r2 then (
                l1 := link_to ty2 r1;
                lrefs := l1::!lrefs
              ) else (
                l2 := link_to ty1 r2;
                lrefs := l2::!lrefs
              )
          | TyMva({contents=NoLink(r1,_)} as l1), _ ->
              l1 := link_to ty2 r1;
              lrefs := l1::!lrefs
          | _, TyMva({contents=NoLink(r2,_)} as l2) ->
              l2 := link_to ty1 r2;
              lrefs := l2::!lrefs
          | TyCon(tc1,tys1),TyCon(tc2,tys2) when tc1 = tc2 ->
              List.iter2 walk tys1 tys2
          | _, _ ->
              raise (Unify_fail !lrefs)
  in
    walk ty1 ty2

let occur_check lrefs ty =
  let visiting = mark() and visited = mark() in
  let rec walk ty =
    match ty with
      | TyMva{contents=LinkTo{mark=mk}} when mk == visiting ->
          raise (Occur_check !lrefs)
      | TyMva{contents=LinkTo{mark=mk}} when mk == visited -> ()
      | TyMva{contents=LinkTo({typ=ty} as node)} ->
          node.mark <- visiting;
          walk ty;
          node.mark <- visited
      | TyCon(_,tys) -> List.iter walk tys
      | _ -> ()
  in walk ty

(** 型付けを行う *)
let typeof ctx tm =
  let lrefs = ref [] in
  let rec walk ctx rank = function
    | TmVar x as tm ->
        instanciate rank tm (Context.get_typ ctx x)
    | TmCon(c,vs) as tm ->
        tm,snd(instanciate rank tm (typ_of_const c vs))
    | TmAbs(b,topt,tm) ->
        let ty1 = fresh_mvar rank in
        let ctx' = Context.add_type ctx b ty1 in
        let tm,ty2 = walk ctx' rank tm in
          TmAbs(b,Some ty1,tm),tarrow ty1 ty2
    | TmApp(tm1,tm2) ->
        let ty = fresh_mvar rank in
        let tm1,ty1 = walk ctx rank tm1 in
        let tm2,ty2 = walk ctx rank tm2 in
          unify lrefs ty1 (tarrow ty2 ty);
          occur_check lrefs ty1;
          TmApp(tm1,tm2),ty
    | TmLet(b,topt,tm1,tm2) ->
        let tm1',ty1 = walk ctx (rank + 1) tm1 in
        let tm1',ty1 = if is_syntactic_value tm1 || is_lazy b then
          generalize (rank + 1) tm1' ty1
        else
          tm1',ty1
        in
        let ctx' = Context.add_type ctx b ty1 in
        let tm2',ty2 = walk ctx' rank tm2 in
          TmLet(b,Some ty1,tm1',tm2'),ty2
    | _ -> assert false
  in
    walk ctx 0 tm

let typing ctx tm =
  let tm',ty = typeof ctx tm in
    if is_syntactic_value tm then generalize 0 tm' ty else tm',ty


