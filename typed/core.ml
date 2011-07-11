(** lambda評価器 *)
open ListAux
open Absyn
open Type
open Context
open Prims

exception Unify_fail of link ref list
exception Occur_check of link ref list
exception Label_fail of string * link ref list

(** 1ステップの評価を行う *)
(*
 * [構文]
 * 
 * v ::= x | m | \b1.t | c v1…vn | v1,…,vn
 * t ::= t1 t2
 *     | let b = t1 in t2
 *     | case t of c1 -> t1 | … | ... -> t
 *     | t1,…,tn
 * b ::= x | \x | _
 * E ::= []
 *     | E t | (\x.t) E | (\_.t) E
 *     | case E of c1 -> t1 | … | ... -> t
 *     | (v1,…,Ei,…,tn)
 * 
 * [letの変換]
 * let b = t1 in t2 ⇒ (\b.t2) t1
 * 
 * [β簡約規則]
 * (\_.t) v → v
 * (\x.t) v → t[x:=v]
 * (\\x.t) t' → t[x:=t']
 * 
 *)
let rec eval_step ctx store = function
  | tm when is_value tm ->
      Prims.tm_error "*** no eval rule ***"
  | TmCon(Const.CnNth i,[TmCon(Const.CnTpl _,vs)]) ->
      List.nth vs (i-1)
  | TmCon(Const.CnSel l,[TmCon(Const.CnRcd ls,vs)]) ->
      List.assoc l (List.combine ls vs)
  | TmCon(Const.CnSym d,vs) ->
      delta_reduc store d vs
  | TmLet(bt,tm1,tm2) ->
      TmApp(TmAbs(bt,tm2),tm1)
  | TmApp(TmAbs(((Eager _|Wild) as b,topt),tm1),tm2) ->
      if is_value tm2 then
        term_subst_top tm2 tm1
      else
        TmApp(TmAbs((b,topt),tm1),eval_step ctx store tm2)
  | TmApp(TmAbs((Lazy _,_),tm1),tm2) ->
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
  | TmTpp(TmCon(c,vs),ty2) ->
      TmCon(c,vs)
  | TmTpp(tm1,ty2) ->
      TmTpp(eval_step ctx store tm1,ty2)
  | _ -> Prims.tm_error "*** no eval rule ***"

(** 項が値になるまで評価を行う *)
let eval ctx store tm =
  let rec iter tm =
    Printf.printf "---> %s\n" (Absyn.to_string ctx tm);
    if is_value tm then
      tm
    else
      iter (eval_step ctx store tm)
  in
    iter tm

let generalize ctx rank tm b ty =
  let generalize_ rank tm ty =
    let id_ref = ref 0 in
    let ts_ref = ref [] in
    let rec walk = function
      | TyMva{contents=NoLink(mvid,r)} when r >= rank ->
          let id = !id_ref in
            if not (List.mem_assoc mvid !ts_ref) then (
              ts_ref := (mvid,Printf.sprintf "t%d" id)::!ts_ref;
              incr id_ref
            )
      | TyMva{contents=LinkTo{typ=ty}} -> walk ty
      | TyCon(tc,tys) -> List.iter walk tys
      | ty -> ()
    in
      walk ty;
      (
        List.fold_left
          (fun tm (mvid,t) -> term_gen t mvid tm) tm !ts_ref,
        List.fold_left
          (fun ty (mvid,t) -> typ_gen t mvid ty) ty !ts_ref
      )
  in
  let monoralize_ ty =
    let rec walk ty = match ty with
      | TyMva({contents=NoLink(mvid,r)} as link) ->
          link := NoLink(mvid,no_rank)
      | TyMva{contents=LinkTo{typ=ty}} -> walk ty
      | TyCon(_,ts) -> List.iter walk ts
      | _ -> assert false
    in
      walk ty
  in
    if is_lazy b || is_syntactic_value tm then
      generalize_ rank tm ty
    else
      (monoralize_ ty; tm,ty)

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
          | TyMva({contents=NoLink(_,r1)} as l1),
            TyMva({contents=NoLink(_,r2)} as l2) ->
              if r1 > r2 then (
                l1 := link_to ty2 r1;
                lrefs := l1::!lrefs
              ) else (
                l2 := link_to ty1 r2;
                lrefs := l2::!lrefs
              )
          | TyMva({contents=NoLink(_,r1)} as l1), _ ->
              l1 := link_to ty2 r1;
              lrefs := l1::!lrefs
          | _, TyMva({contents=NoLink(_,r2)} as l2) ->
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
let typeof lrefs ctx tm =
  let rec walk ctx rank = function
    | TmVar x as tm ->
        instanciate rank tm (Context.get_typ ctx x)
    | TmMem _ -> assert false (* プログラムテキスト中には出現しない *)
    | TmCon(c,vs) as tm ->
        instanciate rank tm (Type.of_const c)
    | TmAbs((b,_),tm) ->
        let ty1 = fresh_mvar rank in
        let ctx' = Context.add_typebind ctx b ty1 in
        let tm',ty2 = walk ctx' rank tm in
          TmAbs((b,Some ty1),tm'),tarrow ty1 ty2
    | TmApp(tm1,tm2) ->
        let ty = fresh_mvar rank in
        let tm1,ty1 = walk ctx rank tm1 in
        let tm2,ty2 = walk ctx rank tm2 in
          unify lrefs ty1 (tarrow ty2 ty);
          occur_check lrefs ty1;
          TmApp(tm1,tm2),ty
    | TmLet((b,_),tm1,tm2) ->
        let tm1',ty1 = walk ctx (rank + 1) tm1 in
        let tm1',ty1' = generalize ctx (rank + 1) tm1' b ty1 in
        let ctx' = Context.add_typebind ctx b ty1' in
        let tm2',ty2 = walk ctx' rank tm2 in
          TmLet((b,Some ty1'),tm1',tm2'),ty2
    | _ -> assert false
  in
    walk ctx 0 tm

(*
  (\<t>.tm1) <ty2> → tm1[t:=ty2]
  (x <ty1> ... <tyn>)
  (#l <ty1> <ty2>) → #l --- ty1はフィールドlを含む型，ty2がlの型
  (#n <ty1> <ty2>) → #n --- ty1はn以上の組型,ty2はn番目の型
  let x:<t>=>T = \<t>.E in ... x <X> ...
  | TmVar of int
  | TmMem of int
  | TmCon of Const.t * term list
  | TmAbs of (binder * Type.t option) * term
  | TmApp of term * term
  | TmLet of (binder * Type.t option) * term * term
  | TmCas of term * case list
  | TmAsc of term * Type.t
  | TmTbs of string * term
  | TmTpp of term * Type.t
  | TmOvr of Type.t * (Type.t option * term) list

*)
let rec type_eval lrefs ctx = function
  | (TmVar _ | TmMem _ | TmCon _ | TmTbs _) as tm -> tm
  | TmAbs((b,topt),tm1) ->
      let ctx' = Context.add_bind ctx b in
        TmAbs((b,topt),type_eval lrefs ctx' tm1)
  | TmApp(tm1,tm2) ->
      TmApp(type_eval lrefs ctx tm1,type_eval lrefs ctx tm2)
  | TmLet((b,Some ty),tm1,tm2) ->
      let tm1' = type_eval lrefs ctx tm1 in
      let ctx' = Context.add_termbind ctx b tm1' ty 1 in
        TmLet((b,Some ty),tm1',type_eval lrefs ctx' tm2)
  | TmTpp(TmTbs(t,tm1),ty2) ->
      type_eval lrefs ctx (tytm_subst_top ty2 tm1)
  | TmTpp(TmVar x,ty2) ->
      let tm',o = Context.get_term ctx x in
        type_eval lrefs ctx (TmTpp(term_shift (x + o) tm',ty2))
  | TmTpp(tm1,(TyMva{contents=NoLink _} as ty2)) ->
      TmTpp(type_eval lrefs ctx tm1,ty2)
  | TmTpp(tm1,(TyMva{contents=LinkTo{typ=ty2}})) ->
      type_eval lrefs ctx (TmTpp(tm1,ty2))
  | TmTpp(tm1,ty2) ->
      let tm1' = type_apply lrefs ctx tm1 ty2 in
        type_eval lrefs ctx tm1'
  | _ -> assert false
and type_apply lrefs ctx tm ty =
  match tm with
    | TmTbs(t,tm1) -> tytm_subst_top ty tm1
    | TmTpp(TmCon(Const.CnSel l,[]),ty1) ->
        let ty = repr ty in (
            match ty with
              | TyCon(TyCRcd ls,tys) when List.mem l ls ->
                  let ty' = List.assoc l (List.combine ls tys) in
                    unify lrefs ty1 ty';
                    TmCon(Const.CnSel l,[])
              | _ -> raise (Label_fail(l,!lrefs))
          )
    | TmVar x ->
        let tm',o = Context.get_term ctx x in
          type_apply lrefs ctx (term_shift (x + o) tm') ty
    | (TmCon _ | TmTpp _) as tm ->
        type_eval lrefs ctx tm
    | _ -> assert false

let typing ctx tm b =
  let lrefs = ref [] in
  let rank = 0 in
  let tm,ty = typeof lrefs ctx tm in
    print_string (Absyn.to_string ctx tm);
    let tm = type_eval lrefs ctx tm in
    generalize ctx rank tm b ty


