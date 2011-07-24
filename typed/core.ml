(** lambda評価器 *)
open ListAux
open Absyn
open Type
open Context
open Prims

exception Unify_fail  of link ref list
exception Occur_check of link ref list
exception Label_fail  of string * link ref list
exception Tuple_fail  of int * link ref list
exception Case_fail   of link ref list
exception Over_fail   of link ref list

(*
 * case_reduc: case簡約
 * 
 * case c v1…vn of c1 -> t1 | c2 -> t2 | … | cm -> tm | ... -> t
 * →
 * - ti v1…vn    --- if c = c2
 * - t (c v1…vn) --- else
 *)
exception Return_term of term
let case_reduc cn vs cs =
  let rec const_match cs vs =
    match cs,vs with
      | [],_ -> true
      | Const(cn,cs1)::cs2,TmCon(cn',vs1)::vs2 ->
          cn = cn' && const_match cs1 vs1 && const_match cs2 vs2
      | _ -> false
  in
    try
      List.iter (
      function
        | CsPat(Const(cn',cs),tm) when cn = cn' && const_match cs vs ->
            let vs' = List.cut (List.length cs) vs in
              raise (Return_term(tm_apps tm vs'))
        | CsDef tm -> raise (Return_term(TmApp(tm,TmCon(cn,vs))))
        | _ -> ()
    ) cs;
    (tm_error "*** no match case ***")
  with Return_term tm -> tm

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
  | tm when is_value tm -> assert false
      (* Prims.tm_error "*** no eval rule ***" *)
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
  | TmApp(TmCon(c,vs) as tm1,tm2) when is_value tm2 ->
      if Const.arity c > List.length vs then
        TmCon(c,vs@[tm2])
      else
        TmApp(eval_step ctx store tm1,tm2)
  | TmApp(tm1,tm2) ->
      if is_value tm1 then
        TmApp(tm1,eval_step ctx store tm2)
      else
        TmApp(eval_step ctx store tm1,tm2)
  | TmFix(TmAbs(b,tm)) as f->
      term_subst_top f tm
  | TmVar x ->
      let tm',o = Context.get_glbl ctx x in
        term_shift (x + o) tm'
  | TmCas(TmCon(c,vs),cs) ->
      case_reduc c vs cs
  | TmCas(tm1,cs) when not (is_value tm1) ->
      TmCas(eval_step ctx store tm1,cs)
  | TmTpp(TmCon(c,vs),ty2) ->
      TmCon(c,vs)
  | TmTpp(TmTbs(x,tm1),ty2) ->
      tytm_subst_top ty2 tm1
  | TmTpp(tm1,ty2) ->
      TmTpp(eval_step ctx store tm1,ty2)
  | TmTbs(t,tm1) ->
      let ctx' = Context.add_name ctx t in
        TmTbs(t,eval_step ctx' store tm1)
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
      | TyAll _ -> assert false
      | ty -> ()
    in
      walk ty;
      (
        List.fold_left
          (fun tm (mvid,t) -> term_gen t mvid tm) tm !ts_ref,
        List.fold_left
          (fun ty (mvid,t) -> typ_gen t mvid ty) ty !ts_ref
      )
(*
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
*)
  in
    generalize_ rank tm ty

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

(* ty2の型変数のランクがrankより大きければrankにする *)
let update_rank lrefs rank ty1 ty2 =
  let rec walk = function
    | ty when ty == ty1 -> raise (Occur_check !lrefs)
    | TyMva{contents=LinkTo{typ=ty}} -> walk ty
    | TyMva({contents=NoLink(id,r)} as l) when r > rank -> l := NoLink(id,rank)
    | TyCon(_,tys) -> List.iter walk tys
    | _ -> ()
  in walk ty2

let unify lrefs ty1 ty2 =
  let rec walk ty1 ty2 =
    let ty1 = repr ty1 and ty2 = repr ty2 in
      if ty1 == ty2 then () else
        match ty1,ty2 with
          | TyMva({contents=NoLink(id1,r1)} as l1),
            TyMva({contents=NoLink(id2,r2)} as l2) ->
              if r1 > r2 then (
                l1 := link_to ty2 id1 r1;
                lrefs := l1::!lrefs
              ) else (
                l2 := link_to ty1 id2 r2;
                lrefs := l2::!lrefs
              )
          | TyMva({contents=NoLink(id1,r1)} as l1), _ ->
              update_rank lrefs r1 ty1 ty2;
              l1 := link_to ty2 id1 r1;
              lrefs := l1::!lrefs
          | _, TyMva({contents=NoLink(id2,r2)} as l2) ->
              update_rank lrefs r2 ty2 ty1;
              l2 := link_to ty1 id2 r2;
              lrefs := l2::!lrefs
          | TyCon(tc1,tys1),TyCon(tc2,tys2) when tc1 = tc2 ->
              List.iter2 walk tys1 tys2
          | _, _ ->
              raise (Unify_fail !lrefs)
  in
    walk ty1 ty2
(*
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
*)
(*
  (\<t>.tm1) <ty2> → tm1[t:=ty2]
  (x <ty1> ... <tyn>)
  (#l <ty1> <ty2>) → #l --- ty1はフィールドlを含む型，ty2がlの型
  (#n <ty1> <ty2>) → #n --- ty1はn以上の組型,ty2はn番目の型
  let x:<t>=>T = \<t>.E in ... x <X> ...

*)
let type_eval lrefs ctx tm =
  let changed = ref true in
  let rec walk ctx = function
    | TmVar x when Context.can_get_term ctx x ->
        let tm',o = Context.get_term ctx x in
          changed := true;
          term_shift (x + o) tm'
    | (TmVar _ | TmMem _ | TmCon _) as tm -> tm
    | TmTbs _ as tm -> tm
(*    | TmTbs(t,tm) -> TmTbs(t,walk ctx tm) *)
    | TmAbs((b,topt),tm1) ->
        let ctx' = Context.add_namebind ctx b in
          TmAbs((b,topt),walk ctx' tm1)
    | TmApp(tm1,tm2) ->
        TmApp(walk ctx tm1,walk ctx tm2)
    | TmCas(tm1,cs) ->
        let tm1' = walk ctx tm1 in
          TmCas(tm1',
                List.map (
                  function
                    | CsPat(cn,tm) -> CsPat(cn,walk ctx tm)
                    | CsDef tm     -> CsDef(walk ctx tm)
                ) cs)
    | TmLet((b,Some ty),tm1,tm2) ->
        let tm1' = walk ctx tm1 in
        let ctx' = Context.add_termbind ctx b tm1' 1 in
          TmLet((b,Some ty),tm1',walk ctx' tm2)
    | TmFix tm ->
        TmFix(walk ctx tm)
    | TmTpp(TmTbs(t,tm1),ty2) ->
        changed := true;
        tytm_subst_top ty2 tm1
(*
    | TmTpp(TmVar x,ty2) ->
        let tm',o = Context.get_term ctx x in
          changed := true;
          TmTpp((term_shift (x + o) tm'),ty2)
*)
    | TmTpp(TmTpp(TmCon(Const.CnSel l,[]),ty1),ty2) as tm ->
        let ty2 = repr ty2 in
          ( match ty2 with
              | TyCon(TyCRcd ls,tys) when List.mem l ls ->
                  let ty' = List.assoc l (List.combine ls tys) in
                    unify lrefs ty1 ty';
                    changed := true;
                    TmCon(Const.CnSel l,[])
              | TyMva{contents=NoLink _} -> tm
              | _ -> raise (Label_fail(l,!lrefs)) )
    | TmTpp(TmTpp(TmCon(Const.CnNth i,[]),ty1),ty2) as tm ->
        let ty2 = repr ty2 in
          ( match ty2 with
              | TyCon(TyCTpl n,tys) when i <= n ->
                  let ty' = List.nth tys (i-1) in
                    unify lrefs ty1 ty';
                    changed := true;
                    TmCon(Const.CnNth i,[])
              | TyMva{contents=NoLink _} -> tm
              | _ -> raise (Tuple_fail(i,!lrefs)) )
    | TmTpp(tm1,ty2) ->
        TmTpp(walk ctx tm1,ty2)
    | TmOvr(ty1,os) ->
        let os' = List.filter (
          fun (topt,tm) -> match topt with
            | None -> assert false
            | Some ty ->
                let ty1' = Type.copy ty1 in
                let ty' = Type.copy ty in
                  try
                    unify lrefs ty' ty1'; true
                  with Unify_fail _ -> changed := true; false
        ) os in (
          match os' with
            | [] -> raise (Over_fail !lrefs)
            | [Some ty,tm] -> changed := true; unify lrefs ty ty1; tm
            | [None,tm] -> assert false
            | _ -> TmOvr(ty1,os') )
    | _ -> assert false
  in
  let rec loop tm =
    Printf.printf "...> %s\n" (Absyn.to_string ctx tm);
    if !changed then ( changed := false; loop (walk ctx tm) ) else tm
  in
    loop tm

(** 型付けを行う *)
let typeof lrefs ctx tm =
  let rec walk_const rank (Const(cn,cs)) =
    let ty1 = snd(instanciate rank (TmCon(cn,[])) (Type.of_const cn)) in
    let ty2 = fresh_mvar rank in
    let tys = List.map (walk_const rank) cs in
      unify lrefs ty1 (tarrows (tys@[ty2]));
      ty2
  in
  let rec walk ctx rank = function
    | TmVar x as tm ->
        instanciate rank tm (Context.get_typ ctx x)
    | TmMem _ -> assert false (* プログラムテキスト中には出現しない *)
    | TmCon(Const.CnSym("ref") as c,_) as tm ->
        instanciate (rank-1) tm (Type.of_const c)
    | TmCon(c,[]) as tm ->
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
(*          occur_check lrefs ty1; update_rank中でoccur checkする *)
          TmApp(tm1,tm2),ty
    | TmLet((b,_),tm1,tm2) ->
        let tm1',ty1 = walk ctx (rank + 1) tm1 in
        let _ = type_eval lrefs ctx tm1' in
        let tm1',ty1' = generalize ctx (rank + 1) tm1' b ty1 in
        let ctx' = Context.add_typebind ctx b ty1' in
        let tm2',ty2 = walk ctx' rank tm2 in
          TmLet((b,Some ty1'),tm1',tm2'),ty2
    (*
        Γ |- E : T->T
      --------------------
       Γ |- fix E : T
    *)
    | TmFix tm ->
        let tm',ty' = walk ctx rank tm in
        let ty = fresh_mvar rank in
          unify lrefs ty' (tarrow ty ty);
          TmFix tm',ty
    (*
      Γ |- E : T
      Γ |- Ci : Ti1 -> ... Tim -> T  mはCiのアリティ
      Γ |- Ei : Ti1 -> ... Tim -> T' mはCiのアリティ
     -------------------------------------------------
      Γ |- case E of C1 -> E1 | ... | Cn -> En : T'
    *)
    | TmCas(tm1,cs) ->
        let tm1',ty1 = walk ctx rank tm1 in
        let ty2 = fresh_mvar rank in
        let cs' =
          List.map (
            function
              | CsPat(c,tm) ->
                  let ty_c = walk_const rank c in
                  let tm',ty_e = walk ctx rank tm in
                    unify lrefs ty1 (result_type ty_c);
                    unify lrefs ty2 (result_type ty_e);
                    ( try
                        List.iter2
                          (unify lrefs) (arg_types ty_c) (arg_types ty_e)
                      with Invalid_argument _ ->
                        raise (Case_fail !lrefs) );
                    CsPat(c,tm')
              | CsDef tm ->
                  let tm',ty = walk ctx rank tm in
                    unify lrefs ty (tarrow ty1 ty2);
                    CsDef tm'
          ) cs
        in
          TmCas(tm1',cs'),ty2

    (*
            Γ |- Ei : Ti     ∃θ.θTi = θT
     -------------------------------------------------
      Γ |- over T of E1 | ... | En : T
    *)
    | TmOvr(ty,os) ->
        let os' = List.map (
          fun (_,tm) ->
            let tm',ty' = walk ctx rank tm in
            let ty = Type.copy ty in
              unify lrefs ty ty';
              Some ty',tm'
        ) os in
          TmOvr(ty,os'),ty
    | _ -> assert false

  in
    walk ctx 0 tm


let typing ctx tm b =
  let lrefs = ref [] in
  let rank = 0 in
  let tm,ty = typeof lrefs ctx tm in
  let _ = type_eval lrefs ctx tm in
  let tm,ty = generalize ctx rank tm b ty in
    print_string (Absyn.to_string ctx tm); print_newline();
    tm,ty

let restore lrefs =
  List.iter (
    fun lref -> match !lref with
      | LinkTo { old = (id,rank) } -> lref := NoLink(id,rank)
      | _ -> assert false
  ) lrefs

