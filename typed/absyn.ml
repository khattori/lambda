(**
   Absyn: 抽象構文木定義
*)
open ListAux
open Printf
open Context
open Const
open Type

exception Parse_error
exception Multiple_labels of string


(** 項の定義 *)
(*
  T ::= Type.t
      | typeof E
  E ::= x                     (x∈Ident)
      | c v1 ... vn           (c∈Const)
      | m                     (m∈Address)
      | \b.E
      | E1 E2
      | let b = E1 in E2
      | E1,...,En
      | { l1=E1;...;ln=En }   (l∈Label)
      | E.l
      | case E of Cs
      | E:T
      | \<t>.E
      | E <T>
      | over T of Ks
  Cs ::= c1 -> E1 |...| cn -> En
       | c1 -> E1 |...| cn -> En | ... -> E
  b ::= x | \x | _
  Ks ::= T1 => E1 |...| Tn => En
       | T1 => E1 |...| Tn => En | ... -> E
*)
type term =
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
and case  =
  | CsPat of const * term
  | CsDef of term
and const = Const of Const.t * const list

(** 項がリストかどうか判定 *)
let rec is_list s vs = match s,vs with
  | "nil",[] -> true
  | "cons",[_;TmCon(CnSym s,vs)] -> is_list s vs
  | _ -> false

(** 項を文字列に変換する *)
let rec to_string ctx = function
  | TmVar x ->
      sprintf "%s(%d)" (Context.index2name ctx x) x
  | TmMem m -> sprintf "<%d>" m
  | TmCon(cn,[]) -> Const.to_string cn
  | TmCon(CnSym s,vs) when is_list s vs ->
      sprintf "{%s}" (String.concat "; " (to_string_list ctx vs))
  | TmCon(CnTpl n,vs) ->
      sprintf "(%s%s)"
        (String.concat ", " (List.map (to_string ctx) vs))
        (if List.length vs < n then
           sprintf ",<%d>" (n - (List.length vs))
         else
           "")
  | TmCon(CnRcd ls,vs) ->
      sprintf "{%s}"
        (String.concat "; "
           (List.map2_unb
              (fun l v -> sprintf "%s = %s" l (to_string ctx v)) ls vs))
  | TmCon(cn,vs) ->
      sprintf "(%s %s)"
        (Const.to_string cn)
        (String.concat " " (List.map (to_string ctx) vs))
  | TmAbs((b,topt),tm) ->
      let ctx',s = to_string_bind ctx b in
        sprintf "(\\%s%s.%s)" s (topt_to_string ctx topt) (to_string ctx' tm)
  | TmApp(tm1,tm2) ->
      sprintf "(%s %s)" (to_string ctx tm1) (to_string ctx tm2)
  | TmLet((b,topt),tm1,tm2) ->
      let ctx',s = to_string_bind ctx b in
        sprintf "(let %s%s = %s in %s)"
          s (topt_to_string ctx topt) (to_string ctx tm1) (to_string ctx' tm2)
  | TmCas(tm1,cs) ->
      sprintf "(case %s of %s)"
        (to_string ctx tm1)
        (String.concat " | " (List.map (to_string_case ctx) cs))
  | TmAsc(tm,ty) ->
      sprintf "(%s:%s)" (to_string ctx tm) (Type.to_string ctx ty)
  | TmTbs(t,tm) ->
      let ctx',s = Context.fresh_name ctx t in
        sprintf "(\\<%s>.%s)" s (to_string ctx' tm)
  | TmTpp(tm1,ty2) ->
      sprintf "(%s <%s>)" (to_string ctx tm1) (Type.to_string ctx ty2)
  | TmOvr(ty,ovs) ->
      sprintf "(over %s of %s)"
        (Type.to_string ctx ty)
        (String.concat " | " (List.map (to_string_over ctx) ovs))
and to_string_list ctx = function
  | [] -> []
  | [t;TmCon(_,vs)] -> to_string ctx t::to_string_list ctx vs
  | _ -> assert false
and to_string_binds ctx0 bs =
  let foldf (ctx,ss) (b,topt) =
    let ctx',s = to_string_bind ctx b in
      ctx',sprintf "%s%s" s (topt_to_string ctx0 topt)::ss
  in
  let ctx',ss = List.fold_left foldf (ctx0,[]) bs in
    ctx',String.concat "," (List.rev ss)
and to_string_bind ctx = function
  | Wild as b -> (Context.add_bind ctx b),"_"
  | Eager x   -> Context.fresh_name ctx x
  | Lazy x    ->
      let ctx',x' = Context.fresh_name ctx x
      in
        ctx',sprintf "\\%s" x'
and to_string_binding ctx (b,tm) = match b with
  | Wild _  -> sprintf    "_ = %s"   (to_string ctx tm)
  | Eager x -> sprintf   "%s = %s" x (to_string ctx tm)
  | Lazy  x -> sprintf "\\%s = %s" x (to_string ctx tm)
and to_string_case ctx = function
  | CsPat(c,tm) ->
      sprintf "%s -> %s" (to_string_const c) (to_string ctx tm)
  | CsDef tm    -> sprintf "... -> %s" (to_string ctx tm)
and to_string_const (Const(cn,cs)) =
  match cs with
    | [] -> Const.to_string cn
    | cs ->
        sprintf "(%s %s)"
          (Const.to_string cn)
          (String.concat " " (List.map to_string_const cs))
and to_string_over ctx (topt,tm) =
  sprintf "%s%s" (to_string ctx tm) (topt_to_string ctx topt)


(* De Bruijin index *)
(*
 * map: 項置換のための補助関数
 *
 *)
let typ_map onvar onmva c ty =
  let rec walk c ty = match ty with
    | TyVar x       -> onvar c x
    | TyAll(t,ty')  -> TyAll(t,walk (c+1) ty')
    | TyCon(tc,tys) -> TyCon(tc,List.map (walk c) tys)
    | TyMva{contents=NoLink(id,rank)} -> onmva c ty id rank
    | TyMva{contents=LinkTo{typ=ty}}  -> walk c ty
  in
    walk c ty

let term_map onvar ontyp c tm =
  let rec walk c tm = match tm with
    | TmVar x           -> onvar c x
    | TmMem _           -> tm
    | TmCon(cn,vs)      -> TmCon(cn,List.map (walk c) vs)
    | TmAbs(bt,tm')     -> TmAbs(bt_map c bt,walk (c + 1) tm')
    | TmApp(tm1,tm2)    -> TmApp(walk c tm1,walk c tm2)
    | TmLet(bt,tm1,tm2) ->
        TmLet(bt_map c bt,walk c tm1,walk (c + 1) tm2)
    | TmCas(tm,cs)      -> TmCas(walk c tm, cs_map c cs)
    | TmAsc(tm,ty)      -> TmAsc(walk c tm,ontyp c ty)
    | TmOvr(ty,os)      -> TmOvr(ontyp c ty,os_map c os)
    | TmTbs(t,tm')      -> TmTbs(t,walk (c+1) tm')
    | TmTpp(tm1,ty2)    -> TmTpp(walk c tm1,ontyp c ty2)
  and bt_map c (b,topt) =
    match topt with
      | None     -> b,None
      | Some ty1 -> b,Some(ontyp c ty1)
  and cs_map c =
    List.map (function
                | CsPat(con,t) -> CsPat(con,walk c t)
                | CsDef t      -> CsDef(walk c t))
  and os_map c =
    List.map (
      fun (topt,tm) ->
        (match topt with None -> None | Some ty -> Some(ontyp c ty)),
        walk c tm
    )
  in
    walk c tm

(*
 * shift: シフト操作
 * 
 *   ↑d,c(k)                = k          --- if k < c
 *                             k + d      --- if k >= c
 *   ↑d,c(\.t1)             = \.↑d,c+1(t1)
 *   ↑d,c(t1 t2)            = ↑d,c(t1) ↑d,c(t2)
 *   ↑d,c(let x = t1 in t2) = let x = ↑d,c(t1) in ↑d,c+1(t2)
 * 
 *)
let typ_shift_above d c ty =
  typ_map
    (fun c x -> if x >= c then TyVar(x+d) else TyVar x)
    (fun c ty _ _ -> ty)
    c ty
let typ_shift d ty = typ_shift_above d 0 ty
let term_shift_above d c tm =
  term_map
    (fun c x -> if x >= c then TmVar(x+d) else TmVar x)
    (typ_shift_above d)
    c tm
let term_shift d tm = term_shift_above d 0 tm

(*
 * subst: 置換操作
 * 
 *   [j:->s]k                  = s     --- if k = j
 *                               k     --- else
 *   [j:->s]\.t1               = \.[j+1:->↑1,0(s)]t1
 *   [j:->s](t1 t2)            = [j:->s]t1 [j:->s]t2
 *   [j:->s](let x = t1 in t2) = let x = [j:->s]t1 in [j+1:->↑1,0(s)]t2
 * 
 * 以下の実装では，shift操作を一気にやっている
 *)
let typ_subst j tyS tyT =
  typ_map
    (fun c x -> if x == c then typ_shift c tyS else TyVar x)
    (fun c ty _ _ -> ty)
    j tyT
let term_subst j tmS tmT =
  term_map
    (fun c x -> if x == c then term_shift c tmS else TmVar x)
    (fun c ty -> ty)
    j tmT
let tytm_subst j tyS tmT =
  term_map
    (fun c x -> TmVar x)
    (fun c tyT -> typ_subst c tyS tyT)
    j tmT

(*
 * subst_top: β簡約における置換
 * 
 *   (\x.t2) t1     → ↑-1,0([0:->↑1,0(t2)]t1)
 *   (<t>=>ty1) ty2 → ↑-1,0([0:->↑1,0(ty2)]ty1)
 *)
let typ_subst_top ty1 ty2 =
  typ_shift (-1) (typ_subst 0 (typ_shift 1 ty1) ty2)
let term_subst_top tm1 tm2 =
  term_shift (-1) (term_subst 0 (term_shift 1 tm1) tm2)
let tytm_subst_top ty tm =
  term_shift (-1) (tytm_subst 0 (typ_shift 1 ty) tm)

(* メタ変数を型変数にする *)
let typ_mvar2tyvar mvid j tyS =
  typ_map
    (fun c x -> TyVar x)
    (fun c ty id rank -> if id == mvid then TyVar c else ty)
    j tyS
let term_mvar2tyvar mvid j tmS =
  term_map
    (fun c x -> TmVar x)
    (fun c ty -> typ_mvar2tyvar mvid c ty)
    j tmS
let term_gen s mvid tm =
  TmTbs(s,term_mvar2tyvar mvid 0 (term_shift 1 tm))
let typ_gen s mvid ty =
  TyAll(s,typ_mvar2tyvar mvid 0 (typ_shift 1 ty))

(*
 * is_value: 項が値かどうか判定
 * 
 *)
let is_value tm =
  let rec walk = function
    | TmCon(c,vs) -> Const.is_value c vs
    | TmMem _ | TmAbs _ | TmTbs _ -> true
    | _ -> false
  in
    walk tm

(*
 * is_syntactic_value: 項がsyntacticな値かどうか判定
 *)
let rec is_syntactic_value = function
  | TmVar _ | TmCon _ | TmAbs _ | TmMem _ | TmTbs _ -> true
  | TmTpp(tm,_) -> is_syntactic_value tm
  | tm -> is_ctor_term tm
and is_ctor_term = function
  | TmCon(c,_) -> is_ctor c
  | TmApp(c,tm) when is_ctor_term c -> is_syntactic_value tm
  | TmTpp(c,_) -> is_ctor_term c
  | _ -> false

(* 
 * tm_apps: 入れ子になったλ適用の項を作る
 * 
 * E E1...En を ((...((E E1) E2) ...) En)に変換
 * 
 *)
let rec tm_apps tm tms =
  match tms with
    | [] -> tm
    | tm'::tms' -> tm_apps (TmApp(tm,tm')) tms'

(* 定数項の生成用関数 *)
let tm_int n     = TmCon(CnInt n,[])
let tm_rea r     = TmCon(CnRea r,[])
let tm_str s     = TmCon(CnStr s,[])
let tm_sym s vs  = TmCon(CnSym s,vs)
let tm_tuple tms = tm_apps (TmCon(CnTpl(List.length tms),[])) tms
let tm_record lts =
  let ls,tms = List.split lts in
    List.check_dup (fun l -> raise (Multiple_labels l)) ls;
    tm_apps (TmCon(CnRcd ls,[])) tms

