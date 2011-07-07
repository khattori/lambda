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
      | \Bs.E
      | E1 E2
      | let Bs = E1 in E2
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
  Bs ::= b
       | b1,...,bn        n ≧ 2
       | b1,...,bn ...    n ≧ 2
  b ::= x | \x | _
  Ks ::= T1 => E1 |...| Tn => En
       | T1 => E1 |...| Tn => En | ... -> E
  
*)
type term =
  | TmVar of int
  | TmMem of int
  | TmCon of Const.t * term list
  | TmAbs of (binder * Type.t option) list * term
  | TmApp of term * term
  | TmLet of (binder * Type.t option) list * term * term
  | TmTpl of term list
  | TmRcd of (binder * term) list
  | TmSel of term * string
  | TmCas of term * case list
  | TmAsc of term * Type.t
  | TmTbs of string * term
  | TmTpp of term * Type.t
  | TmOvr of Type.t * (Type.t option * term) list
and case =
  | CsPat of Const.t * term
  | CsDef of term
(** 項を文字列に変換する *)
let rec to_string ((tmctx,tyctx) as ctxs) = function
  | TmVar x ->
      sprintf "%s(%d)" (Context.index2name tmctx x) x
  | TmMem m -> sprintf "<%d>" m
  | TmCon(cn,[]) -> Const.to_string cn
  | TmCon(cn,vs) ->
      sprintf "(%s %s)"
        (Const.to_string cn)
        (String.concat " " (List.map (to_string ctxs) vs))
  | TmAbs(bs,tm) ->
      let tmctx',s = to_string_binds ctxs bs in
        sprintf "(\\%s.%s)" s (to_string (tmctx',tyctx) tm)
  | TmApp(tm1,tm2) ->
      sprintf "(%s %s)" (to_string ctxs tm1) (to_string ctxs tm2)
  | TmLet(bs,tm1,tm2) ->
      let tmctx',s = to_string_binds ctxs bs in
        sprintf "(let %s = %s in %s)"
          s (to_string ctxs tm1) (to_string (tmctx',tyctx) tm2)
  | TmTpl tms ->
        sprintf "(%s)" (String.concat ", " (List.map (to_string ctxs) tms))
  | TmRcd rcd ->
      sprintf "{ %s }"
        (String.concat "; " (List.map (to_string_binding ctxs) rcd))
  | TmSel(tm1,l) ->
      sprintf "%s.%s" (to_string ctxs tm1) l
  | TmCas(tm1,cs) ->
      sprintf "(case %s of %s)"
        (to_string ctxs tm1)
        (String.concat " | " (List.map (to_string_case ctxs) cs))
  | TmAsc(tm,ty) ->
      sprintf "(%s:%s)" (to_string ctxs tm) (Type.to_string tyctx ty)
  | TmTbs(t,tm) ->
      let tyctx',s = Context.fresh_name tyctx t in
        sprintf "(\\<%s>.%s)" s (to_string (tmctx,tyctx') tm)
  | TmTpp(tm1,ty2) ->
      sprintf "(%s <%s>)" (to_string ctxs tm1) (Type.to_string tyctx ty2)
  | TmOvr(ty,ovs) ->
      sprintf "(over %s of %s)"
        (Type.to_string tyctx ty)
        (String.concat " | " (List.map (to_string_over ctxs) ovs))
and to_string_binds (tmctx,tyctx) bs =
  let foldf (tmctx,ss) (b,topt) =
    let tmctx',s = to_string_bind tmctx b in
      tmctx',sprintf "%s%s" s (topt_to_string tyctx topt)::ss
  in
  let tmctx',ss = List.fold_left foldf (tmctx,[]) bs in
    tmctx',String.concat "," (List.rev ss)
and to_string_bind ctx = function
  | Wild as b -> (Context.add_bind ctx b),"_"
  | Eager x   -> Context.fresh_name ctx x
  | Lazy x    ->
      let ctx',x' = Context.fresh_name ctx x
      in
        ctx',sprintf "\\%s" x'
and to_string_binding ctxs (b,tm) = match b with
  | Wild _  -> sprintf "_ = %s" (to_string ctxs tm)
  | Eager x -> sprintf "%s = %s" x (to_string ctxs tm)
  | Lazy  x -> sprintf "\\%s = %s" x (to_string ctxs tm)
and to_string_case ctxs = function
  | CsPat(c,tm) -> sprintf "%s -> %s" (Const.to_string c) (to_string ctxs tm)
  | CsDef tm    -> sprintf "... -> %s" (to_string ctxs tm)
and to_string_over ((tmctx,tyctx) as ctxs) (topt,tm) =
  sprintf "%s%s" (to_string ctxs tm) (topt_to_string tyctx topt)


(* De Bruijin index *)
(*
 * map: 項置換のための補助関数
 *
 *)
let typ_map onvar c ty =
  let rec walk c ty = match ty with
    | TyVar x       -> onvar c x
    | TyAll(t,ty')  -> TyAll(t,walk (c+1) ty')
    | TyCon(tc,tys) -> TyCon(tc,List.map (walk c) tys)
    | TyMva{contents=NoLink _} -> ty
    | TyMva{contents=LinkTo{typ=ty}} -> walk c ty
  in
    walk c ty

let term_map onvar ontyp c tm =
  let rec walk c tm = match tm with
    | TmVar x           -> onvar c x
    | TmMem _           -> tm
    | TmCon(cn,vs)      -> TmCon(cn,List.map (walk c) vs)
    | TmAbs(bs,tm')     -> TmAbs(bs_map c bs,walk (c + List.length bs) tm')
    | TmApp(tm1,tm2)    -> TmApp(walk c tm1,walk c tm2)
    | TmLet(bs,tm1,tm2) ->
        TmLet(bs_map c bs,walk c tm1,walk (c + List.length bs) tm2)
    | TmTpl(ts)         -> TmTpl(List.map (walk c) ts)
    | TmRcd(bs)         -> TmRcd(List.map (fun (b,t) -> b,walk c t) bs)
    | TmSel(tm,l)       -> TmSel(walk c tm,l)
    | TmCas(tm,cs)      -> TmCas(walk c tm, cs_map c cs)
    | TmAsc(tm,ty)      -> TmAsc(walk c tm,ontyp c ty)
    | TmOvr(ty,os)      -> TmOvr(ontyp c ty,os_map c os)
    | TmTbs(t,tm')      -> TmTbs(t,walk (c+1) tm')
    | TmTpp(tm1,ty2)    -> TmTpp(walk c tm1,ontyp c ty2)
  and bs_map c =
    List.map
      (fun (b,topt) -> match topt with
         | None     -> b,None
         | Some ty1 -> b,Some(ontyp c ty1))
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
let tytm_subst_top tyS tmT =
  term_shift (-1) (tytm_subst 0 (typ_shift 1 tyS) tmT)


(*
 * is_value: 項が値かどうか判定
 * 
 *)
let rec is_value tm =
  let rec walk tm =
    match tm with
      | TmCon(CnSym s,vs) -> (
            match List.assoc s !_table_ref with
              | Ctor _ -> true
              | Dtor a -> List.length vs < a
        )
      | TmTpl(tms) -> List.for_all is_value tms
      | TmCon _ | TmMem _ | TmAbs _ | TmTbs _ -> true
      | _ -> false
  in
    walk tm

(*
 * is_syntactic_value: 項がsyntacticな値かどうか判定
 *)
let is_syntactic_value = function
  | TmCon _ | TmAbs _ | TmMem _ -> true
  | _ -> false

(*
 * check_record: レコードに同一ラベル名が含まれているか判定
 *)
let check_record rcd =
  let xs = List.filter_map (
    fun (b,_) -> match b with Eager x | Lazy x -> Some x | Wild -> None
  ) rcd in
    List.check_dup (fun x -> raise (Multiple_labels x)) xs;
    rcd

(* 定数項の生成用関数 *)
let tm_int n    = TmCon(CnInt n,[])
let tm_rea r    = TmCon(CnRea r,[])
let tm_str s    = TmCon(CnStr s,[])
let tm_sym s vs = TmCon(CnSym s,vs)
