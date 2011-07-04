(**
   Absyn: 抽象構文木定義
*)
open ListAux
open Printf
open Context
open Type

exception Parse_error
exception Multiple_labels of string

(** シンボルの種類 *)
type kind =
  | Ctor of int      (** コンストラクタ: アリティ *)
  | Dtor of int      (** デストラクタ　: アリティ *)

(** 定数項の定義 *)
type const =
  | CnInt  of int                (** 整数         *)
  | CnRea  of float              (** 浮動小数点数 *)
  | CnStr  of string             (** 文字列       *)
  | CnSym  of string             (** 定数シンボル *)

(** 定数項を文字列表現に変換する *)
let const_to_string = function
  | CnInt i -> sprintf "%d" i
  | CnRea d -> sprintf "%g" d
  | CnStr s -> sprintf "%S" s
  | CnSym s -> s

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
  | TmCon of const * term list
  | TmAbs of (binder * typ option) list * term
  | TmApp of term * term
  | TmLet of (binder * typ option) list * term * term
  | TmTpl of term list
  | TmRcd of (binder * term) list
  | TmSel of term * string
  | TmCas of term * case list
  | TmAsc of term * typ
  | TmTbs of string * term
  | TmTpp of term * typ
  | TmOvr of typ * over list
and case =
  | CsPat of const * term
  | CsDef of term
and over = typ option * term

(** 項を文字列に変換する *)
let rec to_string ((tmctx,tyctx) as ctxs) = function
  | TmVar x ->
      sprintf "%s(%d)" (Context.index2name tmctx x) x
  | TmCon(cn,[]) -> const_to_string cn
  | TmCon(cn,vs) ->
      sprintf "(%s %s)"
        (const_to_string cn)
        (String.concat " " (List.map (to_string ctxs) vs))
  | TmMem m -> sprintf "<%d>" m
  | TmAbs(b,topt,tm) ->
      let tmctx',s = to_string_bind tmctx b in
        sprintf "(\\%s%s.%s)"
          s (topt_to_string tyctx topt) (to_string (tmctx',tyctx) tm)
  | TmApp(tm1,tm2) ->
      sprintf "(%s %s)" (to_string ctxs tm1) (to_string ctxs tm2)
  | TmLet(b,topt,tm1,tm2) ->
      let tmctx',s = to_string_bind tmctx b in
        sprintf "(let %s%s = %s in %s)"
          s (topt_to_string tyctx topt) (to_string ctxs tm1)
          (to_string (tmctx',tyctx) tm2)
  | TmTbs(t,tm) ->
      let tyctx',s = Context.fresh_name tyctx t in
        sprintf "(\\<%s>.%s)" s (to_string (tmctx,tyctx') tm)
  | TmTpp(tm1,ty2) ->
      sprintf "(%s <%s>)" (to_string ctxs tm1) (Type.to_string tyctx ty2)

and to_string_bind ctx = function
  | Wild as b -> (Context.add_bind ctx b),"_"
  | Eager x   -> Context.fresh_name ctx x
  | Lazy x    ->
      let ctx',x' = Context.fresh_name ctx x
      in
        ctx',sprintf "\\%s" x'

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
    | TmVar x               -> onvar c x
    | TmMem _               -> tm
    | TmCon(cn,vs)          -> TmCon(cn,List.map (walk c) vs)
    | TmAbs(b,None,tm')     -> TmAbs(b,None,walk (c+1) tm')
    | TmAbs(b,Some ty1,tm2) -> TmAbs(b,Some(ontyp c ty1),walk (c+1) tm2)
    | TmApp(tm1,tm2)        -> TmApp(walk c tm1,walk c tm2)
    | TmLet(b,None,tm1,tm2) -> TmLet(b,None,walk c tm1, walk (c+1) tm2)
    | TmLet(b,Some ty,tm1,tm2) ->
        TmLet(b,Some(ontyp c ty),walk c tm1, walk (c+1) tm2)
    | TmTbs(t,tm')          -> TmTbs(t,walk (c+1) tm')
    | TmTpp(tm1,ty2)        -> TmTpp(walk c tm1,ontyp c ty2)
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
 * is_syntactic_value: 項がsyntacticな値かどうか判定
 *)
let is_syntactic_value = function
  | TmCon _ | TmAbs _ | TmMem _ -> true
  | _ -> false
