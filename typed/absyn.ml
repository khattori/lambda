(**
   Absyn: 抽象構文木定義
*)
open ListAux
open Printf
open Context

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

(** 型の定義 *)
(*
  T ::= t
      | k T1...Tn
      | T -> T
      | <t> => T
*)
type tycon =
  | TyCArr
  | TyCSym of string
type typ =
  | TyVar of int
  | TyMva of link ref
  | TyCon of tycon * typ list
  | TyFun of string * typ
and link =
  | NoLink of int * int (* rank * id *)
  | LinkTo of node
and node = { typ: typ; mutable mark: unit ref; mutable old: int }

let mark() = ref ()
let no_mark = mark()
let no_rank = -1
let link_to ty rank = LinkTo{ typ = ty; mark = no_mark; old = rank }

(* パス圧縮を行う *)
let rec repr ty =
  match ty with
    | TyMva({contents=LinkTo{typ=ty;old=rank}} as link) ->
        let ty = repr ty in link := link_to ty rank; ty
    | _ -> ty

(** 型を文字列に変換する *)
let rec typ_to_string ctx = function
  | TyVar x ->
      sprintf "'%s(%d)" (Context.index2name ctx x) x
  | TyMva{contents=NoLink(r,id)} ->
      sprintf "'X<%d>" id
  | TyMva{contents=LinkTo{typ=ty}} ->
      typ_to_string ctx ty
  | TyCon(TyCSym s,[]) -> s
  | TyCon(TyCSym s,ts) ->
      sprintf "(%s %s)" s (String.concat " " (List.map (typ_to_string ctx) ts))
  | TyCon(TyCArr,[ty1;ty2]) ->
      sprintf "(%s -> %s)" (typ_to_string ctx ty1) (typ_to_string ctx ty2)
  | TyAll(x,ty) ->
      let ctx',s = Context.fresh_name ctx x in
        sprintf "('%s => %s)" s (typ_to_string ctx' ty)

let topt_to_string ctx = function
  | None -> ""
  | Some ty -> sprintf ":%s" typ_to_string ctx ty

(** 項の定義 *)
(*
  E ::= x (∈ Ident)
      | c v1 ... vn    ---  c(∈ Const)
      | m (∈ Address)
      | \b:T.E
      | \<t>.E
      | E1 E2
      | E <T>
      | let B = E1 in E2
  b ::= x | \x | _
*)
type term =
  | TmVar of int
  | TmMem of int
  | TmCon of const * term list
  | TmAbs of binder * typ option * term
  | TmTbs of string * term
  | TmApp of term * term
  | TmTpp of term * typ
  | TmLet of binder * typ option * term * term

(** 項を文字列に変換する *)
let rec to_string ctx tm =
  match tm with
    | TmVar x ->
        sprintf "%s(%d)" (Context.index2name ctx x) x
    | TmCon(cn,[]) -> const_to_string cn
    | TmCon(cn,vs) ->
        sprintf "(%s %s)"
          (const_to_string cn)
          (String.concat " " (List.map (to_string ctx) vs))
    | TmMem m -> sprintf "<%d>" m
    | TmAbs(b,topt,tm) ->
        let ctx',s = to_string_bind ctx b in
          sprintf "(\\%s%s.%s)" s (topt_to_string ctx topt) (to_string ctx' tm)
    | TmApp(tm1,tm2) ->
        sprintf "(%s %s)" (to_string ctx tm1) (to_string ctx tm2)
    | TmLet(b,topt,tm1,tm2) ->
        let ctx',s = to_string_bind ctx b in
          sprintf "(let %s%s = %s in %s)"
            s (to_string ctx tm1) (topt_to_string ctx topt)
            (to_string ctx' tm2)
    | TmTbs(t,tm) ->
        let ctx',s = Context.fresh_name ctx t in
          sprintf "(\\<%s>.%s)" s (to_string ctx' tm)
    | TmTpp(tm1,ty2) ->
        sprintf "(%s <%s>)" (to_string ctx tm1) (typ_to_string ctx ty2)

and to_string_bind ctx b = match b with
  | Wild -> (Context.add_bind ctx b),"_"
  | Eager x -> Context.fresh_name ctx x
  | Lazy x  ->
      let ctx',x' = Context.fresh_name ctx x
      in
        ctx',sprintf "\\%s" x'
and to_string_binding ctx (b,tm) = match b with
  | Wild    -> sprintf    "_ = %s"   (to_string ctx tm)
  | Eager x -> sprintf   "%s = %s" x (to_string ctx tm)
  | Lazy  x -> sprintf "\\%s = %s" x (to_string ctx tm)

(*
 * print: 抽象構文木の出力
 *)
let rec print ctx tm =
  print_string (to_string ctx tm)

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
  in
    walk c ty

let term_map onvar ontyp c tm =
  let rec walk c tm = match tm with
    | TmVar x               -> onvar c x
    | TmCon(cn,vs)          -> TmCon(cn,List.map (walk c) vs)
    | TmAbs(b,None,tm')     -> TmAbs(b,None,walk (c+1) tm')
    | TmAbs(b,Some ty1,tm2) -> TmAbs(b,Some(ontype c ty1),walk (c+1) tm2)
    | TmApp(tm1,tm2)        -> TmApp(walk c tm1,walk c tm2)
    | TmLet(b,None,tm1,tm2) -> TmLet(b,None,walk c tm1, walk (c+1) tm2)
    | TmLet(b,Some ty,tm1,tm2) ->
        TmLet(b,Some(ontype c ty),walk c tm1, walk (c+1) tm2)
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
    j TmT

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
  term_shfit (-1) (tytm_subst 0 (typ_shift 1 tyS) tmT)

