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

(** 項の定義 *)
(*
  E ::= x (∈ Ident)
      | c v1 ... vn    ---  c(∈ Const)
      | m (∈ Address)
      | \B.E
      | E1 E2
      | let B = E1 in E2
      | case E of c1 -> E1 | ... -> En
      | E1,...,En                         --- タプル
      | { b1 = E1; ...; bn = En }         --- レコード
      | E.l                               --- 要素参照 
  b ::= l | \l | _     l (∈ Label) 
  B ::= x | \x | _ | B,B 
*)
type term =
  | TmVar of int
  | TmMem of int
  | TmCon of const * term list
  | TmAbs of binder * term
  | TmApp of term * term
  | TmLet of binder * term * term

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
    | TmAbs(b,tm) ->
        let ctx',s = to_string_bind b in
          sprintf "(\\%s.%s)" s (to_string ctx' tm)
    | TmApp(tm1,tm2) ->
        sprintf "(%s %s)" (to_string ctx tm1) (to_string ctx tm2)
    | TmLet(b,tm1,tm2) ->
        let ctx',s = to_string_bind b in
          sprintf "(let %s = %s in %s)"
            s (to_string ctx tm1) (to_string ctx' tm2)
and to_string_bind ctx b = match b with
  | Wild    -> "_"
  | Eager x -> sprintf "%s" x
  | Lazy  x -> sprintf "\\%s" x
and to_string_binding ctx (b,tm) =
  sprintf    "%s = %s" (to_string_bind ctx b) (to_string ctx tm)

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
let term_map onvar t =
  let rec walk c t = match t with
    | TmVar x           -> onvar c x
    | TmCon(cn,vs)      -> TmCon(cn,List.map (walk c) vs)
    | TmAbs(b,t1)       -> TmAbs(b,walk (c + 1) t1)
    | TmApp(t1,t2)      -> TmApp(walk c t1,walk c t2)
    | TmLet(b,t1,t2)    -> TmLet(b,walk c t1, walk (c + 1) t2)
    | other             -> other
  in
    walk 0 t

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
let term_shift d t =
  term_map
    (fun c x -> if x >= c then TmVar(x + d) else TmVar x)
    t

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
let term_subst j s t =
  term_map
    (fun c x -> if x == j + c then term_shift c s else TmVar x)
    t

(*
 * subst_top: β簡約における置換
 * 
 *   (\x.t1) t2 → ↑-1,0([0:->↑1,0(t2)]t1)
 *
 *)
(*
let term_subst_top t1 t2 =
  term_shift (-1) (term_subst 0 (term_shift 1 t2) t1)
*)
(*
 * (\x.t1) t2 → σ0(t1,t2)
 * 
 * σn(m,t)     = m        if m < n
 * σn(n,t)     = ↑n,0(t)
 * σn(m,t)     = m-1      if m > n
 * σn(\.t',t)  = \.σn+1(t',t)
 * σn(t1 t2,t) = σn(t1,t) σn(t2,t)
 *)
let term_subst_top t1 t2 =
  term_map
    (fun c x ->
       if x < c then TmVar x
       else if x == c then term_shift c t2
       else TmVar(x - 1))
    t1

