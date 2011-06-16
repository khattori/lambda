(**
   Absyn: 抽象構文木定義
*)
open Printf
open Context

exception Parse_error

(* 項の定義 *)
(*
  E ::= x (∈ Ident)
      | c (∈ Const)
      | \x.E | \(x).E
      | E1 E2
      | let x = E1 in E2 | let x ::= E1 in E2
*)

type term =
  | TmVar of int
  | TmCon of Const.t
  | TmAbs of strategy * string * term
  | TmApp of term * term
  | TmLet of bind list * term
and bind = strategy * string * term
and command =
  | Defn of bind list
  | Eval of term
  | Noop

(*
 * print: 抽象構文木の出力
 * 
 *)
let rec print ctx tm =
  match tm with
    | TmVar x -> print_string (Context.index2name ctx x)
    | TmCon c -> Const.print c
    | TmAbs(Eager,x,tm) ->
        let ctx',x' = Context.fresh_name ctx x in
          printf "(\\%s" x'; printf "."; print ctx' tm; printf ")"
    | TmAbs(Lazy,x,tm) ->
        let ctx',x' = Context.fresh_name ctx x in
          printf "(\\(%s)" x'; printf "."; print ctx' tm; printf ")"
    | TmApp(tm1,tm2) ->
        printf "("; print ctx tm1; printf " "; print ctx tm2; printf ")"
    | TmLet(binds,tm2) ->
        printf "(let ";
        let ctx' = List.fold_left (print_bind ctx) ctx binds
        in
          printf " in ";
          print ctx' tm2; printf ")"
and print_bind ctx ctx' (s,x,tm) =
  let ctx'', x' = Context.fresh_name ctx' x in
    (
      match s with
        | Eager -> printf "%s = " x'
        | Lazy  -> printf "%s ::= " x'
    );
    print ctx tm; printf ";"; ctx''


(* De Bruijin index *)
(*
 * map: 項置換のための補助関数
 *
 *)
let term_map onvar t =
  let rec walk c t = match t with
    | TmVar x         -> onvar c x
    | TmAbs(s,x,t1)   -> TmAbs(s,x,walk (c + 1) t1)
    | TmApp(t1,t2)    -> TmApp(walk c t1,walk c t2)
    | TmLet(binds,t2) ->
        TmLet(List.map (fun (s,x,t1) -> s,x,walk c t1) binds,
              walk (c + (List.length binds)) t2)
    | con             -> con
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

(*
 * is_value: 項が値かどうか判定
 * 
 *)
let rec is_value tm =
  let rec walk tm =
    match tm with
      | TmApp(tm1,tm2) when is_value tm2 -> walk tm1 - 1
      | TmCon(c) when Const.is_cstr c -> Const.arity c
      | TmCon(c) when Const.is_dstr c -> Const.arity c - 1
      | TmCon _ | TmAbs _ -> 0
      | _ -> -1
  in
    walk tm >= 0

let check_value oncon tm =
  let rec walk tm =
    match tm with
      | TmCon(c) when oncon c -> Const.arity c
      | TmApp(tm1,tm2) when is_value tm2 -> walk tm1 - 1
      | _ -> -1
  in
    walk tm == 0

(*
 * is_dstr_value: 項がデストラクタかどうか判定
 *)
let is_dstr_value tm =
  check_value Const.is_dstr tm

(*
 * is_cstr_value: 項がコンストラクタかどうか判定
 *)
let is_cstr_value tm =
  check_value Const.is_cstr tm


