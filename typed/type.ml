(** 型定義 *)
(*
  T ::= t
      | k T...T 　　　　
      | T -> T
      | T,...,T
      | { l:T;...;l:T }
  S ::= T 
      | \/t.S
*)
open Printf
open ListAux
open Const

type tyc =
  | TyCArr
  | TyCTpl of int
  | TyCRcd of string list
  | TyCSym of string

type t =
  | TyVar of int
  | TyMva of link ref
  | TyCon of tyc * t list
  | TyAll of string * t
and link =
  | NoLink of int * int (* id * rank *)
  | LinkTo of node
and node = { typ: t; mutable mark: unit ref; mutable old: int }

let tint           = TyCon(TyCSym "Int",   []  )
let treal          = TyCon(TyCSym "Real",  []  )
let tstring        = TyCon(TyCSym "String",[]  )

let tarrow ty1 ty2 = TyCon(TyCArr,[ty1;ty2])
let tarrows tys =
  let rec iter = function
    | [ty] -> ty
    | t::ts -> tarrow t (iter ts)
    | [] -> assert false
  in
    iter tys

let vararg_ctor tycon n =
  let rec iter i ty =
    if i < 0 then
      ty
    else
      iter (i-1) (TyAll(sprintf "t%d" i,ty))
  in
  let tvs = List.make (fun i -> TyVar i) n in
    iter (n-1) (tarrows (tvs@[TyCon(tycon,tvs)]))

let ttuple a =
  vararg_ctor (TyCTpl a) a

let trecord xs =
  vararg_ctor (TyCRcd xs) (List.length xs)

let mark() = ref ()
let no_mark = mark()
let no_rank = -1
let link_to ty rank = LinkTo{ typ = ty; mark = no_mark; old = rank }

(** 新しいメタ変数を生成 *)
let fresh_mvar =
  let id_ref_ = ref 0
  in
    fun rank ->
      let id = !id_ref_ in
      let mvar = TyMva(ref (NoLink(id,rank)))
      in
        incr id_ref_;
        mvar

(* パス圧縮 *)
let rec repr = function
  | TyMva({contents=LinkTo{typ=ty;old=rank}} as link) ->
      let ty = repr ty in link := link_to ty rank; ty
  | ty -> ty

let rec to_string ctx = function
  | TyVar x -> sprintf "%s(%d)" (Context.index2name ctx x) x
  | TyMva({contents=LinkTo{typ=ty}}) -> to_string ctx ty
  | TyMva({contents=NoLink(id,_)}) ->
      sprintf "X%d" id
  | TyCon(TyCArr,[ty1;ty2]) ->
      sprintf "(%s -> %s)" (to_string ctx ty1) (to_string ctx ty2)
  | TyCon(TyCArr,_) -> assert false
  | TyCon(TyCTpl _,ts) ->
      sprintf "(%s)" (String.concat ", " (List.map (to_string ctx) ts))
  | TyCon(TyCRcd ls,ts) ->
      sprintf "{ %s }"
        (String.concat "; "
           (List.map2 (fun l t -> sprintf "%s: %s" l (to_string ctx t)) ls ts))
  | TyCon(TyCSym s,[]) -> s
  | TyCon(TyCSym s,ts) ->
      sprintf "(%s %s)" s (String.concat " " (List.map (to_string ctx) ts))
  | TyAll(s,ty) ->
      let ctx',s = Context.fresh_name ctx s in
        sprintf "(<%s> => %s)" s (to_string ctx' ty)
let topt_to_string ctx = function
  | None -> ""
  | Some ty -> sprintf ":%s" (to_string ctx ty)

(* 型コンストラクタ登録 *)
let ( (add_tycon      : string -> int -> unit),
      (is_symbol_tycon: string -> bool) )
    =
  let table_ref_ = ref [] in
    ( (fun s arity -> table_ref_ := (s,arity)::!table_ref_),
      (fun s -> List.mem_assoc s !table_ref_) )

(* データコンストラクタの型登録 *)
let ( (add_const: string -> t -> unit),
      (get_type : string -> t) )
    =
  let table_ref_ = ref [] in
    ( (fun s t -> table_ref_ := (s,t)::!table_ref_),
      (fun s -> List.assoc s !table_ref_) )

(** 定数の型を取得 *)
let of_const = function
  | CnInt _ -> tint
  | CnRea _ -> treal
  | CnStr _ -> tstring
  | CnTpl a -> ttuple a
  | CnNth i -> TyAll("t0",TyAll("t1",tarrow (TyVar 0) (TyVar 1)))
  | CnRcd ls-> trecord ls
  | CnSel l -> TyAll("t0",TyAll("t1",tarrow (TyVar 0) (TyVar 1)))
  | CnSym s -> get_type s
