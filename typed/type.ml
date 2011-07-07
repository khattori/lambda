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

type tyc =
  | TyCArr
  | TyCTpl
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

let tarrow ty1 ty2 = TyCon(TyCArr,[ty1;ty2])
let tarrows tys =
  let rec iter = function
    | [ty] -> ty
    | t::ts -> tarrow t (iter ts)
    | [] -> assert false
  in
    iter tys

let mark() = ref ()
let no_mark = mark()
let no_rank = -1
let link_to ty rank = LinkTo{ typ = ty; mark = no_mark; old = rank }

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
      sprintf "X(%d)" id
  | TyCon(TyCArr,[ty1;ty2]) ->
      sprintf "(%s -> %s)" (to_string ctx ty1) (to_string ctx ty2)
  | TyCon(TyCArr,_) -> assert false
  | TyCon(TyCTpl,ts) ->
      sprintf "(%s)" (String.concat "," (List.map (to_string ctx) ts))
  | TyCon(TyCRcd ls,ts) ->
      sprintf "{%s}"
        (String.concat ";"
           (List.map2 (fun l t -> sprintf "%s:%s" l (to_string ctx t)) ls ts))
  | TyCon(TyCSym s,[]) -> s
  | TyCon(TyCSym s,ts) ->
      sprintf "(%s %s)" s (String.concat " " (List.map (to_string ctx) ts))
  | TyAll(s,ty) ->
      let ctx',s = Context.fresh_name ctx s in
        sprintf "(<%s> => %s)" s (to_string ctx' ty)
let topt_to_string ctx = function
  | None -> ""
  | Some ty -> sprintf ":%s" (to_string ctx ty)


let ( (add_tycon: string -> int -> unit),
      (is_tycon : string -> bool) )
    =
  let table_ref_ = ref [] in
    ( (fun s arity -> table_ref_ := (s,arity)::!table_ref_),
      (fun s -> List.mem_assoc s !table_ref_) )

