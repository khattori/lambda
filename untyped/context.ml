exception Multiple_names of string
exception Unbound_name of string

type binder =
  | Wild
  | Eager of string
  | Lazy of string

type 'a binding =
  | NameBind
  | TermBind of 'a * int

type 'a t = (string * 'a binding) list

let empty = []

let index2name ctx x =
  Printf.sprintf "%s(%d)" (fst(List.nth ctx x)) x

let rec name2index ctx x =
  match ctx with
    | [] -> raise (Unbound_name x)
    | (y,_)::rest ->
        if y = x then 0 else 1 + (name2index rest x)
let add_term ctx x tm o =
  (x,TermBind(tm,o))::ctx

let add_bind ctx b = match b with
  | Wild    -> ("_",NameBind)::ctx
  | Eager x -> (x,  NameBind)::ctx
  | Lazy x  -> (x,  NameBind)::ctx
let add_binds ctx bs =
  let bs' = List.filter (function Eager s | Lazy s -> true | _ -> false) bs in
  let xs = List.map (function Eager s | Lazy s -> s | _ -> assert false) bs' in
  let xs = List.sort compare xs in
  let _ =
    List.fold_left (
      fun x y -> if x = y then raise (Multiple_names x) else y
    ) "" xs
  in
    List.fold_left add_bind ctx bs

let rec fresh_name ctx x =
  if List.mem_assoc x ctx
  then
    fresh_name ctx (x ^ "'")
  else
    ((x,NameBind)::ctx), x

let get_term ctx x =
  match snd(List.nth ctx x) with
    | TermBind(tm,o) -> tm,o
    | _ -> assert false


