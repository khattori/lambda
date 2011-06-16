open Printf

type t =
  | CInt of int
  | CSym of string
  | CMem of int

let print = function
  | CInt i -> printf "%d" i
  | CSym s -> print_string s
  | CMem m -> printf "<%d>" m

type kind =
  | Cstr of int
  | Dstr of int

let table_ref: (string * kind) list ref = ref []

let is_cstr c = match c with
  | CMem _ -> false
  | CInt _ -> true
  | CSym s ->
      match List.assoc s !table_ref with
        | Cstr _ -> true | Dstr _ -> false

let is_dstr c = match c with
  | CMem _ -> false
  | CInt _ -> false
  | CSym s ->
      match List.assoc s !table_ref with
        | Cstr _ -> false | Dstr _ -> true

let arity c = match c with
  | CMem _ -> assert false
  | CInt _ -> 0
  | CSym s ->
      match List.assoc s !table_ref with
        | Cstr a | Dstr a -> a
