open Printf

type t =
  | CInt  of int
  | CReal of float
  | CStr  of string
  | CSym  of string
  | CMem  of int

let to_string = function
  | CInt i  -> sprintf "%d" i
  | CReal d -> sprintf "%g" d
  | CSym s  -> s
  | CStr s  -> sprintf "\"%s\"" s
  | CMem m  -> sprintf "<%d>" m
let print c = print_string (to_string c)

type kind =
  | Cstr of int
  | Dstr of int

let get_symbol c = match c with
  | CSym s -> s
  | _ -> assert false

let table_ref: (string * kind) list ref = ref []
let is_symbol s = List.mem_assoc s !table_ref
let add_cstr c arity =
  table_ref := (c,Cstr arity)::!table_ref

let is_cstr c = match c with
  | CMem _ -> false
  | CInt _ | CStr _ | CReal _ -> true
  | CSym s ->
      match List.assoc s !table_ref with
        | Cstr _ -> true | Dstr _ -> false

let is_dstr c = match c with
  | CMem _ | CInt _ | CReal _ | CStr _ -> false
  | CSym s ->
      match List.assoc s !table_ref with
        | Cstr _ -> false | Dstr _ -> true

let arity c = match c with
  | CMem _ -> assert false
  | CInt _ | CReal _ | CStr _ -> 0
  | CSym s ->
      match List.assoc s !table_ref with
        | Cstr a | Dstr a -> a
