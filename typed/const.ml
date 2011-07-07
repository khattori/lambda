(** 定数項の操作 *)

open Printf
open Context
open Type

(** シンボルの種類 *)
type kind =
  | Ctor of int      (** コンストラクタ: アリティ *)
  | Dtor of int      (** デストラクタ　: アリティ *)

(** 定数項の定義 *)
type t =
  | CnInt  of int                (** 整数         *)
  | CnRea  of float              (** 浮動小数点数 *)
  | CnStr  of string             (** 文字列       *)
  | CnSym  of string             (** 定数シンボル *)

(** 定数項を文字列表現に変換する *)
let to_string = function
  | CnInt i -> sprintf "%d" i
  | CnRea d -> sprintf "%g" d
  | CnStr s -> sprintf "%S" s
  | CnSym s -> s

let tint     = TyCon(TyCSym "Int",   []  )
let treal    = TyCon(TyCSym "Real",  []  )
let tstring  = TyCon(TyCSym "String",[]  )

(* コンストラクタ／デストラクタのシンボルテーブル *)
let _table_ref = ref []

(** コンストラクタを登録する *)
let add_ctor (s:string) arity =
  _table_ref := (s,Ctor arity)::!_table_ref

(** デストラクタを登録する *)
let add_dtor (s:string) arity =
  _table_ref := (s,Dtor arity)::!_table_ref

(** 文字列がシンボル定数か判定する *)
let is_symbol (s:string) =
  List.mem_assoc s !_table_ref

(** コンストラクタか判定する *)
let is_ctor = function
  | CnInt _ | CnStr _ | CnRea _ -> true
  | CnSym s ->
      match List.assoc s !_table_ref with
        | Ctor _ -> true | Dtor _ -> false

(** デストラクタか判定する *)
let is_dtor cn = not(is_ctor cn)

(** 定数項のアリティ（引数の数）を取得する *)
let arity = function
  | CnInt _ | CnRea _ | CnStr _ -> 0
  | CnSym s ->
      match List.assoc s !_table_ref with Ctor n | Dtor n -> n

let ( (add_type: string -> Type.t -> unit),
      (get_type: string -> Type.t) )
    =
  let table_ref_ = ref [] in
    ( (fun s t -> table_ref_ := (s,t)::!table_ref_),
      (fun s -> List.assoc s !table_ref_) )

let to_type = function
  | CnInt _ -> tint
  | CnRea _ -> treal
  | CnStr _ -> tstring
  | CnSym s -> get_type s

