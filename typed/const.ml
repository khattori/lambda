(** 定数項の操作 *)

open Printf
open Context
open Absyn

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

(*
 * is_value: 項が値かどうか判定
 * 
 *)
let rec is_value tm =
  let rec walk tm =
    match tm with
      | TmCon(CnSym s,vs) -> (
            match List.assoc s !_table_ref with
              | Ctor _ -> true
              | Dtor a -> List.length vs < a
        )
      | TmCon _ | TmMem _ | TmAbs _ -> true
      | _ -> false
  in
    walk tm



(* 定数項の生成用関数 *)
let tm_int n    = TmCon(CnInt n,[])
let tm_rea r    = TmCon(CnRea r,[])
let tm_str s    = TmCon(CnStr s,[])
let tm_sym s vs = TmCon(CnSym s,vs)
