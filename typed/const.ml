(** 定数項の操作 *)

open Printf
open Context

(** シンボルの種類 *)
type kind =
  | Ctor of int      (** コンストラクタ: アリティ *)
  | Dtor of int      (** デストラクタ　: アリティ *)

(** 定数項の定義 *)
type t =
  | CnInt  of int                (** 整数           *)
  | CnRea  of float              (** 浮動小数点数   *)
  | CnStr  of string             (** 文字列         *)
  | CnTpl  of int                (** タプル         *)
  | CnNth  of int                (** タプル取り出し *)
  | CnRcd  of string list        (** レコード       *)
  | CnSel  of string             (** フィールド選択 *)
  | CnSym  of string             (** 定数シンボル   *)

(** 定数項を文字列表現に変換する *)
let to_string = function
  | CnInt i -> sprintf "%d" i
  | CnRea d -> sprintf "%g" d
  | CnStr s -> sprintf "%S" s
  | CnTpl a -> sprintf "(,<%d>)" a
  | CnNth i -> sprintf "#%d" i
  | CnRcd ls-> sprintf "{%s}" (String.concat ";" ls)
  | CnSel s -> sprintf "#%s" s
  | CnSym s -> s

(* コンストラクタ／デストラクタのシンボルテーブル *)
let _table_ref = ref []

(** コンストラクタを登録する *)
let add_ctor (s:string) arity =
  _table_ref := (s,Ctor arity)::!_table_ref

(** デストラクタを登録する *)
let add_dtor (s:string) arity =
  _table_ref := (s,Dtor arity)::!_table_ref

let cn_map onlit ontpl onnth onrcd onsel onsym = function
  | CnInt _ | CnRea _ | CnStr _ -> onlit
  | CnTpl a  -> ontpl a
  | CnNth i  -> onnth i
  | CnRcd ls -> onrcd ls
  | CnSel l  -> onsel l
  | CnSym s  -> onsym (List.assoc s !_table_ref)

(** 文字列がシンボル定数か判定する *)
let is_symbol_const (s:string) =
  List.mem_assoc s !_table_ref

(** 定数項のアリティ（引数の数）を取得する *)
let arity =
  cn_map
    0
    (fun n -> n)
    (fun _ -> 1)
    (fun ls -> List.length ls)
    (fun _ -> 1)
    (function Ctor n | Dtor n -> n)

(** コンストラクタか判定する *)
let is_ctor =
  cn_map
    true
    (fun _ -> true)
    (fun _ -> false)
    (fun _ -> true)
    (fun _ -> false)
    (function Ctor _ -> true | Dtor _ -> false)

(** デストラクタか判定する *)
let is_dtor cn = not(is_ctor cn)

(** 値か判定する *)
let is_value c vs =
  let n = List.length vs in
  let a = arity c in
    if is_ctor c then n <= a else n < a

