(** 束縛管理のためのコンテクスト操作：

    - De Bruijinインデックスの変換
    - 大域変数の定義
*)

open ListAux

(** 同一の変数名が一度に多重定義された *)
exception Multiple_names of string
(** 未定の変数名の参照 *)
exception Unbound_name of string

(** 束縛変数の種別定義 *)
type binder =
  | Wild                 (** ワイルドカード（無名変数）*)
  | Eager of string      (** 先行評価される変数 *)
  | Lazy of string       (** 遅延評価される変数 *)

(** 束縛エントリの種別定義 *)
type ('a,'b) binding =
  | NameBind                  (** 変数名 *)
  | TermBind of 'a * 'b * int (** 大域変数管理：項と型同時束縛時のoffsetの組 *)


(** コンテクスト型の定義 *)
type ('a,'b) t = (string * ('a,'b) binding) list

(** 空のコンテクストを返す *)
let empty = []

(** コンテクストを結合する *)
let join ctx1 ctx2 = ctx1 @ ctx2

(** De Bruijinインデックスに対応する変数名を取得 *)
let index2name ctx x =
  fst (List.nth ctx x)

(** 変数名に対応するDe Bruijinインデックスを取得する *)
let rec name2index ctx x =
  match ctx with
    | [] -> raise (Unbound_name x)
    | (y,_)::rest ->
        if y = x then 0 else 1 + (name2index rest x)

(** コンテクストに名前束縛を追加する *)
let add_bind ctx b = match b with
  | Wild             -> ("_",NameBind)::ctx
  | Eager x | Lazy x -> (x,  NameBind)::ctx

(** add_bindの複数バージョン．
    同じ名前を登録するとMultiple_names例外を投げる．
*)
let add_binds ctx bs =
  let xs =
    List.filter_map
      (function Eager s | Lazy s -> Some s | _ -> None) bs in
    List.check_dup (fun s -> raise (Multiple_names s)) xs;
    List.fold_left add_bind ctx bs

(** 変数名をコンテクストに追加する．

    既に，同じ名前がコンテクストに登録されていた場合，名前の付け替えを
    行う．
*)
let rec fresh_name ctx x =
  if List.mem_assoc x ctx
  then
    fresh_name ctx (x ^ "'")
  else
    ((x,NameBind)::ctx), x

(** コンテクストに大域変数の定義を追加する

    @param ctx コンテクスト
    @param x 大域変数名
    @param tm 定義する項
    @param o 同時定義のためのオフセット

    @return 新しいコンテクスト
*)
let add_term ctx x tm ty o =
  (x,TermBind(tm,ty,o))::ctx

(** コンテクストを参照し，大域変数の定義を取得する

    @param ctx コンテクスト
    @param x 大域変数名

    @return 対応する項とオフセットの組
*)
let get_term ctx x =
  match snd(List.nth ctx x) with
    | TermBind(tm,_,o) -> tm,o
    | _ -> assert false

let get_typ ctx x =
  match snd(List.nth ctx x) with
    | TermBind(_,ty,o) -> ty,o
    | _ -> assert false
