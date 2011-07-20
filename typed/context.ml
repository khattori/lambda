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

let is_lazy = function Lazy _ -> true | _ -> false
let binder_to_string = function
  | Wild    -> "_"
  | Eager x -> Printf.sprintf "%s" x
  | Lazy x  -> Printf.sprintf "\\%s" x

(** 束縛エントリの種別定義 *)
type ('a,'b) binding =
  | NameBind                        (** 変数名 *)
  | TypeBind of 'b
  | TermBind of 'a * int
  | GlblBind of 'a * 'a * 'b * int  (** 大域変数管理 *)


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

let on_bind ctx add = function
  | Wild             -> add ctx "_"
  | Eager x | Lazy x -> add ctx x

(** コンテクストに名前を追加 **)
let add_name  ctx x  = (x,NameBind)::ctx
let add_names ctx xs =
  List.check_dup (fun s -> raise (Multiple_names s)) xs;
  List.fold_left add_name ctx xs

(** コンテクストに名前束縛を追加する *)
let add_namebind  ctx b  = on_bind ctx add_name b
let add_namebinds ctx bs =
  let xs =
    List.filter_map
      (function Eager s | Lazy s -> Some s | _ -> None) bs in
    List.check_dup (fun s -> raise (Multiple_names s)) xs;
    List.fold_left add_namebind ctx bs

(** コンテクストに大域変数の定義を追加する

    @param ctx コンテクスト
    @param x 大域変数名
    @param tm 定義する項
    @param o 同時定義のためのオフセット

    @return 新しいコンテクスト
*)
let add_glbl     ctx x tm1 tm2 ty o = (x,GlblBind(tm1,tm2,ty,o))::ctx
let add_glblbind ctx b tm1 tm2 ty o = on_bind ctx add_glbl b tm1 tm2 ty o

let add_term     ctx x tm o = (x,TermBind(tm,o))::ctx
let add_termbind ctx b tm o = on_bind ctx add_term b tm o

let add_type      ctx x ty  = (x,TypeBind ty)::ctx
let add_typebind  ctx b ty  = on_bind ctx add_type b ty
let add_typebinds ctx bs ts = List.fold_left2 add_typebind ctx bs ts

(** 変数名をコンテクストに追加する．

    既に，同じ名前がコンテクストに登録されていた場合，名前の付け替えを
    行う．
*)
let rec fresh_name ctx x =
  if List.mem_assoc x ctx
  then
    fresh_name ctx (x ^ "'")
  else
    add_name ctx x, x

(** コンテクストを参照し，大域変数の定義を取得する

    @param ctx コンテクスト
    @param x 大域変数名

    @return 対応する項とオフセットの組
*)
let get_term ctx x =
  match snd(List.nth ctx x) with
    | TermBind(tm,o) -> tm,o
    | GlblBind(tm1,tm2,_,o) -> tm2,o
    | _ -> assert false
let can_get_term ctx x =
  match snd(List.nth ctx x) with
    | TermBind _ | GlblBind _  -> true
    | _ -> false

let get_typ ctx x =
  match snd(List.nth ctx x) with
    | GlblBind(_,_,ty,_) -> ty
    | TypeBind ty -> ty
    | _ -> assert false

let get_glbl ctx x =
  match snd(List.nth ctx x) with
    | GlblBind(tm1,tm2,_,o) -> tm1,o
    | _ -> assert false
