(** リファレンスセルのための格納域の操作:

    格納域は再利用しない（すなわちGCは未実装な）ので，無駄にリファレン
    スセルを使いまくると，メモリが尽きる．

*)

(** 格納域の型定義:
    
    配列への参照と要素数の組として表現
*)
type t = Absyn.term array ref * int ref

(* 値をインクリメントし，直前の値を返す *)
let _incr_ret n_ref =
  let n = !n_ref in incr n_ref; n

(** 新しい格納域を生成する:

    ダミーの0番地アドレスを初期値として格納しておく
*)
let create () =
  ref (Array.make 256 (Absyn.TmMem 0)), ref 0

(** 格納域に新しい領域を確保し，項を追加する:

    格納域が一杯になったら，倍の領域を確保する
 *)
let extend (arr_ref,n_ref) v =
  if Array.length !arr_ref >= !n_ref then
    arr_ref := Array.append !arr_ref !arr_ref;
  !arr_ref.(!n_ref) <- v;
  _incr_ret n_ref

(** 更新 *)
let update (arr_ref,_) addr v =
  !arr_ref.(addr) <- v

(** 参照 *)
let lookup (arr_ref,_) addr =
  !arr_ref.(addr)

