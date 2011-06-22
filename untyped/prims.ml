(** プリミティブの定義
    
    新たなコンストラクタ定数や演算子などはここで定義してやればよい．
    
*)

open Absyn
open Const

let tm_error msg = TmCon(CnSym "error",[TmCon(CnStr msg,[])])
let tm_error_wrong_argument_type s =
  tm_error (s ^ ": wrong argument type")
let tm_error_divided_by_zero s =
  tm_error (s ^ ": divided by zero")

let error_ store cs = match cs with
  | [TmCon(CnStr msg,_)] -> failwith msg
  | [v] -> tm_error_wrong_argument_type "error_"
  | _ -> assert false

(* 整数演算 *)
let iadd_ store cs = match cs with
  | [TmCon(CnInt n,_); TmCon(CnInt m,_)] -> tm_int(n + m)
  | _ -> tm_error_wrong_argument_type "iadd_"
let isub_ store cs = match cs with
  | [TmCon(CnInt n,_); TmCon(CnInt m,_)] -> tm_int(n - m)
  | _ -> tm_error_wrong_argument_type "isub_"
let imul_ store cs = match cs with
  | [TmCon(CnInt n,_); TmCon(CnInt m,_)] -> tm_int(n * m)
  | _ -> tm_error_wrong_argument_type "imul_"
let idiv_ store cs = match cs with
  | [TmCon(CnInt n,_); TmCon(CnInt m,_)] ->
      (try tm_int(n / m) with _ -> tm_error_divided_by_zero "idiv_")
  | _ -> tm_error_wrong_argument_type "idiv_"
let imod_ store cs = match cs with
  | [TmCon(CnInt n,_); TmCon(CnInt m,_)] ->
      (try tm_int(n mod m) with _ -> tm_error_divided_by_zero "imod_")
  | _ -> tm_error_wrong_argument_type "imod_"
let igt_  store cs = match cs with
  | [TmCon(CnInt n,_); TmCon(CnInt m,_); v1; v2] ->
      if n > m then v1 else v2
  | _ -> tm_error_wrong_argument_type "igt_"

(* 文字列演算 *)
let scat_ store cs = match cs with
  | [TmCon(CnStr s,_); TmCon(CnStr t,_)] -> tm_str(s^t)
  | _ -> tm_error_wrong_argument_type "scat_"
let itos_ store cs = match cs with
  | [TmCon(CnInt n,_)] -> tm_str(string_of_int n)
  | _ -> tm_error_wrong_argument_type "itos_"
let mtos_ store cs = match cs with
  | [TmMem n] -> tm_str("<" ^ string_of_int n ^ ">")
  | _ -> tm_error_wrong_argument_type "mtos_"

(* 格納域操作 *)
let ref_ store cs = match cs with
  | [v] ->
      let m = Store.extend store v in TmMem m
  | _ -> assert false
let drf_ store cs = match cs with
  | [TmMem m] -> Store.lookup store m
  | _ -> tm_error_wrong_argument_type "drf_"
let asn_ store cs = match cs with
  | [TmMem m;tm] -> Store.update store m tm; tm
  | _ -> tm_error_wrong_argument_type "asn_"
(* 等価比較 *)
let beq_ store cs = match cs with
  | [TmCon(c1,vs1);TmCon(c2,vs2); v1; v2] when c1 = c2 && vs1 == vs2 -> v1
  | [x; y; v1; v2] -> v2
  | _ -> assert false

(*
 * fix v => v (fix v)
 *)
(*
let fix_ store cs = match cs with
  | [v] -> TmApp(v,(TmApp(TmCon(CnSym "fix"),v)))
  | _ -> assert false
*)
(* 
 * exit => 終了
 *)
let exit_ store cs = match cs with
  | [] -> exit 0
  | _ -> assert false

(** プリミティブの定義 *)
(* コンストラクタ *)
let _ctor_table = [
  ( "nil",   0 );
  ( "cons",  2 );
  ( "true",  0 );
  ( "false", 0 );
]

(* リスト生成用関数 *)
let nil  = TmCon(CnSym "nil",[])
let cons x y = TmApp(TmApp(TmCon(CnSym "cons",[]),x),y)
let rec list = function
  | [] -> nil
  | x::xs -> cons x (list xs)

(* デストラクタ *)
let _dtor_table = [
  ( "iadd_", (2, iadd_)  );
  ( "isub_", (2, isub_)  );
  ( "imul_", (2, imul_)  );
  ( "idiv_", (2, idiv_)  );
  ( "imod_", (2, imod_)  );
  ( "itos_", (1, itos_)  );
  ( "mtos_", (1, mtos_)  );
  ( "scat_", (2, scat_)  );
  ( "igt_",  (4, igt_)   );
  ( "ref",   (1, ref_)   );
  ( "!",     (1, drf_)   );
  ( ":=",    (2, asn_)   );
  ( "beq",   (4, beq_)   );
(*  ( "fix",   (1, fix_)   ); *)
  ( "exit",  (0, exit_)  );
  ( "error", (1, error_) );
]

(* デストラクタの関数を取得 *)
let get_dtor_fun d =
  snd(List.assoc d _dtor_table)

(* 定数シンボルテーブルに登録 *)
let _ =
  List.iter (fun (s,arity)     -> Const.add_ctor s arity) _ctor_table;
  List.iter (fun (s,(arity,_)) -> Const.add_dtor s arity) _dtor_table

