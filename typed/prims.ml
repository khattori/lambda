(** プリミティブの定義
    
    新たなコンストラクタ定数や演算子などはここで定義してやればよい．
    
*)

open Absyn
open Const

let tm_unit  = TmCon(CnSym "unit",[])

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
let outs_ store cs = match cs with
  | [TmCon(CnStr s,_)] -> print_string s; tm_unit
  | _ -> tm_error_wrong_argument_type "outs_"
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
  | [TmMem m1;TmMem m2; v1; v2] when m1 = m2 -> v1
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

(* 型コンストラクタ *)
let _ttor_table = [
  ( "Void",    0 );
  ( "Unit",    0 );
  ( "Int",     0 );
  ( "String",  0 );
  ( "Real",    0 );
  ( "Bool",    0 );
  ( "Ref",     1 );
]
let tvoid   = TyCon(TyCSym "Void",[])
let tunit   = TyCon(TyCSym "Unit",[])
let tbool   = TyCon(TyCSym "Bool",[])
let tint    = TyCon(TyCSym "Int",[])
let treal   = TyCon(TyCSym "Real",[])
let tstring = TyCon(TyCSym "String",[])
let tref ty = TyCon(TyCSym "Ref",[ty])
(* コンストラクタ *)
let _ctor_table = [
  ( "unit",  (0, tunit) );
  ( "true",  (0, tbool) );
  ( "false", (0, tbool) );
]

(* デストラクタ *)
let _dtor_table = [
  ( "iadd_", (2, iadd_, tarrows[tint;tint;tint]) );
  ( "isub_", (2, isub_, tarrows[tint;tint;tint]) );
  ( "imul_", (2, imul_, tarrows[tint;tint;tint]) );
  ( "idiv_", (2, idiv_, tarrows[tint;tint;tint]) );
  ( "imod_", (2, imod_, tarrows[tint;tint;tint]) );
  ( "itos_", (1, itos_, tarrow tint tstring )   );
  ( "mtos_", (1, mtos_, TyAll("t",tarrow (tref(TyVar 0)) tstring)) );
  ( "scat_", (2, scat_, tarrows[tstring;tstring;tstring]) );
  ( "outs_", (1, outs_, tarrow tstring tunit)  );
  ( "igt_",  (4, igt_,  TyAll("t",tarrows[tint;tint;TyVar 0;TyVar 0;TyVar 0])) );
  ( "ref",   (1, ref_,  TyAll("t",tarrow (TyVar 0) (tref(TyVar 0))))   );
  ( "!",     (1, drf_,  TyAll("t",tarrow (tref(TyVar 0)) (TyVar 0)))   );
  ( ":=",    (2, asn_,  TyAll("t",tarrows[tref(TyVar 0);TyVar 0;TyVar 0]))   );
  ( "beq_",  (4, beq_,  TyAll("t0",TyAll("t1",tarrows[TyVar 0;TyVar 0;TyVar 1;TyVar 1;TyVar 1])))   );
(*  ( "fix",   (1, fix_)   ); *)
  ( "exit",  (0, exit_, tvoid)  );
  ( "error", (1, error_, tarrow tstring tvoid) );
]

(* デストラクタの関数を取得 *)
let get_dtor_fun d =
  let _,f,_ = List.assoc d _dtor_table in f

(* 定数シンボルテーブルに登録 *)
let _ =
  List.iter (fun (s,(arity,_))   -> Const.add_ctor s arity) _ctor_table;
  List.iter (fun (s,(arity,_,_)) -> Const.add_dtor s arity) _dtor_table

let typ_table =
  List.map (fun (s,(_,t)) -> s,t) _ctor_table
    @ List.map (fun (s,(_,_,t)) -> s,t) _dtor_table

let get_const_type s =
  List.assoc s typ_table
