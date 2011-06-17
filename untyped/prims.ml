(** プリミティブの定義 *)
open Absyn
open Const

let tm_error msg = TmApp(TmCon(CSym "error"),TmCon(CStr msg))
let tm_error_wrong_argument_type s =
  tm_error (s ^ ": wrong argument type")
let tm_error_divided_by_zero s =
  tm_error (s ^ ": divided by zero")

let error_ store cs = match cs with
  | [TmCon(CStr msg)] -> failwith msg
  | [v] -> tm_error_wrong_argument_type "error_"
  | _ -> assert false

let hd_ store cs = match cs with
  | [TmApp(TmApp(TmCon(CSym "::"),v),_)] -> v
  | _ -> tm_error_wrong_argument_type "hd_"
let tl_ store cs = match cs with
  | [TmApp(TmApp(TmCon(CSym "::"),_),v)] -> v
  | _ -> tm_error_wrong_argument_type "tl_"

(* 整数演算 *)
let iadd_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] -> TmCon(CInt(n + m))
  | _ -> tm_error_wrong_argument_type "iadd_"
let isub_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] -> TmCon(CInt(n - m))
  | _ -> tm_error_wrong_argument_type "isub_"
let imul_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] -> TmCon(CInt(n * m))
  | _ -> tm_error_wrong_argument_type "imul_"
let idiv_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] ->
      (try TmCon(CInt(n / m)) with _ -> tm_error_divided_by_zero "idiv_")
  | _ -> tm_error_wrong_argument_type "idiv_"
let imod_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] ->
      (try TmCon(CInt(n mod m)) with _ -> tm_error_divided_by_zero "imod_")
  | _ -> tm_error_wrong_argument_type "imod_"
let igt_  store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m); v1; v2] ->
      if n > m then v1 else v2
  | _ -> tm_error_wrong_argument_type "igt_"

(* 格納域操作 *)
let ref_ store cs = match cs with
  | [v] ->
      let m = Store.extend store v in TmCon(CMem m)
  | _ -> assert false
let drf_ store cs = match cs with
  | [TmCon(CMem m)] -> Store.lookup store m
  | _ -> tm_error_wrong_argument_type "drf_"
let asn_ store cs = match cs with
  | [TmCon(CMem m);tm] -> Store.update store m tm; TmCon(CSym "unit")
  | _ -> tm_error_wrong_argument_type "asn_"
(* 等価比較 *)
let beq_ store cs = match cs with
  | [c1; c2; v1; v2] when is_cstr_value c1 && is_cstr_value c2 && c1 = c2 -> v1
  | [x; y; v1; v2] -> v2
  | _ -> assert false

(*
 * fix v => v (fix v)
 *)
(*
let fix_ store cs = match cs with
  | [v] -> TmApp(v,(TmApp(TmCon(CSym "fix"),v)))
  | _ -> assert false
*)
(* 
 * exit => 終了
 *)
let exit_ store cs = match cs with
  | [] -> exit 0
  | _ -> assert false

(** プリミティブの定義 *)

let cstr_table = [
  ( "::",    2 );
]

let dstr_table = [
  ( "hd",    (1, hd_)    );
  ( "tl",    (1, tl_)    );
  ( "iadd_", (2, iadd_)  );
  ( "isub_", (2, isub_)  );
  ( "imul_", (2, imul_)  );
  ( "idiv_", (2, idiv_)  );
  ( "imod_", (2, imod_)  );
  ( "igt_",  (4, igt_)   );
  ( "ref",   (1, ref_)   );
  ( "!",     (1, drf_)   );
  ( ":=",    (2, asn_)   );
  ( "beq",   (4, beq_)   );
(*  ( "fix",   (1, fix_)   ); *)
  ( "exit",  (0, exit_)  );
  ( "error", (1, error_) );
]

let dstr_apply d store vs =
  let arity,f = List.assoc (get_symbol d) dstr_table in
    if arity == List.length vs then
      f store vs
    else
      assert false

let _ =
  Const.table_ref :=
    (List.map (fun (s,arity)     -> s,Cstr arity) cstr_table)
  @ (List.map (fun (s,(arity,_)) -> s,Dstr arity) dstr_table)

(*
data true;
data false;
def if    = \b.\(t1).\(t2).case b of true -> t1
                                   | false -> t2
                                   | ... -> (\x.error "if: type mismatch");
def ==    = \t1.\t2.beq t1 t2 true false;
def not   = \t.== t false;
def andalso = \t1.\(t2).if t1 t2 false;
def orelse  = \t1.\(t2).if t1 true t2;
def !=    = \t1.\t2.beq t1 t2 false true;
def >     = \t1.\t2.igt_ t1 t2 true false;
def >=    = \t1.\t2.orelse (> t1 t2) (== t1 t2);
def <     = \t1.\t2.igt_ t2 t1 true false;
def <=    = \t1.\t2.orelse (< t1 t2) (== t1 t2);
def min   = \t1.\t2.if (<= t1 t2) t1 t2;
def max   = \t1.\t2.if (>= t1 t2) t1 t2;

def fix   = \f.(\x.f (x x)) (\x.f (x x));
def fact  = fix (\(fact).\n.if (== n 0) 1 ( imul_ n (fact (isub_ n 1))));

def evenodd =
        fix (\(eo).:: (\n.if (== n 0) true (tl eo (isub_ n 1)))
                           (\n.if (== n 0) false (hd eo (isub_ n 1))));
def even = hd evenodd
and odd  = tl evenodd;




*)
