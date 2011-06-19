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
  | [c1; c2; v1; v2] when is_ctor_value c1 && is_ctor_value c2 && c1 = c2 -> v1
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
let ctor_table = [
  ( "nil", 0 );
  (* 構文木 *)
  (* type tm =      *)
  ( "tm_var", 1); (* | TmVar of int *)
  ( "tm_con", 1); (* | TmCon of Const.t *)
  ( "tm_abs", 1); (* | TmAbs of binder list * term *)
  ( "tm_app", 1); (* | TmApp of term * term *)
  ( "tm_let", 1); (* | TmLet of binder list * term * term *)
  ( "tm_cas", 1); (* | TmCas of term * case list *)
  ( "tm_tpl", 1); (* | TmTpl of term list *)
  ( "tm_rcd", 1); (* | TmRcd of (binder * term) list *)
  ( "tm_lbl", 1); (* | TmLbl of term * string *)
  ( "tm_quo", 1); (* | TmQuo of term *)
  (* and case = PatnCase of Const.t * term | DeflCase of term *)
  ( "ca_pat", 1);
  ( "ca_dfl", 1);
  (* 定数            type t =          *)
  ( "cn_int", 1); (* | CInt  of int    *)
  ( "cn_rea", 1); (* | CReal of float  *)
  ( "cn_str", 1); (* | CStr  of string *)
  ( "cn_sym", 1); (* | CSym  of string *)
  ( "cn_mem", 1); (* | CMem  of int    *)
  ( "bn_wild",  0);
  ( "bn_eager", 1);
  ( "bn_lazy",  1);
]

let sym s = TmCon(CSym s)
let nil = TmCon(CSym "nil")

let bn_wild    = sym "bn_wild"
let bn_eager x = TmApp(sym "bn_eager",TmCon(CStr x))
let bn_lazy x  = TmApp(sym "bn_lazy", TmCon(CStr x))

let ca_pat c t = TmApp(sym "ca_pat",TmTpl[c;t])
let ca_dfl t   = TmApp(sym "ca_dfl",t)

let cn_int n = TmApp(sym "cn_int",TmCon(CInt n))
let cn_rea r = TmApp(sym "cn_rea",TmCon(CReal r))
let cn_str s = TmApp(sym "cn_str",TmCon(CStr s))
let cn_sym s = TmApp(sym "cn_sym",sym s)
let cn_mem m = TmApp(sym "cn_mem",TmCon(CInt m))

let tm_var x        = TmApp(sym "tm_var",TmCon(CInt x))
let tm_con c        = TmApp(sym "tm_con",c)
let tm_abs bs t     = TmApp(sym "tm_abs",TmTpl[bs;t])
let tm_app t1 t2    = TmApp(sym "tm_app",TmTpl[t1;t2])
let tm_let bs t1 t2 = TmApp(sym "tm_let",TmTpl[bs;t1;t2])
let tm_cas t cs     = TmApp(sym "tm_cas",TmTpl[t;cs])
let tm_tpl ts       = TmApp(sym "tm_tpl",ts)
let tm_rcd rs       = TmApp(sym "tm_rcd",rs)
let tm_lbl t l      = TmApp(sym "tm_lbl",TmTpl[t;TmCon(CStr l)])
let tm_quo t        = TmApp(sym "tm_quo",t)

let dtor_table = [
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

let dtor_apply d store vs =
  let arity,f = List.assoc (get_symbol d) dtor_table in
    if arity == List.length vs then
      f store vs
    else
      assert false

let _ =
  Const.table_ref :=
    (List.map (fun (s,arity)     -> s,Ctor arity) ctor_table)
  @ (List.map (fun (s,(arity,_)) -> s,Dtor arity) dtor_table)

(*
data true;
data false;
def if    = \b.\\t1.\\t2.case b of true -> t1
                                 | false -> t2
                                 | ... -> (\x.error "if: type mismatch");
def ==    = \t1.\t2.beq t1 t2 true false;
def not   = \t.== t false;
def andalso = \t1.\\t2.if t1 t2 false;
def orelse  = \t1.\\t2.if t1 true t2;
def !=    = \t1.\t2.beq t1 t2 false true;
def >     = \t1.\t2.igt_ t1 t2 true false;
def >=    = \t1.\t2.orelse (> t1 t2) (== t1 t2);
def <     = \t1.\t2.igt_ t2 t1 true false;
def <=    = \t1.\t2.orelse (< t1 t2) (== t1 t2);
def min   = \t1.\t2.if (<= t1 t2) t1 t2;
def max   = \t1.\t2.if (>= t1 t2) t1 t2;
def fix   = \f.(\x.f (x x)) (\x.f (x x));
def fact  = fix (\\fact.\n.if (== n 0) 1 ( imul_ n (fact (isub_ n 1))));

def maxv = fix (\\maxv.\x.\y.if (== y nil) x (if (> x y) (maxv x) (maxv y)));
def minv = fix (\\minv.\x.\y.if (== y nil) x (if (> x y) (minv y) (minv x)));

def even,odd =
  let evenodd =
     fix (\\eo.:: (\n.if (== n 0) true (tl eo (isub_ n 1)))
                          (\n.if (== n 0) false (hd eo (isub_ n 1))))
  in 
    hd evenodd,tl evenodd;

*)
