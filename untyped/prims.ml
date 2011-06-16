(** プリミティブの定義 *)
open Absyn
open Const

let hd_ store cs = match cs with
  | [TmApp(TmApp(TmCon(CSym "::"),v),_)] -> v
  | _ -> failwith "hd_"
let tl_ store cs = match cs with
  | [TmApp(TmApp(TmCon(CSym "::"),_),v)] -> v
  | _ -> failwith "tl_"

let iadd_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] -> TmCon(CInt(n + m))
  | _ -> failwith "iadd_"
let isub_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] -> TmCon(CInt(n - m))
  | _ -> failwith "isub_"
let imul_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] -> TmCon(CInt(n * m))
  | _ -> failwith "imul_"
let idiv_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] -> TmCon(CInt(n / m))
  | _ -> failwith "idiv_"
let imod_ store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m)] -> TmCon(CInt(n mod m))
  | _ -> failwith "imod_"
let igt_  store cs = match cs with
  | [TmCon(CInt n); TmCon(CInt m); v1; v2] ->
      if n > m then v1 else v2
  | _ -> failwith "igt_"

let ref_ store cs = match cs with
  | [v] ->
      let m = Store.extend store v in TmCon(CMem m)
  | _ -> failwith "ref_"

let drf_ store cs = match cs with
  | [TmCon(CMem m)] -> Store.lookup store m
  | _ -> failwith "drf_"

let asn_ store cs = match cs with
  | [TmCon(CMem m);tm] ->
      Store.update store m tm;
      TmCon(CSym "unit")
  | _ -> failwith "asn_"

let beq_ store cs = match cs with
  | [c1; c2; v1; v2] when is_cstr_value c1 && is_cstr_value c2 && c1 = c2 -> v1
  | [x; y; v1; v2] -> v2
  | _ -> failwith "beq_"

(*
 * fix v => v (fix v)
 *)
let fix_ store cs = match cs with
  | [v] -> TmApp(v,(TmApp(TmCon(CSym "fix"),v)))
  | _ -> failwith "fix_"

(*
 * case (inl v) v1 v2 => v1 v
 * case (inr v) v1 v2 => v2 v
 *)
let case_ store cs = match cs with
  | [TmApp(TmCon(CSym "inl"), v); v1; v2] -> TmApp(v1,v)
  | [TmApp(TmCon(CSym "inr"), v); v1; v2] -> TmApp(v2,v)
  | _ -> failwith "case_"

(* 
 * exit => 終了
 *)
let exit_ store cs = match cs with
  | [] -> exit 0
  | _ -> failwith "exit_"

(** プリミティブの定義 *)

let cstr_table = [
  ( "unit",  0 );
  ( "inl",   1 );
  ( "inr",   1 );
  ( "::",    2 );
]

let dstr_table = [
  ( "case",  (3, case_)  );
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
  ( "fix",   (1, fix_)   );
  ( "exit",  (0, exit_)  );
]

let dstr_apply d store vs =
  let arity,f = List.assoc d dstr_table in
    if arity == List.length vs then
      f store vs
    else
      failwith "dstr_apply: argno mismatch"

let symbols =
  (List.map fst cstr_table) @ (List.map fst dstr_table)

let _ =
  Const.table_ref :=
    (List.map (fun (s,arity)     -> s,Cstr arity) cstr_table)
  @ (List.map (fun (s,(arity,_)) -> s,Dstr arity) dstr_table)

(*
def true  = inl unit;
def false = inr unit;
def if    = \b.\(t1).\(t2).case b (\_.t1) (\_.t2);
def ==    = \t1.\t2.beq t1 t2 true false;
def not   = \t.== t false;
def andalso = \t1.\(t2).if t1 t2 false;
def orelse  = \t1.\(t2).if t1 true t2;
def !=    = \t1.\t2.beq t1 t2 false true;
def >     = \t1.\t2.gt t1 t2 true false;
def >=    = \t1.\t2.orelse (> t1 t2) (== t1 t2);
def <     = \t1.\t2.gt t2 t1 true false;
def <=    = \t1.\t2.orelse (< t1 t2) (== t1 t2);
def min   = \t1.\t2.if (<= t1 t2) t1 t2;
def max   = \t1.\t2.if (>= t1 t2) t1 t2;

def evenodd =
        fix (\(eo).:: (\n.if (== n 0) true (tl eo (- n 1)))
                           (\n.if (== n 0) false (hd eo (- n 1))));
def even = hd evenodd
and odd  = tl evenodd;

def fact  = fix (\(fact).\n.if (== n 0) 1 ( * n (fact (- n 1))));

def Sum1 = \x.(inl x);
def Sum2 = \x.(inr (inl x));
def Sum3 = \x.(inr (inr (inl x)));
def Sum4 = \x.(inr (inr (inr x)));

*)
