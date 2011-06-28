(** リスト操作のための補助関数定義 *)

module List =
struct
  include List

(** リストのフィルターと写像を同時に行う *)
(* filter_map: ('a -> 'b option) -> 'a list -> 'b list *)
let filter_map f xs =
  let rec iter acc = function
    | [] -> rev acc
    | x::xs -> match f x with None -> iter acc xs | Some y -> iter (y::acc) xs
  in
    iter [] xs

(** リストが重複した要素を持っているか調べる *)
(* has_dup: 'a list -> bool *)
let has_dup xs =
  let rec iter = function
    | [] -> false
    | x::xs -> if mem x xs then true else iter xs
  in
    iter xs

(** リストが重複した要素を持っているかチェックする *)
(* check_dup: ('a -> unit) -> 'a list -> unit *)
let check_dup f xs =
  let rec iter = function
    | [] -> ()
    | x::xs -> if mem x xs then f x else iter xs
  in
    iter xs

end
