(*
 * listAux.ml: ���X�g����̂��߂̕⏕�֐���`
 *)

module List =
struct
  include List

(*
 * filter_map: ('a -> 'b option) -> 'a list -> 'b list
 *   -- ���X�g�̃t�B���^�[�Ǝʑ��𓯎��ɍs��
 *)
let filter_map f xs =
  let rec iter acc = function
    | [] -> rev acc
    | x::xs -> match f x with None -> iter acc xs | Some y -> iter (y::acc) xs
  in
    iter [] xs

(*
 * has_dup: 'a list -> bool
 *   -- ���X�g���d�������v�f�������Ă��邩���ׂ�
 *)
let has_dup xs =
  let rec iter = function
    | [] -> false
    | x::xs -> if mem x xs then true else iter xs
  in
    iter xs

(*
 * check_dup: ('a -> unit) -> 'a list -> unit
 *   -- ���X�g���d�������v�f�������Ă��邩�`�F�b�N����
 *)
let check_dup f xs =
  let rec iter = function
    | [] -> ()
    | x::xs -> if mem x xs then f x else iter xs
  in
    iter xs

end
