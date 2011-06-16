type 'a t = 'a ref list ref

let create () = ref []

let extend store v =
  let m = List.length !store in
    store := !store @ [ref v];
    m

let update store m v =
  (List.nth !store m) := v

let lookup store m =
  !(List.nth !store m)

