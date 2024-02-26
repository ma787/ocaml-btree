open OUnit2
open Btree

let rec is_valid_tree tree acc = match tree with
| Il (v::next, pl::pls, c::cn, r, t) ->
  let lk, lp = List.length (v::next) + acc, List.length (pl::pls) + acc in 
  let lc = if acc=0 then List.length (c::cn) else lk+1 in
  if lk != lp then false
  else if (not r && (lk < (t-1) || lk > (2*t -1))) then false
  else if (not r && (lc < t || lc > 2*t)) || (r && lc<2) then false
  else (is_valid_tree c 0) && (is_valid_tree (Il (next, pls, cn, r, t)) (acc+1))
| Il ([], [], c::[], _, _) -> is_valid_tree c 0
| Lf (ks, pls, r, t) ->
  let lk, lp = List.length ks, List.length pls in
  if lk != lp then false
  else if r then true
  else if lk < (t-1) || lk > (2*t -1) then false
  else true
| _ -> false

let rec payload_match tree items = 
let rec get_pair tree k = match tree with
| Il (v::next, pl::pls, _::cn, r, t) -> if v=k then (v, pl) else get_pair (Il (next, pls, cn, r, t)) k
| Lf (v::next, pl::pls, r, t) -> if v=k then (v, pl) else get_pair (Lf (next, pls, r, t)) k
| _ -> raise (NotFound "key not found in node") in match items with
| (k, pl)::its -> let c = search tree k in let tk, tp = get_pair c k in
tk=k && tp=pl && payload_match tree its
| [] -> true

let remove_items items toremove = let eq a b = a=b in let m a = not (List.exists (eq a) toremove) in List.filter m items
let rec keys_from_pair items = match items with
| (k, _)::its -> k::(keys_from_pair its)
| [] -> [] 

let rec create_key_list n l = if n=0 then l else let i = Random.int 10000 in if List.mem i l then create_key_list n l else create_key_list (n-1) (i::l)
let rec create_list l = match l with
| k::ks -> (k, Random.int 1000000)::(create_list ks)
| [] -> []

let get_test_tree =
  let t = Random.int 30 in
  let pairs = create_list (create_key_list 200 []) in
  let tree = insert_list (create_btree t) pairs in t, tree, pairs

let slice l li ui =
let rec drop l n = if n=0 then l else match l with
| _::cs -> drop cs (n-1)
| [] -> raise (Failure "out of range") in
let rec take oldl newl n = if n=0 then newl else match oldl with
| c::cs -> take cs (c::newl) (n-1)
| [] -> raise (Failure "out of range") in
take (drop l li) [] (ui-li)

let string_of_pair_list l =
let rec string_of_pairs l = match l with
| (k, pl)::cs -> "(" ^ (string_of_int k) ^ ", " ^ (string_of_int pl) ^ ")" ^ (if cs=[] then "" else ", " ^ (string_of_pairs cs))
| [] -> "" in
"[" ^ (string_of_pairs l) ^ "]"

let its = [(63, 1); (16, 2); (51, 3); (77, 4); (61, 5); (43, 6); (57, 7); (12, 8); (44, 9); (72, 10); (45, 11); (34, 12); (20, 13); (7, 14); (93, 15); (29, 16); (58, 17); (59, 18); (60, 19); (62, 20)];;
let ks = keys_from_pair its;;
let tr1 = [(7, 14); (63, 1); (72, 10); (45, 11); (44, 9)];;
let tr2 = tr1 @ [(34, 12); (60, 19); (12, 8); (29, 16); (16, 2)]
let kr1 = keys_from_pair tr1;;
let kr2 = keys_from_pair tr2;;
let its1 = remove_items its tr1;;
let its2 = remove_items its tr2;;
let a = insert_list (create_btree 2) its;;
let a1 = delete_list a kr1;;
let a2 = delete_list a kr2;;
let a3 = insert_list a2 tr2;;
let a4 = delete_list a ks;;
let b = insert_list (create_btree 3) its;;
let b1 = delete_list b kr1;;
let b2 = delete_list b kr2;;
let b3 = insert_list b2 tr2;;
let b4 = delete_list b ks;;

let bf, c, its3 = get_test_tree;;
let ks2 = keys_from_pair its3;;
let tr3 = let n = Random.int 75 in slice its3 n (200-n);;
let kr3 = keys_from_pair tr3;;
let its4 = remove_items its3 tr3;;
let c1 = delete_list c kr3;;
let c2 = insert_list c1 tr3;;
let c3 = delete_list c ks2;;

let tests = "test suite for btree" >::: [
  "inserting a series of elements (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a 0));
  "payloads and keys match (t=2)" >:: (fun _ -> assert_bool "" (payload_match a its));
  "deleting 5 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a1 0));
  "deleting 5 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a1 its1));
  "deleting 10 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a2 0));
  "deleting 10 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a2 its2));
  "reinserting the deleted elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a3 0));
  "reinserting the deleted elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a3 its));
  "deleting all elements results in valid tree (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a4 0));
  "deleting all elements results in empty tree (t=2)" >:: (fun _ -> assert_equal a4 (Lf ([], [], true, 2)));
  "inserting a series of elements (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree a 0));
  "payloads and keys match (t=3)" >:: (fun _ -> assert_bool "" (payload_match a its));
  "deleting 5 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b1 0));
  "deleting 5 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b1 its1));
  "deleting 10 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b2 0));
  "deleting 10 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b2 its2));
  "reinserting the deleted elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b3 0));
  "reinserting the deleted elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b3 its));
  "deleting all elements results in valid tree (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b4 0));
  "deleting all elements results in empty tree (t=3)" >:: (fun _ -> assert_equal b4 (Lf ([], [], true, 3)));
  "inserting a series of elements (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c 0));
  "payloads and keys match (random t)" >:: (fun _ -> assert_bool "" (payload_match c its3));
  "deleting random number of elements maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c1 0));
  "deleting random number of elements maintains key/payload pairs (random t)" >:: (fun _ -> assert_bool "" (payload_match c1 its4));
  "reinserting the deleted elements maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c2 0));
  "reinserting the deleted elements maintains key/payload pairs (random t)" >:: (fun _ -> assert_bool "" (payload_match c2 its3));
  "deleting all elements results in valid tree (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c3 0));
  "deleting all elements results in empty tree (random t)" >:: (fun _ -> assert_equal c3 (Lf ([], [], true, bf))) 
]

let _ = run_test_tt_main tests
