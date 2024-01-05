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

let rec create_list n = if n=0 then [] else (Random.int 10000, Random.int 1000000)::(create_list (n-1))

let test_tree =
  let t = Random.int 30 in
  let pairs = create_list 200 in
  let tree = insert_list (create_btree t) pairs in
  if is_valid_tree tree 0 && payload_match tree pairs then true else false

let its = [(63, 1); (16, 2); (51, 3); (77, 4); (61, 5); (43, 6); (57, 7); (12, 8); (44, 9); (72, 10); (45, 11); (34, 12); (20, 13); (7, 14); (93, 15); (29, 16); (58, 17); (59, 18); (60, 19); (62, 20)];;
let tr1 = [(7, 14); (63, 1); (72, 10); (45, 11); (44, 9)];;
let tr2 = tr1 @ [(34, 12); (60, 19); (12, 8); (29, 16); (16, 2)]
let kr1 = keys_from_pair tr1;;
let kr2 = keys_from_pair tr2;;
let its1 = remove_items its tr1;;
let its2 = remove_items its1 tr2;;
let a = insert_list (create_btree 2) its;;
let a1 = delete_list a kr1;;
let a2 = delete_list a kr2;;
let a3 = insert_list a2 tr2;;
let b = insert_list (create_btree 3) its;;
let b1 = delete_list b kr1;;
let b2 = delete_list b kr2;;
let b3 = insert_list b2 tr2;;

let tests = "test suite for btree" >::: [
  "inserting a series of elements (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a 0));
  "payloads and keys match (t=2)" >:: (fun _ -> assert_bool "" (payload_match a its));
  "deleting 5 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a1 0));
  "deleting 5 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a1 its1));
  "deleting 10 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a2 0));
  "deleting 10 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a2 its2));
  "reinserting the deleted elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a3 0));
  "reinserting the deleted elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a3 its));
  "inserting a series of elements (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree a 0));
  "payloads and keys match (t=3)" >:: (fun _ -> assert_bool "" (payload_match a its));
  "deleting 5 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b1 0));
  "deleting 5 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b1 its1));
  "deleting 10 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b2 0));
  "deleting 10 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b2 its2));
  "reinserting the deleted elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b3 0));
  "reinserting the deleted elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b3 its));
  "testing tree with random branching factor, keys and payloads" >:: (fun _ -> assert_bool "" test_tree)
]

let _ = run_test_tt_main tests