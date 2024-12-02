open OUnit2
open Btree
open Attrs
open Tree_ops

module KeyAndPl = struct
  type t = int * int
  let compare e1 e2 = Int.compare (fst e1) (fst e2)
end

module KeyAndPlSet = Set.Make(KeyAndPl)

let rec get_largest tree =
  let rec last l = match l with
  | c::cs -> if cs=[] then c else last cs 
  | [] -> raise (Failure "empty list") in
  if is_leaf tree then
    let ks, _, _, _, _ = get_all tree in last ks
  else let c2 = get_child tree [] in get_largest c2

let rec get_smallest tree =
  if is_leaf tree then get_hd tree
  else let c1 = get_child tree [get_hd tree] in get_smallest c1

let is_valid_tree tree =
  let rec valid_tree tree ckey visited =
    if ckey=[] then 
      let c2 = get_child tree ckey in valid_tree c2 [get_hd c2] false
    else if visited then 
      let c1 = get_child tree ckey in valid_tree c1 [get_hd c1] false
    else let leaf, next = is_leaf tree, get_next tree (List.hd ckey) in
    let ks, pls, cn, r, t = get_all tree in
    let lk, lp, lc = List.length ks, List.length pls, List.length cn in
    if lk != lp || (not leaf && lc != lk+1) then false
    else if r && leaf then true
    else if not r && (lk < (t-1) || lk > (2*t-1)) then false
    else if leaf then true
    else let c1 = get_child tree ckey in
      valid_tree c1 [get_hd c1] false && valid_tree tree next true in
  let ks, pls, _, r, _ = get_all tree in
  if not r then false
  else if ks=[] then pls=[] && (is_leaf tree)
  else valid_tree tree [get_hd tree] false

let payload_match tree items =
  let rec check_node tree items ckey visited =
    let go_next next new_items =
      let c1, c2 = get_child tree ckey, get_child tree next in
      let matched, next_items = check_node c1 new_items [get_hd c1] false in
      if not (matched && List.hd ckey > get_largest c1) then false, next_items
      else if List.hd ckey >= (get_smallest c2) then false, next_items
      else if next=[] then check_node c2 next_items [get_hd c2] false
      else check_node tree next_items next true in
    let leaf, next = is_leaf tree, get_next tree (List.hd ckey) in
    if visited then go_next next items
    else let ks, pls, _, _, _ = get_all tree in
      let combined = List.combine ks pls in
      let node_items = KeyAndPlSet.of_list combined in
      if not (combined=(KeyAndPlSet.elements node_items)) then false, items
      else 
        if not KeyAndPlSet.(is_empty (diff node_items items)) then false, items
        else let new_items = KeyAndPlSet.diff items node_items in
          if leaf then true, new_items else go_next next new_items in
  let ks, _, _, _, _ = get_all tree in
  if ks=[] then true
  else
    let item_set = KeyAndPlSet.of_list items in 
    let matched, new_items = check_node tree item_set [get_hd tree] false in
    matched && KeyAndPlSet.is_empty new_items

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

let its = [(63, 1); (16, 2); (51, 3); (77, 4); (61, 5); (43, 6); (57, 7); (12, 8); (44, 9); (72, 10); (45, 11); (34, 12); (20, 13); (7, 14); (93, 15); (29, 16); (58, 17); (59, 18); (60, 19); (62, 20)];;
let item_set = KeyAndPlSet.of_list its
let ks = keys_from_pair its;;
let tr1 = [(7, 14); (63, 1); (72, 10); (45, 11); (44, 9)];;
let tr2 = tr1 @ [(34, 12); (60, 19); (12, 8); (29, 16); (16, 2)]
let kr1 = keys_from_pair tr1;;
let kr2 = keys_from_pair tr2;;
let its1 = KeyAndPlSet.(elements (diff item_set (of_list tr1)));;
let its2 = KeyAndPlSet.(elements (diff item_set (of_list tr2)));;
let a = insert_list (create_btree 2) its;;
let a1 = delete_list a kr1;;
let a2 = delete_list a kr2;;
let a3 = insert_list a2 tr2;;
let a4 = delete_list a ks;;
let a5 = let k = get_hd a in swap a (k, get_pl_from_key a k) (find_predecessor a k) k false 0;;
let a6 = let k = get_hd a in swap a (k, get_pl_from_key a k) (find_successor a k) k false 0;;
let b = insert_list (create_btree 3) its;;
let b1 = delete_list b kr1;;
let b2 = delete_list b kr2;;
let b3 = insert_list b2 tr2;;
let b4 = delete_list b ks;;
let b5 = let k = get_hd b in swap b (k, get_pl_from_key b k) (find_predecessor b k) k false 0;;
let b6 = let k = get_hd b in swap b (k, get_pl_from_key b k) (find_successor b k) k false 0;;

let bf, c, its3 = get_test_tree;;
let items3_set = KeyAndPlSet.of_list its3;;
let ks2 = keys_from_pair its3;;
let tr3 = let n = Random.int 75 in slice its3 n (200-n);;
let kr3 = keys_from_pair tr3;;
let its4 = KeyAndPlSet.(elements (diff items3_set (of_list tr3)));;
let c1 = delete_list c kr3;;
let c2 = insert_list c1 tr3;;
let c3 = delete_list c ks2;;
let c4 = let k = get_hd c in swap c (k, get_pl_from_key c k) (find_predecessor c k) k false 0;;
let c5 = let k = get_hd c in swap c (k, get_pl_from_key c k) (find_successor c k) k false 0;;

let tests = "test suite for btree" >::: [
  "inserting a series of elements (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a));
  "payloads and keys match (t=2)" >:: (fun _ -> assert_bool "" (payload_match a its));
  "deleting 5 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a1));
  "deleting 5 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a1 its1));
  "deleting 10 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a2));
  "deleting 10 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a2 its2));
  "reinserting the deleted elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a3));
  "reinserting the deleted elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a3 its));
  "deleting all elements results in valid tree (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a4));
  "deleting all elements results in empty tree (t=2)" >:: (fun _ -> assert_equal a4 (Lf ([], [], true, 2)));
  "swapping with predecessor maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a5));
  "swapping with predecessor causes order violation (t=2)" >:: (fun _ -> assert_bool "" (not (payload_match a5 its)));
  "swapping with successor maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a6));
  "swapping with successor causes order violation (t=2)" >:: (fun _ -> assert_bool "" (not (payload_match a6 its)));  
  "inserting a series of elements (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree a));
  "payloads and keys match (t=3)" >:: (fun _ -> assert_bool "" (payload_match a its));
  "deleting 5 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b1));
  "deleting 5 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b1 its1));
  "deleting 10 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b2));
  "deleting 10 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b2 its2));
  "reinserting the deleted elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b3));
  "reinserting the deleted elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b3 its));
  "deleting all elements results in valid tree (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b4));
  "deleting all elements results in empty tree (t=3)" >:: (fun _ -> assert_equal b4 (Lf ([], [], true, 3)));
  "swapping with predecessor maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b5));
  "swapping with predecessor causes order violation (t=3)" >:: (fun _ -> assert_bool "" (not (payload_match b5 its)));
  "swapping with successor maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b6));
  "swapping with successor causes order violation (t=3)" >:: (fun _ -> assert_bool ((to_string b) ^ "\n" ^ (to_string b6)) (not (payload_match b6 its)));
  "inserting a series of elements (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c));
  "payloads and keys match (random t)" >:: (fun _ -> assert_bool "" (payload_match c its3));
  "deleting random number of elements maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c1));
  "deleting random number of elements maintains key/payload pairs (random t)" >:: (fun _ -> assert_bool "" (payload_match c1 its4));
  "reinserting the deleted elements maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c2));
  "reinserting the deleted elements maintains key/payload pairs (random t)" >:: (fun _ -> assert_bool "" (payload_match c2 its3));
  "deleting all elements results in valid tree (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c3));
  "deleting all elements results in empty tree (random t)" >:: (fun _ -> assert_equal c3 (Lf ([], [], true, bf)));
  "swapping with predecessor maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c4));
  "swapping with predecessor causes order violation (random t)" >:: (fun _ -> assert_bool "" (not (payload_match c4 its)));
  "swapping with successor maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c5));
  "swapping with successor causes order violation (random t)" >:: (fun _ -> assert_bool "" (not (payload_match c5 its)));
]

let _ = run_test_tt_main tests