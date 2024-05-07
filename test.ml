open OUnit2
open Btree
open Attrs
open Serial
open Tree_ops

module KeyAndPl = struct
  type t = int32 * string
  let compare e1 e2 = Int32.compare (fst e1) (fst e2)
end

module KeyAndPlSet = Set.Make(KeyAndPl)

module ToString = struct
  let string_of_int32_list l = "[" ^ (List.fold_left (fun acc x -> acc ^ Int32.to_string x ^ ",") "" l) ^ "]"

  let rec item_list_to_string items acc = match items with
  | (k, pl)::its -> acc ^ "(" ^ (Int32.to_string k) ^ ", " ^ 
  (String.sub pl 0 10) ^ "), " ^ item_list_to_string its acc
  | [] -> acc 

  let storage_to_string tree storage =
    let rec s_to_string items acc = match items with
    | (k, cs)::its -> acc ^ "(" ^ (Int32.to_string k) ^ ", " ^ 
    (Cstruct.to_string cs ~off:0 ~len:10) ^ "), " ^ s_to_string its acc
    | [] -> acc in
    let its = List.filter (fun (s, _) -> List.exists (fun k -> Int32.equal s k) 
    (get_all_keys tree)) storage in s_to_string its ""
  end

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
    let ks, cn, r, t, id = get_all tree in
    let lk, lc = List.length ks, List.length cn in
    if (not r && id<2) || (not leaf && lc != lk+1) then false
    else if r && leaf then true
    else if not r && (lk < (t-1) || lk > (2*t-1)) then false
    else if leaf then true
    else let c1 = get_child tree ckey in
      valid_tree c1 [get_hd c1] false && valid_tree tree next true in
  let ks, _, r, _, id = get_all tree in
  if (not r || r && id!=1) then false
  else if ks=[] then is_leaf tree
  else valid_tree tree [get_hd tree] false

let payload_match tree items storage =
  let rec check_node tree items ckey visited =
    let go_next next new_items =
      let c1, c2 = get_child tree ckey, get_child tree next in
      let matched, next_items = check_node c1 new_items [get_hd c1] false in
      if not (matched && List.hd ckey > get_largest c1) then false, next_items
      else if List.hd ckey >= (get_smallest c2) then false, next_items
      else if next=[] then check_node c2 next_items [get_hd c2] false
      else check_node tree next_items next true in
    try
    let leaf, next = is_leaf tree, get_next tree (List.hd ckey) in
    if visited then go_next next items
    else let ks, _, _, _, _ = get_all tree in
      let in_storage = List.map (fun k -> Cstruct.to_string (List.assoc k storage)) ks in
      let node_items = KeyAndPlSet.of_list (List.combine ks in_storage) in
      if not KeyAndPlSet.(is_empty (diff node_items items)) then false, items
      else let new_items = KeyAndPlSet.diff items node_items in
        if leaf then true, new_items else go_next next new_items 
    with Not_found -> false, items in
  let ks, _, _, _, _ = get_all tree in
  if ks=[] then true
  else
    let item_set = KeyAndPlSet.of_list items in 
    let matched, new_items = check_node tree item_set [get_hd tree] false in
    matched && KeyAndPlSet.is_empty new_items

let rec same_tree tr1 tr2 =
  let get_keys tr = let ks, _, _, _, _ = get_all tr in ks in
  let get_cn tr = let _, cn, _, _, _ = get_all tr in cn in
  let l1, l2 = Attrs.is_leaf tr1, Attrs.is_leaf tr2 in
  if l1 && l2 then get_keys tr1 = get_keys tr2
  else if not (l1 || l2) then try
    (get_keys tr1 = get_keys tr2) && List.fold_left2 (fun acc a b ->
      acc && (same_tree a b)) true (get_cn tr1) (get_cn tr2)
  with Invalid_argument _ -> false
  else false 


let all_chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
let block_size = 256;;

let rec random_string n =
  if n=0 then ""
  else let i = Random.int 62 in
  String.make 1 all_chars.[i] ^ random_string (n-1)

let rec keys_from_pair items = match items with
| (k, _)::its -> k::(keys_from_pair its)
| [] -> [] 

let rec create_key_list n l = if n=0 then l else let i = Random.int32 (Int32.of_int 800) in if List.mem i l then create_key_list n l else create_key_list (n-1) (i::l)
let rec create_payload_list l = match l with
| _::ks -> (random_string block_size)::(create_payload_list ks)
| [] -> []

let slice l li ui =
let rec drop l n = if n=0 then l else match l with
| _::cs -> drop cs (n-1)
| [] -> raise (Failure "out of range") in
let rec take oldl newl n = if n=0 then newl else match oldl with
| c::cs -> take cs (c::newl) (n-1)
| [] -> raise (Failure "out of range") in
take (drop l li) [] (ui-li)

let ks = List.map Int32.of_int [63; 16; 51; 77; 61; 43; 57; 12; 44; 72; 45; 34; 20; 7; 93; 29; 58; 59; 60; 62];;
let pls = create_payload_list ks;;
let its = List.combine ks pls;;
let item_set = KeyAndPlSet.of_list its;;
let head_pointer = Int32.of_int (List.length !Storage.pointers -1);;

let ins tree items t = 
  let tr = insert_list ~block_size tree items in
  tr, of_cstruct t head_pointer, !Storage.storage;;

let del tree keys t =
  let tr = delete_list ~block_size tree keys in
  tr, of_cstruct t head_pointer, !Storage.storage;;

let new_tree t items = insert_list ~block_size (create_btree ~block_size t) items;;

let kr1 = List.map Int32.of_int [7; 63; 72; 45; 44];;
let pl1 = List.map (fun i -> List.assoc i its) kr1;;
let tr1 = List.combine kr1 pl1;;
let kr2 = kr1 @ (List.map Int32.of_int [34; 60; 12; 29; 16]);;
let pl2 = List.map (fun i -> List.assoc i its) kr2;;
let tr2 = List.combine kr2 pl2;;
let its1 = KeyAndPlSet.(elements (diff item_set (of_list tr1)));;
let its2 = KeyAndPlSet.(elements (diff item_set (of_list tr2)));;

(* tests for B-tree of degree 2 *)
let a, a_cs, s = ins (new_tree 2 []) its 2;;
let a1, a1_cs, s1 = del a kr1 2;;
let a2, a2_cs, s2 = del (new_tree 2 its) kr2 2;;
let a3, a3_cs, s3 = ins a2 tr2 2;;
let a4, a4_cs, _s4 = del (new_tree 2 its) ks 2;;
let a5 =
  let a = new_tree 2 its in 
  let k = get_hd a in swap a k (find_predecessor a k) k 0 0;;
let a5_cs, s5 = of_cstruct 2 head_pointer, !Storage.storage;;
let a6 =
  let a = new_tree 2 its in 
  let k = get_hd a in swap a k (find_successor a k) k 0 0;;
let a6_cs, s6 = of_cstruct 2 head_pointer, !Storage.storage;;


(* tests for B-tree of degree 3 *)
let b, b_cs, sb = ins (new_tree 3 []) its 3;;
let b1, b1_cs, sb1 = del b kr1 3;;
let b2, b2_cs, sb2 = del (new_tree 3 its) kr2 3;;
let b3, b3_cs, sb3 = ins b2 tr2 3;;
let b4, b4_cs, _sb4 = del (new_tree 3 its) ks 3;;
let b5 =
  let b = new_tree 3 its in 
  let k = get_hd b in swap b k (find_predecessor b k) k 0 0;;
let b5_cs, sb5 = of_cstruct 3 head_pointer, !Storage.storage;;
let b6 =
  let b = new_tree 3 its in 
  let k = get_hd b in swap b k (find_successor b k) k 0 0;;
let b6_cs, sb6 = of_cstruct 3 head_pointer, !Storage.storage;;


(* tests for B-tree of random degree *)
let get_test_tree n =
  let t = (Random.int 15) + 2 in
  let keys = create_key_list n [] in
  let payloads = create_payload_list keys in
  let pairs = List.combine keys payloads in
  let tree = insert_list (create_btree ~block_size t) ~block_size pairs in 
  t, tree, pairs

let t, c, its3 = get_test_tree 300;;

let items3_set = KeyAndPlSet.of_list its3;;
let ks2 = keys_from_pair its3;;
let tr3 = let n = Random.int 75 in slice its3 n (200-n);;
let kr3 = keys_from_pair tr3;;
let its4 = KeyAndPlSet.(elements (diff items3_set (of_list tr3)));;

let c_cs, sc = of_cstruct t head_pointer, !Storage.storage;;
let c1, c1_cs, sc1 = del c kr3 t;;
let c2, c2_cs, sc2 = ins (new_tree t its4) tr3 t;;
let c3, c3_cs, _sc3 = del (new_tree t its3) ks2 t;;
let c4 =
  let c = new_tree t its3 in 
  let k = get_hd c in swap c k (find_predecessor c k) k 0 0;;
let c4_cs, sc4 = of_cstruct t head_pointer, !Storage.storage;;
let c5 =
  let c = new_tree t its3 in 
  let k = get_hd c in swap c k (find_successor c k) k 0 0;;
let c5_cs, sc5 = of_cstruct t head_pointer, !Storage.storage;;

let tests = "test suite for btree" >::: [
  "inserting a series of elements (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a));
  "payloads and keys match (t=2)" >:: (fun _ -> assert_bool "" (payload_match a its s));
  "tree structure maintained in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a a_cs));
  "deleting 5 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a1));
  "deleting 5 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a1 its1 s1));
  "deleting 5 elements maintains tree structure in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a1 a1_cs));
  "deleting 10 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a2));
  "deleting 10 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a2 its2 s2));
  "deleting 10 elements maintains tree structure in storage (t=2)" >:: (fun _ -> assert_bool ("tree: " ^ to_string a2 ^ "\nin storage: " ^ to_string a2_cs ^ "\n") (same_tree a2 a2_cs));
  "reinserting the deleted elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a3));
  "reinserting the deleted elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a3 its s3));
  "reinserting the deleted elements maintains tree structure in storage (t=2)" >:: (fun _ -> assert_bool ("tree: " ^ to_string a3 ^ "\nin storage: " ^ to_string a3_cs ^ "\n") (same_tree a3 a3_cs));
  "deleting all elements results in valid tree (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a4));
  "deleting all elements results in empty tree (t=2)" >:: (fun _ -> assert_equal a4 (Lf ([], true, 2, 1)));
  "deleting all elements results in empty tree in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a4 a4_cs));
  "swapping with predecessor maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a5));
  "swapping with predecessor causes order violation (t=2)" >:: (fun _ -> assert_bool "" (not (payload_match a5 its s5)));
  "swapping with predecessor maintains tree structure in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a5 a5_cs));
  "swapping with successor maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a6));
  "swapping with successor causes order violation (t=2)" >:: (fun _ -> assert_bool "" (not (payload_match a6 its s6)));
  "swapping with successor maintains tree structure in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a6 a6_cs));  
  "inserting a series of elements (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree a));
  "payloads and keys match (t=3)" >:: (fun _ -> assert_bool "" (payload_match b its sb));
  "tree structure maintained in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b b_cs));
  "deleting 5 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b1));
  "deleting 5 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b1 its1 sb1));
  "deleting 5 elements maintains tree structure in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b1 b1_cs));
  "deleting 10 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b2));
  "deleting 10 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b2 its2 sb2));
  "deleting 10 elements maintains tree structure in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b2 b2_cs));
  "reinserting the deleted elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b3));
  "reinserting the deleted elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b3 its sb3));
  "reinserting the deleted elements maintains tree structure in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b3 b3_cs));
  "deleting all elements results in valid tree (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b4));
  "deleting all elements results in empty tree (t=3)" >:: (fun _ -> assert_equal b4 (Lf ([], true, 3, 1)));
  "deleting all elements results in empty tree in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b4 b4_cs));
  "swapping with predecessor maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b5));
  "swapping with predecessor causes order violation (t=3)" >:: (fun _ -> assert_bool "" (not (payload_match b5 its sb5)));
  "swapping with predecessor maintains tree structure in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b5 b5_cs));
  "swapping with successor maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b6));
  "swapping with successor causes order violation (t=3)" >:: (fun _ -> assert_bool ((to_string b) ^ "\n" ^ (to_string b6)) (not (payload_match b6 its sb6)));
  "swapping with successor maintains tree structure in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b6 b6_cs));
  "inserting a series of elements (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c));
  "payloads and keys match (random t)" >:: (fun _ -> assert_bool "" (payload_match c its3 sc));
  "tree structure maintained in storage (random t)" >:: (fun _ -> assert_bool "" (same_tree c c_cs));
  "deleting random number of elements maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c1));
  "deleting random number of elements maintains key/payload pairs (random t)" >:: (fun _ -> assert_bool "" (payload_match c1 its4 sc1));
  "deleting random number of elements maintains tree structure in storage (random t)" >:: (fun _ -> assert_bool ("tree: " ^ to_string c1 ^ "\nin storage: " ^ to_string c1_cs ^ "\n") (same_tree c1 c1_cs));
  "reinserting the deleted elements maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c2));
  "reinserting the deleted elements maintains key/payload pairs (random t)" >:: (fun _ -> assert_bool "" (payload_match c2 its3 sc2));
  "reinserting the deleted elements maintains tree structure in storage (random t)" >:: (fun _ -> assert_bool "" (same_tree c2 c2_cs));
  "deleting all elements results in valid tree (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c3));
  "deleting all elements results in empty tree (random t)" >:: (fun _ -> assert_equal c3 (Lf ([], true, t, 1)));
  "deleting all elements results in empty tree in storage (random t)" >:: (fun _ -> assert_bool "" (same_tree c3 c3_cs)); 
  "swapping with predecessor maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c4));
  "swapping with predecessor causes order violation (random t)" >:: (fun _ -> assert_bool "" (not (payload_match c4 its sc4)));
  "swapping with predecessor maintains tree structure in storage (random t)" >:: (fun _ -> assert_bool "" (same_tree c4 c4_cs));
  "swapping with successor maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c5));
  "swapping with successor causes order violation (random t)" >:: (fun _ -> assert_bool "" (not (payload_match c5 its sc5)));
  "swapping with successor maintains tree structure in storage (random t)" >:: (fun _ -> assert_bool "" (same_tree c5 c5_cs));
]

let _ = run_test_tt_main tests