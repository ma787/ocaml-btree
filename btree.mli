type keys = int list
type pl = int
type node = 
| Lf of keys * pl list * bool * int 
| Il of keys * pl list * node list * bool * int

exception MalformedTree of string
exception NotFound of string
exception InvalidOperation of string

module Attrs : sig
    val to_string: node -> string
    val get_hd: node -> int
    val is_leaf: node -> bool
    val get_all: node -> keys * pl list * node list * bool * int
end

module Tree_ops : sig
    val get_next: node -> int -> int list
    val get_pl_from_key: node -> int -> pl
    val get_child: node -> int list -> node
end

val search: node -> int -> node

val find_predecessor: node -> int -> int * pl
val find_successor: node -> int -> int * pl

val swap: node -> (int * pl) -> (int * pl) -> int -> bool -> int -> node

val insert_list: node -> (int * pl) list -> node
val delete_list: node -> pl list -> node

val create_btree: pl -> node
