(*
 run SCC on the dependency graph, each SCC corresponds to a recursive bind that need to be fixed 
*)

open Ast

exception Unreachable

type src = PassUniqueId.dst
type dst = <
   seq: no;
   pattern: yes;
   lambda: no;
   call: no;
   recbind: no; 
   unique_id: yes;
   bind_only: yes;
   letin: no>
