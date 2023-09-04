open Ast

type deRecBind = <
   seq: no;
   pattern: no;
   compound_type: yes;
   lambda: yes;
   call: yes;
   letin: yes;
   unpin: no>

type dePattern = PassDePattern.dePattern

(* TODO: build a dependency graph indicating the dependency of binding *)
