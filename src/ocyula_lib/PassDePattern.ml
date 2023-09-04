open Ast

type dePattern = <
   seq: no;
   pattern: no;
   compound_type: yes;
   lambda: yes;
   call: yes;
   letin: yes;
   unpin: yes>

type deSeq = PassDeseq.deSeq
