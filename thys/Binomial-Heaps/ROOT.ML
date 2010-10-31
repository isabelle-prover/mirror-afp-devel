(*
  no_document use_thys ["This_Theory1", "This_Theory2"];
  use_thys ["That_Theory1", "That_Theory2", "That_Theory3"];
*)

no_document use_thys ["Multiset"];

use_thys ["BinomialHeap", "SkewBinomialHeap"];

(* Keep these in, they are to early detect problems with the code generator *)
no_document use_thys ["Efficient_Nat"];
no_document use_thys ["Test"];
