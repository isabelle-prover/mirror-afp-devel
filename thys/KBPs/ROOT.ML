(* For quick turnarounds. *)
(*
Toplevel.skip_proofs := true;
quick_and_dirty := true;
*)
short_names := true;
show_question_marks_default := false;

no_document use_thys
 [
   "~~/src/HOL/Library/LaTeXsugar",
   "~~/src/HOL/Library/OptionalSugar"
 ];

no_document use_thys
 [
  "AssocList",
  "DFS",
  "Extra",
  "Kripke",
  "List_local",
  "Mapping",
  "MapOps",
  "Traces",
  "Trie"
];

use_thys
 [
  "KBPs",
  "KBPsAuto",
  "KBPsAlg",
  "SPRViewSingle",
  "Robot",
  "SPRViewDet",
  "MuddyChildren"
 ];
