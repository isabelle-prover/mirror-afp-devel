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
  "Extra",
  "List_local",
  "Mapping"
];

use_thys
 [
  "DFS",
  "Kripke",
  "MapOps",
  "Traces",
  "Trie",
  "KBPs",
  "KBPsAuto",
  "KBPsAlg",
  "SPRViewSingle",
  "Robot",
  "SPRViewDet",
  "MuddyChildren"
 ];
