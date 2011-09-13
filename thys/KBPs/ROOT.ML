Name_Space.names_short_default := true;
Printer.show_question_marks_default := false;

no_document use_thys
 [
   "~~/src/HOL/Library/LaTeXsugar",
   "~~/src/HOL/Library/OptionalSugar",
  "~~/src/HOL/Library/AList",
  "Extra",
  "List_local",
  "~~/src/HOL/Library/Mapping"
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
