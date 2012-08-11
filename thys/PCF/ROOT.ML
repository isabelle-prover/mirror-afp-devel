Printer.show_question_marks_default := false;

no_document use_thys
 ["~~/src/HOL/HOLCF/HOLCF",
  "~~/src/HOL/Library/Product_Lattice",
  "Dual_Lattice",
  "Basis"
];

use_thys [
  "Logical_Relations",
  "PCF",
  "OpSem",
  "Continuations"
];
