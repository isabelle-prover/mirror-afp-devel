goals_limit := 1;

no_document use_thys ["List_Prefix", "While_Combinator", "Efficient_Nat"];

use_thys [
  "J/TypeSafe",
  "J/Annotate",

(*"Example",*)

  "J/execute_Bigstep",
  "J/execute_WellType",

  "JVM/JVMDefensive",
  "JVM/JVMListExample"
];
