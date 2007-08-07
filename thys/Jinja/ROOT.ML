goals_limit := 1;

no_document use_thys [
  "List_Prefix",
  "While_Combinator",
  "Efficient_Nat",
  "Executable_Set"
];

use_thys [
  "J/TypeSafe",
  "J/Annotate",

  (*"Example",*)

  "J/execute_Bigstep",
  "J/execute_WellType",

  "JVM/JVMDefensive",
  "JVM/JVMListExample",

  "BV/BVExec",
  "BV/LBVJVM",
  "BV/BVNoTypeError",
  "BV/BVExample",

  "Compiler/TypeComp"
];
