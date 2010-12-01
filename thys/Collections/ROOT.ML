no_document use_thys 
  ["common/Misc",
   "common/Assoc_List",
   "common/RBT_add",
   "common/Dlist_add",
   "common/Array",
   "Efficient_Nat",
   "While_Combinator",
   "../Binomial-Heaps/BinomialHeap",
   "../Binomial-Heaps/SkewBinomialHeap",
   "../Finger-Trees/FingerTree"
   ];

use_thys 
   [ (* Specifications *)
    "MapSpec", "OrderedMap", "SetSpec", "OrderedSet", "ListSpec", "AnnotatedListSpec", "PrioSpec", "PrioUniqueSpec",
     (* Generic Algorithms *)
    "MapGA", "SetGA", "SetByMap", "ListGA", "SetIndex", "Algos", "AnnotatedListGAPrioImpl", "AnnotatedListGAPrioUniqueImpl",
     (* Implementations *)
    "MapStdImpl", "SetStdImpl",
    "Fifo", "BinoPrioImpl", "SkewPrioImpl", "FTAnnotatedListImpl", "FTPrioImpl", "FTPrioUniqueImpl"
    ];

no_document use_thys ["StdInst"];

use_thys
   ["Collections",
    "Userguide",
    (* Examples *)
    "examples/itp_2010", "examples/Exploration", "examples/Exploration_DFS", "All"];
