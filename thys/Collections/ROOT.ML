no_document use_thys 
  ["common/Misc",
   "common/Assoc_List",
   "common/RBT_add",
   "common/Dlist_add",
   "common/Array",
   "~~/src/HOL/Library/Efficient_Nat",
   "~~/src/HOL/Library/While_Combinator",
   "../Binomial-Heaps/BinomialHeap",
   "../Binomial-Heaps/SkewBinomialHeap",
   "../Finger-Trees/FingerTree"
   ];

use_thys 
   [ (* Specifications *)
     "spec/Spec_Chapter",
     "spec/MapSpec", "spec/SetSpec",
     "spec/ListSpec", "spec/AnnotatedListSpec", "spec/PrioSpec", 
     "spec/PrioUniqueSpec",
     (* Generic Algorithms *)
     "gen_algo/Gen_Algo_Chapter",
     "gen_algo/MapGA", "gen_algo/SetGA", "gen_algo/SetByMap", 
     "gen_algo/ListGA", "gen_algo/SetIndex", "gen_algo/Algos", 
     "gen_algo/PrioByAnnotatedList",
     "gen_algo/PrioUniqueByAnnotatedList",
     (* Implementations *)
     "impl/Impl_Chapter",
     "impl/Impl_Overview",
     "impl/MapStdImpl", "impl/SetStdImpl", "impl/Fifo", "impl/BinoPrioImpl", 
     "impl/SkewPrioImpl", "impl/FTAnnotatedListImpl", "impl/FTPrioImpl", 
     "impl/FTPrioUniqueImpl"
    ];

no_document use_thys ["gen_algo/StdInst"];

use_thys
   ["Collections",
    "Userguide",
    (* Examples *)
    "examples/Examples_Chapter",
    "examples/itp_2010", "examples/Exploration", 
    "examples/Exploration_DFS", 
    "examples/All"];
