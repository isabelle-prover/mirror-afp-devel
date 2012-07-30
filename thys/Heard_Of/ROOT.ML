no_document use_thys ["../Stuttering_Equivalence/StutterEquivalence"];

use_thys [
  (* generic model and reduction theorem *)
  "HOModel", "Reduction",
  (* utility lemmas about majorities *)
  "Majorities",
  (* algorithms for benign faults *)
  "otr/OneThirdRuleProof",
  "uv/UvProof",
  "lastvoting/LastVotingProof",
  (* algorithms for Byzantine faults *)
  "ute/UteProof",
  "ate/AteProof",
  "eigbyz/EigbyzProof"
];
