
no_document use_thys ["Permutation", "Multiset"];

use_thys [
  "Base",

(* NOTES omitted permutations and try to reuse library stuff *)

  "Formula",
  "Sequents",

(* NOTES for sequents, had to prove a few lemmas to import the permutation stuff from the HOL lib. The few lemmas easily prove A <~~> B for typical A and B by reducing to element counts. This also fixes a todo in Permutation.thy - we can reduce perms to counts, and multisets could already be reduced to counts. Thus A <~~> B = (multiset_of A = multiset_of B) is easy. *)

  "Tree",
  "Completeness",
  "Soundness"
];
