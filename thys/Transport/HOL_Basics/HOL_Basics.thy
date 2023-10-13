\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>HOL-Basics\<close>
theory HOL_Basics
  imports
    LBinary_Relations
    LFunctions
    Galois
    Orders
    Predicates
begin

paragraph \<open>Summary\<close>
text \<open>Library on top of HOL axioms, as required for Transport \<^cite>\<open>"transport"\<close>.
Requires \<^emph>\<open>only\<close> the HOL axioms, nothing else.
Includes:
\<^enum> Basic concepts on binary relations, relativised properties,
  and restricted equalities e.g. @{term "left_total_on"} and @{term "eq_restrict"}.
\<^enum> Basic concepts on functions, relativised properties, and generalised relators,
  e.g. @{term "injective_on"} and @{term "dep_mono_wrt_pred"}.
\<^enum> Basic concepts on orders and relativised order-theoretic properties,
  e.g. @{term "partial_equivalence_rel_on"}.
\<^enum> Galois connections, Galois equivalences, order equivalences, and
  other related concepts on order functors,
  e.g. @{term "galois.galois_equivalence"}.
\<^enum> Basic concepts on predicates.
\<^enum> Syntax bundles for HOL @{dir "HOL_Syntax_Bundles"}.
\<^enum> Alignments for concepts that have counterparts in the HOL library -
  see @{dir "HOL_Alignments"}.\<close>

end
