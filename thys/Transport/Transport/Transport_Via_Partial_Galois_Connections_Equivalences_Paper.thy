\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport Paper Guide\<close>
theory Transport_Via_Partial_Galois_Connections_Equivalences_Paper
  imports
    Transport
    Transport_Natural_Functors
    Transport_Partial_Quotient_Types
    Transport_Prototype
    Transport_Lists_Sets_Examples
    Transport_Dep_Fun_Rel_Examples
    Transport_Typedef_Base
begin

text \<open>

\<^item> Section 3.1: Order basics can be found in
  @{theory "Transport.Binary_Relation_Properties"},
  @{theory "Transport.Preorders"},
  @{theory "Transport.Partial_Equivalence_Relations"},
  @{theory "Transport.Equivalence_Relations"}, and
  @{theory "Transport.Order_Functions_Base"}.
Theorem

\<^item> Section 3.2: Function relators and monotonicity can be found in
  @{theory "Transport.Function_Relators"} and
  @{theory "Transport.Functions_Monotone"}

\<^item> Section 3.3: Galois relator can be found in
  @{theory "Transport.Galois_Relator_Base"}.

  \<^item> Lemma 1: @{theory "Transport.Transport_Partial_Quotient_Types"}
  (*results from Appendix*)

  \<^item> Lemma 3: @{thm "galois_prop.Galois_right_iff_left_Galois_if_galois_prop"}

\<^item> Section 3.4: Partial Galois Connections and Equivalences can be found in
  @{theory "Transport.Half_Galois_Property"},
  @{theory "Transport.Galois_Property"},
  @{theory "Transport.Galois_Connections"},
  @{theory "Transport.Galois_Equivalences"}, and
  @{theory "Transport.Order_Equivalences"}.

  \<^item> Lemma 2: @{theory "Transport.Transport_Partial_Quotient_Types"}
  (*results from Appendix*)

  \<^item> Lemma 4: @{thm "galois.galois_equivalence_left_right_if_transitive_if_order_equivalence"}

  \<^item> Lemma 5: @{thm "galois.order_equivalence_if_reflexive_on_in_field_if_galois_equivalence"}

\<^item> Section 4.1: Closure (Dependent) Function Relator can be found in
  @{dir "Functions"}.

  \<^item> Monotone function relator @{theory "Transport.Monotone_Function_Relator"}.

  \<^item> Setup of construction @{theory "Transport.Transport_Functions_Base"}.

  \<^item> Theorem 1: see @{theory "Transport.Transport_Functions"}

  \<^item> Theorem 2: see @{thm "transport_Mono_Dep_Fun_Rel.left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI'"}
  (*results from Appendix*)

  \<^item> Lemma 6: @{thm "transport_Mono_Fun_Rel.galois_connection_left_rightI"}

  \<^item> Lemma 7: @{thm "transport_Mono_Fun_Rel.left_Galois_iff_Fun_Rel_left_GaloisI"}

  \<^item> Theorem 7: @{thm "transport_Mono_Dep_Fun_Rel.galois_connection_left_right_if_mono_if_galois_connectionI'"}

  \<^item> Theorem 8: @{thm "transport_Mono_Dep_Fun_Rel.left_Galois_iff_Dep_Fun_Rel_left_Galois_if_mono_if_galois_connectionI'"}

  \<^item> Lemma 8 @{thm "transport_Mono_Dep_Fun_Rel.left_rel_eq_tdfr_leftI_if_equivalencesI"}

  \<^item> Lemma 9: @{thm "transport_Mono_Fun_Rel.left_rel_eq_tfr_leftI"}

\<^item> Section 4.2: Closure Natural Functors can be found in
  @{dir "Natural_Functors"}.
  \<^item> Theorem 3: see @{theory "Transport.Transport_Natural_Functors"}

  \<^item> Theorem 4: @{thm "transport_natural_functor.left_Galois_eq_Frel_left_Galois"}


\<^item> Section 4.3: Closure Compositions can be found in @{dir "Compositions"}.

  \<^item> Setup for simple case in @{theory "Transport.Transport_Compositions_Agree_Base"}

  \<^item> Setup for generic case in @{theory "Transport.Transport_Compositions_Generic_Base"}

  \<^item> Theorem 5: @{thm "transport_comp.preorder_equivalenceI"} and

    @{thm "transport_comp.partial_equivalence_rel_equivalenceI"}
  \<^item> Theorem 6: @{thm "transport_comp.left_Galois_eq_comp_left_GaloisI"}

  (*results from Appendix*)
  \<^item> Theorem 9: see @{dir "Compositions/Agree"}, results in

    @{locale transport_comp_same}.
  \<^item> Theorem 10: @{thm "transport_comp.galois_connection_left_right_if_galois_equivalenceI"}

  \<^item> Theorem 11: @{thm "transport_comp.left_Galois_eq_comp_left_GaloisI'"}

\<^item> Section 5:

  \<^item> Implementation @{theory "Transport.Transport_Prototype"}:
    Note: the command "trp" from the paper is called @{command trp_term} and the
    method "trprover" is called "trp\_term\_prover".

  \<^item> Example 1: @{theory "Transport.Transport_Lists_Sets_Examples"}

  \<^item> Example 2: @{theory "Transport.Transport_Dep_Fun_Rel_Examples"}

  \<^item> Example 3: \<^url>\<open>https://github.com/kappelmann/Isabelle-Set/blob/fdf59444d9a53b5279080fb4d24893c9efa31160/Isabelle_Set/Integers/Integers_Transport.thy\<close>

\<^item> Proof: Partial Quotient Types are a special case:
  @{theory "Transport.Transport_Partial_Quotient_Types"}

\<^item> Proof: Typedefs are a special case:
  @{theory "Transport.Transport_Typedef_Base"}

\<^item> Proof: Set-Extensions are a special case: \<^url>\<open>https://github.com/kappelmann/Isabelle-Set/blob/fdf59444d9a53b5279080fb4d24893c9efa31160/Isabelle_Set/Set_Extensions/Set_Extensions_Transport.thy\<close>

\<^item> Proof: Bijections as special case:
  @{theory "Transport.Transport_Bijections"}
\<close>

end
