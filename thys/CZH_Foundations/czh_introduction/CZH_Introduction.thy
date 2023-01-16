(* Copyright 2021 (C) Mihails Milehins *)

chapter\<open>Introduction\<close>
theory CZH_Introduction
  imports ZFC_in_HOL.ZFC_Typeclasses
begin



section\<open>Background\<close>


text\<open>
This article presents a foundational framework
that will be used for the formalization of
elements of the theory of 1-categories in the object logic 
\<open>ZFC in HOL\<close> (\<^cite>\<open>"paulson_zermelo_2019"\<close>, also see
\<^cite>\<open>"barkaoui_partizan_2006"\<close>) of the formal proof assistant 
\<open>Isabelle\<close> \<^cite>\<open>"paulson_natural_1986"\<close> in future articles.
It is important to note that this chapter serves as 
an introduction to the entire development and not merely
its foundational part. 

There already exist several formalizations of the foundations of category 
theory in Isabelle. In the context of the work presented here, the most relevant
formalizations (listed in the chronological order) are 
\<^cite>\<open>"caccamo_higher-order_2001-1" and "caccamo_higher-order_2001"\<close>, 
\<^cite>\<open>"okeefe_category_2005"\<close>, \<^cite>\<open>"katovsky_category_2010"\<close> and 
\<^cite>\<open>"stark_category_2016"\<close>.
Arguably, the most well developed and maintained entry is 
\<^cite>\<open>"stark_category_2016"\<close>: it subsumes the majority of the content of 
\<^cite>\<open>"okeefe_category_2005"\<close> and \<^cite>\<open>"katovsky_category_2010"\<close>.

From the perspective of the methodology that was chosen for the formalization, 
this work differs significantly from the aforementioned previous work.
In particular, the categories are modelled as terms of the type \<^typ>\<open>V\<close> 
and no attempt is made to generalize the concept of a category to arbitrary 
types. The inspiration for the chosen approach is drawn from  
\<^cite>\<open>"feferman_set-theoretical_1969"\<close>,
\<^cite>\<open>"sica_doing_2006"\<close> and \<^cite>\<open>"shulman_set_2008"\<close>.

The primary references for this work are 
\<open>Categories for the Working Mathematician\<close> \<^cite>\<open>"mac_lane_categories_2010"\<close>
by Saunders Mac Lane, \<open>Category Theory in Context\<close> 
by Emily Riehl \<^cite>\<open>"riehl_category_2016"\<close> and 
\<open>Categories and Functors\<close> by Bodo Pareigis \<^cite>\<open>"bodo_categories_1970"\<close>. 
The secondary sources of information include the textbooks 
\<^cite>\<open>"adamek_abstract_2006"\<close> and \<^cite>\<open>"hungerford_algebra_2003"\<close>, 
as well as several online encyclopedias
(including \<^cite>\<open>"noauthor_nlab_nodate"\<close>, 
\<^cite>\<open>"noauthor_wikipedia_2001"\<close>, 
\<^cite>\<open>"noauthor_proofwiki_nodate"\<close>
and \<^cite>\<open>"noauthor_encyclopedia_nodate"\<close>). 
Of course, inspiration was also drawn from the previous formalizations of 
category theory in Isabelle. 

It is likely that none of the content that is formalized in this work
is original in nature. However, explicit citations
are not provided for many results that were deemed to be trivial.
\<close>




section\<open>Related and previous work\<close>


text\<open>
To the best knowledge of the author, this work is the first attempt
to develop a formalization of elements of category theory in the 
object logic ZFC in HOL by modelling categories as terms of the type \<^typ>\<open>V\<close>.
However, it should be noted that the formalization of category theory in
\<^cite>\<open>"katovsky_category_2010"\<close> largely rested 
on the object logic HOL/ZF \<^cite>\<open>"barkaoui_partizan_2006"\<close>, which is 
equiconsistent with the ZFC in HOL \<^cite>\<open>"paulson_zermelo_2019"\<close>. 
Nonetheless, in \<^cite>\<open>"katovsky_category_2010"\<close>, the objects and arrows
associated with categories were modelled as terms of arbitrary
types. The object logic HOL/ZF was used for the exposition of 
the category \<open>Set\<close> of all sets and functions between them 
and a variety of closely related concepts.
In this sense, the methodology employed in 
\<^cite>\<open>"katovsky_category_2010"\<close> could be seen as a combination of the 
methodology employed in this work and the methodology followed in
\<^cite>\<open>"okeefe_category_2005"\<close> and \<^cite>\<open>"stark_category_2016"\<close>.
Furthermore, in \<^cite>\<open>"chen_hotg_2021"\<close>, 
the authors have experimented with the formalization of category 
theory in Higher-Order Tarski-Grothendieck (HOTG)
theory \<^cite>\<open>"brown_higher-order_2019"\<close> using a methodology that 
shares many similarities with the approach that was chosen in this study.

The formalizations of various elements of category theory 
in other proof assistants are abundant.
While a survey of such formalizations is outside of the scope of
this work, it is important to note that there exist at least two examples 
of the formalization of elements of category theory in a set-theoretic setting
similar to the one that is used in this work. 
More specifically, elements of category theory were formalized in
the Tarski-Grothendieck Set Theory in the Mizar proof assistant 
\<^cite>\<open>"noauthor_association_nodate"\<close> (and
published in the associated electronic journal 
\<^cite>\<open>"grabowski_preface_2014"\<close>) 
and the proof assistant Metamath
\<^cite>\<open>"megill_metamath_2019"\<close>.
The following references contain some of the 
relevant articles in \<^cite>\<open>"grabowski_preface_2014"\<close>, but the list may not be 
exhaustive: 
\<^cite>\<open>"bylinski_introduction_1990" and "bylinski_subcategories_1990" and "bylinski_opposite_1991" and "trybulec_natural_1991" and "bylinski_category_1991" and "muzalewski_categories_1991" and "trybulec_isomorphisms_1991" and "muzalewski_category_1991" and "muzalewski_category_1991-1" and "bancerek_comma_1991" and "bylinski_products_1991" and "trybulec_isomorphisms_1992" and "bylinski_cartesian_1992" and "bancerek_categorial_1996" and "trybulec_categories_1996" and "bancerek_indexed_1996" and "trybulec_functors_1996" and "nieszczerzewski_category_1997" and "kornilowicz_categories_1997" and "kornilowicz_composition_1998" and "bancerek_concrete_2001" and "kornilowicz_products_2012" and "riccardi_object-free_2013" and "golinski_coproducts_2013" and "riccardi_categorical_2015" and "riccardi_exponential_2015"\<close>.
\<close>

end