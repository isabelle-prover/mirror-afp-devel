
---------------------------------
Since I understand some of the general facts may be included in the distribution, 
I have rated the facts from Fun2.thy and Wellfounded2.thy, with a score from 1 to 3, 
according to what I think is their potential usefulness (the higher the rate, the higher 
the usefulness) -- rates appear as comments before lemmas (hence are not visible in 
the pdf document, but only in the Isabelle scripts).  
In the rating, I have not fully considered the dependencies between these facts.  
I have not rated the facts in Order_Relation2, since they are all extremely basic facts 
about the introduced order-related notions, and are quite interconnected, so I think they 
should be either included or excluded altogether (except for a couple of facts (and their 
prerequisites) needed in Wellfounded2, which can be easily isolated).    
I am not experienced in assessing the usefulness of mathematical theorems, so my rating 
may be very amateurish.  
---------------------------------


Short description of the theories' main content:
-----------------------------------------------

The "minor" theories Fun2, Wellfounded2 and Order_Relation2 are
extensions of the existing theories Fun, Well-founded and
Order_Relation: 
-- Fun2 states more facts (mainly) concerning injections, bijections, inverses, 
and (numeric) cardinals of finite sets. 
-- Wellfounded2 states variations of well-founded 
recursion and well-founded recursion. 
-- Order_Relation fixes a relation, defines upper and lower bounds
operators and proves many basic properties for these
(depending on assumptions such as reflexivity or transitivity).

The "major" theories are:
-- Wellorder_Relation: Here one fixes a well-order relation, and then:
----- 1) Defines the concepts of maximum (of two elements) minimum (of a set), supremum,
      successor (of a set), and order filter (i.e., downwards closed set, a.k.a.
      initial segment).  
-- Wellorder_Embedding:
----- 2) For two well-order relations,
      defines *well-order embeddings* as injective functions copying
      the source into an order filter of the target and *compatible functions*
      as those preserving the order.  Also, *isomorphisms* 
      and *strict embeddings* are defined to be embeddings which are, and respectively
      are not, bijections.

-- Constructions_on_Wellorders:
----- 1) Defines direct images, restrictions, disjoint unions and 
      bounded squares of well-orders.
----- 2) Defines the relations "ordLeq", "ordLess" and "ordIso" 
      between well-order relations (concrete syntax: r <=o r', r <o r' and 
      r =o r', respectively), defined by the existence of an embedding, 
      strict embedding and isomorphism, respectively between the two members.  
      Among the properties proved for these relations:
--------- ordLeq is total;
--------- ordLess (on a fixed type) is well-founded.

-- Cardinal_Order_Relation:
---- 1) Defines a *cardinal order* to be a well-order minim w.r.t. "ordLeq" 
     (or, equivalently, minimal w.r.t. "ordLess").
     ordLess being well-founded together with the well-ordering theorem (from theory Zorn.thy)
     ensures the existence of a cardinal relation on any given set. In addition, 
     a cardinal relation on a set is unique up to order isomorphism. 
---- 2) Defines the cardinal of a set A, |A|, to be SOME cardinal
     order on it (unique up to =o, according to the above). 
---- 3) Proves properties of cardinals, including their
     interactions with sums, products, unions, lists,
     powersets, sets of finite sets. Among them, nontrivial
     facts concerning the invariance of infinite cardinals
     under some of these constructs -- e.g., if A is infinite,
     than the cardinal of lists/words over A is the same (up to
     the "cardinal equality" =o) as that of A.
---- 5) Studies the connection between the introduced (order-based) notion
     of cardinal and the numeric one previously defined for
     finite sets (operator "card").  On the way, one introduces the cardinal omega
     (natLeq) and the finite cardinals (natLeq_on n).
---- 6) Defines and proves the existence of successor cardinals.  


Here is a list of names of proved facts concerning cardinalities which are 
expressed independently of notions of order, and of potential interest 
for "working mathematicians":
--- one_set_greater, one_type_greater (their proofs use the 
    fact that ordinals are totally ordered)
--- Plus_into_Times, Plus_into_Times_types, 
    Plus_infinite_bij_betw, Plus_infinite_bij_betw_types,  
    Times_same_infinite_bij_betw, Times_same_infinite_bij_betw_types, 
    Times_infinite_bij_betw, Times_infinite_bij_betw_types
    inj_on_UNION_infinite, List_infinite_bij_betw, List_infinite_bij_betw_types
    Fpow_infinite_bij_betw 
    (their proofs employ cardinals)




Minor technicalities and naming issues:
---------------------------------------

-1. Even though I would have preferred to use "initial segment" instead of 
"order filter", I chose the latter to avoid terminological clash with 
the operator "init_seg_of" from Zorn.thy.  The latter expresses a related, but different 
concept -- it considers a relation, rather than a set, as initial segment of a relation.  


0. I prefer to define the upper-bound operations under, underS
etc. as opposed to working with combinations of relation image,
converse and diagonal, because the former seem more intuitive
notations when we think of orderings (but of course I cannot
define them as abbreviations, as this would have a global
effect, also affecting cases where one does not think of relations 
as orders). Moreover, in my locales the relation parameter r for
under, underS etc. is fixed, hence these operations can keep r
implicit. To get a concrete glimpse at my aesthetic reason for
introducing these operations: otherwise, instead of "underS a",
I would have to write "(r - Id)^-1 `` {a}" or "r^-1 `` {a} - Id".


1. Even though the main focus of this development are
the well-order relations, I prove the basic results on order relations
and bounds as generally as possible.
To the contrary, the results concerning minima, suprema and successors
are stated for well-order relations, not maximally generally.


2. "Refl_on A r" requires in particular that "r <= A <*> A",
and therefore whenever "Refl_on A r", we have that necessarily
"A = Field r". This means that in a theory of orders the domain
A would be redundant -- I decided not to include it explicitly
for most of the tehory.


3. An infinite ordinal/cardinal is one for which the field is infinite.
I always prefer the slightly more verbose "finite(Field r)" to the more compact
but less standard equivalent condition "finite r".


4. I (re?)proved Cantor's paradox and the Cantor-Bernstein
theorem, since I could not find them in the Isabelle archives.
In fact, I do not know whether *set versions* of these (as
opposed to *type versions*) exist. (Anyway, these facts are
straightforward and do not require ordinals/cardinals.)


5. After I proved lots of facts about injections and
bijections, I discovered that a couple of
fancier (set-restricted) version of some of them are proved in
the theory FuncSet. However, I did not need here restricted
abstraction and such, and felt I should not import the whole
theory for just a couple of minor facts.


6. I found that local definitions are sometimes preferable to
"let" notations, especially when large expressions are
involved. I introduce local definitions as follows:

obtain a where a_def: "a = ..." by blast

There are at least two main advantages I can see in local
definitions compared to "let" notations: 
- (i) goals (in the goal buffer) are more readable; 
- (ii) one has control on when to
expand the definition, preventing blast/auto/force from creating
undesired surprises.

Moreover, the use of local definitions in combination with
"unfolding" simulates perfectly the behavior "let" notations.

It would be nice to have a syntactic sugar for such local
definitions, such as "define a by ...".



Notes for myself (or for anyone who would like to enrich these theories in the future)
--------------------------------------------------------------------------------------

Theory Fun2.thy:
- Careful: "inj" is an abbreviation for "inj_on UNIV", while  
  "bij" is not an abreviation for "bij_betw UNIV UNIV", but 
  a defined constant; there is no "surj_betw", but only "surj". 
- In subsection "Purely functional properties": 
-- Recall lemma "comp_inj_on". 
-- A lemma for inj_on corresponding to "bij_betw_imp_card" already exists, and is called "card_inj_on_le".
- In subsection "Properties involving Hilbert choice": 
-- One should refrain from trying to prove "intuitive" properties of f conditioned 
  by properties of (Inv f A), such as "bij_betw A' A (Inv f A) ==> bij_betw A A' f".  
  They usually do not hold, since one cannot usually infer the well-definedness of "Inv f A". 
- A lemma "bij_betw_Inv_LEFT" -- why didn't "proof(auto simp add: bij_betw_Inv_left)" finish the proof?
-- Recall lemma "bij_betw_Inv". 
- In subsection "Other facts": 
-- Does the lemma "atLeastLessThan_injective" already exist anywhere? 

Theory Order_Relation2.thy:
- In subsection "Auxiliaries": 
-- Recall the lemmas "order_on_defs", "Field_def", "Domain_def", "Range_def", "converse_def". 
-- Recall that "refl_on r A" forces r to not be defined outside A.  
   This is  why "partial_order_def" 
   can afford to use non-parameterized versions of antisym and trans.  
-- Recall the ASCII notation for "converse r": "r ^-1". 
-- Recall the abbreviations: 
   abbreviation "Refl r ≡ refl_on (Field r) r"
   abbreviation "Preorder r ≡ preorder_on (Field r) r"
   abbreviation "Partial_order r ≡ partial_order_on (Field r) r"
   abbreviation "Total r ≡ total_on (Field r) r"
   abbreviation "Linear_order r ≡ linear_order_on (Field r) r"
   abbreviation "Well_order r ≡ well_order_on (Field r) r"

Theory Wellorder_Relation.thy:
- In subsection "Auxiliaries": recall lemmas "order_on_defs"
- In subsection "The notions of maximum, minimum, supremum, successor and order filter": 
  Should I define all constants from "wo_rel" in "rel" instead, 
  so that their outside definition not be conditional in "wo_rel r"? 

Theory Wellfounded2.thy:
  Recall the lemmas "wfrec" and "wf_induct". 

Theory Wellorder_Embedding:
- Recall "inj_on_def" and "bij_betw_def". 
- Line 5 in the proof of lemma embed_in_Field: I have to figure out for this and many other 
  situations:  Why did it work without annotations to Refl_under_in?
- At the proof of theorem "wellorders_totally_ordered" (and, similarly, elsewhere): 
  Had I used metavariables instead of local definitions for H, f, g and test, the 
  goals (in the goal window) would have become unreadable, 
  making impossible to debug theorem instantiations.  
- At lemma "embed_unique": If I add the attribute "rule format" at lemma, I get an error at qed.

Theory Constructions_on_Wellorders:
- Some of the lemmas in this section are about more general kinds of relations than 
  well-orders, but it is not clear whether they are useful in such more general contexts.
- Recall that "equiv" does not have the "equiv_on" and "Equiv" versions, 
 like the order relation. "equiv" corresponds, for instance, to "well_order_on". 
- The lemmas "ord_trans" are not clearly useful together, as their employment within blast or auto 
tends to diverge.  

Theory Cardinal_Order_Relation:
- Careful: if "|..|" meets an outer parehthesis, an extra space needs to be inserted, as in
  "( |A| )". 
- At lemma like ordLeq_Sigma_mono1: Not worth stating something like ordLeq_Sigma_mono2 -- 
  would be a mere instance of card_of_Sigma_mono2.  
- At lemma ordLeq_Sigma_cong2: Again, no reason for stating something like ordLeq_Sigma_cong2.  
- At lemma Fpow_Pow_finite: why wouldn't a version of this lemma with "... Int finite" 
also be proved by blast?  










