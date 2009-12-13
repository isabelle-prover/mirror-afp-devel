(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header "Isabelle Collections Framework Userguide"
theory Userguide
imports 
  Collections
  Efficient_Nat
begin
text_raw {*\label{thy:Userguide}*}

subsection "Introduction"
text {*
  The Isabelle Collections Framework defines interfaces of various collection types and provides some standard implementations and generic algorithms.

  The relation between the data-structures of the collection framework and standard Isabelle datatypes (e.g. for sets and maps) is established by abstraction functions.

  Currently, the Isabelle Collections Framework provides set and map implementations based on associative lists and red-black trees. Moreover, an implementation of a FIFO-queue based on
  lists is provided.
*}

subsubsection "Getting Started"
text {*
  To get started with the Isabelle Collections Framework (assuming that you are already familiar with Isabelle/HOL and Isar),
  you should first read the introduction (this section), that provides many basic examples. 
  Section~\ref{sec:userguide.structure} explains the concepts of the Isabelle Collections Framework in more detail.
  Section~\ref{sec:userguide.ext} provides information on extending the framework along with detailed examples, and 
  Section~\ref{sec:userguide.design} contains a discussion on the design of this framework.
*}

subsubsection "Introductory Example"
text {*
  We introduce the Isabelle Collections Framework by a simple example.

  Given a set of elements represented by a red-black tree, and a list, 
  we want to filter out all elements that are not contained in the set. 
  This can be done by Isabelle/HOL's @{const filter}-function\footnote{Note that Isabelle/HOL uses the list comprehension syntax @{term [source] "[x\<leftarrow>l. P x]"}
  as syntactic sugar for filtering a list.}:
*}

definition rbt_restrict_list :: "'a::linorder rs \<Rightarrow> 'a list \<Rightarrow> 'a list"
where "rbt_restrict_list s l == [ x\<leftarrow>l. rs_memb x s ]"

text {*
  The type @{typ "'a rs"} is the type of sets backed by red-black trees.
  Note that the element type of sets backed by red-black trees must be
  of sort @{text linorder}.
  The function @{const rs_memb} tests membership on such sets.
*}  

text {* Next, we show correctness of our function: *}
lemma rbt_restrict_list_correct: 
  assumes [simp]: "rs_invar s"
  shows "rbt_restrict_list s l = [x\<leftarrow>l. x\<in>rs_\<alpha> s]"
  by (simp add: rbt_restrict_list_def rs.memb_correct)

text {*
  The lemma @{thm [source] rs.memb_correct}: @{thm [display] rs.memb_correct[no_vars]} 

  states correctness of the @{const rs_memb}-function. 
  The function @{const rs_\<alpha>} maps a red-black-tree to the set that it represents.
  Moreover, we have to explicitely keep track of the invariants of the used data-structure,
  in this case red-black trees. 
  The predicate @{const rs_invar} denotes the invariant for red-black trees that represent sets.

  Note that many correctness lemmas for standard RBT-set-operations are summarized by the lemma @{thm [source] rs_correct}:
    @{thm [display] rs_correct[no_vars]}
*}

text {*
  All implementations provided by this library are compatible with the Isabelle/HOL code-generator.
  Now follow some examples of using the code-generator and the related value-command:
*}

text {*
  There are conversion functions from lists to sets and, vice-versa, from sets to lists:
*}
value "list_to_rs [1::int..10]"
value "rs_to_list (list_to_rs [1::int .. 10])"
value "rs_to_list (list_to_rs [1::int,5,6,7,3,4,9,8,2,7,6])"

text {*
  Note that sets make no guarantee about ordering, hence the only thing we can 
  prove about conversion from sets to lists is:
    @{thm [source] rs.to_list_correct}: @{thm [display] rs.to_list_correct[no_vars]}

*}


value "rbt_restrict_list (list_to_rs [1::nat,2,3,4,5]) [1::nat,9,2,3,4,5,6,5,4,3,6,7,8,9]"

definition "test n = (list_to_rs [(1::int)..n])"

export_code test in SML module_name test
ML {*
  open test;
  
  test 90000

*}

subsubsection "Theories"
text {*
  To make available the whole collections framework to your formalization, import the theory @{theory Collections}.

  Other theories in the Isabelle Colelction Framework include:
  \begin{description}
    \item[@{theory SetSpec}] Specification of sets and set functions
    \item[@{theory SetGA}] Generic algorithms for sets
    \item[@{theory SetStdImpl}] Standard set implementations (list, rb-tree, hash)
    \item[@{theory MapSpec}] Specification of maps
    \item[@{theory MapGA}] Generic algorithms for maps
    \item[@{theory MapStdImpl}] Standard map implementations (list,rb-tree, hash)
    \item[@{theory Algos}] Various generic algorithms
    \item[@{theory SetIndex}] Generic algorithm for building indices of sets
    \item[@{theory Fifo}] Amortized fifo queue
    \item[@{theory DatRef}] Data refinement for the while combinator
  \end{description}

*}

subsubsection "Iterators"
text {* An important concept when using collections are iterators. An iterator is a kind of generalized fold-functional.
  Like the fold-functional, it applies a function to all elements of a set and modifies a state. There are
  no guarantees about the iteration order. But, unlike the fold functional, you can prove useful properties of iterations
  even if the function is not left-commutative. Proofs about iterations are done in invariant style, establishing an
  invariant over the iteration.

  The iterator combinator for red-black tree sets is @{const rs_iterate}, and the proof-rule that is usually used is:
    @{thm [source] rs.iterate_rule_P}: @{thm [display] rs.iterate_rule_P[no_vars]}

  The invariant @{term I} is parameterized with the set of remaining elements that have not yet been iterated over and the
  current state. The invariant has to hold for all elements remaining and the initial state: @{term "I (rs_\<alpha> S) \<sigma>0"}. 
  Moreover, the invariant has to be preserved by an iteration step: 
    @{term [display] "\<And>x it \<sigma>. \<lbrakk>x \<in> it; it \<subseteq> rs_\<alpha> S; I it \<sigma>\<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>)"}
  And the proposition to be shown for the final state must be a consequence of the invarant for no 
  elements remaining: @{term "\<And>\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"}. 
*}

thm rs.iteratei_rule_P[no_vars]

text {*
  A generalization of iterators are {\em interruptible iterators} where iteration is only continues while some condition on the state holds.
  Reasoning over interruptible iterators is also done by invariants: 
    @{thm [source] rs.iteratei_rule_P}: @{thm [display] rs.iteratei_rule_P[no_vars]}

  Here, interruption of the iteration is handled by the premise
    @{term [display] "\<And>\<sigma> it. \<lbrakk>it \<subseteq> rs_\<alpha> S; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"}
  that shows the proposition from the invariant for any intermediate state of the 
  iteration where the continuation condition 
  does not hold (and thus the iteration is interrupted).
*}

text {*
  As an example of reasoning about results of iterators, we implement a function
  that converts a hashset to a list that contains precisely the elements of the set.
*}

definition "hs_to_list' s == hs_iterate (op #) s []"

text {*
  The correctness proof works by establishing the invariant that the list contains
  all elements that have already been iterated over.
*}
lemma hs_to_list'_correct: 
  assumes INV: "hs_invar s"
  shows "set (hs_to_list' s) = hs_\<alpha> s"
  apply (unfold hs_to_list'_def)
  apply (rule_tac 
    I="\<lambda>it \<sigma>. set \<sigma> = hs_\<alpha> s - it"
    in hs.iterate_rule_P[OF INV])
  txt {* The resulting proof obligations are easily discharged using auto: *}
  apply auto
  done


text {*
  As an example for an interruptible iterator, 
  we define a bounded existential-quantification over the list elements.
  As soon as the first element is found that fulfills the predicate,
  the iteration is interrupted.
  The state of the iteration is simply a boolean, indicating the (current) result of the quantification:
*}

definition "hs_bex s P == hs_iteratei (\<lambda>\<sigma>. \<not> \<sigma>) (\<lambda>x \<sigma>. P x) s False"

lemma hs_bex_correct: 
  "hs_invar s \<Longrightarrow> hs_bex s P \<longleftrightarrow> (\<exists>x\<in>hs_\<alpha> s. P x)"
  apply (unfold hs_bex_def)
  txt {* The invariant states that the current result matches the result of the quantification
    over the elements already iterated over: *}
  apply (rule_tac 
    I="\<lambda>it \<sigma>. \<sigma> \<longleftrightarrow> (\<exists>x\<in>hs_\<alpha> s - it. P x)" 
    in hs.iteratei_rule_P)
  txt {* The resulting proof obligations are easily discharged by auto: *}
  apply auto
  done


subsection "Structure of the Framework"
text_raw {*\label{sec:userguide.structure}*}
text {*
  The concepts of the framework are roughly based on the object-oriented concepts of interfaces, implementations and generic algorithms.

  The concepts used in the framework are the following:
  \begin{description}
    \item[Interfaces] An interface describes some concept by providing an abstraction mapping $\alpha$ to a related Isabelle/HOL-concept.
      The definition is generic in the datatype used to implement the concept (i.e. the concrete data structure). An interface is specified by means 
      of a locale that fixes the abstraction mapping and an invariant.
      For example, the set-interface contains an abstraction mapping to sets, and is specified by the locale @{text SetSpec.set}.
      An interface roughly matches the concept of a (collection) interface in Java, e.g. {\em java.util.Set}.
  
    \item[Functions] A function specifies some functionality involving interfaces. A function is specified by means of a locale.
                      For example, membership query for a set is specified by the locale @{const [source] SetSpec.set_memb} and
                      equality test between two sets is a function specified by @{const [source] SetSpec.set_equal}.
                      A function roughly matches a method declared in an interface, e.g. {\em java.util.Set\#contains, java.util.Set\#equals}.

    \item[Generic Algorithms] A generic algorithm specifies, in a generic way, how to implement a function using other functions. For example,
                              the equality test for sets may be implemented using a subset function. It is described by the constant @{const [source] SetGA.subset_equal} and the
                              corresponding lemma @{thm [source] SetGA.subset_equal_correct}. There is no direct match of generic algorithms in the Java Collections Framework. The
                              most related concept are abstract collection interfaces, that provide some default algorithms, e.g. {\em java.util.AbstractSet}.
                              The concept of {\em Algorithm} in the C++ Standard Template Library \cite{C++STL} matches the concept of Generic Algorithm quite well.


    \item[Implementation] An implementation of an interface provides a data structure for that interface together with an abstraction mapping and an invariant. Moreover, it provides implementations for some (or all) 
       functions of that interface.
       For example, red-black trees are an implementation of the set-interface, with the abstraction mapping @{const rs_\<alpha>} and invariant @{const rs_invar}; and the 
       constant @{const rs_ins} implements the insert-function, as stated by the lemma @{thm [source] rs_ins_impl}.
       An implementation matches a concrete collection interface in Java, e.g. {\em java.util.TreeSet}, and the methods implemented by such an interface, e.g. {\em java.util.TreeSet\#add}.


    \item[Instantiation] An instantiation of a generic algorithm provides actual implementations for the used functions. For example,
        the generic equality-test algorithm can be instantiated to use red-black-trees for both arguments (resulting in the function @{const rr_equal} and the lemma @{thm [source] rr_equal_impl}).
        While some of the functions of an implementation need to be implemented specifically, many functions may be obtained by instantiating generic algorithms.
        In Java, instantiation of a generic algorithm is matched most closely by inheriting from an abstract collection interface. In the C++ Standard Template Library instantiation of generic algorithms
        is done implicitely when using them.

  \end{description}

*}

  subsubsection "Naming Conventions"
  text {*
    There are the following general naming conventions used inside the Isabelle Collections Framework:
    Each implementation has a two-letter and a one-letter abbreviation, that are used as prefixes for the related constants, lemmas and instantiations.

    The two-letter abbreviations should be unique over all interfaces and instantiations, the one-letter abbreviations should be unique
    over all implementations of the same interface.
    Names that reference the implementation of only one interface are prefixed with that implementation's two-letter abbreviation (e.g. @{const hs_ins} for insertion into a HashSet (hs,h)),
    names that reference more than one implementation are prefixed with the one-letter abbreviations (e.g. @{const lhh_union} for set union between a ListSet(ls,l) and a HashSet(hs,h), yielding a HashSet)
    
    Currently, there are the following abbreviations:
    \begin{description}
      \item[lm,l] List Map
      \item[rm,r] RB-Tree Map
      \item[hm,h] Hash Map
      \item[ls,l] List Set
      \item[rs,r] RB-Tree Set
      \item[hs,h] Hash Set
    \end{description}

    Each function @{text name} of an interface @{text interface} is declared in a locale @{text interface_name}. This locale provides a fact @{text name_correct}. For example, there is the locale @{const set_ins} providing
    the fact @{thm [source] set_ins.ins_correct}.
    An implementation instantiates the locales of all implemented functions, using its two-letter abbreviation as instantiation prefix. For example, the HashSet-implementation instantiates the locale @{const set_ins} 
    with the prefix {\em hs}, yielding the lemma @{thm [source] hs.ins_correct}. Moreover, an implementation with two-letter abbreviation {\em aa} provides a lemma @{text aa_correct} 
    that summarizes the correctness facts for the basic 
    operations. It should only contain those facts that are safe to be used with the simplifier. E.g., the correctness facts for basic operations on hash sets are available via the lemma @{thm [source] hs_correct}.
  *}

subsection "Extending the Framework"
text_raw {*\label{sec:userguide.ext}*}
  text {* This section illustrates, by example, how to add new interfaces, functions, generic algorithms and implementations to the framework: *}

  subsubsection "Interfaces"
  text {*
    An interface provides a new concept, that is usually mapped to a related Isabelle/HOL-concept. 
    An interface is defined by providing a locale that fixes an abstraction mapping and
    an invariant. For example, consider the definition of an interface for sets:
    *}

  locale set' = 
    -- "Abstraction mapping to Isabelle/HOL sets"
    fixes \<alpha> :: "'s \<Rightarrow> 'a set"
    -- "Invariant"
    fixes invar :: "'s \<Rightarrow> bool"

  text {*
    The invariant makes it possible for an implementation to restrict to certain subsets of the type's universal set.
    Theoretically, this could also be done by a typedef, however, this is not supported by the code generator (as of Isabelle2009).
    *}

  subsubsection "Functions"
  text {*
    A function describes some operation on instances of an interface. It is specified by providing a locale that includes
    the locale of the interface, fixes a parameter for the operation and makes a correctness assumption.
    For an interface @{text interface} and an operation @{text name}, the function's locale has the name @{text interface_name},
    the fixed parameter has the name @{text name} and the correctness assumption has the name @{text name_correct}.

    As an example, consider the specifications of the insert function for sets and the empty set:
    *}
  locale set'_ins = set' +
    -- "Give reasonable names to types:"
    constrains \<alpha> :: "'s \<Rightarrow> 'a set"
    -- "Parameter for function:"
    fixes ins :: "'a \<Rightarrow> 's \<Rightarrow> 's"
    -- {* Correctness assumption. A correctness assumption usually consists of two parts:
      \begin{itemize}
        \item A description of the operation on the abstract level, assuming that the operands satisfy the invariants.
        \item The invariant preservation assumptions, i.e. assuming that the result satisfies its invariants if the operands do.
      \end{itemize}
    *}
    assumes ins_correct: 
      "invar s \<Longrightarrow> \<alpha> (ins x s) = insert x (\<alpha> s)"
      "invar s \<Longrightarrow> invar (ins x s)"

  locale set'_empty = set' +
    constrains \<alpha> :: "'s \<Rightarrow> 'a set"
    fixes empty :: "'s"
    assumes empty_correct: 
      "\<alpha> empty = {}"
      "invar empty"
  
  text {*
    In general, more than one interface or more than one instance of the same interface may be involved in a function.
    Consider, for example, the intersection of two sets. It involves three instances of set interfaces, two for the 
    operands and one for the result:
    *}

  locale set'_inter = set' \<alpha>1 invar1 + set' \<alpha>2 invar2 + set' \<alpha>3 invar3 
    for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1 
    and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2 
    and \<alpha>3 :: "'s3 \<Rightarrow> 'a set" and invar3 
    +
    fixes inter :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's3"
    assumes inter_correct: 
      "\<lbrakk>invar1 s1; invar2 s2\<rbrakk> \<Longrightarrow> \<alpha>3 (inter s1 s2) = \<alpha>1 s1 \<inter> \<alpha>2 s2"
      "\<lbrakk>invar1 s1; invar2 s2\<rbrakk> \<Longrightarrow> invar3 (inter s1 s2)"

  text {* For use in further examples, we also specify a function that converts a list to a set *}
  locale set'_list_to_set = set' +
    constrains \<alpha> :: "'s \<Rightarrow> 'a set"
    fixes list_to_set :: "'a list \<Rightarrow> 's"
    assumes list_to_set_correct: 
      "\<alpha> (list_to_set l) = set l"
      "invar (list_to_set l)"

  subsubsection "Generic Algorithm"
  text {*
    A generic algorithm describes how to implement a function using implementations of other functions. 
    Thereby, it is parametric in the actual implementations of the functions.

    A generic algorithm comes with the definition of a function and a correctness lemma. The function takes the
    required functions as arguments. The convention for argument order is that the required functions come first,
    then the implemented function's arguments.

    Consider, for example, the generic algorithm to convert a list to a set\footnote{To keep the presentation simple, 
    we use a non-tail-recursive version here}. This function requires implementations of the {\em empty} and {\em ins} functions\footnote{Due to name-clashes with @{const [long_names] Map.empty} and @{const [long_names] RBT.ins} we have to
      use slightly different parameter names here}:
    *}

  fun list_to_set' :: "'s \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's) 
    \<Rightarrow> 'a list \<Rightarrow> 's" where
    "list_to_set' empt ins' [] = empt" |
    "list_to_set' empt ins' (a#ls) = ins' a (list_to_set' empt ins' ls)"

  lemma list_to_set'_correct:
    fixes empty ins
    -- {* Assumptions about the required function implementations: *}
    assumes "set'_empty \<alpha> invar empty"
    assumes "set'_ins \<alpha> invar ins"
    -- {* Provided function: *}
    shows "set'_list_to_set \<alpha> invar (list_to_set' empty ins)"
  proof -
    interpret set'_empty \<alpha> invar empty by fact
    interpret set'_ins \<alpha> invar ins by fact
    
    { 
      fix l
      have "\<alpha> (list_to_set' empty ins l) = set l 
            \<and> invar (list_to_set' empty ins l)"
        by (induct l) 
           (simp_all add: empty_correct ins_correct)
    }
    thus ?thesis 
      by unfold_locales auto
  qed

  text_raw {*\paragraph{Generic Algorithms with ad-hoc function specification}*}
  text {* The collection framework also contains a few generic algorithms that do not implement a function that is specified via a locale, 
    but the function is specified ad-hoc within the correctness lemma. An example is the generic algorithm @{const [source] Algos.map_to_nat} that computes an injective map
    from the elements of a given finite set to an initial segment of the natural numbers. There is no locale specifying such a function, but the function is implicitly specified 
    by the correctness lemma @{thm [source] map_to_nat_correct}: @{thm [display] map_to_nat_correct[no_vars]}

    This kind of ad-hoc specification should only be used when it is unlikely that the same function may be
    implemented differently.
    *}


  subsubsection {* Implementation *}
  text {*
    An implementation of an interface defines an actual data structure, an invariant, and
    implementations of the functions.
    An implementation has a two-letter abbreviation that should be unique and a one-letter abbreviation that
    should be unique amongst all implementations of the same interface.

    Consider, for example, a set implementation by distinct lists. It has the abbreviations (ls,l). To avoid name clashes with the
    existing list-set implementation in the framework, we use ticks (') here and there to disambiguate the names.
    *}

  -- "The type of the data structure should be available as the two-letter abbreviation: "
  types 'a ls' = "'a list"
  -- "The abstraction function:"
  definition "ls'_\<alpha> == set"
  -- "The invariant: In our case we constrain the lists to be distinct:"
  definition "ls'_invar == distinct"
  -- "The locale of the interface is interpreted with the two-letter abbreviation as prefix:"
  interpretation ls': set' ls'_\<alpha> ls'_invar .

  text {*
    Next, we implement some functions. The implementation of a function @{text name} is prefixed by the two-letter prefix:
    *}

  definition "ls'_empty == []"
  text {* Each function implementation has a corresponding lemma that shows the instantiation of the locale. It is named
    by the function's name suffixed with @{text "_impl"}: 
    *}
  lemma ls'_empty_impl: "set'_empty ls'_\<alpha> ls'_invar ls'_empty"
    by (unfold_locales)
       (auto simp add: ls'_empty_def ls'_invar_def ls'_\<alpha>_def)

  text {* The corresponding function's locale is interpreted with the function implementation and the interface's two-letter abbreviation as prefix: *}
  interpretation ls': set'_empty ls'_\<alpha> ls'_invar ls'_empty
    using ls'_empty_impl .
  text {* This generates the lemma 
    @{thm [source] ls'.empty_correct}: @{thm [display] ls'.empty_correct[no_vars]}
    *}

  definition "ls'_ins x l == if x\<in>set l then l else x#l"

  text {* Correctness may optionally be established using separate lemmas. These should be suffixed with {\em \_aux}
    to indicate that they should not be used by other proofs:*}
  lemma ls'_ins_correct_aux: 
    "ls'_invar l \<Longrightarrow> ls'_\<alpha> (ls'_ins x l) = insert x (ls'_\<alpha> l)"
    "ls'_invar l \<Longrightarrow> ls'_invar (ls'_ins x l)"
    by (auto simp add: ls'_ins_def ls'_invar_def ls'_\<alpha>_def)

  lemma ls'_ins_impl: "set'_ins ls'_\<alpha> ls'_invar ls'_ins"
    by unfold_locales
       (simp_all add: ls'_ins_correct_aux)

  interpretation ls': set'_ins ls'_\<alpha> ls'_invar ls'_ins
    using ls'_ins_impl .

  subsubsection {* Instantiations (Generic Algorithm)*}
  text {*
    The instantiation of a generic algorithm substitutes actual implementations for the required functions.
    A generic algorithm is instantiated by providing a definition that fixes the function parameters accordingly.
    Moreover, an @{text "impl"}-lemma and an interpretation of the implemented function's locale is provided.
    These can usually be constructed canonically from the generic algorithm's correctness lemma:

    For example, consider conversion from lists to list-sets by instantiating the @{const list_to_set'}-algorithm:
    *}
  definition "ls'_list_to_set == list_to_set' ls'_empty ls'_ins"
  lemmas ls'_list_to_set_impl = list_to_set'_correct[OF ls'_empty_impl ls'_ins_impl, folded ls'_list_to_set_def]
  interpretation ls': set'_list_to_set ls'_\<alpha> ls'_invar ls'_list_to_set 
    using ls'_list_to_set_impl .

  text {*
    Note that the actual framework slightly deviates from the naming convention here, the corresponding instantiation of
    @{const [source] SetGA.gen_list_to_set} is called @{const list_to_ls}, the @{text impl}-lemma is called @{thm [source] list_to_ls_impl}.
    *}

  text {*
    Generating all possible instantiations of generic algorithms based on the available implementations can be done mechanically.
    Currently, we have not implemented such an approach on the Isabelle ML-level. However, we used an ad-hoc ruby-script ({\em scripts/inst.rb}) to generate the
    thy-file {\em StdInst.thy} from the file {\em StdInst.in.thy}.
    *}


subsection "Design Issues"
text_raw {*\label{sec:userguide.design}*}
  text {*
    In this section, we motivate some of the design decisions of the Isabelle Collections Framework and report our experience with alternatives.
    Many of the design decisions are justified by restrictions of Isabelle/HOL and the code generator, so that there may be better
    options if those restrictions should vanish from future releases of Isabelle/HOL.
    *}

  text {*
    The main design goals of this development are:
    \begin{enumerate}
      \item\label{dg_unified} Make available various implementations of collections under a unified interface.
      \item\label{dg_extensible} It should be easy to extend the framework by new interfaces, functions, algorithms, and implementations.
      \item\label{dg_concise} Allow simple and concise reasoning over functions using collections.
      \item\label{dg_genalgo} Allow generic algorithms, that are independent of the actual data structure that is used.
      \item\label{dg_exec} Support generation of executable code.
      \item\label{dg_control} Let the user precisely control what data structures are used in the implementation.
    \end{enumerate}
    *}

  subsubsection {* Data Refinement *}
  text {*
    In order to allow simple reasoning over collections, we use a data refinement approach. Each collection
    interface has an abstraction function that maps it on a related Isabelle/HOL concept (abstract level).
    The specification of functions are also relative to the abstraction.
    This allows most of the correctness reasoning to be done on the abstract level. On this level,
    the tool support is more elaborated and one is not yet fixed to a concrete implementation.
    In a next step, the abstract specification is refined to use an actual implementation (concrete level). The correctness properties
    proven on the abstract level usually transfer easily to the concrete level.

    Moreover, the user has precise control how the refinement is done, i.e. what data structures are used. An alternative would be to do refinement
    completely automatic, as e.g. done in the code generator setup of the Theory~{\em Executable-Set}. This has teh advantage that it induces less writing overhead.
    The disadvantage is that the user looses a great amount of control over the refinement. For example, in {\em Executable-Set}, all sets have to be represented by lists,
    and there is no possibility to represent one set differently from another. 
    *}

  subsubsection {* Grouping Functions *}
  text {*
    We have experimented with grouping functions of an interface together via a record.
    This has the advantage that parameterization of generic algorithms becomes simpler,
    as multiple function parameters are replaced by a single record parameter.
    However, on the other hand, a choice of sensible groups of functions is not obvious,
    and the use of the functions is a bit more writing overhead.
    As the generic algorithms in this framework only depend on a few function parameters,
    we have not grouped operations together. However, this may well make sense for more complex
    generic algorithms, that depend on many functions. A borderline example are the generic indexing algorithms
    defined in Theory~@{theory SetIndex}. The algorithms depend on quite a few functions. While we need to explicitely
    specify them as parameters, we try to simplify reasoning about them by defining an appropriate locale.
    *}

  subsubsection {* Locales for Generic Algorithms *}
  text {*
    Another tempting possibility to define a generic algorithm is to define a locale that includes
    the locales of all required functions, and do the definition of the generic algorithm inside that locale.
    This has the advantage that the function parameters are made implicit, thus improving readability.
    On the other hand, the code generator has problems with generating code
    from definitions inside a locale. Currently, one has to manually set up the code generator for such definitions. 
    Moreover, when fixing function parameters in the declaration of the locale, their types will be infered independently of
    the definitions later done in the locale context. In order to get the correct types, one has to add explicit type constraints.
    These tend to become rather lengthy, especially for iterator states.
    The approach taken in this framework -- passing the required functions as explicit parameters to a generic algorithm --
    usually needs less type constraints, as type inference usually does most of the job, in particular it infers the correct types of iterator states.
    *}

  subsubsection {* Explicit Invariants vs Typedef *}
  text {*
    The interfaces of this framework use explicit invariants. A more elegant alterative would be to use
    typedefs to make the invariants implicit, e.g. one could define the type of all well-formed RB-trees.
    However, this approach is not supported by the code generator (as of Isabelle2009), hence we had to chose
    the explicit invariant approach.
    *}


end
