section {* Common Proof Methods and Idioms *} 
theory Idioms 
imports "../Sep_Main" "Open_List" Circ_List Hash_Set_Impl
begin 
text_raw{*\label{thy:ex:idioms}*}

  text {*
    This theory gives a short documentation of common proof techniques and 
    idioms for the separation logic framework. For this purpose, it presents
    some proof snippets (inspired by the other example theories), and heavily
    comments on them.
    *}

  subsection {* The Method @{text "sep_auto"}*}
  text {* The most versatile method of our framework is @{text "sep_auto"},
    which integrates the verification condition generator, the entailment
    solver and some pre- and postprocessing tactics based on the simplifier 
    and classical reasoner. It can be applied to a Hoare-triple or entailment
    subgoal, and will try to solve it, and any emerging new goals. It stops
    when the goal is either solved or it gets stuck somewhere. *}

  text {* As a simple example for @{text "sep_auto"} consider the following
    program that does some operations on two circular lists: *}
  definition "test \<equiv> do {
    l1 \<leftarrow> cs_empty;
    l2 \<leftarrow> cs_empty;
    l1 \<leftarrow> cs_append ''a'' l1;
    l2 \<leftarrow> cs_append ''c'' l2;
    l1 \<leftarrow> cs_append ''b'' l1;
    l2 \<leftarrow> cs_append ''e'' l2;
    l2 \<leftarrow> cs_prepend ''d'' l2;
    l2 \<leftarrow> cs_rotate l2;
    return (l1,l2)
  }"
  
  text {* The @{text "sep_auto"} method does all the 
    necessary frame-inference automatically, and thus manages to prove
    the following lemma in one step: *}
  lemma "<emp> 
    test 
    <\<lambda>(l1,l2). cs_list [''a'',''b''] l1 
      * cs_list [''c'',''e'',''d''] l2>\<^sub>t"
    unfolding test_def
    apply (sep_auto)
    done

  text {* @{text "sep_auto"} accepts all the section-options of the classical
    reasoner and simplifier, e.g., @{text "simp add/del:"}, @{text "intro:"}.
    Moreover, it has some more section options, the most useful being 
    @{text "heap add/del:"} to add or remove Hoare-rules that are applied
    with frame-inference. A complete documentation of the accepted options can
    be found in Section~\ref{sec:auto:overview}.
    *}

  text {* As a typical example, consider the following proof: *}
  lemma complete_ht_rehash: 
    "<is_hashtable l ht> ht_rehash ht 
    <\<lambda>r. is_hashtable l ht * is_hashtable (ls_rehash l) r>"
  proof -
    have LEN: " l \<noteq> [] \<Longrightarrow> Suc 0 < 2 * length l" by (cases l) auto
    show ?thesis
      apply (rule cons_pre_rule[OF ht_imp_len])
      unfolding ht_rehash_def
      apply (sep_auto 
        heap: complete_ht_new_sz complete_ht_copy
        simp: ls_rehash_def LEN
      ) -- "Here we add a heap-rule, and some simp-rules"
      done
  qed

  subsection {* Applying Single Rules *}
  text {* \paragraph{Hoare Triples} In this example, we show how to do
    a proof step-by-step. *}

  lemma
    "<os_list xs n> os_prepend x n <os_list (x # xs)>"
    unfolding os_prepend_def
    txt {* The rules to deconstruct compound statements are contained in the
      @{text "sep_decon_rules"} collection *}
    thm sep_decon_rules
    apply (rule sep_decon_rules)
    txt {* The rules for statement that deend on the heap are
      contained in the @{text sep_heap_rules} collection. The
      @{text "fi_rule"}-lemma prepares frame inference for them *}
    apply (rule sep_heap_rules[THEN fi_rule])
    apply frame_inference -- "This method does the frame-inference"
    
    txt {* The consequence rule comes in three versions, 
      @{text "const_rule"}, @{text "cons_pre_rule"}, 
      and @{text "cons_post_rule"}*}
    apply (rule cons_post_rule) 
    apply (rule sep_decon_rules)

    txt {* A simplification unfolds @{text "os_list"} and extract the
      pure part of the assumption *}
    apply (clarsimp)

    txt {* We can use @{text "ent_ex_postI"} to manually introduce 
      existentials in entailsments *}
    apply (rule_tac x=xa in ent_ex_postI)
    apply (rule_tac x=n in ent_ex_postI)
    txt {* The simplifier has a setup for assertions, so it will do the rest *}
    apply simp
    done

  text {* Note that the proof above can be done with @{text "sep_auto"},
    the "Swiss army knife" of our framework *}
  lemma
    "<os_list xs n> os_prepend x n <os_list (x # xs)>"
    unfolding os_prepend_def by sep_auto

  text {* \paragraph{Entailment} This example presents an actual proof
    from the circular list theory, where we have to manually apply a
    rule and give some hints to frame inference *}
  lemma cs_append_rule: 
    "<cs_list l p> cs_append x p <cs_list (l@[x])>"
    apply (cases p)
    apply (sep_auto simp: cs_append.simps)

    apply (sep_auto simp: cs_append.simps heap: lseg_append)
    txt {* At this point, we are left with an entailment subgoal that sep-auto
      cannot solve. A closer look reveals that we could use the rule
      @{text "lseg_append"}. 
      
      With the @{text "ent_frame_fwd"}-rule, we can manually apply a rule to
      solve an entailment, involving frame inference. In this case, we have
      the additional problem that frame-inference guesses
      a wrong instantiation, and is not able to infer the frame.
      So we have to pre-instantiate the rule, as done below. *}
    apply (rule_tac s1=pp in ent_frame_fwd[OF lseg_append])
    apply frame_inference -- "Now frame-inference is able to infer the frame"

    txt {* Now we are left with a trivial entailment, modulo commutativity of
      star. This can be handled by the entailment solver: *}
    apply solve_entails
    done



  subsection {* Functions with Explicit Recursion *}
  text {* If the termination argument of a function depends on one of
    its parameters, we can use the function package. For example, 
    the following function inserts elements from a list into a hash-set: *}

  fun ins_from_list 
    :: "('x::{heap,hashable}) list \<Rightarrow> 'x hashset \<Rightarrow> 'x hashset Heap" 
    where
    "ins_from_list [] hs = return hs" |
    "ins_from_list (x # l) hs = do { hs \<leftarrow> hs_ins x hs; ins_from_list l hs }"

  text {* Proofs over such functions are usually done by structural
    induction on the explicit parameter, in this case, on the list *}
  lemma ins_from_list_correct:
    "<is_hashset s hs> ins_from_list l hs <is_hashset (s\<union>set l)>\<^sub>t"
  proof (induction l arbitrary: hs s)
    case (Cons x l) 
    txt {* In the induction step, the induction hypothesis has to be 
      declared as a heap-rule, as @{text "sep_auto"} currently does not
      look for potential heap-rules among the premises of the subgoal *}
    show ?case by (sep_auto heap: Cons.IH)
  qed sep_auto


  subsection {*
    Functions with Recursion Involving the Heap
    *}
  text {* If the termination argument of a function depends on data stored on
    the heap, @{text "partial_function"} is a useful tool.

    Note that, despite the name, proving a Hoare-Triple @{text "<\<dots>> \<dots> <\<dots>>"}
    for something defined with @{text "partial_function"} implies total 
    correctness.
    *}

  text {* In the following example, we compute the sum of a list, using an
    iterator. Note that the partial-function package does not provide a
    code generator setup by default, so we have to add a @{text "[code]"}
    attribute manually*}
  partial_function (heap) os_sum' :: "int os_list_it \<Rightarrow> int \<Rightarrow> int Heap" 
    where [code]:
    "os_sum' it s = do {
      b \<leftarrow> os_it_has_next it;
      if b then do {
        (x,it') \<leftarrow> os_it_next it;
        os_sum' it' (s+x)
      } else return s
    }"

  text {* The proof that the function is correct can be done by induction
    over the representation of the list that we still have to iterate over.
    Note that for iterators over sets, we need induction on finite sets,
    cf. also @{text "To_List_Ga.thy"} *}

  lemma os_sum'_rule: 
    "<os_is_it l p l' it> 
    os_sum' it s 
    <\<lambda>r. os_list l p * \<up>(r = s + listsum l')>\<^sub>t"
  proof (induct l' arbitrary: it s)
    case Nil thus ?case
      txt {* To unfold the definition of a partial function, we have to use 
        @{text "subst"}. Note that @{text "simp"} would loop, unfolding the
        function arbitrarily deep *}
      apply (subst os_sum'.simps)
      txt {* @{text "sep_auto"} accepts all the section parameters that 
        @{text "auto"} does, eg. @{text "intro:"} *}
      apply (sep_auto intro: os.quit_iteration)
      done
  next
    case (Cons x l')
    show ?case
      apply (subst os_sum'.simps)
      txt {* Additionally, @{text "sep_auto"} accepts some more section 
        parameters. The most common one, @{text "heap:"}, declares rules 
        to be used with frame inference. See Section~\ref{sec:auto:overview}
        for a complete overview.*}
      apply (sep_auto heap: Cons.hyps)
      done
  qed


  subsection {* Precision Proofs *}
  text {*
    Precision lemmas show that an assertion uniquely determines some of its
    parameters. Our example shows that two list segments from the same start 
    pointer and with the same list, also have to end at the same end pointer.
    *}
  
  lemma lseg_prec3: 
    "\<forall>q q'. h \<Turnstile> (lseg l p q * F1) \<and>\<^sub>A (lseg l p q' * F2) \<longrightarrow> q=q'"
    apply (intro allI)
  proof (induct l arbitrary: p F1 F2)
    case Nil thus ?case 
      apply simp -- "A precision solver for references and arrays is included
        in the standard simplifier setup. Building a general precision solver
        remains future work."
      by metis -- "Unfortunately, the simplifier cannot cope with arbitrarily  
        directed equations, so we have to use some more powerful tool"
  next
    case (Cons x l)
    show ?case
      apply clarsimp
  
      apply (subgoal_tac "na=n")
  
      txt {* The @{text "prec_frame"} and @{text "prec_frame'"} rules are 
        useful to do precision proofs *}
      apply (erule prec_frame'[OF Cons.hyps])
      apply frame_inference
      apply frame_inference
  
      apply (drule prec_frame[OF sngr_prec])
      apply frame_inference
      apply frame_inference
      apply simp
      done
  qed
end
