header {* \chapter{Examples} \label{ch:examples} \isaheader{Examples from ITP-2010 slides} *}
theory itp_2010
imports "../Collections"
begin

text {*
  Illustrates the various possibilities how to use the ICF in your own 
  algorithms by simple examples. The examples all use the data refinement scheme,
  and either define a generic algorithm or fix the operations.
*}


  -- "Example for slides"

subsection "List to Set"
text {*
  In this simple example we do conversion from a list to a set.
  We define an abstract algorithm.
  This is then refined by a generic algorithm using a locale and by a generic 
  algorithm fixing its operations as parameters.
*}
  subsubsection "Straightforward version"
  -- "Abstract algorithm"
  fun set_a where
    "set_a [] s = s" |
    "set_a (a#l) s = set_a l (insert a s)"

  -- "Correctness of aa"
  lemma set_a_correct: "set_a l s = set l \<union> s"
    by (induct l arbitrary: s) auto

  -- "Generic algorithm"
  fun (in StdSetDefs) set_i where
    "set_i [] s = s" |
    "set_i (a#l) s = set_i l (ins a s)"

  -- "Correct implementation of ca"
  lemma (in StdSet) set_i_impl: "invar s \<Longrightarrow> invar (set_i l s) \<and> \<alpha> (set_i l s) = set_a l (\<alpha> s)"
    by (induct l arbitrary: s) (auto simp add: correct)

  -- "Instantiation"
  (* We need to declare a constant to make the code generator work *)
  definition "hs_seti == hsr.set_i"
  declare hsr.set_i.simps[folded hs_seti_def, code]

  lemmas hs_set_i_impl = hsr.set_i_impl[folded hs_seti_def]

export_code hs_seti in SML file -

  -- "Code generation"
  ML {* @{code hs_seti} *} 
  (*value "hs_seti [1,2,3::nat] hs_empty"*)

  subsubsection "Tail-Recursive version"
  -- "Abstract algorithm"
  fun set_a2 where
    "set_a2 [] = {}" |
    "set_a2 (a#l) = (insert a (set_a2 l))"

  -- "Correctness of aa"
  lemma set_a2_correct: "set_a2 l = set l"
    by (induct l) auto

  -- "Generic algorithm"
  fun (in StdSetDefs) set_i2 where
    "set_i2 [] = empty" |
    "set_i2 (a#l) = (ins a (set_i2 l))"

  -- "Correct implementation of ca"
  lemma (in StdSet) set_i2_impl: "invar s \<Longrightarrow> invar (set_i2 l) \<and> \<alpha> (set_i2 l) = set_a2 l"
    by (induct l) (auto simp add: correct)

  -- "Instantiation"
  definition "hs_seti2 == hsr.set_i2"
  declare hsr.set_i2.simps[folded hs_seti2_def, code]

  lemmas hs_set_i2_impl = hsr.set_i2_impl[folded hs_seti2_def]

  -- "Code generation"
  ML {* @{code hs_seti2} *} 
  (*value "hs_seti [1,2,3::nat] hs_empty"*)

subsubsection "With explicit operation parameters"

  -- "Alternative for few operation parameters"
  fun set_i' where
    "!!ins. set_i' ins [] s = s" |
    "!!ins. set_i' ins (a#l) s = set_i' ins l (ins a s)"

  lemma (in StdSet) set_i'_impl:
    "invar s \<Longrightarrow> invar (set_i' ins l s) \<and> \<alpha> (set_i' ins l s) = set_a l (\<alpha> s)"
    by (induct l arbitrary: s) (auto simp add: correct)

  -- "Instantiation"
  definition "hs_seti' == set_i' hs_ins"
  lemmas hs_set_i'_impl = hsr.set_i'_impl[folded hs_seti'_def, unfolded hs_ops_unfold]

  -- "Code generation"
  ML {* @{code hs_seti'} *} 
  (*value "hs_seti' [1,2,3::nat] hs_empty"*)


subsection "Complex Example: Filter Average"
text {*
  In this more complex example, we develop a function that filters from a set all
  numbers that are above the average of the set.
 
  First, we formulate this as a generic algorithm using a locale.
  This solution illustrates some technical problems with larger generic 
  algorithms:
  \begin{itemize}
    \item Operations that are used with different types within the generic 
          algorithm need to be specified multiple times, once for every type.
          This is an inherent problem with Isabelle's type system, and there is
          no obvious solution.
          This effect occurs especially when one uses the same type of set/map 
          for different element types, or uses operations that have some 
          additional type parameters, like the iterators in our example.

    \item The code generator has problems generating code for instantiated 
          algorithms. This is due to the resulting equations having the 
          instantiated part fixed on their lhs. This problem could probably be 
          solved within the code generator. The workaround we use here is to 
          define one new constant per function and instantiation and alter the 
          code equations using this definitions. This could probably be automated
          and/or integrated into the code generator.

  \end{itemize}

  The second possibility avoids the above problems by fixing the used 
  implementaion beforehand. Changing the implementation is still easy by
  changing the used operations. In this example, all used operations are 
  introduced by abbbreviations, localizing the required changes to a small part
  of the theory.
  

*}

  abbreviation "average S == \<Sum>S div card S"

  locale MyContextDefs =
    StdSetDefs ops for ops :: "(nat,'s,'more) set_ops_scheme" +
    fixes iterate :: "('s,nat,nat\<times>nat) iterator"
    fixes iterate' :: "('s,nat,'s) iterator"
  begin
    definition avg_aux :: "'s \<Rightarrow> nat\<times>nat" 
      where
      "avg_aux s == iterate (\<lambda>x (c,s). (c+1, s+x)) s (0,0)"

    definition "avg s == case avg_aux s of (c,s) \<Rightarrow> s div c"

    definition "filter_le_avg s == let a=avg s in
      iterate' (\<lambda>x s. if x\<le>a then ins x s else s) s empty"
  end

  locale MyContext = MyContextDefs ops iterate iterate' +
    StdSet ops +
    it!: set_iterate \<alpha> invar iterate +
    it'!: set_iterate \<alpha> invar iterate'
    for ops iterate iterate'
  begin
    lemma avg_aux_correct: "invar s \<Longrightarrow> avg_aux s = (card (\<alpha> s), \<Sum>(\<alpha> s) )"
      apply (unfold avg_aux_def)
      apply (rule_tac 
        I="\<lambda>it (c,sum). c=card (\<alpha> s - it) \<and> sum=\<Sum>(\<alpha> s - it)" 
        in it.iterate_rule_P)
      apply auto
      apply (subgoal_tac "\<alpha> s - (it - {x}) = insert x (\<alpha> s - it)")
      apply auto
      apply (subgoal_tac "\<alpha> s - (it - {x}) = insert x (\<alpha> s - it)")
      apply auto
      done

    lemma avg_correct: "invar s \<Longrightarrow> avg s = average (\<alpha> s)"
      unfolding avg_def
      using avg_aux_correct
      by auto

    lemma filter_le_avg_correct: 
      "invar s \<Longrightarrow> 
        invar (filter_le_avg s) \<and> 
        \<alpha> (filter_le_avg s) = {x\<in>\<alpha> s. x\<le>average (\<alpha> s)}"
      unfolding filter_le_avg_def Let_def
      apply (rule_tac
        I="\<lambda>it r. invar r \<and> \<alpha> r = {x\<in>\<alpha> s - it. x\<le>average (\<alpha> s)}"
        in it'.iterate_rule_P)
      apply (auto simp add: correct avg_correct)
      done
  end

  interpretation hs_ctx: MyContext hs_ops hs_iterate hs_iterate
    by unfold_locales

  definition "test_hs == hs_ins (1::nat) (hs_ins 10 (hs_ins 11 hs_empty))"
  definition "testfun_hs == hs_ctx.filter_le_avg"

  definition "hs_avg_aux == hs_ctx.avg_aux"
  definition "hs_avg == hs_ctx.avg"
  definition "hs_filter_le_avg == hs_ctx.filter_le_avg"
  lemmas hs_ctx_defs = hs_avg_aux_def hs_avg_def hs_filter_le_avg_def 

  lemmas [code] = hs_ctx.avg_aux_def[folded hs_ctx_defs]
  lemmas [code] = hs_ctx.avg_def[folded hs_ctx_defs]
  lemmas [code] = hs_ctx.filter_le_avg_def[folded hs_ctx_defs]


  interpretation rs_ctx: MyContext rs_ops rs_iterate rs_iterate
    by unfold_locales

  definition "test_rs == rs_ins (1::nat) (rs_ins 10 (rs_ins 11 rs_empty))"
  definition "testfun_rs == rs_ctx.filter_le_avg"

  definition "rs_avg_aux == rs_ctx.avg_aux"
  definition "rs_avg == rs_ctx.avg"
  definition "rs_filter_le_avg == rs_ctx.filter_le_avg"
  (* TODO/FIXME: Why is here an additional type/ itself parameter ??? *)
  lemmas rs_ctx_defs = rs_avg_aux_def rs_avg_def rs_filter_le_avg_def 

  lemmas [code] = rs_ctx.avg_aux_def[folded rs_ctx_defs]
  lemmas [code] = rs_ctx.avg_def[folded rs_ctx_defs]
  lemmas [code] = rs_ctx.filter_le_avg_def[folded rs_ctx_defs]


  -- "Code generation"
  ML {* @{code hs_filter_le_avg} @{code test_hs} *} 


  -- "Using abbreviations"

  type_synonym 'a my_set = "'a hs"
  abbreviation "my_\<alpha> == hs_\<alpha>"
  abbreviation "my_invar == hs_invar"
  abbreviation "my_empty == hs_empty"
  abbreviation "my_ins == hs_ins"
  abbreviation "my_iterate == hs_iterate"
  lemmas my_correct = hs_correct
  lemmas my_iterate_rule_P = hs.iterate_rule_P

  definition avg_aux :: "nat my_set \<Rightarrow> nat\<times>nat" 
    where
    "avg_aux s == my_iterate (\<lambda>x (c,s). (c+1, s+x)) s (0,0)"

  definition "avg s == case avg_aux s of (c,s) \<Rightarrow> s div c"

  definition "filter_le_avg s == let a=avg s in
    my_iterate (\<lambda>x s. if x\<le>a then my_ins x s else s) s my_empty"

  lemma avg_aux_correct: "my_invar s \<Longrightarrow> avg_aux s = (card (my_\<alpha> s), \<Sum>(my_\<alpha> s) )"
    apply (unfold avg_aux_def)
    apply (rule_tac 
      I="\<lambda>it (c,sum). c=card (my_\<alpha> s - it) \<and> sum=\<Sum>(my_\<alpha> s - it)" 
      in my_iterate_rule_P)
    apply auto
    apply (subgoal_tac "my_\<alpha> s - (it - {x}) = insert x (my_\<alpha> s - it)")
    apply auto
    apply (subgoal_tac "my_\<alpha> s - (it - {x}) = insert x (my_\<alpha> s - it)")
    apply auto
    done

  lemma avg_correct: "my_invar s \<Longrightarrow> avg s = average (my_\<alpha> s)"
    unfolding avg_def
    using avg_aux_correct
    by auto

  lemma filter_le_avg_correct: 
    "my_invar s \<Longrightarrow> 
    my_invar (filter_le_avg s) \<and> 
    my_\<alpha> (filter_le_avg s) = {x\<in>my_\<alpha> s. x\<le>average (my_\<alpha> s)}"
    unfolding filter_le_avg_def Let_def
    apply (rule_tac
      I="\<lambda>it r. my_invar r \<and> my_\<alpha> r = {x\<in>my_\<alpha> s - it. x\<le>average (my_\<alpha> s)}"
      in my_iterate_rule_P)
    apply (auto simp add: my_correct avg_correct)
    done


  definition "test_set == my_ins (1::nat) (my_ins 2 (my_ins 3 my_empty))"

  export_code avg_aux avg filter_le_avg test_set in SML module_name Test file -

end

