header {* \isaheader{Automatic Refinement Examples} *}
theory Automatic_Refinement
imports "../Refine" "../Autoref_Collection_Bindings"
begin
  text {*
    This theory demonstrates the usage of the autodet-tool for automatic
    determinization.
    *}


text {* We start with a worklist-algorithm *}
definition "exploresl succ s0 st \<equiv>
  do {
    (_,_,f)\<leftarrow>WHILET (\<lambda>(wl,es,f). wl\<noteq>[] \<and> \<not>f) (\<lambda>(wl,es,f). do {
      let s=hd wl; let wl=tl wl;
      if s\<in>es then 
        RETURN (wl,es,f)
      else if s=st then 
        RETURN ([],{},True)
      else 
        RETURN (wl @ succ s,insert s es,f)
    }) ([s0],{},False);
    RETURN f
  }"

text {*
  The following is a typical approach for usage of the automatic 
  refinement method. The desired refinements are specified by the type,
  declaring partially instantiated @{text "spec_R"}-lemmas as
  @{text "[autoref_spec]"}. Here, @{text "'c"} is the concrete type, and
  @{text "'a"} is the abstract type that shall be translated to @{text "'c"}.

  Note that @{text "spec_Id"} is a shortcut for @{text "spec_R"} with 
  @{text "'c='a"}.

  In general, variables that occur in the lemma, e.g., parameters of the
  function to be refined, will not be translated automatically. Hence, the
  assumptions of the lemma must specify appropriate relations. In our example,
  we use the same parameters for the abstract and concrete algorithm.
*}
schematic_lemma 
  fixes s0::"'V::hashable"
  notes [autoref_spec] =
    spec_Id[where 'a="bool"] 
    spec_Id[where 'a="'V"]
    spec_Id[where 'a="'V list"]
    spec_R[where 'c="'V hs" and 'a="'V set"]
  shows "\<lbrakk>(succ,succ)\<in>Id; (s0,s0)\<in>Id; (st,st)\<in>Id\<rbrakk> \<Longrightarrow> 
    (?f::?'a nres) \<le>\<Down>(?R) (exploresl succ s0 st)" 
  unfolding exploresl_def apply -
  apply (refine_autoref)
  done

text {*
  Unfortunately, Isabelle/HOL has some pitfalls here:
  \begin{itemize}
  \item Make sure that all type variables refered to in a 
    @{text "notes"}-section occur in a fixes-section {\em before} the 
    notes-section. Otherwise, Isabelle forgets to assign the 
    typeclass-constraints to the noted theorems. Alternatively,
    you may pass the specification theorems as arguments to the autoref-method.
  \item If you use a schematic refinement relation at the toplevel 
    (@{text "?R"} in this example), make sure to also explicitely specify a
    schematic type for it (@{text "?f::?'a nres"} in this example). Otherwise,
    Isabelle just assigns it a fixed type variable that cannot be further
    instantiated.
  \end{itemize}
*}


text {* Autoref also accept spec-theorems as arguments: *}
schematic_lemma 
  fixes s0::"'V::hashable"
  shows "\<lbrakk>(succ,succ)\<in>Id; (s0,s0)\<in>Id; (st,st)\<in>Id\<rbrakk> \<Longrightarrow> 
    (?f::?'a nres) \<le>\<Down>(?R) (exploresl succ s0 st)" 
  unfolding exploresl_def apply -
  apply (refine_autoref
    spec_Id[where 'a="bool"] 
    spec_Id[where 'a="'V"]
    spec_Id[where 'a="'V list"]
    spec_R[where 'c="'V hs" and 'a="'V set"]
  )
  done

text {*
  If you forget something, in this case, a specification to translate 
  @{text "bool"}, the method @{text "refine_autoref"} will stop at the
  expression that it could not completely translate. Here, single-step mode
  (@{text "refine_autoref (ss)"}) helps to identify
  the problem: It stops after each step applied to the subgoal. Note that it
  may have result sequences with more than one element. In this case,
  use @{text "back"} to switch through the alternatives.
*}

schematic_lemma 
  fixes s0::"'V::hashable"
  notes [autoref_spec] =
    (*spec_Id[where 'a="bool"]*) 
    spec_Id[where 'a="'V"]
    spec_Id[where 'a="'V list"]
    spec_R[where 'c="'V hs" and 'a="'V set"]
  shows "\<lbrakk>(succ,succ)\<in>Id; (s0,s0)\<in>Id; (st,st)\<in>Id\<rbrakk> \<Longrightarrow> 
    (?f::?'a nres) \<le>\<Down>(?R) (exploresl succ s0 st)" 
  unfolding exploresl_def apply -
  apply (refine_autoref)
  txt {* Push refinement as far as possible *}
  apply (refine_autoref (ss))+
  back -- {*There are many alternatives. However, already the first goal of the 
    first alternative, i.e. @{text "(?cb10, False) \<in> ?Rb10"}, indicates the
    problem --- there is no specification to translate booleans.*}
  oops

text {*
  In the next example, we have two sets of the same type: Both, the
  workset and the visited set are sets of nodes.
*}
definition "explores1 succ s0 st \<equiv>
  do {
    (_,_,f)\<leftarrow>WHILET (\<lambda>(ws,es,f). ws\<noteq>{} \<and> \<not>f) (\<lambda>(ws,es,f). do {
      ASSERT (ws\<noteq>{}); s\<leftarrow>SPEC (\<lambda>s. s\<in>ws); 
      let ws=ws-{s};
      let es=es\<union>{s};
      if s=st then 
        RETURN ({},{},True)
      else 
        RETURN (ws \<union> (set (succ s) - es),es,f)
    }) ({s0},{},False);
    RETURN f
  }"

text {*
  First, we translate both sets to hashsets.
*}
schematic_lemma 
  fixes s0::"'V::hashable"
  notes [autoref_spec] = 
    spec_Id[where 'a="bool"] 
    spec_Id[where 'a="'V"]
    spec_Id[where 'a="'V list"]
    spec_R[where 'c="'V hs" and 'a="'V set"]
  shows "\<lbrakk>(succ,succ)\<in>Id; (s0,s0)\<in>Id; (st,st)\<in>Id\<rbrakk> \<Longrightarrow> 
    (?f::?'a nres) \<le>\<Down>(?R) (explores1 succ s0 st)"  
  unfolding explores1_def
  apply refine_autoref
  done

text {*
  As a second alternative, we use tagging to translate the sets
  to different concrete sets. Here, tags are used to indicate
  the desired concretization. 
*}
definition "explores1' succ s0 st \<equiv>
  do {
    (_,_,f)\<leftarrow>WHILET (\<lambda>(ws,es,f). ws\<noteq>{} \<and> \<not>f) (\<lambda>(ws,es,f). do {
      ASSERT (ws\<noteq>{}); s\<leftarrow>SPEC (\<lambda>s. s\<in>ws); 
      let ws=ws-{s};
      let es=es\<union>{s};
      if s=st then 
        RETURN ({},{},True)
      else 
        RETURN (ws \<union> (set (succ s) - es),es,f)
    }) (TAG ''workset'' {s0},TAG ''visited-set'' {},False);
    RETURN f
  }"

schematic_lemma test: 
  fixes s0::"'V::hashable"
  notes [autoref_spec] = 
    spec_Id[where 'a="'V"]
    spec_Id[where 'a="'V list"]
    spec_Id[where 'a="bool"]
    spec_R[where 'a="'V set" and R="br ls_\<alpha> ls_invar"]
    spec_R[where 'a="'V set" and R="br hs_\<alpha> hs_invar"]
    TAG_dest[where name="''workset''" and R="br ls_\<alpha> ls_invar"]
    TAG_dest[where name="''visited-set''" and R="br hs_\<alpha> hs_invar"]
  
  shows "\<lbrakk>(succ,succ)\<in>Id; (s0,s0)\<in>Id; (st,st)\<in>Id\<rbrakk> 
    \<Longrightarrow> (?f::?'a nres) \<le>\<Down>?R (explores1' succ (s0::'V) st)" 
  unfolding explores1'_def
  apply refine_autoref
  done

end
