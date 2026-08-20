(*  Title:       Implementation of DPN pre$^*$-algorithm
    ID:
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section \<open>Implementation of DPN pre$^*$-algorithm\<close>

theory DPN_implEx
imports DPN FSM_ex
begin
text \<open>
  In this section, we provide a straightforward executable specification of the DPN-algorithm. 
  It has a polynomial complexity, but is far from having optimal complexity.
\<close>

subsection \<open> Representation of DPN and M-automata \<close>
type_synonym 'c rule_ex = "'c\<times>'c\<times>'c\<times>'c list" 
type_synonym 'c DPN_ex = "'c rule_ex list"

definition "rule_repr == { ((p,\<gamma>,p',c'),(p#[\<gamma>],a,p'#c')) | p \<gamma> p' c' a . True }"
definition "rules_repr == { (l,l') . rule_repr `` set l = l' }"

lemma rules_repr_cons: "\<lbrakk> (R,S)\<in>rules_repr \<rbrakk> \<Longrightarrow> ((p,\<gamma>,p',c')\<in>set R) = (\<exists>a. (p#[\<gamma>] \<hookrightarrow>\<^bsub>a\<^esub> p'#c') \<in> S)"
  by (unfold rules_repr_def rule_repr_def) blast

text \<open> We define the mapping to sp-states explicitely, well-knowing that it makes the algorithm even more inefficient \<close>
definition "find_sp d s p == first_that (\<lambda>t. let (sh,ph,qh)=t in if s=sh \<and> p=ph then Some qh else None) d"

text \<open> This locale describes an M-automata together with its representation used in the implementation \<close>
locale MFSM_ex = MFSM +
  fixes R and D
  assumes rules_repr: "(R,rules M)\<in>rules_repr"
  assumes D_above: "\<delta> A \<subseteq> set D" and D_below: "set D \<subseteq> ps_upper M A"

text \<open> This lemma exports the additional conditions of locale MFSM\_ex to locale MFSM \<close>
lemma (in MFSM) MFSM_ex_alt: "MFSM_ex M A R D \<longleftrightarrow> (R,rules M)\<in>rules_repr \<and> \<delta> A \<subseteq> set D \<and> set D \<subseteq> ps_upper M A"
  using MFSM_axioms by (unfold MFSM_def MFSM_ex_def MFSM_ex_axioms_def) (auto)

lemmas (in MFSM_ex) D_between = D_above D_below

text \<open> The representation of the sp-states behaves as expected \<close>
lemma (in MFSM_ex) find_sp_cons:
  assumes A: "s\<in>cstates A" "p\<in>csyms M"
  shows "find_sp D s p = Some (sp A s p)"
proof -
  let ?f = "(\<lambda>t. let (sh,ph,qh)=t in if s=sh \<and> p=ph then Some qh else None)"
  from A have "(s,p,sp A s p)\<in>set D" using cstate_succ_ex' D_between by simp
  moreover have "?f (s,p,sp A s p) = Some (sp A s p)" by auto
  ultimately obtain sp' where G: "find_sp D s p = Some sp'"
    using first_thatI1[of "(s,p,sp A s p)" D ?f "sp A s p"] by (unfold find_sp_def, blast)
  with first_thatE1[of ?f D sp'] obtain t where "t\<in>set D \<and> ?f t=Some sp'" by (unfold find_sp_def, blast)
  hence "(s,p,sp')\<in>set D" by (cases t, auto split: if_splits)
  with A D_between have "sp'=sp A s p" using cstate_succ_unique' by simp
  with G show ?thesis by simp
qed

subsection \<open> Next-element selection \<close>
text \<open> The implementation goes straightforward by implementing a function to return the next transition to be added to the transition relation of the automata being saturated \<close>

definition sel_next:: "'c DPN_ex \<Rightarrow> ('s,'c) delta \<Rightarrow> ('s \<times> 'c \<times> 's) option" where
  "sel_next R D == 
     first_that (\<lambda>r. let (p,\<gamma>,p',c') = r in
       first_that (\<lambda>t. let (q,pp',sp') = t in 
         if pp'=p' then
           case find_sp D q p of
             Some spt \<Rightarrow> (case lookup (\<lambda>q'. (spt,\<gamma>,q') \<notin> set D) D sp' c' of
               Some q' \<Rightarrow> Some (spt,\<gamma>,q') |
               None \<Rightarrow> None
             ) | _ \<Rightarrow> None
         else None
       ) D
     ) R"
  
text \<open> The state of our algorithm consists of a representation of the DPN-rules and a representation of the transition relations of the automata being saturated \<close>
type_synonym ('c,'s) seln_state = "'c DPN_ex \<times> ('s,'c) delta"

text \<open> As long as the next-element function returns elements, these are added to the transition relation and the algorithm is applied recursively. @{text "sel_next_state"} describes the next-state selector function, 
  and @{text "seln_R"} describes the corresponding recursion relation. \<close>
 
definition
  "sel_next_state S == let (R,D)=S in case sel_next R D of None \<Rightarrow> None | Some t \<Rightarrow> Some (R,t#D)"

definition
  "seln_R == graph sel_next_state"

lemma seln_R_alt: "seln_R == {((R,D),(R,t#D)) | R D t. sel_next R D = Some t}"
  by (rule eq_reflection, unfold seln_R_def graph_def sel_next_state_def) (auto split: option.split_asm)

subsection \<open> Termination \<close>
subsubsection \<open> Saturation upper bound \<close>
text \<open> Before we can define the algorithm as recursive function, we have to prove termination, that is well-foundedness of the corresponding recursion relation @{text "seln_R"} \<close>

text \<open> We start by defining a trivial finite upper bound for the saturation, simply as the set of all possible transitions in the automata. Intuitively, this bound is valid because the
  saturation algorithm only adds transitions, but never states to the automata \<close>
definition
  "seln_triv_upper R D == states D \<times> ((fst\<circ>snd) ` (set R) \<union> alpha D) \<times> states D"

lemma seln_triv_upper_finite: "finite (seln_triv_upper R D)" by (unfold seln_triv_upper_def) (auto simp add: states_finite alpha_finite)

lemma D_below_triv_upper: "set D \<subseteq> seln_triv_upper R D" using statesAlpha_subset 
  by (unfold seln_triv_upper_def) auto

lemma seln_triv_upper_subset_preserve: "set D \<subseteq> seln_triv_upper A D' \<Longrightarrow> seln_triv_upper A D \<subseteq> seln_triv_upper A D'" 
  by (unfold seln_triv_upper_def) (blast intro: statesAlphaI dest: statesE alphaE)

lemma seln_triv_upper_mono: "set D \<subseteq> set D' \<Longrightarrow> seln_triv_upper R D \<subseteq> seln_triv_upper R D'"
  by (unfold seln_triv_upper_def) (auto dest: states_mono alpha_mono)
  
lemma seln_triv_upper_mono_list: "seln_triv_upper R D \<subseteq> seln_triv_upper R (t#D)" by (auto intro!: seln_triv_upper_mono)
lemma seln_triv_upper_mono_list': "x\<in>seln_triv_upper R D \<Longrightarrow> x\<in>seln_triv_upper R (t#D)" using seln_triv_upper_mono_list by (fast)

text \<open> The trivial upper bound is not changed by inserting a transition to the automata that was already below the upper bound \<close>
lemma seln_triv_upper_inv: "\<lbrakk>t\<in>seln_triv_upper R D; set D' = insert t (set D)\<rbrakk> \<Longrightarrow> seln_triv_upper R D = seln_triv_upper R D'"
  by (unfold seln_triv_upper_def) (auto dest: statesAlpha_insert)

text \<open> States returned by @{text "find_sp"} are valid states of the underlying automaton \<close>
lemma find_sp_in_states: "find_sp D s p = Some qh \<Longrightarrow> qh\<in>states D" by (unfold find_sp_def) (auto dest: first_thatE1 split: if_splits simp add: statesAlphaI)

text \<open> The next-element selection function returns a new transition, that is below the trivial upper bound \<close>
lemma sel_next_below: 
  assumes A: "sel_next R D = Some t"
  shows "t\<notin>set D \<and> t\<in>seln_triv_upper R D"
proof -
  {
    fix q a qh b q'
    assume A: "(q,a,qh)\<in>set D" and B: "(qh,b,q')\<in>trcl (set D)"
    from B statesAlpha_subset[of D] have "q'\<in>states D"
      apply -
      apply (erule (1) trcl_structE)
      using A by (simp_all add: statesAlphaI)
  }
  thus ?thesis
    using A
    apply (unfold sel_next_def seln_triv_upper_def)
    apply (clarsimp dest!: first_thatE1 lookupE1 split: if_splits option.split_asm)
    apply (force simp add: find_sp_in_states dest!: first_thatE1 lookupE1 split: if_splits option.split_asm)
    done
qed

text \<open> Hence, it does not change the upper bound \<close>
corollary sel_next_upper_preserve: "\<lbrakk>sel_next R D = Some t\<rbrakk> \<Longrightarrow> seln_triv_upper R D = seln_triv_upper R (t#D)" proof -
  have "set (t#D) = insert t (set D)" by auto
  moreover assume "sel_next R D = Some t"
  with sel_next_below have "t\<in>seln_triv_upper R D" by blast
  ultimately show ?thesis by (blast dest: seln_triv_upper_inv)
qed

subsubsection \<open> Well-foundedness of recursion relation \<close>
lemma seln_R_wf: "wf (seln_R\<inverse>)" proof -
  let ?rel="{((R,D),(R,D')) | R D D'. set D\<subset>set D' \<and> seln_triv_upper R D = seln_triv_upper R D'}"
  have "seln_R\<inverse> \<subseteq> ?rel\<inverse>"
    apply (unfold seln_R_alt)
    apply (clarsimp, safe)
    apply (blast dest: sel_next_below)
    apply (simp add: seln_triv_upper_mono_list')
    apply (simp add: sel_next_upper_preserve)
    done
  also
  let ?alpha="\<lambda>x. let (R,D)=x in seln_triv_upper R D - set D"
  let ?rel2="finite_psubset\<inverse>"
  have "?rel\<inverse> \<subseteq> inv_image (?rel2\<inverse>) ?alpha" using D_below_triv_upper by (unfold finite_psubset_def, fastforce simp add: inv_image_def seln_triv_upper_finite)
  finally have "seln_R\<inverse> \<subseteq> inv_image (?rel2\<inverse>) ?alpha" .
  moreover
  have "wf (?rel2\<inverse>)" using wf_finite_psubset by simp
  hence "wf (inv_image (?rel2\<inverse>) ?alpha)" by (rule wf_inv_image)
  ultimately show ?thesis by (blast intro: wf_subset)
qed

subsubsection \<open> Definition of recursive function \<close>
function pss_algo_rec :: "('c,'s) seln_state \<Rightarrow> ('c,'s) seln_state"
  where "pss_algo_rec (R,D) = (case sel_next R D of Some t \<Rightarrow> pss_algo_rec (R,t#D) | None \<Rightarrow> (R,D))"
  by pat_completeness auto

termination
  apply (relation "seln_R\<inverse>")
  apply (simp add: seln_R_wf)
  unfolding seln_R_alt by blast

lemma pss_algo_rec_newsimps[simp]: 
  "\<lbrakk>sel_next R D = None\<rbrakk> \<Longrightarrow> pss_algo_rec (R,D) = (R,D)"
  "\<lbrakk>sel_next R D = Some t\<rbrakk> \<Longrightarrow> pss_algo_rec (R,D) = pss_algo_rec (R,t#D)"
  by auto
  
declare pss_algo_rec.simps[simp del]


subsection \<open> Correctness \<close>
subsubsection \<open> seln\_R refines ps\_R \<close>
text \<open>
  We show that @{term seln_R} refines @{term ps_R}, that is that every step made by our implementation corresponds to a step
  in the nondeterministic algorithm, that we already have proved correct in theory DPN.
\<close>
    
  (* FIXME: Spaghetti-proof*)
lemma (in MFSM_ex) sel_nextE1:
  assumes A: "sel_next R D = Some (s,\<gamma>,q')"
  shows "(s,\<gamma>,q')\<notin>set D \<and> (\<exists> q p a c'. s=sp A q p \<and> [p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M \<and> (q,c',q')\<in>trclAD A (set D))" 
proof -
  let ?f = "\<lambda>p \<gamma> p' c' t. let (q,pp',sp') = t in 
       if pp'=p' then
         case find_sp D q p of
           Some s \<Rightarrow> (case lookup (\<lambda>q'. (s,\<gamma>,q') \<notin> set D) D sp' c' of
             Some q' \<Rightarrow> Some (s,\<gamma>,q') |
             None \<Rightarrow> None
           ) | _ \<Rightarrow> None
       else None"

  let ?f1 = "\<lambda>r. let (p,\<gamma>,p',c') = r in first_that (?f p \<gamma> p' c') D"

  from A[unfolded sel_next_def] obtain r where 1: "r\<in>set R \<and> ?f1 r = Some (s,\<gamma>,q')" by (blast dest: first_thatE1)
  then obtain p \<gamma>h p' c' where 2: "r=(p,\<gamma>h,p',c') \<and> first_that (?f p \<gamma>h p' c') D = Some (s,\<gamma>,q')" by (cases r) simp 
  then obtain t where 3: "t\<in>set D \<and> ?f p \<gamma>h p' c' t = Some (s,\<gamma>,q')" by (blast dest: first_thatE1)
  then obtain q sp' where 4: "t=(q,p',sp') \<and> (case find_sp D q p of                
             Some s \<Rightarrow> (case lookup (\<lambda>q'. (s,\<gamma>h,q') \<notin> set D) D sp' c' of
               Some q' \<Rightarrow> Some (s,\<gamma>h,q') |
               None \<Rightarrow> None
             ) | _ \<Rightarrow> None) = Some (s,\<gamma>,q')"
    by (cases t, auto split: if_splits)
  hence 5: "find_sp D q p = Some s \<and> lookup (\<lambda>q'. (s,\<gamma>h,q') \<notin> set D) D sp' c' = Some q' \<and> \<gamma>=\<gamma>h"
    by (simp split: option.split_asm)
  with 1 2 rules_repr obtain a where 6: "(p#[\<gamma>],a,p'#c')\<in>rules M" by (blast dest: rules_repr_cons)
  hence 7: "p\<in>csyms M \<and> p'\<in>csyms M \<and> \<gamma>\<in>ssyms M" by (blast dest: rule_fmt_fs)
  with 3 4 D_below have 8: "q\<in>cstates A \<and> sp'=sp A q p'" by (blast dest: csym_from_cstate' cstate_succ_unique')
  with 5 7 have 9: "s=sp A q p" using D_above D_below by (auto simp add: find_sp_cons)
  have 10: "(s,\<gamma>,q')\<notin>set D \<and> (sp',c',q')\<in>trclAD A (set D)" using 5 8 uniqueSp 7 states_part D_below ps_upper_below_trivial
    apply - apply (rule lookup_trclAD_E1)
    by auto
  moreover have "(q,p'#c',q')\<in>trclAD A (set D)" proof -
    from 7 8 sp_pred_ex D_above have "(q,p',sp')\<in>set D" by auto
    with 10 trclAD.cons show ?thesis using 7 8 alpha_cons states_part by auto
  qed
  ultimately show ?thesis using 9 6 by blast
qed


lemma (in MFSM_ex) sel_nextE2:
  assumes A: "sel_next R D = None"
  shows "\<not>(\<exists> q p \<gamma> q' a c' t. t\<notin>set D \<and> t=(sp A q p,\<gamma>,q') \<and> [p,\<gamma>]\<hookrightarrow>\<^bsub>a\<^esub> c' \<in> rules M \<and> (q,c',q')\<in>trclAD A (set D))"
proof (clarify) \<comment> \<open> Assume we have such a rule and transition, and infer @{term "sel_next R D \<noteq> None"} \<close>
  fix q p \<gamma> q' a pc'
  assume C: "(sp A q p, \<gamma>, q') \<notin> set D" "([p, \<gamma>], a, pc') \<in> rules M" "(q, pc', q') \<in> trclAD A (set D)"

  from C obtain p' c' where SYMS: "p\<in>csyms M \<and> p'\<in>csyms M \<and> \<gamma>\<in>ssyms M \<and> pc'=p'#c'" by (blast dest: rule_fmt)
  have QCS: "q\<in>cstates A" "(q,p',sp A q p')\<in>set D" "(sp A q p',c',q')\<in>trclAD A (set D)" proof -
    from C SYMS obtain sp' where "(q,p',sp')\<in>set D \<and> (sp',c',q')\<in>trclAD A (set D)" by (blast dest: trclAD_uncons)
    moreover with D_below SYMS show "q\<in>cstates A" by (auto intro: csym_from_cstate')
    ultimately show "(q,p',sp A q p')\<in>set D" "(sp A q p',c',q')\<in>trclAD A (set D)" using D_below cstate_succ_unique' by auto
  qed

  from C QCS lookup_trclAD_I1[of "D" "set D" "sp A q p'" c' q' A "(\<lambda>q''. (sp A q p,\<gamma>,q'') \<notin> set D)"] obtain q'' where N1: "lookup (\<lambda>q''. (sp A q p,\<gamma>,q'') \<notin> set D) D (sp A q p') c' = Some q''" by blast

  let ?f = "\<lambda>p \<gamma> p' c' q pp' sp'.            
         if pp'=p' then
           case find_sp D q p of
             Some s \<Rightarrow> (case lookup (\<lambda>q'. (s,\<gamma>,q') \<notin> set D) D sp' c' of
               Some q' \<Rightarrow> Some (s,\<gamma>,q') |
               None \<Rightarrow> None
             ) | _ \<Rightarrow> None
         else None"


  from SYMS QCS have FIND_SP: "find_sp D q p = Some (sp A q p)" using D_below D_above by (simp add: find_sp_cons)
  let ?f1 = "(\<lambda>p \<gamma> p' c'. (\<lambda>t. let (q,pp',sp')=t in ?f p \<gamma> p' c' q pp' sp'))"
  from N1 FIND_SP have N2: "?f1 p \<gamma> p' c' (q,p',sp A q p') = Some (sp A q p, \<gamma>, q'')" by auto
  with QCS first_thatI1[of "(q,p',sp A q p')" D "?f1 p \<gamma> p' c'"] obtain t' where N3: "first_that (?f1 p \<gamma> p' c') D = Some t'" by (blast)
  let ?f2 = "(\<lambda>r. let (p,\<gamma>,p',c') = r in first_that (?f1 p \<gamma> p' c') D)"
  from N3 have "?f2 (p,\<gamma>,p',c') = Some t'" by auto
  moreover from SYMS C rules_repr have "(p,\<gamma>,p',c')\<in>set R" by (blast dest: rules_repr_cons)
  ultimately obtain t'' where "first_that ?f2 R = Some t''" using first_thatI1[of "(p, \<gamma>, p', c')" R ?f2] by (blast)
  hence "sel_next R D = Some t''" by (unfold sel_next_def)
  with A show False by simp
qed

lemmas (in MFSM_ex) sel_nextE = sel_nextE1 sel_nextE2

lemma (in MFSM_ex) seln_cons1: "\<lbrakk>sel_next R D = Some t\<rbrakk> \<Longrightarrow> (set D,insert t (set D))\<in>ps_R M A" using D_below by (cases t, auto dest: sel_nextE intro: ps_R.intros)
lemma (in MFSM_ex) seln_cons2: "sel_next R D = None \<Longrightarrow> set D\<notin>Domain (ps_R M A)" by (blast dest: sel_nextE elim: ps_R.cases)

lemma (in MFSM_ex) seln_cons1_rev: "\<lbrakk>set D\<notin>Domain (ps_R M A)\<rbrakk> \<Longrightarrow> sel_next R D = None" by (cases "sel_next R D") (auto iff add: seln_cons1 seln_cons2)
lemma (in MFSM_ex) seln_cons2_rev: "\<lbrakk>set D\<in>Domain (ps_R M A)\<rbrakk> \<Longrightarrow> \<exists>t. sel_next R D = Some t \<and> (set D,insert t (set D))\<in>ps_R M A" 
  by (cases "sel_next R D") (auto iff add: seln_cons1 seln_cons2 ps_R_dom_below)

text \<open> DPN-specific abstraction relation, to associate states of deterministic algorithm with states of @{term ps_R} \<close>
definition "\<alpha>seln M A == { (set D, (R,D)) | D R. MFSM_ex M A R D}"

lemma \<alpha>selnI: "\<lbrakk>S=set D; MFSM_ex M A R D\<rbrakk> \<Longrightarrow> (S,(R,D))\<in>\<alpha>seln M A"
  by (unfold \<alpha>seln_def) auto

lemma \<alpha>selnD: "(S,(R,D))\<in>\<alpha>seln M A \<Longrightarrow> S=set D \<and> MFSM_ex M A R D"
  by (unfold \<alpha>seln_def) auto

lemma \<alpha>selnD': "(S,C)\<in>\<alpha>seln M A \<Longrightarrow> S=set (snd C) \<and> MFSM_ex M A (fst C) (snd C)" by (cases C, simp add: \<alpha>selnD)

lemma \<alpha>seln_single_valued: "single_valued ((\<alpha>seln M A)\<inverse>)"
  by  (unfold \<alpha>seln_def) (auto intro: single_valuedI)

theorem (in MFSM) seln_refines: "seln_R \<le>\<^bsub>\<alpha>seln M A\<^esub> (ps_R M A)" proof (rule refinesI)
  show "\<alpha>seln M A O seln_R \<subseteq> ps_R M A O \<alpha>seln M A" proof (rule refines_compI)
    fix a c c'
    assume ABS: "(a,c)\<in>\<alpha>seln M A" and R: "(c,c')\<in>seln_R"
    then obtain R D t where 1: "c=(R,D) \<and> c'=(R,t#D) \<and> sel_next R D = Some t" by (unfold seln_R_alt, blast)
    moreover with ABS have 2: "a=set D \<and> MFSM_ex M A R D" by (unfold \<alpha>seln_def, auto)
    ultimately have 3: "(set D,(set (t#D))) \<in> ps_R M A" using MFSM_ex.seln_cons1[of M A R D] by auto
    moreover have "(set (t#D), (R,t#D))\<in>\<alpha>seln M A"
    proof -
      from 2 have "\<delta> A \<subseteq> set D" using MFSM_ex.D_above[of M A R D] by auto 
      with 3 have "\<delta> A \<subseteq> set (t#D)" "set (t#D) \<subseteq> ps_upper M A" using ps_R_below by (fast+)
      with 2 have "MFSM_ex M A R (t#D)" by (unfold MFSM_ex_alt, simp)
      thus ?thesis unfolding \<alpha>seln_def by auto
    qed
    ultimately show "\<exists>a'. (a, a') \<in> ps_R M A \<and> (a', c') \<in> \<alpha>seln M A" using 1 2 by blast
  qed
next
  show "\<alpha>seln M A `` Domain (ps_R M A) \<subseteq> Domain seln_R"
    apply (rule refines_domI)
    apply (unfold \<alpha>seln_def seln_R_alt)
    apply (unfold Domain_iff)
    apply (clarsimp)
    apply (fast dest: MFSM_ex.seln_cons2_rev)
    done
qed

subsubsection \<open> Computing transitions only \<close>
definition pss_algo :: "'c DPN_ex \<Rightarrow> ('s,'c) delta \<Rightarrow> ('s,'c) delta" where "pss_algo R D \<equiv> snd (pss_algo_rec (R,D))"


subsubsection \<open> Correctness \<close>

text \<open> We have to show that the next-state selector function's graph refines @{text "seln_R"}. This is trivial because we defined @{text "seln_R"} to be that graph \<close>
lemma sns_refines: "graph sel_next_state \<le>\<^bsub>Id\<^esub> seln_R" by (unfold seln_R_def) simp

interpretation det_impl: detRef_impl pss_algo_rec sel_next_state seln_R
  apply (rule detRef_impl.intro)
  apply (simp_all only: detRef_wf_transfer[OF seln_R_wf] sns_refines)
  apply (unfold sel_next_state_def)
  apply (auto split: option.splits)
  done

text \<open> And then infer correctness of the deterministic algorithm \<close>

theorem (in MFSM_ex) pss_correct: 
  assumes D_init: "set D = \<delta> A"
  shows "lang (A\<lparr> \<delta>:=set (pss_algo R D) \<rparr>) = pre_star (rules M) A"
proof (rule correct)
  have "(set D, (R,D))\<in>\<alpha>seln M A" by (intro refl \<alpha>selnI) unfold_locales
  moreover have "((R,D),pss_algo_rec (R,D))\<in>ndet_algo (seln_R)" by (simp add: det_impl.algo_correct)
  ultimately obtain d' where 1: "(d',pss_algo_rec (R,D))\<in>\<alpha>seln M A \<and> (set D,d')\<in>ndet_algo (ps_R M A)" using refines_ndet_algo[OF seln_refines] by blast
  hence "d'=set (snd (pss_algo_rec (R,D)))" by (blast dest: \<alpha>selnD')
  with 1 show "(\<delta> A, set (pss_algo R D)) \<in> ndet_algo (ps_R M A)" using D_init unfolding pss_algo_def by simp
qed
  
corollary (in MFSM) pss_correct:
  assumes repr: "set D = \<delta> A" "(R,rules M)\<in>rules_repr"
  shows "lang (A\<lparr> \<delta>:=set (pss_algo R D) \<rparr>) = pre_star (rules M) A"
proof -
  interpret MFSM_ex "sep M" M A R D
    apply simp_all
    apply unfold_locales
    apply (simp_all add: repr initial_delta_below)
    done
  from repr show ?thesis by (simp add: pss_correct)
qed

text \<open> Generate executable code \<close>

export_code pss_algo checking SML


end
