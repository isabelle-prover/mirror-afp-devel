section \<open>Convergence of Traces\<close>

text \<open>This theory defines convergence of traces in observable FSMs and provides results on
      sufficient conditions to establish that two traces converge.
      Furthermore it is shown how convergence can be employed in proving language equivalence.\<close>


theory Convergence
imports "../Minimisation" "../Distinguishability" "../State_Cover" "HOL-Library.List_Lexorder"
begin

subsection \<open>Basic Definitions\<close>

(* two traces converge if they are both in the language of the FSM and reach the same state *)
fun converge :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list  \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> bool" where
  "converge M \<pi> \<tau> = (\<pi> \<in> L M \<and> \<tau> \<in> L M \<and> (LS M (after_initial M \<pi>) = LS M (after_initial M \<tau>)))"

fun preserves_divergence :: "('a,'b,'c) fsm \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "preserves_divergence M1 M2 A = (\<forall> \<alpha> \<in> L M1 \<inter> A . \<forall> \<beta> \<in> L M1 \<inter> A . \<not> converge M1 \<alpha> \<beta> \<longrightarrow> \<not> converge M2 \<alpha> \<beta>)"

fun preserves_convergence :: "('a,'b,'c) fsm \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "preserves_convergence M1 M2 A = (\<forall> \<alpha> \<in> L M1 \<inter> A . \<forall> \<beta> \<in> L M1 \<inter> A . converge M1 \<alpha> \<beta> \<longrightarrow> converge M2 \<alpha> \<beta>)"

lemma converge_refl :
  assumes "\<alpha> \<in> L M"
shows "converge M \<alpha> \<alpha>"
  using assms by auto

lemma convergence_minimal :
  assumes "minimal M"
  and     "observable M"
  and     "\<alpha> \<in> L M"
  and     "\<beta> \<in> L M"
shows "converge M \<alpha> \<beta> = ((after_initial M \<alpha>) = (after_initial M \<beta>))"
proof 
  have *:"(after_initial M \<alpha>) \<in> states M"
    using \<open>\<alpha> \<in> L M\<close> by (meson after_is_state assms(2)) 
  have **:"(after_initial M \<beta>) \<in> states M"
    using \<open>\<beta> \<in> L M\<close> by (meson after_is_state assms(2)) 

  show "converge M \<alpha> \<beta> \<Longrightarrow> ((after_initial M \<alpha>) = (after_initial M \<beta>))"
    using * ** \<open>minimal M\<close> unfolding minimal.simps converge.simps
    by blast 

  show "((after_initial M \<alpha>) = (after_initial M \<beta>)) \<Longrightarrow> converge M \<alpha> \<beta>"
    unfolding converge.simps using assms(3,4) by simp
qed
  

lemma state_cover_assignment_diverges :
  assumes "observable M"
  and     "minimal M"
  and     "is_state_cover_assignment M f"
  and     "q1 \<in> reachable_states M"
  and     "q2 \<in> reachable_states M"
  and     "q1 \<noteq> q2"
shows "\<not> converge M (f q1) (f q2)"
proof -
  have "f q1 \<in> L M" 
    using assms(3,4)
    by (metis from_FSM_language is_state_cover_assignment.simps language_contains_empty_sequence language_io_target_append language_prefix reachable_state_is_state) 
  moreover have "q1 \<in> io_targets M (f q1) (initial M)"
    using assms(3,4) unfolding is_state_cover_assignment.simps by blast
  ultimately have "(after_initial M (f q1)) = q1"
    using assms(1)
    by (metis (no_types, lifting) observable_after_path observable_path_io_target singletonD) 

  have "f q2 \<in> L M" 
    using assms(3,5)
    by (metis from_FSM_language is_state_cover_assignment.simps language_contains_empty_sequence language_io_target_append language_prefix reachable_state_is_state) 
  moreover have "q2 \<in> io_targets M (f q2) (initial M)"
    using assms(3,5) unfolding is_state_cover_assignment.simps by blast
  ultimately have "(after_initial M (f q2)) = q2"
    using assms(1)
    by (metis (no_types, lifting) observable_after_path observable_path_io_target singletonD) 

  show ?thesis
    using convergence_minimal[OF assms(2,1) \<open>f q1 \<in> L M\<close> \<open>f q2 \<in> L M\<close>] \<open>q1 \<noteq> q2\<close>
    unfolding \<open>(after_initial M (f q1)) = q1\<close> \<open>(after_initial M (f q2)) = q2\<close>
    by simp
qed


lemma converge_extend :
  assumes "observable M"
  and     "converge M \<alpha> \<beta>"
  and     "\<alpha>@\<gamma> \<in> L M" 
  and     "\<beta> \<in> L M"
shows "\<beta>@\<gamma> \<in> L M"
  by (metis after_io_targets assms(1) assms(2) assms(3) assms(4) converge.simps language_io_target_append language_prefix observable_io_targets observable_io_targets_language singletonI the_elem_eq)


lemma converge_append :
  assumes "observable M"
  and     "converge M \<alpha> \<beta>"
  and     "\<alpha>@\<gamma> \<in> L M"
  and     "\<beta> \<in> L M"
shows "converge M (\<alpha>@\<gamma>) (\<beta>@\<gamma>)"
  using after_language_append_iff[OF assms(1,3)]
  using after_language_append_iff[OF assms(1) converge_extend[OF assms]]
  using assms converge_extend
  unfolding converge.simps
  by blast 


lemma non_initialized_state_cover_assignment_diverges :
  assumes "observable M"
  and     "minimal M"
  and     "\<And> q . q \<in> reachable_states M \<Longrightarrow> q \<in> io_targets M (f q) (initial M)"
  and     "\<And> q . q \<in> reachable_states M \<Longrightarrow> f q \<in> L M \<inter>  SC"
  and     "q1 \<in> reachable_states M"
  and     "q2 \<in> reachable_states M"
  and     "q1 \<noteq> q2"
shows "\<not> converge M (f q1) (f q2)"
proof -

  have "f q1 \<in> L M" 
    using assms(4,5) by blast
  moreover have "q1 \<in> io_targets M (f q1) (initial M)"
    using assms(3,5) by blast
  ultimately have "(after_initial M (f q1)) = q1"
    using assms(1)
    by (metis (no_types, lifting) observable_after_path observable_path_io_target singletonD) 

  have "f q2 \<in> L M" 
    using assms(4,6) by blast
  moreover have "q2 \<in> io_targets M (f q2) (initial M)"
    using assms(3,6) by blast
  ultimately have "(after_initial M (f q2)) = q2"
    using assms(1)
    by (metis (no_types, lifting) observable_after_path observable_path_io_target singletonD) 

  show ?thesis
    using convergence_minimal[OF assms(2,1) \<open>f q1 \<in> L M\<close> \<open>f q2 \<in> L M\<close>] \<open>q1 \<noteq> q2\<close>
    unfolding \<open>(after_initial M (f q1)) = q1\<close> \<open>(after_initial M (f q2)) = q2\<close>
    by simp
qed


lemma converge_trans_2 :
  assumes "observable M" and "minimal M" and "converge M u v"
  shows "converge M (u@w1) (u@w2) = converge M (v@w1) (v@w2)"
        "converge M (u@w1) (u@w2) = converge M (u@w1) (v@w2)" 
        "converge M (u@w1) (u@w2) = converge M (v@w1) (u@w2)" 
proof -
  have "converge M (u@w1) (u@w2) = converge M (v@w1) (v@w2) \<and> converge M (u@w1) (u@w2) = converge M (u@w1) (v@w2) \<and> converge M (u@w1) (u@w2) = converge M (v@w1) (u@w2)"
  proof (cases "u@w1 \<in> L M \<and> u@w2 \<in> L M")
    case False
    then consider "u@w1 \<notin> L M" | "u@w2 \<notin> L M"
      by blast
    then have "v@w1 \<notin> L M \<or> v@w2 \<notin> L M"
      using after_language_iff[OF assms(1), of u "initial M" w1]
            after_language_iff[OF assms(1), of u "initial M" w2]
            after_language_iff[OF assms(1), of v "initial M" w1]
            after_language_iff[OF assms(1), of v "initial M" w2]
      by (metis assms(3) converge.elims(2))
    then show ?thesis
      by (meson assms(1) assms(3) converge.elims(2) converge_extend) 
  next
    case True
    then have "u@w1 \<in> L M" and "u@w2 \<in> L M" by auto
    then have "v@w1 \<in> L M" and "v@w2 \<in> L M"
      by (meson assms(1) assms(3) converge.simps converge_extend)+
    
    have "u \<in> L M" using \<open>u@w1 \<in> L M\<close> language_prefix by metis
    have "v \<in> L M" using \<open>v@w1 \<in> L M\<close> language_prefix by metis

    have "after_initial M u = after_initial M v"
      using \<open>u \<in> L M\<close> \<open>v \<in> L M\<close> assms(1) assms(2) assms(3) convergence_minimal by blast
    moreover have "after_initial M (u @ w1) = after_initial M (v @ w1)"
      by (metis calculation True \<open>v @ w1 \<in> L M\<close> after_split assms(1))
    ultimately have "after_initial M (u @ w2) = after_initial M (v @ w2)"
      by (metis (no_types) True \<open>v @ w2 \<in> L M\<close> after_split assms(1))

    have "converge M (u@w1) (u@w2) = converge M (v@w1) (v@w2)"
      using True \<open>after_initial M (u @ w1) = after_initial M (v @ w1)\<close> \<open>after_initial M (u @ w2) = after_initial M (v @ w2)\<close> \<open>v @ w1 \<in> L M\<close> \<open>v @ w2 \<in> L M\<close> 
      by auto
    moreover have "converge M (u@w1) (u@w2) = converge M (u@w1) (v@w2)"
      using True \<open>after_initial M (u @ w2) = after_initial M (v @ w2)\<close> \<open>v @ w2 \<in> L M\<close> by auto
    moreover have "converge M (u@w1) (u@w2) = converge M (v@w1) (u@w2)"
      using True \<open>after_initial M (u @ w1) = after_initial M (v @ w1)\<close> \<open>v @ w1 \<in> L M\<close> by auto 
    ultimately show ?thesis 
      by blast
  qed
  then show "converge M (u@w1) (u@w2) = converge M (v@w1) (v@w2)"
        "converge M (u@w1) (u@w2) = converge M (u@w1) (v@w2)" 
        "converge M (u@w1) (u@w2) = converge M (v@w1) (u@w2)" 
    by blast+
qed


lemma preserves_divergence_converge_insert :
  assumes "observable M1"
      and "observable M2"
      and "minimal M1"
      and "minimal M2"
      and "converge M1 u v"
      and "converge M2 u v"
      and "preserves_divergence M1 M2 X"
      and "u \<in> X"
shows "preserves_divergence M1 M2 (Set.insert v X)"
proof -
  have "\<And> w . w \<in> L M1 \<inter> X \<Longrightarrow> \<not>converge M1 v w \<Longrightarrow> \<not>converge M2 v w"
  proof -
    fix w
    assume "w \<in> L M1 \<inter> X" and "\<not>converge M1 v w" 

    then have "\<not>converge M1 u w"
      using assms(5)
      using converge.simps by blast 
    then have "\<not>converge M2 u w"
      using assms(5-8)
      by (meson IntI \<open>w \<in> L M1 \<inter> X\<close> converge.elims(2) preserves_divergence.simps) 
    then show "\<not>converge M2 v w"
      using assms(6) converge.simps by blast
  qed
  then show ?thesis
    using assms(7)
    unfolding preserves_divergence.simps
    by (metis (no_types, lifting) Int_insert_right_if1 assms(1) assms(2) assms(3) assms(4) assms(5) converge.elims(2) convergence_minimal insert_iff)
qed

lemma preserves_divergence_converge_replace :
  assumes "observable M1"
      and "observable M2"
      and "minimal M1"
      and "minimal M2"
      and "converge M1 u v"
      and "converge M2 u v"
      and "preserves_divergence M1 M2 (Set.insert u X)"
shows "preserves_divergence M1 M2 (Set.insert v X)"
proof -
  have "u \<in> L M1" and "v \<in> L M1"
    using assms(5) by auto
  then have "after_initial M1 u = after_initial M1 v"
    using assms(1) assms(3) assms(5) convergence_minimal by blast
  
  have "\<And> w . w \<in> L M1 \<inter> X \<Longrightarrow> \<not>converge M1 v w \<Longrightarrow> \<not>converge M2 v w"
  proof -
    fix w
    assume "w \<in> L M1 \<inter> X" and "\<not>converge M1 v w" 

    then have "\<not>converge M1 u w"
      using assms(5)
      using converge.simps by blast 
    then have "\<not>converge M2 u w"
      using assms(5-7)
      by (meson IntD1 IntD2 IntI \<open>w \<in> L M1 \<inter> X\<close> converge.elims(2) insertCI preserves_divergence.elims(1)) 
    then show "\<not>converge M2 v w"
      using assms(6) converge.simps by blast
  qed

  have "\<And> \<alpha> \<beta> . \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> insert v X \<Longrightarrow> \<beta> \<in> L M1 \<Longrightarrow> \<beta> \<in> insert v X \<Longrightarrow> \<not> converge M1 \<alpha> \<beta> \<Longrightarrow> \<not> converge M2 \<alpha> \<beta>"
  proof -
    fix \<alpha> \<beta>  assume "\<alpha> \<in> L M1" "\<alpha> \<in> insert v X" "\<beta> \<in> L M1" "\<beta> \<in> insert v X" "\<not> converge M1 \<alpha> \<beta>"

    then consider "\<alpha> = v \<and> \<beta> = v" |
                  "\<alpha> = v \<and> \<beta> \<in> X" |
                  "\<alpha> \<in> X \<and> \<beta> = v" |
                  "\<alpha> \<in> X \<and> \<beta> \<in> X"
      by blast
    then show "\<not> converge M2 \<alpha> \<beta>"
    proof cases
      case 1
      then show ?thesis 
        using \<open>\<alpha> \<in> L M1\<close> \<open>\<beta> \<in> L M1\<close> \<open>\<not> converge M1 \<alpha> \<beta>\<close> by auto
    next
      case 2
      then show ?thesis
        by (metis IntI \<open>\<And>w. \<lbrakk>w \<in> L M1 \<inter> X; \<not> converge M1 v w\<rbrakk> \<Longrightarrow> \<not> converge M2 v w\<close> \<open>\<beta> \<in> L M1\<close> \<open>\<not> converge M1 \<alpha> \<beta>\<close>)
    next
      case 3
      then show ?thesis
        by (metis IntI \<open>\<And>w. \<lbrakk>w \<in> L M1 \<inter> X; \<not> converge M1 v w\<rbrakk> \<Longrightarrow> \<not> converge M2 v w\<close> \<open>\<alpha> \<in> L M1\<close> \<open>\<not> converge M1 \<alpha> \<beta>\<close> converge.simps) 
    next
      case 4
      then show ?thesis 
        using assms(7) unfolding preserves_divergence.simps
        using \<open>\<alpha> \<in> L M1\<close> \<open>\<beta> \<in> L M1\<close> \<open>\<not> converge M1 \<alpha> \<beta>\<close> by blast 
    qed
  qed
  then show ?thesis
    unfolding preserves_divergence.simps by blast
qed

lemma preserves_divergence_converge_replace_iff :
  assumes "observable M1"
      and "observable M2"
      and "minimal M1"
      and "minimal M2"
      and "converge M1 u v"
      and "converge M2 u v"
shows "preserves_divergence M1 M2 (Set.insert u X) = preserves_divergence M1 M2 (Set.insert v X)"
proof -
  have *: "converge M1 v u" using assms(5) by auto
  have **: "converge M2 v u" using assms(6) by auto

  show ?thesis
    using preserves_divergence_converge_replace[OF assms]
          preserves_divergence_converge_replace[OF assms(1-4) * **]
    by blast
qed

lemma preserves_divergence_subset :
  assumes "preserves_divergence M1 M2 B"
  and     "A \<subseteq> B"
shows "preserves_divergence M1 M2 A"
  using assms unfolding preserves_divergence.simps by blast

lemma preserves_divergence_insertI :
  assumes "preserves_divergence M1 M2 X"
  and     "\<And> \<alpha> . \<alpha> \<in> L M1 \<inter> X \<Longrightarrow> \<beta> \<in> L M1 \<Longrightarrow> \<not>converge M1 \<alpha> \<beta> \<Longrightarrow> \<not>converge M2 \<alpha> \<beta>"
shows "preserves_divergence M1 M2 (Set.insert \<beta> X)" 
  using assms unfolding preserves_divergence.simps
  by (metis Int_insert_right converge.elims(2) converge.elims(3) insertE) 

lemma preserves_divergence_insertE :
  assumes "preserves_divergence M1 M2 (Set.insert \<beta> X)"
shows "preserves_divergence M1 M2 X"
and   "\<And> \<alpha> . \<alpha> \<in> L M1 \<inter> X \<Longrightarrow> \<beta> \<in> L M1 \<Longrightarrow> \<not>converge M1 \<alpha> \<beta> \<Longrightarrow> \<not>converge M2 \<alpha> \<beta>"
using assms unfolding preserves_divergence.simps
  by blast+

lemma distinguishes_diverge_prefix :
  assumes "observable M"
  and     "distinguishes M (after_initial M u) (after_initial M v) w"
  and     "u \<in> L M"
  and     "v \<in> L M"
  and     "w' \<in> set (prefixes w)"
  and     "w' \<in> LS M (after_initial M u)"
  and     "w' \<in> LS M (after_initial M v)"
shows "\<not>converge M (u@w') (v@w')"
proof 
  assume "converge M (u @ w') (v @ w')"

  obtain w'' where "w = w'@w''"
    using assms(5)
    using prefixes_set_ob by auto 

  have "u@w' \<in> L M"
    using assms(3,6) after_language_iff[OF assms(1)]
    by blast 
  then have *:"(w \<in> LS M (after_initial M u)) = (w'' \<in> LS M (after_initial M (u@w')))"
    using after_language_append_iff[OF assms(1)]
    unfolding \<open>w = w'@w''\<close>
    by blast

  have "v@w' \<in> L M"
    using assms(4,7) after_language_iff[OF assms(1)]
    by blast 
  then have **:"(w \<in> LS M (after_initial M v)) = (w'' \<in> LS M (after_initial M (v@w')))"
    using after_language_append_iff[OF assms(1)]
    unfolding \<open>w = w'@w''\<close>
    by blast

  have "(w \<in> LS M (after_initial M u)) = (w \<in> LS M (after_initial M v))"
    unfolding * **
    using \<open>converge M (u @ w') (v @ w')\<close>
    by (metis converge.elims(2))
  then show False
    using \<open>distinguishes M (after_initial M u) (after_initial M v) w\<close>
    unfolding distinguishes_def
    by blast
qed

lemma converge_distinguishable_helper :
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and "converge M1 \<pi> \<alpha>"
  and "converge M2 \<pi> \<alpha>"
  and "converge M1 \<tau> \<beta>"
  and "converge M2 \<tau> \<beta>"
  and "distinguishes M2 (after_initial M2 \<pi>) (after_initial M2 \<tau>) v"
  and "L M1 \<inter> {\<alpha>@v,\<beta>@v} = L M2 \<inter> {\<alpha>@v,\<beta>@v}"
shows "(after_initial M1 \<pi>) \<noteq> (after_initial M1 \<tau>)"
proof -
  have "LS M1 (after_initial M1 \<pi>) = LS M1 (after_initial M1 \<alpha>)"
    by (meson assms(5) converge.elims(2)) 
  have "LS M1 (after_initial M1 \<tau>) = LS M1 (after_initial M1 \<beta>)"
    by (meson assms(7) converge.elims(2)) 
  have "LS M2 (after_initial M2 \<pi>) = LS M2 (after_initial M2 \<alpha>)"
    by (meson assms(6) converge.elims(2)) 
  have "LS M2 (after_initial M2 \<tau>) = LS M2 (after_initial M2 \<beta>)"
    by (meson assms(8) converge.elims(2)) 

  have "v \<in> LS M2 (after_initial M2 \<pi>) \<longleftrightarrow> v \<notin> LS M2 (after_initial M2 \<tau>)"
    using assms(9) unfolding distinguishes_def by blast
  then have "v \<in> LS M2 (after_initial M2 \<alpha>) \<longleftrightarrow> v \<notin> LS M2 (after_initial M2 \<beta>)"
    using \<open>LS M2 (after_initial M2 \<pi>) = LS M2 (after_initial M2 \<alpha>)\<close> \<open>LS M2 (after_initial M2 \<tau>) = LS M2 (after_initial M2 \<beta>)\<close> by blast
  then have "\<alpha>@v \<in> L M2 \<longleftrightarrow> \<beta>@v \<notin> L M2"
    by (meson after_language_iff assms(2) assms(6) assms(8) converge.elims(2))
  then have "\<alpha>@v \<in> L M1 \<longleftrightarrow> \<beta>@v \<notin> L M1"
    using assms(10)
    by (metis (no_types, lifting) Int_insert_right inf_sup_ord(1) insert_subset)
  then have "v \<in> LS M1 (after_initial M1 \<alpha>) \<longleftrightarrow> v \<notin> LS M1 (after_initial M1 \<beta>)"
    by (meson after_language_iff assms(1) assms(5) assms(7) converge.elims(2))
  then have "v \<in> LS M1 (after_initial M1 \<pi>) \<longleftrightarrow> v \<notin> LS M1 (after_initial M1 \<tau>)"
    using \<open>LS M1 (after_initial M1 \<pi>) = LS M1 (after_initial M1 \<alpha>)\<close> \<open>LS M1 (after_initial M1 \<tau>) = LS M1 (after_initial M1 \<beta>)\<close> by blast 
  then show ?thesis
    by metis 
qed

lemma converge_append_language_iff :
  assumes "observable M"
  and     "converge M \<alpha> \<beta>"
shows "(\<alpha>@\<gamma> \<in> L M) = (\<beta>@\<gamma> \<in> L M)"
  by (metis (no_types) assms(1) assms(2) converge.simps converge_extend)

lemma converge_append_iff :
  assumes "observable M"
  and     "converge M \<alpha> \<beta>"
shows "converge M \<gamma> (\<alpha>@\<omega>) = converge M \<gamma> (\<beta>@\<omega>)"
proof (cases "(\<alpha>@\<omega>) \<in> L M")
  case True
  then show ?thesis 
    using converge_append_language_iff[OF assms] language_prefix[of \<beta> \<omega> M "initial M"]
    using converge_append[OF assms True] 
    by auto
next                                            
  case False
  then show ?thesis 
    using converge_append_language_iff[OF assms]
    using converge.simps by blast 
qed

lemma after_distinguishes_language :
  assumes "observable M1"
  and     "\<alpha> \<in> L M1"
  and     "\<beta> \<in> L M1"
  and     "distinguishes M1 (after_initial M1 \<alpha>) (after_initial M1 \<beta>) \<gamma>"
shows "(\<alpha>@\<gamma> \<in> L M1) \<noteq> (\<beta>@\<gamma> \<in> L M1)"
  unfolding after_language_iff[OF assms(1,2),symmetric]
            after_language_iff[OF assms(1,3),symmetric]
  using assms(4) 
  unfolding distinguishes_def
  by blast

lemma distinguish_diverge :
  assumes "observable M1"
  and     "observable M2"
  and     "distinguishes M1 (after_initial M1 u) (after_initial M1 v) \<gamma>"
  and     "u @ \<gamma> \<in> T"
  and     "v @ \<gamma> \<in> T"
  and     "u \<in> L M1"
  and     "v \<in> L M1"
  and     "L M1 \<inter> T = L M2 \<inter> T"
shows "\<not> converge M2 u v"
proof 
  assume "converge M2 u v"
  then have "u@\<gamma> \<in> L M2 \<longleftrightarrow> v@\<gamma> \<in> L M2"
    using assms(2) converge_append_language_iff by blast
  moreover have "u@\<gamma> \<in> L M1 \<longleftrightarrow> v@\<gamma> \<notin> L M1"
    using assms(1,3,6,7)
    using after_distinguishes_language 
    by blast 
  ultimately show False
    using assms(4,5,8) by blast
qed



lemma distinguish_converge_diverge :
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1" 
  and     "u' \<in> L M1"
  and     "v' \<in> L M1"
  and     "converge M1 u u'"
  and     "converge M1 v v'"
  and     "converge M2 u u'"
  and     "converge M2 v v'"
  and     "distinguishes M1 (after_initial M1 u) (after_initial M1 v) \<gamma>"
  and     "u' @ \<gamma> \<in> T"
  and     "v' @ \<gamma> \<in> T"
  and     "L M1 \<inter> T = L M2 \<inter> T"
shows "\<not> converge M2 u v"
proof -
  have *:"distinguishes M1 (after_initial M1 u') (after_initial M1 v') \<gamma>"
    by (metis (mono_tags, opaque_lifting) assms(1) assms(10) assms(3) assms(6) assms(7) converge.simps convergence_minimal)

  show ?thesis 
    using distinguish_diverge[OF assms(1-2) *]
    by (metis (mono_tags, lifting) assms(9) assms(11) assms(12) assms(13) assms(4) assms(5) assms(8) converge.simps) 
qed

lemma diverge_prefix :
  assumes "observable M"
  and     "\<alpha>@\<gamma> \<in> L M"
  and     "\<beta>@\<gamma> \<in> L M"
  and     "\<not> converge M (\<alpha>@\<gamma>) (\<beta>@\<gamma>)"
shows "\<not> converge M \<alpha> \<beta>"
  by (meson assms converge_append language_prefix)

lemma converge_sym: "converge M u v = converge M v u"
  by auto

lemma state_cover_transition_converges : 
  assumes "observable M"
  and     "is_state_cover_assignment M V"
  and     "t \<in> transitions M"
  and     "t_source t \<in> reachable_states M"
shows "converge M ((V (t_source t)) @ [(t_input t,t_output t)]) (V (t_target t))"
proof -
  have "t_target t \<in> reachable_states M"
    using assms(3,4) reachable_states_next
    by metis

  have "V (t_source t) \<in> L M" and "after_initial M (V (t_source t)) = (t_source t)" 
    using state_cover_assignment_after[OF assms(1,2,4)]
    by simp+

  have "((V (t_source t)) @ [(t_input t,t_output t)]) \<in> L M"
    using after_language_iff[OF assms(1) \<open>V (t_source t) \<in> L M\<close>, of "[(t_input t,t_output t)]"] 
          assms(3)
    unfolding LS_single_transition \<open>after_initial M (V (t_source t)) = (t_source t)\<close>
    by force

  have "FSM.after M (t_source t) [(t_input t, t_output t)] = t_target t"
    using after_transition[OF assms(1)] assms(3)
    by auto
  then have "after_initial M ((V (t_source t)) @ [(t_input t,t_output t)]) = t_target t"
    using \<open>after_initial M (V (t_source t)) = (t_source t)\<close> 
    using after_split[OF assms(1) \<open>((V (t_source t)) @ [(t_input t,t_output t)]) \<in> L M\<close>]
    by force
  then show ?thesis
    using \<open>((V (t_source t)) @ [(t_input t,t_output t)]) \<in> L M\<close>
    using state_cover_assignment_after[OF assms(1,2) \<open>t_target t \<in> reachable_states M\<close>] 
    by auto
qed

lemma equivalence_preserves_divergence :
  assumes "observable M"
  and     "observable I"
  and     "L M = L I"
shows "preserves_divergence M I A"
proof -
  have "\<And> \<alpha> \<beta> . \<alpha> \<in> L M \<inter> A \<Longrightarrow> \<beta> \<in> L M \<inter> A \<Longrightarrow> \<not> converge M \<alpha> \<beta> \<Longrightarrow> \<not> converge I \<alpha> \<beta>"
  proof -
    fix  \<alpha> \<beta> assume "\<alpha> \<in> L M \<inter> A" and "\<beta> \<in> L M \<inter> A" and "\<not> converge M \<alpha> \<beta>"
    then have "after_initial M \<alpha> \<in> states M" and "after_initial M \<beta> \<in> states M" and "LS M (after_initial M \<alpha>) \<noteq> LS M (after_initial M \<beta>)"
      using after_is_state[OF assms(1)]  unfolding converge.simps
      by auto
    then obtain \<gamma> where "(\<gamma> \<in> LS M (after_initial M \<alpha>)) \<noteq> (\<gamma> \<in> LS M (after_initial M \<beta>))"
      by blast
    then have "(\<alpha>@\<gamma> \<in> L M) \<noteq> (\<beta>@\<gamma> \<in> L M)"
      using after_language_iff[OF assms(1)] \<open>\<alpha> \<in> L M \<inter> A\<close> \<open>\<beta> \<in> L M \<inter> A\<close> by blast
    then have "(\<alpha>@\<gamma> \<in> L I) \<noteq> (\<beta>@\<gamma> \<in> L I)"
      using assms(3) by blast
    then show "\<not> converge I \<alpha> \<beta>"
      using assms(2) converge_append_language_iff by blast
  qed
  then show ?thesis
    unfolding preserves_divergence.simps by blast
qed

subsection \<open>Sufficient Conditions for Convergence\<close>


text \<open>The following lemma provides a condition for convergence that assumes the existence
      of a single state cover covering all extensions of length up to (m - |M1|).
      This is too restrictive for the SPYH method but could be used in the SPY method.
      The proof idea has been developed by Wen-ling Huang and adapted by the author to
      avoid requiring the SC to cover traces that contain a proper prefix already not
      in the language of FSM M1.\<close>
lemma sufficient_condition_for_convergence_in_SPY_method :
  fixes M1 :: "('a,'b,'c) fsm"
  fixes M2 :: "('d,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "L M1 \<inter> T = L M2 \<inter> T"
  and     "\<pi> \<in> L M1 \<inter> T"
  and     "\<tau> \<in> L M1 \<inter> T"
  and     "converge M1 \<pi> \<tau>"
  and     "SC \<subseteq> T"
  and     "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> \<exists> io \<in> L M1 \<inter> SC . q \<in> io_targets M1 io (initial M1)"
  and     "preserves_divergence M1 M2 SC"
  and     "\<And> \<gamma> x y . length \<gamma> < m - size_r M1 \<Longrightarrow>
                     \<gamma> \<in> LS M1 (after_initial M1 \<pi>) \<Longrightarrow>
                     x \<in> inputs M1 \<Longrightarrow>
                     y \<in> outputs M1 \<Longrightarrow>
                     \<exists> \<alpha> \<beta> . converge M1 \<alpha> (\<pi>@\<gamma>) \<and> 
                             converge M2 \<alpha> (\<pi>@\<gamma>) \<and>
                             converge M1 \<beta> (\<tau>@\<gamma>) \<and>
                             converge M2 \<beta> (\<tau>@\<gamma>) \<and>
                             \<alpha> \<in> SC \<and>
                             \<alpha>@[(x,y)] \<in> SC \<and>
                             \<beta> \<in> SC \<and>
                             \<beta>@[(x,y)] \<in> SC"   
  and     "\<exists> \<alpha> \<beta> . converge M1 \<alpha> \<pi> \<and> 
                   converge M2 \<alpha> \<pi> \<and>
                   converge M1 \<beta> \<tau> \<and>
                   converge M2 \<beta> \<tau> \<and>
                   \<alpha> \<in> SC \<and>
                   \<beta> \<in> SC" 
  and    "inputs M2 = inputs M1"
  and    "outputs M2 = outputs M1"
shows "converge M2 \<pi> \<tau>"
proof -

  obtain f where f1: "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> q \<in> io_targets M1 (f q) (initial M1)"
             and f2: "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> f q \<in> L M1 \<inter> SC"
    using non_initialized_state_cover_assignment_from_non_initialized_state_cover[OF \<open>\<And> q . q \<in> reachable_states M1 \<Longrightarrow> \<exists> io \<in> L M1 \<inter> SC . q \<in> io_targets M1 io (initial M1)\<close>]
    by blast

  define A where A: "A = (\<lambda> q . Set.filter (converge M1 (f q)) (L M1 \<inter> SC))"

  define Q where Q: "Q = (\<lambda> q . \<Union> \<alpha> \<in> A q . io_targets M2 \<alpha> (initial M2))"

  have "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> Q q \<noteq> {}"
  proof -
    fix q assume "q \<in> reachable_states M1"
    then have "f q \<in> A q"
      using A
      using f2 by auto
    moreover have "f q \<in> L M2"
    proof -
      have "f q \<in> L M1 \<inter> SC"
        using \<open>q \<in> reachable_states M1\<close> f2 by blast 
      then show ?thesis
        using \<open>SC \<subseteq> T\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> by blast
    qed
    ultimately show "Q q \<noteq> {}"
      unfolding Q
      by auto 
  qed

  have "states M2 = (\<Union> q \<in> reachable_states M1 . Q q) \<union> (states M2 - (\<Union> q \<in> reachable_states M1 . Q q))"
  proof -
    have "(\<Union> q \<in> reachable_states M1 . Q q) \<subseteq> reachable_states M2"
    proof 
      fix q assume "q \<in> (\<Union> q \<in> reachable_states M1 . Q q)"
      then obtain \<alpha> where "q \<in> io_targets M2 \<alpha> (initial M2)" 
        unfolding Q by blast
      then show "q \<in> reachable_states M2"
        unfolding io_targets.simps reachable_states_def by blast
    qed
    then show ?thesis
      by (metis Diff_partition reachable_state_is_state subset_iff)
  qed

  have "\<And> q1 q2 . q1 \<in> reachable_states M1 \<Longrightarrow> q2 \<in> reachable_states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> Q q1 \<inter> Q q2 = {}"
  proof -
    fix q1 q2
    assume "q1 \<in> reachable_states M1" and "q2 \<in> reachable_states M1" and "q1 \<noteq> q2"

    have "\<And> \<alpha> \<beta> . \<alpha> \<in> A q1 \<Longrightarrow> \<beta> \<in> A q2 \<Longrightarrow> io_targets M2 \<alpha> (initial M2) \<inter> io_targets M2 \<beta> (initial M2) = {}"
    proof -
      fix \<alpha> \<beta> assume "\<alpha> \<in> A q1" and "\<beta> \<in> A q2"

      then have "converge M1 (f q1) \<alpha>" and "converge M1 (f q2) \<beta>"
        unfolding A
        by (meson member_filter)+
      moreover have "\<not> converge M1 (f q1) (f q2)"  
        using non_initialized_state_cover_assignment_diverges[OF assms(1,3) f1 f2 \<open>q1 \<in> reachable_states M1\<close> \<open>q2 \<in> reachable_states M1\<close> \<open>q1 \<noteq> q2\<close>] .
      ultimately have "\<not> converge M1 \<alpha> \<beta>"
        unfolding converge.simps by blast
      moreover have "\<alpha>\<in>L M1 \<inter> SC"
        using \<open>\<alpha> \<in> A q1\<close> unfolding A
        by (meson member_filter)
      moreover have "\<beta>\<in>L M1 \<inter> SC"
        using \<open>\<beta> \<in> A q2\<close> unfolding A
        by (meson member_filter)
      ultimately have "\<not> converge M2 \<alpha> \<beta>"
        using \<open>preserves_divergence M1 M2 SC\<close>
        unfolding preserves_divergence.simps 
        by blast

      have "\<alpha> \<in> L M2" and "\<beta> \<in> L M2"
        using \<open>\<alpha>\<in>L M1 \<inter> SC\<close> \<open>\<beta>\<in>L M1 \<inter> SC\<close> \<open>SC \<subseteq> T\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> by blast+
      
      have "io_targets M2 \<alpha> (initial M2) = {after_initial M2 \<alpha>}"
        using observable_io_targets[OF \<open>observable M2\<close> \<open>\<alpha> \<in> L M2\<close>]
        unfolding after_io_targets[OF \<open>observable M2\<close> \<open>\<alpha> \<in> L M2\<close>]
        by (metis the_elem_eq)  
      moreover have "io_targets M2 \<beta> (initial M2) = {after_initial M2 \<beta>}"
        using observable_io_targets[OF \<open>observable M2\<close> \<open>\<beta> \<in> L M2\<close>]
        unfolding after_io_targets[OF \<open>observable M2\<close> \<open>\<beta> \<in> L M2\<close>]
        by (metis the_elem_eq)  
      ultimately show "io_targets M2 \<alpha> (initial M2) \<inter> io_targets M2 \<beta> (initial M2) = {}"
        using \<open>\<not> converge M2 \<alpha> \<beta>\<close> unfolding convergence_minimal[OF assms(4,2) \<open>\<alpha> \<in> L M2\<close> \<open>\<beta> \<in> L M2\<close>]
        by (metis Int_insert_right_if0 inf_bot_right singletonD)
    qed

    then show "Q q1 \<inter> Q q2 = {}"
      unfolding Q by blast
  qed
  then have "\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')"
    unfolding Uniq_def
    by blast 


  (* we can partition states of M2 via the Q-classes they belong to (using a single separate class for
     all states not contained in any Q-class *)
  define partition where partition: "partition = (\<lambda> q . if \<exists> q' \<in> reachable_states M1 . q \<in> Q q' 
                                                        then Q (THE q' . q' \<in> reachable_states M1 \<and> q \<in> Q q')
                                                        else (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)))"
                    
  have is_eq: "equivalence_relation_on_states M2 partition"    
  proof-
    let ?r = "{(q1,q2) | q1 q2 . q1 \<in> states M2 \<and> q2 \<in> partition q1}"

    have "\<And> q .partition q \<subseteq> states M2" 
    proof -
      fix q show "partition q \<subseteq> states M2"
      proof (cases "\<exists> q' \<in> reachable_states M1 . q \<in> Q q'")
        case True
        then have "partition q = Q (THE q' . q' \<in> reachable_states M1 \<and> q \<in> Q q')"
          unfolding partition by simp
        then show ?thesis 
          using True \<open>\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')\<close>
          by (metis (no_types, lifting) Q SUP_least io_targets_states) 
      next
        case False
        then show ?thesis unfolding partition
          by auto 
      qed
    qed

    have "\<And> q . q \<in> states M2 \<Longrightarrow> q \<in> partition q"
    proof -
      fix q assume "q \<in> states M2"
      show "q \<in> partition q"
      proof (cases "\<exists> q' \<in> reachable_states M1 . q \<in> Q q'")
        case True
        then have "partition q = Q (THE q' . q' \<in> reachable_states M1 \<and> q \<in> Q q')"
          unfolding partition by simp
        then show ?thesis 
          using True \<open>\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')\<close>
          using the1_equality' by fastforce
      next 
        case False
        then show ?thesis unfolding partition
          using \<open>q \<in> states M2\<close>
          by simp 
      qed
    qed

    have "\<And> q q' . q \<in> states M2 \<Longrightarrow> q' \<in> partition q \<Longrightarrow> q \<in> partition q'" 
    proof -
      fix q q' assume "q \<in> states M2" and "q' \<in> partition q"
      show "q \<in> partition q'"
      proof (cases "\<exists> q' \<in> reachable_states M1 . q \<in> Q q'")
        case True
        then have "partition q = Q (THE q' . q' \<in> reachable_states M1 \<and> q \<in> Q q')"
          unfolding partition by simp
        then obtain q1 where "partition q = Q q1" and "q1 \<in> reachable_states M1" and "q \<in> Q q1"
          using True \<open>\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')\<close>
          using the1_equality' by fastforce 
        then have "q' \<in> Q q1"
          using \<open>q' \<in> partition q\<close> by auto
        then have "partition q' = Q q1"
          using \<open>q1 \<in> reachable_states M1\<close> 
          using the1_equality'[OF \<open>\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')\<close>] 
          unfolding partition
          by auto 
        then show ?thesis 
          using \<open>q \<in> Q q1\<close> \<open>q' \<in> partition q\<close> \<open>partition q = Q q1\<close> by blast
      next
        case False
        then show ?thesis 
          using \<open>q \<in> states M2\<close> \<open>q' \<in> partition q\<close>
          by (simp add: partition) 
      qed
    qed    


    have "\<And> q q' q'' . q \<in> states M2 \<Longrightarrow> q' \<in> partition q \<Longrightarrow> q'' \<in> partition q' \<Longrightarrow> q'' \<in> partition q" 
    proof -
      fix q q' q'' 
      assume "q \<in> states M2" and "q' \<in> partition q" and "q'' \<in> partition q'"
      show "q'' \<in> partition q"
      proof (cases "\<exists> q' \<in> reachable_states M1 . q \<in> Q q'")
        case True
        then have "partition q = Q (THE q' . q' \<in> reachable_states M1 \<and> q \<in> Q q')"
          unfolding partition by simp 
        then obtain q1 where "partition q = Q q1" and "q1 \<in> reachable_states M1" and "q \<in> Q q1"
          using True \<open>\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')\<close>
          using the1_equality' by fastforce 
        then have "q' \<in> Q q1"
          using \<open>q' \<in> partition q\<close> by auto
        then have "partition q' = Q q1"
          using \<open>q1 \<in> reachable_states M1\<close> 
          using the1_equality'[OF \<open>\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')\<close>] 
          unfolding partition
          by auto 
        then have "q'' \<in> Q q1"
          using \<open>q'' \<in> partition q'\<close> by auto
        then have "partition q'' = Q q1"
          using \<open>q1 \<in> reachable_states M1\<close> 
          using the1_equality'[OF \<open>\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')\<close>] 
          unfolding partition
          by auto 
        then show ?thesis
          unfolding \<open>partition q = Q q1\<close> 
          using \<open>q'' \<in> Q q1\<close> by blast 
      next
        case False
        then show ?thesis 
          using \<open>q \<in> states M2\<close> \<open>q' \<in> partition q\<close> \<open>q'' \<in> partition q'\<close> 
          by (simp add: partition) 
      qed
    qed



    have "refl_on (states M2) ?r" unfolding refl_on_def
    proof 
      show "{(q1, q2) |q1 q2. q1 \<in> FSM.states M2 \<and> q2 \<in> partition q1} \<subseteq> FSM.states M2 \<times> FSM.states M2"
        using \<open>\<And> q .partition q \<subseteq> states M2\<close> by blast
      show "\<forall>x\<in>FSM.states M2. (x, x) \<in> {(q1, q2) |q1 q2. q1 \<in> FSM.states M2 \<and> q2 \<in> partition q1}"
      proof
        fix q assume "q \<in> states M2"
        then show "(q,q) \<in> {(q1, q2) |q1 q2. q1 \<in> FSM.states M2 \<and> q2 \<in> partition q1}"
          using \<open>\<And> q . q \<in> states M2 \<Longrightarrow> q \<in> partition q\<close> 
          by blast
      qed
    qed
    moreover have "sym ?r" 
      unfolding sym_def 
      using \<open>\<And> q q' . q \<in> states M2 \<Longrightarrow> q' \<in> partition q \<Longrightarrow> q \<in> partition q'\<close>  \<open>\<And> q .partition q \<subseteq> states M2\<close> 
      by blast
    moreover have "trans ?r"
      unfolding trans_def 
      using \<open>\<And> q q' q'' . q \<in> states M2 \<Longrightarrow> q' \<in> partition q \<Longrightarrow> q'' \<in> partition q' \<Longrightarrow> q'' \<in> partition q\<close>
      by blast 
    ultimately show ?thesis
      unfolding equivalence_relation_on_states_def equiv_def 
      using \<open>\<And> q .partition q \<subseteq> states M2\<close> by blast
  qed


  (* the partitioning results in at most n+1 classes *)
  define n0 where n0: "n0 = card (partition ` states M2)"
  have "n0 \<le> Suc (size_r M1)" and "n0 \<ge> size_r M1"
  proof -
    have "partition ` states M2 \<subseteq> insert (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)) (Q ` reachable_states M1)"
    proof 
      fix X assume "X \<in> partition ` states M2"
      then obtain q where "q \<in> states M2" and "X = partition q"
        by blast
      
      show "X \<in> insert (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)) (Q ` reachable_states M1)"
      proof (cases "\<exists>q'\<in>reachable_states M1. q \<in> Q q'")
        case True
        then show ?thesis 
          unfolding \<open>X = partition q\<close>  partition 
          using the1_equality'[OF \<open>\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')\<close>]
          by auto 
      next
        case False
        then show ?thesis 
          unfolding \<open>X = partition q\<close>  partition 
          by auto
      qed 
    qed
    moreover have "card (insert (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)) (Q ` reachable_states M1)) \<le> Suc (size_r M1)" 
             and  "finite (insert (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)) (Q ` reachable_states M1))"
             and  "card (insert (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)) (Q ` reachable_states M1)) \<ge> size_r M1"
    proof -
      have "finite (Q ` reachable_states M1)"
        using fsm_states_finite[of M1]
        by (metis finite_imageI fsm_states_finite restrict_to_reachable_states_simps(2)) 
      moreover have "card (Q ` reachable_states M1) = size_r M1"
      proof -
        have "card (Q ` reachable_states M1) \<le> size_r M1"
          by (metis card_image_le fsm_states_finite restrict_to_reachable_states_simps(2))
        moreover have "card (Q ` reachable_states M1) \<ge> size_r M1"
          using \<open>finite (Q ` reachable_states M1)\<close>
          by (metis (full_types) \<open>\<And>q. q \<in> reachable_states M1 \<Longrightarrow> Q q \<noteq> {}\<close> \<open>\<And>q2 q1. \<lbrakk>q1 \<in> reachable_states M1; q2 \<in> reachable_states M1; q1 \<noteq> q2\<rbrakk> \<Longrightarrow> Q q1 \<inter> Q q2 = {}\<close> calculation card_eq_0_iff card_union_of_distinct le_0_eq)
        ultimately show ?thesis
          by simp
      qed
      ultimately show "card (insert (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)) (Q ` reachable_states M1)) \<le> Suc (size_r M1)"
                  and "card (insert (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)) (Q ` reachable_states M1)) \<ge> size_r M1"
        by (simp add: card_insert_if)+
      show "finite (insert (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)) (Q ` reachable_states M1))"
        using \<open>finite (Q ` reachable_states M1)\<close>
        by blast 
    qed
    ultimately show "n0 \<le> Suc (size_r M1)" unfolding n0 
      by (meson card_mono le_trans)


    have "(Q ` reachable_states M1) \<subseteq> partition ` states M2"
    proof 
      fix x assume "x \<in> (Q ` reachable_states M1)"
      then obtain q' where "q' \<in> reachable_states M1" and "x = Q q'"
        by blast
      then obtain q where "q \<in> Q q'"
        using \<open>\<And> q . q \<in> reachable_states M1 \<Longrightarrow> Q q \<noteq> {}\<close> by blast
      then obtain \<alpha> where "\<alpha> \<in> A q'" and "q \<in> io_targets M2 \<alpha> (initial M2)"
        unfolding Q by blast
      then have "q \<in> states M2"
        by (meson io_targets_states subset_iff) 
      
      have "\<exists>q'\<in>reachable_states M1. q \<in> Q q'"
        using \<open>q' \<in> reachable_states M1\<close> \<open>q \<in> Q q'\<close> by blast
      then have "partition q = Q q'"
        unfolding partition
        using the1_equality'[OF \<open>\<And> q . Uniq (\<lambda>q' .  q' \<in> reachable_states M1 \<and> q \<in> Q q')\<close>, of q' q] \<open>q \<in> Q q'\<close> \<open>q' \<in> reachable_states M1\<close> 
        by auto
      then show "x \<in> partition ` states M2" 
        using \<open>q \<in> states M2\<close> \<open>x = Q q'\<close>
        by blast 
    qed
    then show "n0 \<ge> size_r M1"
      unfolding n0
      using \<open>finite (insert (states M2 - (\<Union> q \<in> reachable_states M1 . Q q)) (Q ` reachable_states M1))\<close>
      by (metis (full_types) \<open>\<And>q. q \<in> reachable_states M1 \<Longrightarrow> Q q \<noteq> {}\<close> \<open>\<And>q2 q1. \<lbrakk>q1 \<in> reachable_states M1; q2 \<in> reachable_states M1; q1 \<noteq> q2\<rbrakk> \<Longrightarrow> Q q1 \<inter> Q q2 = {}\<close> \<open>partition ` FSM.states M2 \<subseteq> insert (FSM.states M2 - \<Union> (Q ` reachable_states M1)) (Q ` reachable_states M1)\<close> card_mono card_union_of_distinct finite_subset fsm_states_finite restrict_to_reachable_states_simps(2)) 
  qed
      

  moreover have "after_initial M2 \<tau> \<in> ofsm_table M2 partition (m - size_r M1) (after_initial M2 \<pi>)"
  proof -

    define q1 where q1: "q1 = (after_initial M2 \<pi>)"
    define q2 where q2: "q2 = (after_initial M2 \<tau>)"

    have "\<pi> \<in> L M2" and "\<tau> \<in> L M2"
      using assms(7,8,9) by blast+

    have "q1 \<in> states M2"
      using \<open>\<pi> \<in> L M2\<close> after_is_state[OF \<open>observable M2\<close>] unfolding q1 by blast
    have "q2 \<in> states M2"
      using \<open>\<tau> \<in> L M2\<close> after_is_state[OF \<open>observable M2\<close>] unfolding q2 by blast


    moreover have "\<And> \<gamma> . length \<gamma> \<le> m - size_r M1 \<Longrightarrow> (\<gamma> \<in> LS M2 q1) = (\<gamma> \<in> LS M2 q2) \<and> (\<gamma> \<in> LS M2 q1 \<longrightarrow> after M2 q2 \<gamma> \<in> partition (after M2 q1 \<gamma>))"
    proof -
      fix \<gamma> :: "('b\<times>'c) list" 
      assume "length \<gamma> \<le> m - size_r M1"

      then show "((\<gamma> \<in> LS M2 q1) = (\<gamma> \<in> LS M2 q2)) \<and> (\<gamma> \<in> LS M2 q1 \<longrightarrow> after M2 q2 \<gamma> \<in> partition (after M2 q1 \<gamma>))"
      proof (induction \<gamma> rule: rev_induct)
        case Nil

        show ?case
        proof

          have "([] \<in> LS M2 q1)" and "([] \<in> LS M2 q2)"
            using \<open>q1 \<in> states M2\<close> \<open>q2 \<in> states M2\<close>
            by auto
          then have "after M2 q1 [] = q1" and "after M2 q2 [] = q2"
            unfolding Nil 
            by auto
  
  
          obtain \<alpha> \<beta> where "converge M1 \<alpha> \<pi>"
                            "converge M2 \<alpha> \<pi>" 
                            "converge M1 \<beta> \<tau>"
                            "converge M2 \<beta> \<tau>"
                            "\<alpha> \<in> SC" 
                            "\<beta> \<in> SC"
            using assms(15) by blast
          then have "\<alpha> \<in> L M1" and "\<beta> \<in> L M1"
            by auto

          have "\<alpha> \<in> L M2"
            using \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> by blast
          have "\<beta> \<in> L M2"
            using \<open>\<beta> \<in> L M1\<close> \<open>\<beta> \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> by blast
    
          have "([] \<in> LS M2 q1) = ([] \<in> LS M2 (after_initial M2 \<alpha>))"
            using \<open>converge M2 \<alpha> \<pi>\<close> unfolding q1 converge.simps by simp
          also have "\<dots> = ([] \<in> LS M1 (after_initial M1 \<alpha>))"
            using \<open>\<alpha> \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> 
            unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<alpha> \<in> L M1\<close>]
            unfolding after_language_iff[OF \<open>observable M2\<close> \<open>\<alpha> \<in> L M2\<close>]
            unfolding Nil 
            by auto
          also have "\<dots> = ([] \<in> LS M1 (after_initial M1 \<beta>))"
            using \<open>converge M1 \<pi> \<tau>\<close> \<open>converge M1 \<alpha> \<pi>\<close> \<open>converge M1 \<beta> \<tau>\<close> 
            unfolding converge.simps by blast
          also have "\<dots> = ([] \<in> LS M2 (after_initial M2 \<beta>))"
            using \<open>\<beta> \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> 
            unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<beta> \<in> L M1\<close>]
            unfolding after_language_iff[OF \<open>observable M2\<close> \<open>\<beta> \<in> L M2\<close>]
            unfolding Nil
            by auto
          also have "\<dots> = ([] \<in> LS M2 q2)"
            using \<open>converge M2 \<beta> \<tau>\<close> unfolding q2 converge.simps by simp 
          finally show "([] \<in> LS M2 q1) = ([] \<in> LS M2 q2)" .
    
          show "([] \<in> LS M2 q1 \<longrightarrow> after M2 q2 [] \<in> partition (after M2 q1 []))"
          proof 
            assume "[] \<in> LS M2 q1"
            then have "[] \<in> LS M1 (after_initial M1 \<alpha>)"
                  and "[] \<in> LS M1 (after_initial M1 \<beta>)"
              unfolding \<open>([] \<in> LS M2 q1) = ([] \<in> LS M2 (after_initial M2 \<alpha>))\<close>  
                        \<open>([] \<in> LS M2 (after M2 (FSM.initial M2) \<alpha>)) = ([] \<in> LS M1 (after M1 (FSM.initial M1) \<alpha>))\<close>
                        \<open>([] \<in> LS M1 (after M1 (FSM.initial M1) \<alpha>)) = ([] \<in> LS M1 (after M1 (FSM.initial M1) \<beta>))\<close> 
              by simp+
    
            have "\<alpha>@[] \<in> L M1"
              using \<open>[] \<in> LS M1 (after_initial M1 \<alpha>)\<close> unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<alpha> \<in> L M1\<close>] .
            moreover have "\<beta>@[] \<in> L M1"
              using \<open>[] \<in> LS M1 (after_initial M1 \<beta>)\<close> unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<beta> \<in> L M1\<close>] .
            moreover have "converge M1 \<alpha> \<beta>"
              using \<open>converge M1 \<pi> \<tau>\<close> \<open>converge M1 \<alpha> \<pi>\<close> \<open>converge M1 \<beta> \<tau>\<close> 
              unfolding converge.simps by blast
            ultimately have "converge M1 (\<alpha>@[]) (\<beta>@[])"
              using converge_append[OF \<open>observable M1\<close>] language_prefix[of \<beta> "[]" M1 "initial M1"] by blast
    
            have "(\<alpha> @ []) \<in> L M2" and "(\<beta> @ []) \<in> L M2"
              using \<open>\<alpha>@[] \<in> L M1\<close> \<open>\<alpha> \<in> SC\<close> \<open>\<beta>@[] \<in> L M1\<close> \<open>\<beta> \<in> SC \<close>\<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> by auto
            have "after_initial M1 (\<alpha>@[]) \<in> reachable_states M1"
              using observable_after_path[OF \<open>observable M1\<close> ]
              unfolding reachable_states_def
            proof -
              have "\<exists>ps. after M1 (FSM.initial M1) \<alpha> = target (FSM.initial M1) ps \<and> path M1 (FSM.initial M1) ps"
                by (metis (no_types) \<open>\<And>thesis q io. \<lbrakk>io \<in> LS M1 q; \<And>p. \<lbrakk>path M1 q p; p_io p = io; target q p = after M1 q io\<rbrakk> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close> \<open>\<alpha> \<in> L M1\<close>)
              then show "after M1 (FSM.initial M1) (\<alpha> @ []) \<in> {target (FSM.initial M1) ps |ps. path M1 (FSM.initial M1) ps}"
                by auto
            qed 
            have "(\<alpha>@[]) \<in> A (after_initial M1 (\<alpha>@[]))"
              unfolding A 
              using convergence_minimal[OF assms(3,1) _ \<open>\<alpha>@[] \<in> L M1\<close>, of "f (after_initial M1 (\<alpha>@[]))"] 
              using f2[OF \<open>after_initial M1 (\<alpha>@[]) \<in> reachable_states M1\<close>]
              using \<open>\<alpha> \<in> SC\<close>
              unfolding Nil
              by (metis (no_types, lifting) Int_iff \<open>\<alpha> \<in> L M1\<close> \<open>after M1 (FSM.initial M1) (\<alpha> @ []) \<in> reachable_states M1\<close> append_Nil2 assms(1) f1 member_filter observable_after_path observable_path_io_target singletonD)
            then have "after M2 (FSM.initial M2) (\<alpha> @ []) \<in> Q (after_initial M1 (\<alpha>@[]))"
              unfolding Q 
              using observable_io_targets[OF \<open>observable M2\<close> \<open>(\<alpha> @ []) \<in> L M2\<close>]
              unfolding after_io_targets[OF \<open>observable M2\<close> \<open>(\<alpha> @ []) \<in> L M2\<close>]
              by (metis UN_iff insertCI the_elem_eq)
            then have "\<exists>q'\<in>reachable_states M1. after M2 (FSM.initial M2) (\<alpha> @ []) \<in> Q q'"
              using \<open>after_initial M1 (\<alpha>@[]) \<in> reachable_states M1\<close> by blast
            moreover have "(THE q'. q' \<in> reachable_states M1 \<and> after M2 (FSM.initial M2) (\<alpha> @ []) \<in> Q q') = (after_initial M1 (\<alpha>@[]))"
              using \<open>after_initial M1 (\<alpha>@[]) \<in> reachable_states M1\<close>
              using \<open>after M2 (FSM.initial M2) (\<alpha> @ []) \<in> Q (after_initial M1 (\<alpha>@[]))\<close>
              by (simp add: \<open>\<And>q. \<exists>\<^sub>\<le>\<^sub>1 q'. q' \<in> reachable_states M1 \<and> q \<in> Q q'\<close> the1_equality')
            moreover have "after M2 (FSM.initial M2) (\<beta> @ []) \<in> Q (after_initial M1 (\<alpha>@[]))"
            proof -
              have "(\<beta>@[]) \<in> A (after_initial M1 (\<alpha>@[]))"
                using A \<open>\<alpha> @ [] \<in> A (after M1 (FSM.initial M1) (\<alpha> @ []))\<close> \<open>\<beta> @ [] \<in> L M1\<close> \<open>\<beta> \<in> SC\<close> \<open>converge M1 (\<alpha> @ []) (\<beta> @ [])\<close> unfolding Nil by auto
              then show ?thesis
                unfolding Q 
                using observable_io_targets[OF \<open>observable M2\<close> \<open>(\<beta> @ []) \<in> L M2\<close>]
                unfolding after_io_targets[OF \<open>observable M2\<close> \<open>(\<beta> @ []) \<in> L M2\<close>]
                by (metis UN_iff insertCI the_elem_eq)
            qed
            ultimately have "after_initial M2 (\<beta>@[]) \<in> partition (after_initial M2 (\<alpha>@[]))"
              unfolding partition
              by presburger 
            moreover have "after_initial M2 (\<alpha>@[]) = after_initial M2 (\<pi>@[])"
              using converge_append[OF assms(2) \<open>converge M2 \<alpha> \<pi>\<close> \<open>(\<alpha> @ []) \<in> L M2\<close> \<open>\<pi> \<in> L M2\<close>]
              unfolding convergence_minimal[OF assms(4,2) \<open>(\<alpha> @ []) \<in> L M2\<close> converge_extend[OF assms(2) \<open>converge M2 \<alpha> \<pi>\<close> \<open>(\<alpha> @ []) \<in> L M2\<close> \<open>\<pi> \<in> L M2\<close>]]
              .
            moreover have "after_initial M2 (\<beta>@[]) = after_initial M2 (\<tau>@[])"
              using converge_append[OF assms(2) \<open>converge M2 \<beta> \<tau>\<close> \<open>(\<beta> @ []) \<in> L M2\<close> \<open>\<tau> \<in> L M2\<close>]
              unfolding convergence_minimal[OF assms(4,2) \<open>(\<beta> @ []) \<in> L M2\<close> converge_extend[OF assms(2) \<open>converge M2 \<beta> \<tau>\<close> \<open>(\<beta> @ []) \<in> L M2\<close> \<open>\<tau> \<in> L M2\<close>]]
              .
            ultimately show "after M2 q2 [] \<in> partition (after M2 q1 [])"
              unfolding q1 q2 
              unfolding after_split[OF assms(2) converge_extend[OF assms(2) \<open>converge M2 \<alpha> \<pi>\<close> \<open>(\<alpha> @ []) \<in> L M2\<close> \<open>\<pi> \<in> L M2\<close>]]
              unfolding after_split[OF assms(2) converge_extend[OF assms(2) \<open>converge M2 \<beta> \<tau>\<close> \<open>(\<beta> @ []) \<in> L M2\<close> \<open>\<tau> \<in> L M2\<close>]]
              by simp
          qed
        qed
      next
        case (snoc xy \<gamma>)

        obtain x y where "xy = (x,y)"
          by fastforce

        show ?case proof (cases "\<forall> x' y' . (x',y') \<in> set (\<gamma>@[(x,y)]) \<longrightarrow> x' \<in> inputs M1 \<and> y' \<in> outputs M1")
          case False

          have "\<gamma>@[(x,y)] \<notin> LS M2 q1" and "\<gamma>@[(x,y)] \<notin> LS M2 q2"
            using language_io[of "\<gamma>@[(x,y)]" M2 _ ] False 
            unfolding \<open>inputs M2 = inputs M1\<close> \<open>outputs M2 = outputs M1\<close> 
            by blast+
          then show ?thesis 
            unfolding \<open>xy = (x,y)\<close> 
            by blast
        next
          case True

          define s1 where s1: "s1 = (after_initial M1 \<pi>)"
          define s2 where s2: "s2 = (after_initial M1 \<tau>)"

          have "s1 \<in> states M1"
            using \<open>\<pi> \<in> L M1 \<inter> T\<close> after_is_state[OF \<open>observable M1\<close>] unfolding s1 by blast
          have "s2 \<in> states M1"
            using \<open>\<tau> \<in> L M1 \<inter> T\<close> after_is_state[OF \<open>observable M1\<close>] unfolding s2 by blast

          show ?thesis proof (cases "\<gamma> \<in> LS M1 s1")
            case False  (* if \<gamma> is not contained in the language of s1, then by application
                           of the SC it is also not contained in the languages of q1 or q2 *)

            obtain io' x' y' io'' where "\<gamma> = io' @ [(x', y')] @ io''" 
                                  and "io' \<in> LS M1 s1" 
                                  and "io' @ [(x', y')] \<notin> LS M1 s1"
              using language_maximal_contained_prefix_ob[OF False \<open>s1 \<in> states M1\<close> \<open>observable M1\<close>]
              by blast


            have *: "length io' < m - size_r M1"
              using \<open>length (\<gamma> @ [xy]) \<le> m - size_r M1\<close>
              unfolding \<open>\<gamma> = io' @ [(x', y')] @ io''\<close>
              by auto
            have **: "io' \<in> LS M1 (after M1 (FSM.initial M1) \<pi>)"
              using \<open>io' \<in> LS M1 s1\<close> unfolding s1 .
            have "x' \<in> inputs M1" and "y' \<in> outputs M1"
              using True 
              unfolding \<open>\<gamma> = io' @ [(x', y')] @ io''\<close> 
              by auto

            obtain \<alpha> \<beta> where "converge M1 \<alpha> (\<pi> @ io')"
                             "converge M2 \<alpha> (\<pi> @ io')" 
                             "converge M1 \<beta> (\<tau> @ io')" 
                             "converge M2 \<beta> (\<tau> @ io')" 
                             "\<alpha> \<in> SC" 
                             "\<alpha> @ [(x', y')] \<in> SC" 
                             "\<beta> \<in> SC" 
                             "\<beta> @ [(x', y')] \<in> SC"
              using assms(14)[OF * ** \<open>x' \<in> inputs M1\<close> \<open>y' \<in> outputs M1\<close>]
              by blast
            then have "\<alpha> \<in> L M1" and "\<beta> \<in> L M1"
              by auto


            have "\<pi>@io' \<in> L M1"
              using \<open>io' \<in> LS M1 s1\<close> \<open>\<pi> \<in> L M1 \<inter> T\<close>
              using after_language_iff[OF \<open>observable M1\<close>, of \<pi> "initial M1" io']
              unfolding s1
              by blast
            have "converge M1 (\<pi> @ io') (\<tau> @ io')"
              using converge_append[OF \<open>observable M1\<close> \<open>converge M1 \<pi> \<tau>\<close> \<open>\<pi>@io' \<in> L M1\<close> ]
              using \<open>\<tau> \<in> L M1 \<inter> T\<close>
              by blast

            have "(\<pi> @ io') @ [(x', y')] \<notin> L M1"
              using \<open>io' @ [(x', y')] \<notin> LS M1 s1\<close>
              using \<open>\<pi> \<in> L M1 \<inter> T\<close>
              using after_language_iff[OF \<open>observable M1\<close>, of \<pi> "initial M1" "io'@[(x',y')]"]
              unfolding s1
              by auto
            then have "[(x',y')] \<notin> LS M1 (after_initial M1 \<alpha>)"
              using after_language_iff[OF \<open>observable M1\<close> \<open>\<pi>@io' \<in> L M1\<close>, of "[(x',y')]"]
              using \<open>converge M1 \<alpha> (\<pi> @ io')\<close> 
              unfolding converge.simps
              by blast
            then have "[(x',y')] \<notin> LS M1 (after_initial M1 \<beta>)"
              using \<open>converge M1 (\<pi> @ io') (\<tau> @ io')\<close> \<open>converge M1 \<alpha> (\<pi> @ io')\<close> \<open>converge M1 \<beta> (\<tau> @ io')\<close>
              unfolding converge.simps
              by blast

            have "\<alpha> \<in> L M2"
              using \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> by blast
            have "\<beta> \<in> L M2"
              using \<open>\<beta> \<in> L M1\<close> \<open>\<beta> \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> by blast


            have "[(x',y')] \<notin> LS M2 (after_initial M2 \<alpha>)"
              using \<open>\<alpha> @ [(x', y')] \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> 
                    \<open>[(x',y')] \<notin> LS M1 (after_initial M1 \<alpha>)\<close>
              unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<alpha> \<in> L M1\<close>]
              unfolding after_language_iff[OF \<open>observable M2\<close> \<open>\<alpha> \<in> L M2\<close>]
              by blast
            then have "io'@[(x',y')] \<notin> LS M2 q1"
              using \<open>converge M2 \<alpha> (\<pi> @ io')\<close> 
              unfolding q1 converge.simps
              using after_language_append_iff assms(2) by blast 
            then have "\<gamma>@[xy] \<notin> LS M2 q1"
              unfolding \<open>\<gamma> = io' @ [(x', y')] @ io''\<close> 
              using language_prefix
              by (metis append_assoc) 


            have "[(x',y')] \<notin> LS M2 (after_initial M2 \<beta>)"
              using \<open>\<beta> @ [(x', y')] \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> 
                    \<open>[(x',y')] \<notin> LS M1 (after_initial M1 \<beta>)\<close>
              unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<beta> \<in> L M1\<close>]
              unfolding after_language_iff[OF \<open>observable M2\<close> \<open>\<beta> \<in> L M2\<close>]
              by blast
            then have "io'@[(x',y')] \<notin> LS M2 q2"
              using \<open>converge M2 \<beta> (\<tau> @ io')\<close> 
              unfolding q2 converge.simps
              using after_language_append_iff assms(2) by blast 
            then have "\<gamma>@[xy] \<notin> LS M2 q2"
              unfolding \<open>\<gamma> = io' @ [(x', y')] @ io''\<close> 
              using language_prefix
              by (metis append_assoc) 

            then show ?thesis
              using \<open>\<gamma>@[xy] \<notin> LS M2 q1\<close> 
              by blast
          next
            case True
            
            have *: "length \<gamma> < m - size_r M1"
              using \<open>length (\<gamma> @ [xy]) \<le> m - size_r M1\<close>
              by auto
            have **: "\<gamma> \<in> LS M1 (after M1 (FSM.initial M1) \<pi>)"
              using True unfolding s1 .
            have "x \<in> inputs M1" and "y \<in> outputs M1"
              using \<open>\<forall> x' y' . (x',y') \<in> set (\<gamma>@[(x,y)]) \<longrightarrow> x' \<in> inputs M1 \<and> y' \<in> outputs M1\<close>
              by auto  

            
            obtain \<alpha> \<beta> where "converge M1 \<alpha> (\<pi> @ \<gamma>)"
                             "converge M2 \<alpha> (\<pi> @ \<gamma>)" 
                             "converge M1 \<beta> (\<tau> @ \<gamma>)" 
                             "converge M2 \<beta> (\<tau> @ \<gamma>)" 
                             "\<alpha> \<in> SC" 
                             "\<alpha> @ [xy] \<in> SC" 
                             "\<beta> \<in> SC" 
                             "\<beta> @ [xy] \<in> SC"
              using assms(14)[OF * ** \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close>]
              unfolding \<open>xy = (x,y)\<close>
              by blast  
            then have "\<alpha> \<in> L M1" and "\<beta> \<in> L M1"
              by auto
              
            have "\<alpha> \<in> L M2"
              using \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> by blast
            have "\<beta> \<in> L M2"
              using \<open>\<beta> \<in> L M1\<close> \<open>\<beta> \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> by blast

            have "(\<pi> @ \<gamma>) \<in> L M2"
              using \<open>converge M2 \<alpha> (\<pi> @ \<gamma>)\<close> by auto
            have "(\<tau> @ \<gamma>) \<in> L M2"
              using \<open>converge M2 \<beta> (\<tau> @ \<gamma>)\<close> by auto

            have "converge M1 (\<pi> @ \<gamma>) (\<tau> @ \<gamma>)"
              using converge_append[OF \<open>observable M1\<close> \<open>converge M1 \<pi> \<tau>\<close>, of \<gamma>]
              using \<open>converge M1 \<alpha> (\<pi> @ \<gamma>)\<close> \<open>\<tau> \<in> L M1 \<inter> T\<close> 
              by auto

            have "(\<gamma>@[xy] \<in> LS M2 q1) = ([xy] \<in> LS M2 (after_initial M2 (\<pi>@\<gamma>)))"
              unfolding q1 
              using after_language_append_iff[OF \<open>observable M2\<close> \<open>(\<pi> @ \<gamma>) \<in> L M2\<close>] by auto
            also have "\<dots> = ([xy] \<in> LS M2 (after_initial M2 \<alpha>))"
              using \<open>converge M2 \<alpha> (\<pi> @ \<gamma>)\<close> unfolding q1 converge.simps 
              by blast
            also have "\<dots> = ([xy] \<in> LS M1 (after_initial M1 \<alpha>))"
              using \<open>\<alpha>@[xy] \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> 
              unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<alpha> \<in> L M1\<close>]
              unfolding after_language_iff[OF \<open>observable M2\<close> \<open>\<alpha> \<in> L M2\<close>]
              by blast
            also have "\<dots> = ([xy] \<in> LS M1 (after_initial M1 \<beta>))"
              using \<open>converge M1 (\<pi> @ \<gamma>) (\<tau> @ \<gamma>)\<close> \<open>converge M1 \<alpha> (\<pi> @ \<gamma>)\<close> \<open>converge M1 \<beta> (\<tau> @ \<gamma>)\<close> 
              unfolding converge.simps 
              by blast
            also have "\<dots> = ([xy] \<in> LS M2 (after_initial M2 \<beta>))"
              using \<open>\<beta>@[xy] \<in> SC\<close> \<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close> 
              unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<beta> \<in> L M1\<close>]
              unfolding after_language_iff[OF \<open>observable M2\<close> \<open>\<beta> \<in> L M2\<close>]
              by blast
            also have "\<dots> = ([xy] \<in> LS M2 (after_initial M2 (\<tau>@\<gamma>)))"
              using \<open>converge M2 \<beta> (\<tau> @ \<gamma>)\<close> unfolding q1 converge.simps 
              by blast
            also have "\<dots> = (\<gamma>@[xy] \<in> LS M2 q2)"
              unfolding q2 
              using after_language_append_iff[OF \<open>observable M2\<close> \<open>(\<tau> @ \<gamma>) \<in> L M2\<close>] by auto
            finally have p1: "(\<gamma>@[xy] \<in> LS M2 q1) = (\<gamma>@[xy] \<in> LS M2 q2)"
              .

            moreover have "(\<gamma>@[xy] \<in> LS M2 q1 \<longrightarrow> after M2 q2 (\<gamma>@[xy]) \<in> partition (after M2 q1 (\<gamma>@[xy])))"
            proof 
              assume "\<gamma>@[xy] \<in> LS M2 q1"
              then have "[xy] \<in> LS M1 (after_initial M1 \<alpha>)"
                    and "[xy] \<in> LS M1 (after_initial M1 \<beta>)"
                unfolding \<open>(\<gamma>@[xy] \<in> LS M2 q1) = ([xy] \<in> LS M2 (after_initial M2 (\<pi>@\<gamma>)))\<close>  
                          \<open>([xy] \<in> LS M2 (after_initial M2 (\<pi>@\<gamma>))) = ([xy] \<in> LS M2 (after_initial M2 \<alpha>))\<close>
                          \<open>([xy] \<in> LS M2 (after M2 (FSM.initial M2) \<alpha>)) = ([xy] \<in> LS M1 (after M1 (FSM.initial M1) \<alpha>))\<close>
                          \<open>([xy] \<in> LS M1 (after M1 (FSM.initial M1) \<alpha>)) = ([xy] \<in> LS M1 (after M1 (FSM.initial M1) \<beta>))\<close> 
                by simp+
      
              have "\<alpha>@[xy] \<in> L M1"
                using \<open>[xy] \<in> LS M1 (after_initial M1 \<alpha>)\<close> unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<alpha> \<in> L M1\<close>] .
              moreover have "\<beta>@[xy] \<in> L M1"
                using \<open>[xy] \<in> LS M1 (after_initial M1 \<beta>)\<close> unfolding after_language_iff[OF \<open>observable M1\<close> \<open>\<beta> \<in> L M1\<close>] .
              moreover have "converge M1 \<alpha> \<beta>"
                using \<open>converge M1 (\<pi> @ \<gamma>) (\<tau> @ \<gamma>)\<close> \<open>converge M1 \<alpha> (\<pi> @ \<gamma>)\<close> \<open>converge M1 \<beta> (\<tau> @ \<gamma>)\<close> 
                unfolding converge.simps 
                by blast
              ultimately have "converge M1 (\<alpha>@[xy]) (\<beta>@[xy])"
                using converge_append[OF \<open>observable M1\<close>] language_prefix[of \<beta> "[xy]" M1 "initial M1"] by blast
      
              have "(\<alpha> @ [xy]) \<in> L M2" and "(\<beta> @ [xy]) \<in> L M2"
                using \<open>\<alpha>@[xy] \<in> L M1\<close> \<open>\<alpha>@[xy] \<in> SC\<close> \<open>\<beta>@[xy] \<in> L M1\<close> \<open>\<beta>@[xy] \<in> SC \<close>\<open>L M1 \<inter> T = L M2 \<inter> T\<close> \<open>SC \<subseteq> T\<close>  by blast+
              have "after_initial M1 (\<alpha>@[xy]) \<in> reachable_states M1"
                using observable_after_path[OF \<open>observable M1\<close> \<open>\<alpha>@[xy] \<in> L M1\<close>]
                unfolding reachable_states_def
                by (metis (mono_tags, lifting) mem_Collect_eq)
              have "(\<alpha>@[xy]) \<in> A (after_initial M1 (\<alpha>@[xy]))"
                unfolding A
                using convergence_minimal[OF assms(3,1) _ \<open>\<alpha>@[xy] \<in> L M1\<close>, of "f (after_initial M1 (\<alpha>@[xy]))"] 
                using f2[OF \<open>after_initial M1 (\<alpha>@[xy]) \<in> reachable_states M1\<close>]
                using \<open>\<alpha>@[xy] \<in> SC\<close>
                by (metis (no_types, lifting) Int_iff \<open>\<alpha> @ [xy] \<in> L M1\<close> \<open>after M1 (FSM.initial M1) (\<alpha> @ [xy]) \<in> reachable_states M1\<close> assms(1) f1 member_filter observable_after_path observable_path_io_target singletonD) 
              then have "after M2 (FSM.initial M2) (\<alpha> @ [xy]) \<in> Q (after_initial M1 (\<alpha>@[xy]))"
                unfolding Q 
                using observable_io_targets[OF \<open>observable M2\<close> \<open>(\<alpha> @ [xy]) \<in> L M2\<close>]
                unfolding after_io_targets[OF \<open>observable M2\<close> \<open>(\<alpha> @ [xy]) \<in> L M2\<close>]
                by (metis UN_iff insertCI the_elem_eq)
              then have "\<exists>q'\<in>reachable_states M1. after M2 (FSM.initial M2) (\<alpha> @ [xy]) \<in> Q q'"
                using \<open>after_initial M1 (\<alpha>@[xy]) \<in> reachable_states M1\<close> by blast
              moreover have "(THE q'. q' \<in> reachable_states M1 \<and> after M2 (FSM.initial M2) (\<alpha> @ [xy]) \<in> Q q') = (after_initial M1 (\<alpha>@[xy]))"
                using \<open>after_initial M1 (\<alpha>@[xy]) \<in> reachable_states M1\<close>
                using \<open>after M2 (FSM.initial M2) (\<alpha> @ [xy]) \<in> Q (after_initial M1 (\<alpha>@[xy]))\<close>
                by (simp add: \<open>\<And>q. \<exists>\<^sub>\<le>\<^sub>1 q'. q' \<in> reachable_states M1 \<and> q \<in> Q q'\<close> the1_equality')
              moreover have "after M2 (FSM.initial M2) (\<beta> @ [xy]) \<in> Q (after_initial M1 (\<alpha>@[xy]))"
              proof -
                have "(\<beta>@[xy]) \<in> A (after_initial M1 (\<alpha>@[xy]))"
                  using A \<open>\<alpha> @ [xy] \<in> A (after M1 (FSM.initial M1) (\<alpha> @ [xy]))\<close> \<open>\<beta> @ [xy] \<in> L M1\<close> \<open>\<beta> @ [xy] \<in> SC\<close> \<open>converge M1 (\<alpha> @ [xy]) (\<beta> @ [xy])\<close> by auto
                then show ?thesis
                  unfolding Q 
                  using observable_io_targets[OF \<open>observable M2\<close> \<open>(\<beta> @ [xy]) \<in> L M2\<close>]
                  unfolding after_io_targets[OF \<open>observable M2\<close> \<open>(\<beta> @ [xy]) \<in> L M2\<close>]
                  by (metis UN_iff insertCI the_elem_eq)
              qed
              ultimately have "after_initial M2 (\<beta>@[xy]) \<in> partition (after_initial M2 (\<alpha>@[xy]))"
                unfolding partition
                by presburger 
              moreover have "after_initial M2 (\<alpha>@[xy]) = after_initial M2 ((\<pi>@\<gamma>)@[xy])"
                using converge_append[OF assms(2) \<open>converge M2 \<alpha> (\<pi>@\<gamma>)\<close> \<open>(\<alpha> @ [xy]) \<in> L M2\<close> \<open>(\<pi>@\<gamma>) \<in> L M2\<close>]
                unfolding convergence_minimal[OF assms(4,2) \<open>(\<alpha> @ [xy]) \<in> L M2\<close> converge_extend[OF assms(2) \<open>converge M2 \<alpha> (\<pi>@\<gamma>)\<close> \<open>(\<alpha> @ [xy]) \<in> L M2\<close> \<open>(\<pi>@\<gamma>) \<in> L M2\<close>]]
                .
              moreover have "after_initial M2 (\<beta>@[xy]) = after_initial M2 ((\<tau>@\<gamma>)@[xy])"
                using converge_append[OF assms(2) \<open>converge M2 \<beta> (\<tau>@\<gamma>)\<close> \<open>(\<beta> @ [xy]) \<in> L M2\<close> \<open>(\<tau>@\<gamma>) \<in> L M2\<close>]
                unfolding convergence_minimal[OF assms(4,2) \<open>(\<beta> @ [xy]) \<in> L M2\<close> converge_extend[OF assms(2) \<open>converge M2 \<beta> (\<tau>@\<gamma>)\<close> \<open>(\<beta> @ [xy]) \<in> L M2\<close> \<open>(\<tau>@\<gamma>) \<in> L M2\<close>]]
                .
              ultimately show "after M2 q2 (\<gamma>@[xy]) \<in> partition (after M2 q1 (\<gamma>@[xy]))"
                unfolding q1 q2 
                unfolding after_split[OF assms(2) converge_extend[OF assms(2) \<open>converge M2 \<alpha> (\<pi>@\<gamma>)\<close> \<open>(\<alpha> @ [xy]) \<in> L M2\<close> \<open>(\<pi>@\<gamma>) \<in> L M2\<close>]]
                unfolding after_split[OF assms(2) converge_extend[OF assms(2) \<open>converge M2 \<beta> (\<tau>@\<gamma>)\<close> \<open>(\<beta> @ [xy]) \<in> L M2\<close> \<open>(\<tau>@\<gamma>) \<in> L M2\<close>]]
                by (metis \<open>\<gamma> @ [xy] \<in> LS M2 q1\<close> \<open>\<pi> @ \<gamma> \<in> L M2\<close> \<open>\<tau> @ \<gamma> \<in> L M2\<close> \<open>after M2 (after M2 (FSM.initial M2) (\<pi> @ \<gamma>)) [xy] = after M2 (FSM.initial M2) ((\<pi> @ \<gamma>) @ [xy])\<close> \<open>after M2 (after M2 (FSM.initial M2) (\<tau> @ \<gamma>)) [xy] = after M2 (FSM.initial M2) ((\<tau> @ \<gamma>) @ [xy])\<close> after_split assms(2) p1 q1 q2)                
            qed

            ultimately show ?thesis
              by blast
          qed
        qed
      qed
    qed 

    ultimately show ?thesis
      using ofsm_table_set_observable[OF \<open>observable M2\<close> \<open>q1 \<in> states M2\<close> is_eq, of "m - size_r M1"]
      unfolding q1 q2 
      by blast
  qed

  ultimately have "after M2 (FSM.initial M2) \<tau> \<in> ofsm_table M2 partition (m - n0) (after M2 (FSM.initial M2) \<pi>)"
    using ofsm_table_subset[OF \<open>size_r M1 \<le> n0\<close>, of M2 partition "initial M2"]
    by (meson diff_le_mono2 in_mono ofsm_table_subset)

  moreover have "after M2 (FSM.initial M2) \<pi> \<in> states M2"
    by (metis IntD1 after_is_state assms(2) assms(7) assms(8))
    
  ultimately have "after M2 (FSM.initial M2) \<tau> \<in> ofsm_table_fix M2 partition 0 (after M2 (FSM.initial M2) \<pi>)"
    using ofsm_table_fix_partition_fixpoint[OF \<open>equivalence_relation_on_states M2 partition\<close> \<open>size M2 \<le> m\<close>, of "after M2 (FSM.initial M2) \<pi>"]
    unfolding n0
    by blast

  then have "LS M2 (after_initial M2 \<tau>) = LS M2 (after_initial M2 \<pi>)"
    unfolding ofsm_table_fix_set[OF \<open>after M2 (FSM.initial M2) \<pi> \<in> states M2\<close> \<open>observable M2\<close> \<open>equivalence_relation_on_states M2 partition\<close>]
    by blast
  then show ?thesis
    unfolding converge.simps
    by (metis assms(15) converge.elims(2)) 
qed



lemma preserves_divergence_minimally_distinguishing_prefixes_lower_bound :
  fixes M1 :: "('a,'b,'c) fsm"
  fixes M2 :: "('d,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "converge M1 u v"
  and     "\<not>converge M2 u v"
  and     "u \<in> L M2"
  and     "v \<in> L M2"
  and     "minimally_distinguishes M2 (after_initial M2 u) (after_initial M2 v) w"
  and     "wp \<in> list.set (prefixes w)"
  and     "wp \<noteq> w"
  and     "wp \<in> LS M1 (after_initial M1 u) \<inter> LS M1 (after_initial M1 v)"
  and     "preserves_divergence M1 M2 {\<alpha>@\<gamma> | \<alpha> \<gamma> . \<alpha> \<in> {u,v} \<and> \<gamma> \<in> list.set (prefixes wp)}"
  and     "L M1 \<inter> {\<alpha>@\<gamma> | \<alpha> \<gamma> . \<alpha> \<in> {u,v} \<and> \<gamma> \<in> list.set (prefixes wp)} = L M2 \<inter> {\<alpha>@\<gamma> | \<alpha> \<gamma> . \<alpha> \<in> {u,v} \<and> \<gamma> \<in> list.set (prefixes wp)}"
shows "card (after_initial M2 ` {\<alpha>@\<gamma> | \<alpha> \<gamma> . \<alpha> \<in> {u,v} \<and> \<gamma> \<in> list.set (prefixes wp)}) \<ge> length wp + (card (FSM.after M1 (after_initial M1 u) ` (list.set (prefixes wp)))) + 1"
proof -

  define k where "k = length wp"
  then show ?thesis 
    using assms(10,11,12,13,14)
  proof (induction k arbitrary: wp rule: less_induct)
    case (less k)
    
    show ?case proof (cases k)
      case 0
      then have "wp = []"
        using less.prems by auto


      have "{\<alpha>@\<gamma> | \<alpha> \<gamma> . \<alpha> \<in> {u,v} \<and> \<gamma> \<in> list.set (prefixes [])} = {u,v}"
        by auto
      moreover have "(after_initial M2 u) \<noteq> (after_initial M2 v)"
        using assms(9) assms(2) assms(4) assms(6) assms(7) assms(8) convergence_minimal by blast 
      ultimately have "card (after_initial M2 ` {\<alpha>@\<gamma> | \<alpha> \<gamma> . \<alpha> \<in> {u,v} \<and> \<gamma> \<in> list.set (prefixes [])}) = 2"
        by auto
    
      have "FSM.after M1 (after_initial M1 u) ` (list.set (prefixes [])) = {after_initial M1 u}"
        unfolding prefixes_set by auto
      then have "length [] + (card (FSM.after M1 (after_initial M1 u) ` (list.set (prefixes [])))) + 1 = 2"
        by auto
      then show ?thesis
        unfolding \<open>wp = []\<close>
        using \<open>card (after_initial M2 ` {\<alpha>@\<gamma> | \<alpha> \<gamma> . \<alpha> \<in> {u,v} \<and> \<gamma> \<in> list.set (prefixes [])}) = 2\<close>
        by simp
    next
      case (Suc k')

      have "\<And> w''. w'' \<in> set (prefixes wp) \<Longrightarrow> u@w'' \<in> L M1"
        by (metis after_language_iff assms(1) assms(5) converge.elims(2) inf_idem language_prefix less.prems(4) prefixes_set_ob)
      then have "\<And> w''. w'' \<in> set (prefixes wp) \<Longrightarrow> v@w'' \<in> L M1"
        by (meson assms(1) assms(5) converge.elims(2) converge_extend)
    
      have "\<And> w'' . w'' \<in> set (prefixes wp) \<Longrightarrow> converge M1 (u@w'') (v@w'')"
          using \<open>\<And>w''. w'' \<in> set (prefixes wp) \<Longrightarrow> u @ w'' \<in> L M1\<close> assms(1) assms(5) converge.simps converge_append by blast
  
  
      have "\<And> w' . w' \<in> set (prefixes wp) \<Longrightarrow> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes w')} \<subseteq> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes wp)}"
        using prefixes_prefix_subset[of _ wp]
        by blast
      have "\<And> w' . {u @ \<gamma> | \<gamma>. \<gamma> \<in> set (prefixes w')} \<subseteq> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes w')}"
        using prefixes_set_subset by blast
      have "\<And> w' . {v @ \<gamma> | \<gamma>. \<gamma> \<in> set (prefixes w')} \<subseteq> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes w')}"
        using prefixes_set_subset by blast
  
      have "u@wp \<in> L M1"
        by (metis Int_absorb after_language_iff assms(1) assms(5) converge.simps less.prems(4))
      moreover have "u@wp \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes wp)}"
        unfolding prefixes_set by blast
      ultimately have "u@wp \<in> L M2"
        using less.prems(6) by blast 
      then have "wp \<in> LS M2 (after_initial M2 u)"
        by (meson after_language_iff assms(2) language_prefix)
  
  
      have "v@wp \<in> L M1"
        by (meson \<open>u @ wp \<in> L M1\<close> assms(1) assms(5) converge.simps converge_extend)
      moreover have "v@wp \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes wp)}"
        unfolding prefixes_set by blast
      ultimately have "v@wp \<in> L M2"
        using less.prems(6) by blast 
      then have "wp \<in> LS M2 (after_initial M2 v)"
        by (meson after_language_iff assms(2) language_prefix)
  
      have no_conv_2: "\<And> w'' . w'' \<in> set (prefixes wp) \<Longrightarrow> \<not>converge M2 (u@w'') (v@w'') \<and> u@w'' \<in> L M1 \<and> v@w'' \<in> L M1 \<and> u@w'' \<in> L M2 \<and> v@w'' \<in> L M2"
      proof -
        fix w'' assume *: "w'' \<in> set (prefixes wp)"
        then have "w'' \<in> set (prefixes w)" 
          using less.prems
          by (metis (no_types, lifting) insert_subset mk_disjoint_insert prefixes_set_ob prefixes_set_subset)
        
        have "u@w'' \<in> L M1"
          using \<open>\<And>w''. w'' \<in> set (prefixes wp) \<Longrightarrow> u @ w'' \<in> L M1\<close> * by auto
        then have "u@w'' \<in> L M2"
          using assms(14) less.prems *
          by (metis (no_types, lifting) \<open>wp \<in> LS M2 (after_initial M2 u)\<close> after_language_iff assms(2) assms(7) language_prefix prefixes_set_ob) 
        then have "w'' \<in> LS M2 (after_initial M2 u)"
          by (meson after_language_iff assms(2) language_prefix)
  
        have "v@w'' \<in> L M1"
          using \<open>\<And>w''. w'' \<in> set (prefixes wp) \<Longrightarrow> v @ w'' \<in> L M1\<close> * by auto
        then have "v@w'' \<in> L M2"
          using assms(14) less.prems(1) *
          by (metis (no_types, lifting) \<open>wp \<in> LS M2 (after_initial M2 v)\<close> after_language_iff assms(2) assms(8) language_prefix prefixes_set_ob) 
        then have "w'' \<in> LS M2 (after_initial M2 v)"
          by (meson after_language_iff assms(2) language_prefix)
  
        have "distinguishes M2 (after_initial M2 u) (after_initial M2 v) w"
          using assms(9) unfolding minimally_distinguishes_def by auto
        show "\<not>converge M2 (u@w'') (v@w'') \<and> u@w'' \<in> L M1 \<and> v@w'' \<in> L M1 \<and> u@w'' \<in> L M2 \<and> v@w'' \<in> L M2"
          using distinguishes_diverge_prefix[OF assms(2) \<open>distinguishes M2 (after_initial M2 u) (after_initial M2 v) w\<close> assms(7,8) \<open>w'' \<in> set (prefixes w)\<close> \<open>w'' \<in> LS M2 (after_initial M2 u)\<close> \<open>w'' \<in> LS M2 (after_initial M2 v)\<close>] 
                \<open>u@w'' \<in> L M1\<close> \<open>v@w'' \<in> L M1\<close> \<open>u@w'' \<in> L M2\<close> \<open>v@w'' \<in> L M2\<close>
          by blast 
      qed  
  
      have div_on_prefixes : "\<And> w'' . w'' \<in> set (prefixes wp) \<Longrightarrow> after_initial M2 (u@w'') \<noteq> after_initial M2 (v@w'')"
        using no_conv_2
        using assms(2) assms(4) convergence_minimal by blast 
      then have div_on_proper_prefixes : "\<And> w' w'' . w' \<in> set (prefixes wp) \<Longrightarrow> w'' \<in> set (prefixes w') \<Longrightarrow> after_initial M2 (u@w'') \<noteq> after_initial M2 (v@w'')"
        using prefixes_prefix_subset by blast
  
      have "wp = (butlast wp)@[last wp]"
        using Suc less.prems(1)
        by (metis append_butlast_last_id length_greater_0_conv zero_less_Suc) 
      then have "(FSM.after M1 (after_initial M1 u) ` (list.set (prefixes wp))) = Set.insert (FSM.after M1 (after_initial M1 u) wp) (FSM.after M1 (after_initial M1 u) ` (list.set (prefixes (butlast wp))))"
        using prefixes_set_Cons_insert 
        by (metis image_insert) 
  
  
      consider "(FSM.after M1 (after_initial M1 u) wp) \<notin> (FSM.after M1 (after_initial M1 u) ` (list.set (prefixes (butlast wp))))" |
                "(FSM.after M1 (after_initial M1 u) wp) \<in> (FSM.after M1 (after_initial M1 u) ` (list.set (prefixes (butlast wp))))"
        by blast
        
      
           
      obtain w_suffix where "w = (wp)@w_suffix"
        using less.prems(2)
        using prefixes_set_ob by blast 
  
      define wk where wk: "wk = (\<lambda> i . take i wp)"
      define wk' where wk': "wk' = (\<lambda> i . drop i wp)"
  
      have "\<And> i . (wk i)@(wk' i) = wp"
        unfolding wk wk' by auto
      then have "\<And> i . wk i \<in> set (prefixes wp)"
        unfolding prefixes_set
        by auto 
      then have "\<And> i . set (prefixes (wk i)) \<subseteq> set (prefixes wp)"
        by (simp add: prefixes_prefix_subset)
      
      have "\<And> i . i < k \<Longrightarrow> wk' i \<noteq> []"
        using less.prems(1)
        by (simp add: wk')   
  
      have "wk k = wp"
        using less.prems(1)
        by (simp add: wk)   
  
      have "\<And> i . \<not> converge M2 (u @ wk i) (v @ wk i)"
        using no_conv_2[OF \<open>\<And> i . wk i \<in> set (prefixes wp)\<close>] by blast 
      have "\<And> i . u@wk i \<in> L M1"
        using no_conv_2[OF \<open>\<And> i . wk i \<in> set (prefixes wp)\<close>] by blast 
      have "\<And> i . u@wk i \<in> L M2"
        using no_conv_2[OF \<open>\<And> i . wk i \<in> set (prefixes wp)\<close>] by blast 
      have "\<And> i . v@wk i \<in> L M1"
        using no_conv_2[OF \<open>\<And> i . wk i \<in> set (prefixes wp)\<close>] by blast 
      have "\<And> i . v@wk i \<in> L M2"
        using no_conv_2[OF \<open>\<And> i . wk i \<in> set (prefixes wp)\<close>] by blast 
  
      
  
      have "\<And> w'' . w'' \<in> set (prefixes wp) \<Longrightarrow> w'' = wk (length w'')"
        unfolding prefixes_take_iff unfolding wk 
        by auto
      then have "\<And> i w'' . w'' \<in> set (prefixes (wk i)) \<Longrightarrow> \<exists> j . w'' = wk j \<and> j \<le> i"
        by (metis min_def order_refl prefixes_take_iff take_take wk) 
  
  
      have prefixes_same_reaction: "\<And> j . j < k \<Longrightarrow> w_suffix \<in> LS M2 (after_initial M2 (u@wk j)) = (w_suffix \<in> LS M2 (after_initial M2 (v@wk j)))"
      proof -
        fix j assume "j < k" 
  
        then have "wp = (wk j)@(wk' j)" and "(wk' j) \<noteq> []"
          using \<open>\<And> i . (wk i)@(wk' i) = wp\<close> \<open>\<And> i . i < k \<Longrightarrow> wk' i \<noteq> []\<close> by auto
  
        have "distinguishes M2 (after_initial M2 u) (after_initial M2 v) ((wk j)@(wk' j)@w_suffix)"
          using assms(9) 
          unfolding \<open>w = (wp)@w_suffix\<close> \<open>wp = (wk j)@(wk' j)\<close> minimally_distinguishes_def
          by (metis append.assoc)
  
        have "u@wk j \<in> L M2"
          using \<open>\<And>i. u @ wk i \<in> L M2\<close> by blast
        have "v@wk j \<in> L M2"
          using \<open>\<And>i. v @ wk i \<in> L M2\<close> by blast
          
        have *: "minimally_distinguishes M2 (after_initial M2 (u @ wk j)) (after_initial M2 (v @ wk j)) ((wk' j)@w_suffix)"
          using assms(9) minimally_distinguishes_after_append_initial[OF assms(2,4)  \<open>u \<in> L M2\<close> \<open>v \<in> L M2\<close>, of "wk j"]
          using \<open>w = wp @ w_suffix\<close> \<open>wk' j \<noteq> []\<close> \<open>wp = wk j @ wk' j\<close> by auto        
  
        then have "\<not>distinguishes M2 (after_initial M2 (u@wk j)) (after_initial M2 (v@wk j)) w_suffix"
          unfolding minimally_distinguishes_def
          by (metis "*" \<open>u @ wk j \<in> L M2\<close> \<open>v @ wk j \<in> L M2\<close> \<open>wk' j \<noteq> []\<close> append.left_neutral append.right_neutral assms(2) minimally_distinguishes_no_prefix)
        then show "w_suffix \<in> LS M2 (after_initial M2 (u@wk j)) = (w_suffix \<in> LS M2 (after_initial M2 (v@wk j)))"
          unfolding distinguishes_def by blast
      qed
  
      have "\<And> i . u@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}"
        using \<open>\<And>i. wk i \<in> set (prefixes wp)\<close> by blast
      have "\<And> i . v@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}"
        using \<open>\<And>i. wk i \<in> set (prefixes wp)\<close> by blast
      have "u@(wp) \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}"
        using prefixes_set by blast
      have "v@(wp) \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}"
        using prefixes_set by blast
  
  
  
      (* adaptation of the alternative proof by Wen-ling *)
  
      define q where q: "q = (\<lambda> i . after_initial M1 (u@(wk i)))"
      define a where a: "a = (\<lambda> i . after_initial M2 (u@(wk i)))" 
      define b where b: "b = (\<lambda> i . after_initial M2 (v@(wk i)))" 
      define I' where I': "I' = (\<lambda> i . {j . j \<le> Suc k' \<and> q i = q j})"
  
      define l where l: "l = card (q ` (\<Union> i \<in> {..Suc k'} . I' i))"
  
      have q_v: "\<And> i . q i = after_initial M1 (v@(wk i))"
        unfolding q
        by (meson \<open>\<And>i. wk i \<in> set (prefixes wp)\<close> \<open>\<And>w''. w'' \<in> set (prefixes wp) \<Longrightarrow> converge M1 (u @ w'') (v @ w'')\<close> assms(1) assms(3) converge.simps convergence_minimal) 
  
  
      have q_divergence: "\<And> i j . q i \<noteq> q j \<Longrightarrow> a i \<noteq> a j \<and> a i \<noteq> b j \<and> b i \<noteq> a j \<and> b i \<noteq> b j"
      proof -
        fix i j assume "q i \<noteq> q j"
        then have "\<not> converge M1 (u@(wk i)) (u@(wk j))"
          unfolding q
          using assms(1) assms(3) converge.simps convergence_minimal by blast 
        then have "\<not> converge M1 (u@(wk i)) (v@(wk j))"
                  "\<not> converge M1 (v@(wk i)) (u@(wk j))"
                  "\<not> converge M1 (v@(wk i)) (v@(wk j))"
          using assms(1) assms(3) assms(5) converge_trans_2 by blast+
  
        have "\<not> converge M2 (u@(wk i)) (u@(wk j))"
          using \<open>\<not> converge M1 (u@(wk i)) (u@(wk j))\<close>
          using less.prems(5) unfolding preserves_divergence.simps 
          using \<open>\<And>i. u @ wk i \<in> L M1\<close> [of i] \<open>\<And> i . u@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}\<close>[of i]
          using \<open>\<And>i. u @ wk i \<in> L M1\<close> [of j] \<open>\<And> i . u@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}\<close>[of j]
          by blast
        then have "a i \<noteq> a j"
          unfolding a 
          using \<open>\<And>i. u @ wk i \<in> L M2\<close>
          using assms(2) assms(4) convergence_minimal by blast
  
        have "\<not> converge M2 (v@(wk i)) (v@(wk j))"
          using \<open>\<not> converge M1 (v@(wk i)) (v@(wk j))\<close>
          using less.prems(5) unfolding preserves_divergence.simps 
          using \<open>\<And>i. v @ wk i \<in> L M1\<close> [of i] \<open>\<And> i . v@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}\<close>[of i]
          using \<open>\<And>i. v @ wk i \<in> L M1\<close> [of j] \<open>\<And> i . v@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}\<close>[of j]
          by blast
        then have "b i \<noteq> b j"
          unfolding b 
          using \<open>\<And>i. v @ wk i \<in> L M2\<close>
          using assms(2) assms(4) convergence_minimal by blast
  
        have "\<not> converge M2 (u@(wk i)) (v@(wk j))"
          using \<open>\<not> converge M1 (u@(wk i)) (v@(wk j))\<close>
          using less.prems(5) unfolding preserves_divergence.simps 
          using \<open>\<And>i. u @ wk i \<in> L M1\<close> [of i] \<open>\<And> i . u@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}\<close>[of i]
          using \<open>\<And>i. v @ wk i \<in> L M1\<close> [of j] \<open>\<And> i . v@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}\<close>[of j]
          by blast
        then have "a i \<noteq> b j"
          unfolding a b 
          using \<open>\<And>i. u @ wk i \<in> L M2\<close> \<open>\<And>i. v @ wk i \<in> L M2\<close>
          using assms(2) assms(4) convergence_minimal by blast
  
        have "\<not> converge M2 (v@(wk i)) (u@(wk j))"
          using \<open>\<not> converge M1 (v@(wk i)) (u@(wk j))\<close>
          using less.prems(5) unfolding preserves_divergence.simps 
          using \<open>\<And>i. v @ wk i \<in> L M1\<close> [of i] \<open>\<And> i . v@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}\<close>[of i]
          using \<open>\<And>i. u @ wk i \<in> L M1\<close> [of j] \<open>\<And> i . u@wk i \<in> {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes (wp))}\<close>[of j]
          by blast
        then have "b i \<noteq> a j"
          unfolding b a
          using \<open>\<And>i. v @ wk i \<in> L M2\<close> \<open>\<And>i. u @ wk i \<in> L M2\<close>
          using assms(2) assms(4) convergence_minimal by blast
  
        show "a i \<noteq> a j \<and> a i \<noteq> b j \<and> b i \<noteq> a j \<and> b i \<noteq> b j"
          using \<open>a i \<noteq> a j\<close> \<open>a i \<noteq> b j\<close> \<open>b i \<noteq> a j\<close> \<open>b i \<noteq> b j\<close> by auto
      qed
  
      have "\<And> i . a i \<in> states M2"
        by (metis \<open>\<And>i. u @ wk i \<in> L M2\<close> a after_is_state assms(2))
      have "\<And> i . b i \<in> states M2"
        by (metis \<open>\<And>i. v @ wk i \<in> L M2\<close> b after_is_state assms(2))     
  
      have "\<And> i j . i \<le> Suc k' \<Longrightarrow> j \<le> Suc k' \<Longrightarrow>  q i = q j \<Longrightarrow> I' i = I' j"
        unfolding q I' by force
      
      have "\<And> i . i \<le> Suc k' \<Longrightarrow> i \<in> I' i"
        unfolding I' q by force
      moreover have "\<And> i . I' i \<subseteq> {..Suc k'}" 
        unfolding I' by force
      ultimately have "(\<Union> i \<in> {..Suc k'} . I' i) = {..Suc k'}"
        by blast
      then have "card (\<Union> i \<in> {..Suc k'} . I' i) = k'+2"
        by auto
  
  
      have pt1: "finite {..Suc k'}"
        by auto
      have pt2: "{..Suc k'} \<noteq> {}"
        by auto
      have pt3: "(\<And>x. x \<in> {..Suc k'} \<Longrightarrow> I' x \<subseteq> {..Suc k'})"
        using \<open>\<And>i. I' i \<subseteq> {..Suc k'}\<close> atMost_atLeast0 by blast
      have pt4: "(\<And>x. x \<in> {..Suc k'} \<Longrightarrow> I' x \<noteq> {})"
        using \<open>\<And>i. i \<le> Suc k' \<Longrightarrow> i \<in> I' i\<close> by auto
      have pt5: "(\<And>x y. x \<in> {..Suc k'} \<Longrightarrow> y \<in> {..Suc k'} \<Longrightarrow> I' x = I' y \<or> I' x \<inter> I' y = {})"
        using I' by force
      have pt6: "\<Union> (I' ` {..Suc k'}) = {..Suc k'}"
        using \<open>\<Union> (I' ` {..Suc k'}) = {..Suc k'}\<close> by linarith
  
      obtain l I where "I ` {..l} = I' ` {..Suc k'}"
                   and "\<And>i j. i \<le> l \<Longrightarrow> j \<le> l \<Longrightarrow> i \<noteq> j \<Longrightarrow> I i \<inter> I j = {}"
                   and "card (I' ` {..Suc k'}) = Suc l"
        using partition_helper[of "{..Suc k'}" I', OF pt1 pt2 pt3 pt4 pt5 pt6]
        by metis
  
      have "\<And> i . i \<le> l \<Longrightarrow> \<exists> j . j \<le> Suc k' \<and> I i = I' j"
        using \<open>I ` {..l} = I' ` {..Suc k'}\<close> 
        by blast
  
      define S where S: "S = (\<lambda> i . \<Union> j \<in> I i . {a j, b j})"
  
      (* 5 *)
      have "(\<Union> i \<in> {..l} . S i) = (\<Union> i \<in> {..Suc k'} . {a i, b i})"
        unfolding S using \<open>I ` {..l} = I' ` {..Suc k'}\<close>
        by (metis (no_types, lifting) Sup.SUP_cong UN_UN_flatten \<open>\<Union> (I' ` {..Suc k'}) = {..Suc k'}\<close>) 
      then have "card (\<Union> i \<in> {..l} . S i) = card (\<Union> i \<in> {..Suc k'} . {a i, b i})"
        by presburger
  
      (* 6 *)
      moreover have "\<And> i j. i \<le> l \<Longrightarrow> j \<le> l \<Longrightarrow> i \<noteq> j \<Longrightarrow> S i \<inter> S j = {}"
      proof (rule ccontr)
        fix i j assume "i \<le> l" and "j \<le> l" and "i \<noteq> j" and "S i \<inter> S j \<noteq> {}"
        then obtain ii jj where "ii \<in> I i" and "jj \<in> I j" and "{a ii, b ii} \<inter> {a jj, b jj} \<noteq> {}"
          unfolding S by blast
       
        obtain i' j' where "i' \<le> Suc k'" and "j' \<le> Suc k'" and "I i = I' i'" and "I j = I' j'"
          using \<open>i \<le> l\<close> \<open>j \<le> l\<close> \<open>\<And> i . i \<le> l \<Longrightarrow> \<exists> j . j \<le> Suc k' \<and> I i = I' j\<close>
          by meson 
  
        moreover have "I i \<inter> I j = {}"
          by (meson \<open>\<And>j i. \<lbrakk>i \<le> l; j \<le> l; i \<noteq> j\<rbrakk> \<Longrightarrow> I i \<inter> I j = {}\<close> \<open>i \<le> l\<close> \<open>i \<noteq> j\<close> \<open>j \<le> l\<close>)
        ultimately have "I' i' \<inter> I' j' = {}"
          by blast
        then have "q i' \<noteq> q j'"
          unfolding I'
          by (metis I' \<open>I i = I' i'\<close> \<open>\<And>i. i \<le> Suc k' \<Longrightarrow> i \<in> I' i\<close> \<open>\<And>thesis. (\<And>i' j'. \<lbrakk>i' \<le> Suc k'; j' \<le> Suc k'; I i = I' i'; I j = I' j'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> empty_iff inf.idem)
        then have "q ii \<noteq> q jj"
          using I' \<open>I i = I' i'\<close> \<open>I j = I' j'\<close> \<open>ii \<in> I i\<close> \<open>jj \<in> I j\<close> by force
        then have "a ii \<noteq> a jj" "a ii \<noteq> b jj" "b ii \<noteq> a jj" "b ii \<noteq> b jj"
          using q_divergence
          by blast+
        then show False
          using \<open>{a ii, b ii} \<inter> {a jj, b jj} \<noteq> {}\<close>
          by blast
      qed
      moreover have "\<forall> i \<in> {..l} . finite (S i)"
        unfolding S
        by (metis (no_types, lifting) \<open>I ` {..l} = I' ` {..Suc k'}\<close> \<open>\<Union> (I' ` {..Suc k'}) = {..Suc k'}\<close> finite.emptyI finite.insertI finite_UN finite_atMost) 
      ultimately have "card (\<Union> i \<in> {..l} . S i) = (\<Sum> i \<in> {..l} . card (S i))"
        using atMost_iff 
        using card_UN_disjoint[OF finite_atMost[of l], of S]
        by blast        
  
      (* 7 *)
      have eq7: "card (\<Union> i \<in> {..Suc k'} . {a i, b i}) = (\<Sum> i \<in> {..l} . card (S i))"
        unfolding \<open>card (\<Union> i \<in> {..l} . S i) = card (\<Union> i \<in> {..Suc k'} . {a i, b i})\<close>[symmetric]
        unfolding \<open>card (\<Union> i \<in> {..l} . S i) = (\<Sum> i \<in> {..l} . card (S i))\<close>
        by blast
  
      (* 8 *)
      have eq8: "\<And> i . i \<le> l \<Longrightarrow> card (S i) \<ge> Suc (card (I i))"
      proof -
        fix i assume "i \<le> l"
        
        have "S i \<subseteq> states M2"
          unfolding S using \<open>\<And> i . a i \<in> states M2\<close> \<open>\<And> i . b i \<in> states M2\<close>
          by blast
        
        define W where W: "W = {w' \<in> set (prefixes w).
                          w' \<noteq> w \<and>
                          after M2 (after_initial M2 u) w' \<in> S i \<and> after M2 (after_initial M2 v) w' \<in> S i}"
  
        have "wk ` I i \<subseteq> W"
        proof 
          fix x assume "x \<in> wk ` I i"
          then obtain i' where "x = wk i'" and "i' \<in> I i"
            by blast
          then have "a i' \<in> S i" and "b i' \<in> S i"
            unfolding S by blast+
          then have "after M2 (after_initial M2 u) (wk i') \<in> S i"
                    "after M2 (after_initial M2 v) (wk i') \<in> S i"
            unfolding a b 
            using \<open>\<And>i. u @ wk i \<in> L M2\<close> \<open>\<And>i. v @ wk i \<in> L M2\<close>
            by (metis  after_split assms(2))+
          moreover have "wk i' \<noteq> w"
            by (metis (no_types) \<open>\<And>i. wk i \<in> set (prefixes wp)\<close> less.prems(2) less.prems(3) nat_le_linear prefixes_take_iff take_all_iff)
          moreover have "wk i' \<in> set (prefixes w)"
            using \<open>\<And>i. wk i \<in> set (prefixes wp)\<close> less.prems(2) prefixes_prefix_subset by blast
          ultimately show "x \<in> W"
            unfolding \<open>x = wk i'\<close> W
            by blast
        qed
        moreover have "finite W"
        proof -
          have "W \<subseteq> (set (prefixes w))"
            unfolding W by blast
          then show ?thesis
            by (meson List.finite_set rev_finite_subset)
        qed
        ultimately have "card (wk ` I i) \<le> card W"
          by (meson card_mono)        
        moreover have "card (wk ` I i) = card (I i)"
        proof -
          have "\<And> x y . x \<in> I i \<Longrightarrow> y \<in> I i \<Longrightarrow> x \<noteq> y \<Longrightarrow> wk x \<noteq> wk y"
          proof -
            fix x y assume "x \<in> I i" "y \<in> I i" "x \<noteq> y"
            then have "x \<le> Suc k'" "y \<le> Suc k'"
              by (metis UN_I \<open>I ` {..l} = I' ` {..Suc k'}\<close> \<open>\<Union> (I' ` {..Suc k'}) = {..Suc k'}\<close> \<open>i \<le> l\<close> atMost_iff)+
            then show "wk x \<noteq> wk y"
              using \<open>x \<noteq> y\<close> \<open>k = length wp\<close> 
              unfolding wk Suc
              using take_diff by metis
          qed
          moreover have "finite (I i)"
            by (metis \<open>I ` {..l} = I' ` {..Suc k'}\<close> \<open>i \<le> l\<close> atMost_iff finite_UN finite_atMost pt6)
          ultimately show ?thesis  
            using image_inj_card_helper by metis
        qed
        ultimately have "card (I i) \<le> card W"
          by simp
        then have "card (I i) \<le> card (S i) - 1"
          using minimally_distinguishes_proper_prefixes_card[OF assms(2,4) after_is_state[OF assms(2) \<open>u \<in> L M2\<close>] after_is_state[OF assms(2) \<open>v \<in> L M2\<close>] \<open>minimally_distinguishes M2 (after_initial M2 u) (after_initial M2 v) w\<close> \<open>S i \<subseteq> states M2\<close>]
          unfolding W[symmetric]
          by simp
        moreover have "card (S i) > 0"
        proof -
          have "card (I i) > 0"
            by (metis \<open>\<And>i. i \<le> l \<Longrightarrow> \<exists>j\<le>Suc k'. I i = I' j\<close> \<open>card (wk ` I i) = card (I i)\<close> \<open>finite W\<close> \<open>i \<le> l\<close> \<open>wk ` I i \<subseteq> W\<close> atMost_iff card_0_eq gr0I image_is_empty pt4 rev_finite_subset)
          then show ?thesis
            unfolding S
            by (metis S calculation diff_le_self le_0_eq not_gr_zero) 
        qed
        ultimately show "card (S i) \<ge> Suc (card (I i))"
          by linarith
      qed
  
      (* 9 *)
      have "(\<Sum> i \<in> {..l} . card (S i)) \<ge> (\<Sum> i \<in> {..l} . (Suc (card (I i))))"
        using eq8
        by (meson atMost_iff sum_mono) 
      moreover have "(\<Sum> i \<in> {..l} . (Suc (card (I i)))) = (Suc l) + k' + 2"
      proof -
        have "(\<Sum> i \<in> {..l} . (Suc (card (I i)))) = (Suc l) + (\<Sum> i \<in> {..l} . (card (I i)))"
          by (simp add: sum_Suc)
        moreover have "(\<Sum> i \<in> {..l} . (card (I i))) = k' + 2"
        proof -
          have "card (\<Union> i \<in> {..l} . I i) = k' + 2"
            using \<open>card (\<Union> i \<in> {..Suc k'} . I' i) = k'+2\<close>
            using \<open>I ` {..l} = I' ` {..Suc k'}\<close> by presburger 
          moreover have "(\<Sum> i \<in> {..l} . (card (I i))) = card (\<Union> i \<in> {..l} . I i)"
            using sum_image_inj_card_helper[of l I]
            by (metis \<open>I ` {..l} = I' ` {..Suc k'}\<close> \<open>\<And>j i. \<lbrakk>i \<le> l; j \<le> l; i \<noteq> j\<rbrakk> \<Longrightarrow> I i \<inter> I j = {}\<close> \<open>\<Union> (I' ` {..Suc k'}) = {..Suc k'}\<close> atMost_iff finite_UN finite_atMost)
          ultimately show ?thesis
            by auto
        qed
        ultimately show ?thesis
          by linarith
      qed
      ultimately have "(\<Sum> i \<in> {..l} . card (S i)) \<ge> k' + l + 3"
        by auto
      moreover have "card (after_initial M2 ` {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes wp)}) = (\<Sum> i \<in> {..l} . card (S i))"
      proof -
        have "after_initial M2 ` {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes wp)} = (\<Union> i \<in> {..l} . S i)"     
        proof -
          have "set (prefixes wp) = {wk i | i . i \<le> k}"
            using less.prems(1) unfolding wk prefixes_set
            by (metis \<open>\<And>i. wk i \<in> set (prefixes wp)\<close> append_eq_conv_conj le_cases prefixes_set_ob take_all wk)
          then have *:"{\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes wp)} = (\<Union> i \<in> {..Suc k'} . {u@wk i, v@wk i})"
            unfolding Suc by auto
          have **: "(\<Union> i \<in> {..Suc k'} . {a i, b i}) = after_initial M2 ` (\<Union> i \<in> {..Suc k'} . {u@wk i, v@wk i})"
            unfolding a b by blast
          show ?thesis
            unfolding \<open>(\<Union> i \<in> {..l} . S i) = (\<Union> i \<in> {..Suc k'} . {a i, b i})\<close> ** * 
            by simp
        qed
        then show ?thesis
          by (simp add: \<open>card (\<Union> (S ` {..l})) = (\<Sum>i\<le>l. card (S i))\<close>)
      qed
      ultimately have bound_l: "card (after_initial M2 ` {\<alpha> @ \<gamma> |\<alpha> \<gamma>. \<alpha> \<in> {u, v} \<and> \<gamma> \<in> set (prefixes wp)}) \<ge> k + l + 2"
        unfolding Suc by simp
  
      have bound_r: "length wp + card (after M1 (after_initial M1 u) ` set (prefixes wp)) + 1 = k + l + 2"
      proof -
        have "set (prefixes wp) = {wk i | i . i \<le> k}"
          using less.prems(1) unfolding wk prefixes_set
          by (metis \<open>\<And>i. wk i \<in> set (prefixes wp)\<close> append_eq_conv_conj le_cases prefixes_set_ob take_all wk)
  
        let ?witness = "\<lambda>i . SOME j . j \<in> i"
        have "\<And> i . i \<in> (I' ` {..Suc k'}) \<Longrightarrow> ?witness i \<in> i"
          using \<open>\<And>i. i \<le> Suc k' \<Longrightarrow> i \<in> I' i\<close> some_in_eq by auto
        have **:"\<And> Ii Ij . Ii \<in> (I' ` {..Suc k'}) \<Longrightarrow> Ij \<in> (I' ` {..Suc k'}) \<Longrightarrow> Ii \<noteq> Ij \<Longrightarrow> ?witness Ii \<noteq> ?witness Ij"
        proof -
          fix Ii Ij assume "Ii \<in> (I' ` {..Suc k'})" and "Ij \<in> (I' ` {..Suc k'})" and "Ii \<noteq> Ij"
          then have "Ii \<inter> Ij = {}"
            using pt5 by auto
          moreover have "?witness Ii \<in> Ii"
            using \<open>\<And> i . i \<in> (I' ` {..Suc k'}) \<Longrightarrow> ?witness i \<in> i\<close> \<open>Ii \<in> (I' ` {..Suc k'})\<close>
            by blast
          moreover have "?witness Ij \<in> Ij"
            using \<open>\<And> i . i \<in> (I' ` {..Suc k'}) \<Longrightarrow> ?witness i \<in> i\<close> \<open>Ij \<in> (I' ` {..Suc k'})\<close>
            by blast
          ultimately show "?witness Ii \<noteq> ?witness Ij"
            by fastforce 
        qed
        have *: "finite (I' ` {..Suc k'})" 
          by auto
  
        
        have c1: "card (I' ` {..Suc k'}) = card (?witness ` (I' ` {..Suc k'}))"
          using image_inj_card_helper[of "I' ` {..Suc k'}" ?witness, OF * **]
          by auto
  
        have *: "finite (?witness ` (I' ` {..Suc k'}))" 
          by auto
        have **:"\<And> i j . i \<in> (?witness ` (I' ` {..Suc k'})) \<Longrightarrow> j \<in> (?witness ` (I' ` {..Suc k'})) \<Longrightarrow> i \<noteq> j \<Longrightarrow> q i \<noteq> q j"
        proof -
          fix i j assume "i \<in> (?witness ` (I' ` {..Suc k'}))" and "j \<in> (?witness ` (I' ` {..Suc k'}))" and "i \<noteq> j"
  
          obtain i' where "i = ?witness (I' i')" and "i \<in> I' i'" and "i' \<in> {..Suc k'}"
            using \<open>i \<in> (?witness ` (I' ` {..Suc k'}))\<close>
            using \<open>\<And>i. i \<in> I' ` {..Suc k'} \<Longrightarrow> (SOME j. j \<in> i) \<in> i\<close> by blast
          obtain j' where "j = ?witness (I' j')" and "j \<in> I' j'" and "j' \<in> {..Suc k'}"
            using \<open>j \<in> (?witness ` (I' ` {..Suc k'}))\<close>
            using \<open>\<And>i. i \<in> I' ` {..Suc k'} \<Longrightarrow> (SOME j. j \<in> i) \<in> i\<close> by blast
  
          have "I' i' \<noteq> I' j'"
            using \<open>i \<noteq> j\<close>
            using \<open>i = (SOME j. j \<in> I' i')\<close> \<open>j = (SOME j. j \<in> I' j')\<close> by fastforce
          then show "q i \<noteq> q j"
            using \<open>i \<in> I' i'\<close> \<open>j \<in> I' j'\<close>
            unfolding q I'
            by force
        qed   
  
        have c2: "card (I' ` {..Suc k'}) = card (q ` (?witness ` (I' ` {..Suc k'})))"
          using image_inj_card_helper[of "(?witness ` (I' ` {..Suc k'}))" q, OF * **] c1 
          by force
  
        have "q ` (?witness ` (I' ` {..Suc k'})) = q ` (\<Union> i \<in> {..Suc k'} . I' i)" 
        proof 
          show "q ` ?witness ` I' ` {..Suc k'} \<subseteq> q ` \<Union> (I' ` {..Suc k'})"
          proof 
            fix s assume "s \<in> q ` ?witness ` I' ` {..Suc k'}"
            then obtain Ii where "Ii \<in> I' ` {..Suc k'}" and "s = q (?witness Ii)"
              by blast
            then have "s \<in> q ` Ii"
              using \<open>\<And>i. i \<in> I' ` {..Suc k'} \<Longrightarrow> (SOME j. j \<in> i) \<in> i\<close> by blast
            then show "s \<in> q ` \<Union> (I' ` {..Suc k'})"
              using \<open>Ii \<in> I' ` {..Suc k'}\<close> by blast
          qed
          show "q ` \<Union> (I' ` {..Suc k'}) \<subseteq> q ` ?witness ` I' ` {..Suc k'}"
          proof 
            fix s assume "s \<in> q ` \<Union> (I' ` {..Suc k'})"
            then obtain i where "s \<in> q ` (I' i)" and "i \<in> {..Suc k'}"
              by blast
  
            have "?witness (I' i) \<in> I' i"
              using \<open>\<And>i. i \<in> I' ` {..Suc k'} \<Longrightarrow> (SOME j. j \<in> i) \<in> i\<close> \<open>i \<in> {..Suc k'}\<close> by blast
            then have "q ` (I' i) = {q (?witness (I' i))}"
              unfolding q I'
              by fastforce 
            then have "s = q (?witness (I' i))"
              using \<open>s \<in> q ` (I' i)\<close> by blast
            then show "s \<in> q ` ?witness ` I' ` {..Suc k'}"
              using \<open>i \<in> {..Suc k'}\<close> by blast
          qed
        qed
        then have c3: "card (I' ` {..Suc k'}) = card (q ` (\<Union> i \<in> {..Suc k'} . I' i))"
          using c2 by auto
  
  
        have "q ` (\<Union> i \<in> {..Suc k'} . I' i) = after M1 (after_initial M1 u) ` set (prefixes wp)"
        proof -
          have "set (prefixes wp) = {wk i | i . i \<le> k}"
            using less.prems(1) unfolding wk prefixes_set
            by (metis \<open>\<And>i. wk i \<in> set (prefixes wp)\<close> append_eq_conv_conj le_cases prefixes_set_ob take_all wk)
          also have "\<dots> = wk ` {..Suc k'}"
            unfolding Suc
            by (simp add: atMost_def setcompr_eq_image) 
          finally have *:"set (prefixes wp) = wk ` {..Suc k'}" .
  
          have "\<And> i . after_initial M1 (u @ wk i) = after M1 (after_initial M1 u) (wk i)"
            by (metis \<open>\<And>i. u @ wk i \<in> L M1\<close> after_split assms(1))
          then have **: "\<And> X . q ` X = after M1 (after_initial M1 u) ` wk ` X"
            unfolding q
            by fastforce 
          
          show ?thesis
            unfolding * **
            unfolding \<open>(\<Union> i \<in> {..Suc k'} . I' i) = {..Suc k'}\<close>
            by simp
        qed
  
        then have "card (I' ` {..Suc k'}) = card (after M1 (after_initial M1 u) ` set (prefixes wp))"
          using c3 by auto
        then have "card (after M1 (after_initial M1 u) ` set (prefixes wp)) = Suc l"
          using \<open>card (I' ` {..Suc k'}) = Suc l\<close>
          by auto
        then show ?thesis
          unfolding \<open>k = length wp\<close>[symmetric] by auto
      qed
  
      show ?thesis
        using bound_l 
        unfolding bound_r .
    qed
  qed
qed


lemma sufficient_condition_for_convergence :
  fixes M1 :: "('a,'b,'c) fsm"
  fixes M2 :: "('d,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
  and     "converge M1 \<pi> \<tau>"
  and     "L M1 \<inter> T = L M2 \<inter> T"
  and     "\<And> \<gamma> x y . length (\<gamma>@[(x,y)]) \<le> m - size_r M1 \<Longrightarrow>
                  \<gamma> \<in> LS M1 (after_initial M1 \<pi>) \<Longrightarrow>
                  x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow>
                  \<exists> SC \<alpha> \<beta> . SC \<subseteq> T 
                              \<and> is_state_cover M1 SC
                              \<and> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))} \<subseteq> SC
                              \<and> converge M1 \<pi> \<alpha>
                              \<and> converge M2 \<pi> \<alpha>
                              \<and> converge M1 \<tau> \<beta>
                              \<and> converge M2 \<tau> \<beta> 
                              \<and> preserves_divergence M1 M2 SC"
  and     "\<exists> SC \<alpha> \<beta> . SC \<subseteq> T 
                      \<and> is_state_cover M1 SC
                      \<and> \<alpha> \<in> SC \<and> \<beta> \<in> SC
                      \<and> converge M1 \<pi> \<alpha>
                      \<and> converge M2 \<pi> \<alpha>
                      \<and> converge M1 \<tau> \<beta>
                      \<and> converge M2 \<tau> \<beta> 
                      \<and> preserves_divergence M1 M2 SC"
shows "converge M2 \<pi> \<tau>"
proof (cases "inputs M1 = {} \<or> outputs M1 = {}")
  case True
  then have "L M1 = {[]}"
    using language_empty_IO by blast
  then have "\<pi> = []" and "\<tau> = []"
    using assms(9) by auto
  then show ?thesis 
    by auto
next
  case False
 
  define n where n: "n = size_r M1"
  have "n \<le> m"
    using assms(5) n by auto

  show ?thesis proof (rule ccontr)
    assume "\<not> converge M2 \<pi> \<tau>"
    moreover have "\<pi> \<in> L M2" and "\<tau> \<in> L M2"
      using assms(12) by auto
    ultimately have "after_initial M2 \<pi> \<noteq> after_initial M2 \<tau>"
      using assms(2) assms(4) convergence_minimal by blast
    then obtain v where "minimally_distinguishes M2 (after_initial M2 \<pi>) (after_initial M2 \<tau>) v"
      using minimally_distinguishes_ex
      by (metis \<open>\<not> converge M2 \<pi> \<tau>\<close> \<open>\<pi> \<in> L M2\<close> \<open>\<tau> \<in> L M2\<close> after_is_state assms(2) converge.simps)
    then have "distinguishes M2 (after_initial M2 \<pi>) (after_initial M2 \<tau>) v"
      unfolding minimally_distinguishes_def by auto
    then have "v \<noteq> []"
      by (meson \<open>\<pi> \<in> L M2\<close> \<open>\<tau> \<in> L M2\<close> after_is_state assms(2) distinguishes_not_Nil) 
  
    have "length v > m - n"
    proof (rule ccontr)
      assume "\<not> m - n < length v"

      have \<open>v \<in> set (prefixes v)\<close>
        unfolding prefixes_set by auto 


      show False proof (cases "v \<in> LS M1 (after_initial M1 \<pi>)")
        case True

        have "v = (butlast v)@[last v]"
          using \<open>v \<noteq> []\<close> by fastforce
        then obtain x y where "v = (butlast v)@[(x,y)]"
          using prod.exhaust by metis 
        then have "(x,y) \<in> set v"
          using in_set_conv_decomp by force
        then have "x \<in> inputs M1" and "y \<in> outputs M1"
          using language_io[OF True, of x y] by auto
        moreover have "length (butlast v @ [(x, y)]) \<le> m - size_r M1"
          using \<open>\<not> m - n < length v\<close> \<open>v = (butlast v)@[(x,y)]\<close> 
          unfolding n by auto
        moreover have "butlast v \<in> LS M1 (after_initial M1 \<pi>)"
          using True language_prefix[of "butlast v" "[(x,y)]"] 
          unfolding \<open>v = (butlast v)@[(x,y)]\<close>[symmetric]
          by metis
        ultimately obtain SC \<alpha> \<beta> where "SC \<subseteq> T"
                             and "{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes v)} \<subseteq> SC"
                             and "converge M1 \<pi> \<alpha>"
                             and "converge M2 \<pi> \<alpha>"
                             and "converge M1 \<tau> \<beta>"
                             and "converge M2 \<tau> \<beta>"
          using assms(11)[of "(butlast v)" x y] 
          unfolding \<open>v = (butlast v)@[(x,y)]\<close>[symmetric]
          by meson

        
        then have "\<alpha>@v \<in> T" and "\<beta>@v \<in> T"
          using \<open>SC \<subseteq> T\<close> \<open>{\<omega>@\<gamma> | \<omega> \<gamma> . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<gamma> \<in> list.set (prefixes v)} \<subseteq> SC\<close> \<open>v \<in> set (prefixes v)\<close>
          by auto

        then have "L M1 \<inter> {\<alpha>@v,\<beta>@v} = L M2 \<inter> {\<alpha>@v,\<beta>@v}"
          using assms(10) by blast

        have "after_initial M1 \<pi> \<noteq> after_initial M1 \<tau>"
          using converge_distinguishable_helper[OF assms(1-4) \<open>converge M1 \<pi> \<alpha>\<close> \<open>converge M2 \<pi> \<alpha>\<close> \<open>converge M1 \<tau> \<beta>\<close> \<open>converge M2 \<tau> \<beta>\<close> \<open>distinguishes M2 (after_initial M2 \<pi>) (after_initial M2 \<tau>) v\<close> \<open>L M1 \<inter> {\<alpha>@v,\<beta>@v} = L M2 \<inter> {\<alpha>@v,\<beta>@v}\<close>] .
        then show False
          using \<open>converge M1 \<pi> \<tau>\<close>
          by (meson assms(1) assms(3) converge.elims(2) convergence_minimal) 
      next
        case False

        obtain io' x' y' io'' where "v = io'@[(x',y')]@io''"
                              and "io' \<in> LS M1 (after_initial M1 \<pi>)"
                              and "io'@[(x',y')] \<notin> LS M1 (after_initial M1 \<pi>)"
          using language_maximal_contained_prefix_ob[OF False _ assms(1)]
          by (metis after_is_state assms(1) assms(9) converge.simps) 

        have "length io' < m - size_r M1"
          using \<open>\<not> m - n < length v\<close> unfolding \<open>v = io'@[(x',y')]@io''\<close> n by auto
        then have "length (io'@[(x',y')]) \<le> m - size_r M1"
          by auto

        have "x' \<in> inputs M1" and "y' \<in> outputs M1"
        proof -
          have "x' \<in> inputs M1 \<and> y' \<in> outputs M1"
          proof -
            have "(x',y') \<in> set v"
              unfolding \<open>v = io'@[(x',y')]@io''\<close> by auto
            then have "(x', y') \<in> set (\<pi> @ v)" and "(x', y') \<in> set (\<tau> @ v)"
              by auto
            have "\<pi>@v \<in> L M2 \<or> \<tau>@v \<in> L M2"
              using \<open>distinguishes M2 (after_initial M2 \<pi>) (after_initial M2 \<tau>) v\<close>
              unfolding distinguishes_def
              by (metis Un_iff \<open>\<pi> \<in> L M2\<close> \<open>\<tau> \<in> L M2\<close> after_language_iff assms(2)) 
            then show ?thesis 
              using language_io[of "\<pi>@v" M2 "initial M2", OF _ \<open>(x', y') \<in> set (\<pi> @ v)\<close>] 
                    language_io[of "\<tau>@v" M2 "initial M2", OF _ \<open>(x', y') \<in> set (\<tau> @ v)\<close>]
              by (metis assms(7) assms(8))
          qed
          then show "x' \<in> inputs M1" and "y' \<in> outputs M1" 
            by auto
        qed
        

        obtain SC \<alpha> \<beta> where "SC \<subseteq> T"
                             and "{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes (io'@[(x',y')]))} \<subseteq> SC"
                             and "converge M1 \<pi> \<alpha>"
                             and "converge M2 \<pi> \<alpha>"
                             and "converge M1 \<tau> \<beta>"
                             and "converge M2 \<tau> \<beta>"
          using assms(11)[of io' x' y', OF \<open>length (io'@[(x',y')]) \<le> m - size_r M1\<close> \<open>io' \<in> LS M1 (after_initial M1 \<pi>)\<close> \<open>x' \<in> inputs M1\<close> \<open>y' \<in> outputs M1\<close>]
          by meson

        show False proof (cases "v \<in> set (prefixes (io'@[(x',y')]))")
          case True
          then have "\<alpha>@v \<in> T" and "\<beta>@v \<in> T"
            using \<open>SC \<subseteq> T\<close> \<open>{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes (io'@[(x',y')]))} \<subseteq> SC\<close> 
            by auto
  
          then have "L M1 \<inter> {\<alpha>@v,\<beta>@v} = L M2 \<inter> {\<alpha>@v,\<beta>@v}"
            using assms(10) by blast
  
          have "after_initial M1 \<pi> \<noteq> after_initial M1 \<tau>"
            using converge_distinguishable_helper[OF assms(1-4) \<open>converge M1 \<pi> \<alpha>\<close> \<open>converge M2 \<pi> \<alpha>\<close> \<open>converge M1 \<tau> \<beta>\<close> \<open>converge M2 \<tau> \<beta>\<close> \<open>distinguishes M2 (after_initial M2 \<pi>) (after_initial M2 \<tau>) v\<close> \<open>L M1 \<inter> {\<alpha>@v,\<beta>@v} = L M2 \<inter> {\<alpha>@v,\<beta>@v}\<close>] .
          then show False
            using \<open>converge M1 \<pi> \<tau>\<close>
            by (meson assms(1) assms(3) converge.elims(2) convergence_minimal) 
        next
          case False
          then obtain io''' io'''' where "io'' = io'''@io''''"
                                     and "v = io'@[(x',y')]@io'''"
                                     and "io''' \<noteq> []"
            using prefixes_prefix_suffix_ob[of v "io'@[(x',y')]" io''] 
            using \<open>v \<in> set (prefixes v)\<close>
            unfolding \<open>v = io'@[(x',y')]@io''\<close>
            by auto  
          then have "io'@[(x',y')] \<in> set (prefixes v)" and "io'@[(x',y')] \<noteq> v"
            unfolding prefixes_set by auto
          then have "io'@[(x',y')] \<in> LS M2 (after_initial M2 \<pi>)"
            using minimally_distinguishes_proper_prefix_in_language[OF \<open>minimally_distinguishes M2 (after_initial M2 \<pi>) (after_initial M2 \<tau>) v\<close>, of "io'@[(x',y')]"]
            by blast
          then have "io'@[(x',y')] \<in> LS M2 (after_initial M2 \<alpha>)"
            using \<open>converge M2 \<pi> \<alpha>\<close> converge.simps by blast
          then have "\<alpha>@(io'@[(x',y')]) \<in> L M2"
            by (meson \<open>converge M2 \<pi> \<alpha>\<close> after_language_iff assms(2) converge.elims(2))
          moreover have "\<alpha>@(io'@[(x',y')]) \<in> T"
            using \<open>{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes (io'@[(x',y')]))} \<subseteq> SC\<close> \<open>SC \<subseteq> T\<close>
            unfolding prefixes_set by force
          moreover have "\<alpha>@(io'@[(x',y')]) \<notin> L M1"
            by (metis \<open>converge M1 \<pi> \<alpha>\<close> \<open>io' @ [(x', y')] \<notin> LS M1 (after_initial M1 \<pi>)\<close> after_language_iff assms(1) converge.elims(2))
          ultimately show False
            using assms(10) by blast
        qed
      qed
    qed

    define vm where vm: "vm = take (m-n) v"
    define v_suffix where v_suffix: "v_suffix = drop (m-n) v"
    have "length vm = m-n" and "vm \<noteq> v"
      using \<open>m - n < length v\<close> unfolding vm by auto
    have "v = vm@v_suffix"
      unfolding vm v_suffix by auto
    then have "vm \<in> set (prefixes v)"
      unfolding prefixes_set by auto

    have "vm \<in> LS M2 (after_initial M2 \<pi>)" and "vm \<in> LS M2 (after_initial M2 \<tau>)"
      using minimally_distinguishes_proper_prefix_in_language[OF \<open>minimally_distinguishes M2 (after_initial M2 \<pi>) (after_initial M2 \<tau>) v\<close> \<open>vm \<in> set (prefixes v)\<close> \<open>vm \<noteq> v\<close>]
      by auto

    
    
    have "vm \<in> LS M1 (after_initial M1 \<pi>)"
    proof (rule ccontr)
      assume False: "vm \<notin> LS M1 (after_initial M1 \<pi>)"

      obtain io' x' y' io'' where "vm = io'@[(x',y')]@io''"
                              and "io' \<in> LS M1 (after_initial M1 \<pi>)"
                              and "io'@[(x',y')] \<notin> LS M1 (after_initial M1 \<pi>)"
        using language_maximal_contained_prefix_ob[OF False _ assms(1)]
        by (metis after_is_state assms(1) assms(9) converge.simps) 

      have "length io' < m - size_r M1"
        using \<open>length vm = m - n\<close> unfolding \<open>vm = io'@[(x',y')]@io''\<close> n by auto
      then have "length (io'@[(x',y')]) \<le> m - size_r M1"
        by auto

      have "x' \<in> inputs M1"
        using \<open>vm \<in> LS M2 (after_initial M2 \<pi>)\<close>
        unfolding \<open>vm = io'@[(x',y')]@io''\<close>
        using language_io[of "io' @ [(x', y')] @ io''" M2 "initial M2" x' y']
        by (metis append_Cons assms(7) in_set_conv_decomp language_io(1)) 

      have "y' \<in> outputs M1"
        using \<open>vm \<in> LS M2 (after_initial M2 \<pi>)\<close>
        unfolding \<open>vm = io'@[(x',y')]@io''\<close>
        using language_io[of "io' @ [(x', y')] @ io''" M2 "initial M2" x' y']
        by (metis append_Cons assms(8) in_set_conv_decomp language_io(2))
       
      

      obtain SC \<alpha> \<beta> where "SC \<subseteq> T"
                           and "{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes (io'@[(x',y')]))} \<subseteq> SC"
                           and "converge M1 \<pi> \<alpha>"
                           and "converge M2 \<pi> \<alpha>"
                           and "converge M1 \<tau> \<beta>"
                           and "converge M2 \<tau> \<beta>"
        using assms(11)[of io' x' y', OF \<open>length (io'@[(x',y')]) \<le> m - size_r M1\<close> \<open>io' \<in> LS M1 (after_initial M1 \<pi>)\<close> \<open>x' \<in> inputs M1\<close> \<open>y' \<in> outputs M1\<close>]
        by meson

      have "io'@[(x',y')] \<in> LS M2 (after_initial M2 \<pi>)"
        using \<open>vm \<in> LS M2 (after_initial M2 \<pi>)\<close> language_prefix unfolding \<open>vm = io'@[(x',y')]@io''\<close>
        by (metis append_assoc)
      then have "\<alpha>@(io'@[(x',y')]) \<in> L M2"
        by (metis \<open>converge M2 \<pi> \<alpha>\<close> after_language_iff assms(2) converge.simps)
      moreover have "\<alpha>@(io'@[(x',y')]) \<in> T"
        using \<open>{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes (io'@[(x',y')]))} \<subseteq> SC\<close> \<open>SC \<subseteq> T\<close>
        unfolding prefixes_set by force
      moreover have "\<alpha>@(io'@[(x',y')]) \<notin> L M1"
        by (metis \<open>converge M1 \<pi> \<alpha>\<close> \<open>io' @ [(x', y')] \<notin> LS M1 (after_initial M1 \<pi>)\<close> after_language_iff assms(1) converge.elims(2)) 
      ultimately show False 
        using assms(10) by blast
    qed

    obtain SC \<alpha> \<beta> where "SC \<subseteq> T"
                         and "is_state_cover M1 SC"
                         and "{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes vm)} \<subseteq> SC"
                         and "converge M1 \<pi> \<alpha>"
                         and "converge M2 \<pi> \<alpha>"
                         and "converge M1 \<tau> \<beta>"
                         and "converge M2 \<tau> \<beta>"
                         and "preserves_divergence M1 M2 SC"
    proof (cases vm rule: rev_cases)
      case Nil
      then have "list.set (prefixes vm) = {[]}"
        by auto
      then have "\<And> \<alpha> \<beta> . {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes vm)} = {\<alpha>,\<beta>}"
        by blast
      then show ?thesis using assms(12) that
        by force
    next
      case (snoc blvm lvm)
      then obtain x y where "vm = blvm@[(x,y)]"
        using prod.exhaust by metis

      have *:"length (blvm@[(x,y)]) \<le> m - size_r M1"
        using \<open>length vm = m - n\<close> \<open>vm = blvm @ [(x, y)]\<close> n by fastforce
      have **:"blvm \<in> LS M1 (after_initial M1 \<pi>)"
        using \<open>vm = blvm @ [(x, y)]\<close> language_prefix \<open>vm \<in> LS M1 (after_initial M1 \<pi>)\<close>
        by metis
      have ***:"x \<in> inputs M1" and ****:"y \<in> outputs M1"
        using language_io[OF \<open>vm \<in> LS M1 (after_initial M1 \<pi>)\<close>, of x y]
        unfolding \<open>vm = blvm @ [(x, y)]\<close> by auto
      show ?thesis
        using assms(11)[OF * ** *** ****] that 
        unfolding \<open>vm = blvm @ [(x, y)]\<close>[symmetric] by force
    qed
      

    have "vm \<in> LS M1 (after_initial M1 \<alpha>) \<inter> LS M1 (after_initial M1 \<beta>)"
      using \<open>converge M1 \<pi> \<alpha>\<close> \<open>converge M1 \<pi> \<tau>\<close> \<open>converge M1 \<tau> \<beta>\<close> \<open>vm \<in> LS M1 (after_initial M1 \<pi>)\<close> by auto
    then have "vm \<in> LS M1 (after_initial M1 \<alpha>)" by blast
    have "\<alpha> \<in> L M2"
      using \<open>converge M2 \<pi> \<alpha>\<close> by auto
    have "\<beta> \<in> L M2"
      using \<open>converge M2 \<tau> \<beta>\<close> by auto
    have "minimally_distinguishes M2 (after_initial M2 \<alpha>) (after_initial M2 \<beta>) v"
      using \<open>minimally_distinguishes M2 (after_initial M2 \<pi>) (after_initial M2 \<tau>) v\<close>
      by (metis \<open>\<alpha> \<in> L M2\<close> \<open>\<beta> \<in> L M2\<close> \<open>\<pi> \<in> L M2\<close> \<open>\<tau> \<in> L M2\<close> \<open>converge M2 \<pi> \<alpha>\<close> \<open>converge M2 \<tau> \<beta>\<close> assms(2) assms(4) convergence_minimal) 

    have "converge M1 \<alpha> \<beta>"
      using \<open>converge M1 \<pi> \<alpha>\<close> \<open>converge M1 \<tau> \<beta>\<close> assms(9) by auto
    have "\<not>converge M2 \<alpha> \<beta>"
      using \<open>converge M2 \<pi> \<alpha>\<close> \<open>converge M2 \<tau> \<beta>\<close> \<open>\<not>converge M2 \<pi> \<tau>\<close> by auto

      

    have "preserves_divergence M1 M2 {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes vm)}"
      using \<open>{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes vm)} \<subseteq> SC\<close> \<open>preserves_divergence M1 M2 SC\<close> 
      unfolding preserves_divergence.simps by blast

    have "L M1 \<inter> {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)} = L M2 \<inter> {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}"
      using \<open>{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes vm)} \<subseteq> SC\<close> \<open>SC \<subseteq> T\<close> assms(10)
      by blast

    have card_geq: "card (after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}) \<ge> (m-n) + card (after M1 (after_initial M1 \<alpha>) ` set (prefixes vm)) + 1"
      using preserves_divergence_minimally_distinguishing_prefixes_lower_bound[OF assms(1-4) \<open>converge M1 \<alpha> \<beta>\<close> \<open>\<not>converge M2 \<alpha> \<beta>\<close> \<open>\<alpha> \<in> L M2\<close> \<open>\<beta> \<in> L M2\<close> \<open>minimally_distinguishes M2 (after_initial M2 \<alpha>) (after_initial M2 \<beta>) v\<close> \<open>vm \<in> set (prefixes v)\<close> \<open>vm \<noteq> v\<close> \<open>vm \<in> LS M1 (after_initial M1 \<alpha>) \<inter> LS M1 (after_initial M1 \<beta>)\<close> \<open>preserves_divergence M1 M2 {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>,\<beta>} \<and> \<omega>' \<in> list.set (prefixes vm)}\<close> \<open>L M1 \<inter> {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)} = L M2 \<inter> {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}\<close>]
      unfolding \<open>length vm = m-n\<close> .

    have "after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)} \<subseteq> states M2"
    proof 
      fix q assume "q \<in> after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}"
      then obtain w1 w2 where "q = after_initial M2 (w1@w2)"
                          and "w1 \<in> {\<alpha>,\<beta>}"
                          and "w2 \<in> set (prefixes vm)"
        by blast

      have "w2 \<in> LS M2 (after_initial M2 \<alpha>)"
        using \<open>w2 \<in> set (prefixes vm)\<close> unfolding prefixes_set
        by (metis \<open>converge M2 \<pi> \<alpha>\<close> \<open>vm \<in> LS M2 (after_initial M2 \<pi>)\<close> \<open>w2 \<in> set (prefixes vm)\<close> converge.elims(2) language_prefix prefixes_set_ob)
      then have "after_initial M2 (\<alpha>@w2) \<in> states M2"
        by (meson \<open>\<alpha> \<in> L M2\<close> after_is_state after_language_iff assms(2)) 

      have "w2 \<in> LS M2 (after_initial M2 \<beta>)"
        using \<open>w2 \<in> set (prefixes vm)\<close> unfolding prefixes_set
        by (metis \<open>converge M2 \<tau> \<beta>\<close> \<open>vm \<in> LS M2 (after_initial M2 \<tau>)\<close> \<open>w2 \<in> set (prefixes vm)\<close> converge.elims(2) language_prefix prefixes_set_ob)
      then have "after_initial M2 (\<beta>@w2) \<in> states M2"
        by (meson \<open>\<beta> \<in> L M2\<close> after_is_state after_language_iff assms(2)) 

      show "q \<in> states M2"
        unfolding \<open>q = after_initial M2 (w1@w2)\<close>
        using \<open>w1 \<in> {\<alpha>,\<beta>}\<close> \<open>after_initial M2 (\<alpha>@w2) \<in> states M2\<close> \<open>after_initial M2 (\<beta>@w2) \<in> states M2\<close>
        by blast
    qed
    have upper_bound: "card (after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}) \<le> m"
    proof -
      have "card (after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}) \<le> size M2"
        using \<open>after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)} \<subseteq> states M2\<close>
        using fsm_states_finite[of M2] unfolding FSM.size_def
        by (simp add: card_mono)
      then show ?thesis
        using \<open>size M2 \<le> m\<close> by linarith
    qed

    have "after M1 (after_initial M1 \<alpha>) ` set (prefixes vm) \<subseteq> reachable_states M1"
    proof 
      fix q assume "q \<in> after M1 (after_initial M1 \<alpha>) ` set (prefixes vm)"
      then obtain vm' where "q = after M1 (after_initial M1 \<alpha>) vm'" and "vm' \<in> set (prefixes vm)"
        by auto

      have "vm' \<in> LS M1 (after_initial M1 \<alpha>)"
        using \<open>vm' \<in> set (prefixes vm)\<close> unfolding prefixes_set
        by (metis \<open>vm \<in> LS M1 (after_initial M1 \<alpha>)\<close> \<open>vm' \<in> set (prefixes vm)\<close> language_prefix prefixes_set_ob)
      then have "\<alpha>@vm' \<in> L M1"
        by (meson \<open>converge M1 \<pi> \<alpha>\<close> after_language_iff assms(1) converge.simps)
      moreover have "q = after_initial M1 (\<alpha>@vm')"
        unfolding \<open>q = after M1 (after_initial M1 \<alpha>) vm'\<close>
        by (meson after_split assms(1) calculation) 
      ultimately show "q \<in> reachable_states M1"
        using after_reachable_initial[OF assms(1)] by auto
    qed
    moreover have "finite (reachable_states M1)"
      using fsm_states_finite[of M1] reachable_state_is_state[of _ M1]
      by (metis fsm_states_finite restrict_to_reachable_states_simps(2))
    ultimately have "card (after M1 (after_initial M1 \<alpha>) ` set (prefixes vm)) \<le> n"
      unfolding n
      by (metis card_mono)       
    

    have "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> \<exists> io \<in> SC. q \<in> io_targets M1 io (FSM.initial M1)"
      using \<open>is_state_cover M1 SC\<close>
      by auto

    obtain V where "is_state_cover_assignment M1 V"
               and "\<And>q. q \<in> reachable_states M1 \<Longrightarrow> V q \<in> SC"
      using state_cover_assignment_from_state_cover[OF \<open>is_state_cover M1 SC\<close>]
      by blast

    define unreached_states where unreached_states: "unreached_states = reachable_states M1 - (after M1 (after_initial M1 \<alpha>) ` set (prefixes vm))"
    
    have "size_r M1 = card (after M1 (after_initial M1 \<alpha>) ` set (prefixes vm)) + card unreached_states"
      by (metis \<open>after M1 (after_initial M1 \<alpha>) ` set (prefixes vm) \<subseteq> reachable_states M1\<close> \<open>card (after M1 (after_initial M1 \<alpha>) ` set (prefixes vm)) \<le> n\<close> \<open>finite (reachable_states M1)\<close> card_Diff_subset le_add_diff_inverse n rev_finite_subset unreached_states)
      
    have unreached_V: "\<And> q . q \<in> unreached_states \<Longrightarrow> V q \<in> L M1 \<and> V q \<in> L M2 \<and> V q \<in> SC"
    proof -
      fix q assume "q \<in> unreached_states"
      then have "q \<in> reachable_states M1"
        unfolding unreached_states by auto
      then have "after_initial M1 (V q) = q"
        using is_state_cover_assignment_observable_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
        by auto

      have "V q \<in> L M1"
        using is_state_cover_assignment_language[OF \<open>is_state_cover_assignment M1 V\<close>] \<open>q \<in> reachable_states M1\<close> 
        by auto
      moreover have "V q \<in> T" and "V q \<in> SC" 
        using \<open>\<And>q. q \<in> reachable_states M1 \<Longrightarrow> V q \<in> SC\<close> \<open>q \<in> reachable_states M1\<close>  \<open>SC \<subseteq> T\<close>
        by auto
      ultimately have "V q \<in> L M2" 
        by (metis Int_iff assms(10))

      show "V q \<in> L M1 \<and> V q \<in> L M2 \<and> V q \<in> SC"
        using \<open>V q \<in> L M1\<close> \<open>V q \<in> L M2\<close> \<open>V q \<in> SC\<close> by auto 
    qed

    have "\<And> q1 q2 . q1 \<in> unreached_states \<Longrightarrow> q2 \<in> unreached_states \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> after_initial M2 (V q1) \<noteq> after_initial M2 (V q2)"
    proof -
      fix q1 q2 assume "q1 \<in> unreached_states" and "q2 \<in> unreached_states" and "q1 \<noteq> q2"

      then have "q1 \<in> reachable_states M1" and "q2 \<in> reachable_states M1"
        unfolding unreached_states by auto
      then have "after_initial M1 (V q1) = q1" and "after_initial M1 (V q2) = q2"
        using is_state_cover_assignment_observable_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
        by auto
      then have "V q1 \<noteq> V q2"
        using  \<open>q1 \<noteq> q2\<close>
        by metis

      have "V q1 \<in> L M1" and "V q2 \<in> L M1"
        using is_state_cover_assignment_language[OF \<open>is_state_cover_assignment M1 V\<close>] \<open>q1 \<in> reachable_states M1\<close> \<open>q2 \<in> reachable_states M1\<close>
        by auto
      moreover have "V q1 \<in> T" and "V q2 \<in> T" and "V q1 \<in> SC" and "V q2 \<in> SC"
        using \<open>\<And>q. q \<in> reachable_states M1 \<Longrightarrow> V q \<in> SC\<close> \<open>q1 \<in> reachable_states M1\<close> \<open>q2 \<in> reachable_states M1\<close> \<open>SC \<subseteq> T\<close>
        by auto
      ultimately have "V q1 \<in> L M2" and "V q2 \<in> L M2"
        by (metis Int_iff assms(10))+
      
      have "\<not>converge M1 (V q1) (V q2)"
        by (meson \<open>is_state_cover_assignment M1 V\<close> \<open>q1 \<in> reachable_states M1\<close> \<open>q1 \<noteq> q2\<close> \<open>q2 \<in> reachable_states M1\<close> assms(1) assms(3) state_cover_assignment_diverges) 
      then have "\<not>converge M2 (V q1) (V q2)"
        using \<open>V q1 \<in> L M1\<close> \<open>V q2 \<in> L M1\<close> \<open>V q1 \<in> SC\<close> \<open>V q2 \<in> SC\<close> \<open>preserves_divergence M1 M2 SC\<close>
        unfolding preserves_divergence.simps by blast
      then have "after_initial M2 (V q1) \<noteq> after_initial M2 (V q2)"
        using \<open>V q1 \<in> L M2\<close> \<open>V q2 \<in> L M2\<close>
        using assms(2) assms(4) convergence_minimal by blast 
      then show "after_initial M2 (V q1) \<noteq> after_initial M2 (V q2)"
        by auto
    qed


    have lower_bound: "size M2 \<ge> card (after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}) + card unreached_states"
    proof -
      have "finite unreached_states"
        by (simp add: \<open>finite (reachable_states M1)\<close> unreached_states)
      then have "finite ((\<lambda> q . after_initial M2 (V q)) ` unreached_states)"
        by simp 
      
      have "card unreached_states = card ((\<lambda> q . after_initial M2 (V q)) ` unreached_states)"
        using image_inj_card_helper[of unreached_states "(\<lambda> q . after_initial M2 (V q))", OF \<open>finite unreached_states\<close> \<open>\<And> q1 q2 . q1 \<in> unreached_states \<Longrightarrow> q2 \<in> unreached_states \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> after_initial M2 (V q1) \<noteq> after_initial M2 (V q2)\<close>]
        by auto

      have card_helper: "\<And> A B C . A \<inter> B = {} \<Longrightarrow> A \<subseteq> C \<Longrightarrow> B \<subseteq> C \<Longrightarrow> finite C \<Longrightarrow> card C \<ge> card A + card B"
        by (metis Int_Un_distrib card_Un_disjoint card_mono finite_subset inf.absorb_iff2)
      
      have "\<And> q . q \<in> unreached_states \<Longrightarrow> after_initial M2 (V q) \<notin> (after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)})"
      proof 
        fix q assume "q \<in> unreached_states"
                 and "after_initial M2 (V q) \<in> after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}"

        then obtain w1 w2 where "after_initial M2 (V q) = after_initial M2 (w1@w2)"
                            and "w1 \<in> {\<alpha>,\<beta>}"
                            and "w2 \<in> set (prefixes vm)"
          by blast
        then have "(w1@w2) \<in> SC"
          using \<open>{\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha>, \<beta>} \<and> \<omega>' \<in> set (prefixes vm)} \<subseteq> SC\<close> by blast

        have "w2 \<in> LS M2 (after_initial M2 \<alpha>)"
          using \<open>w2 \<in> set (prefixes vm)\<close> unfolding prefixes_set
          by (metis \<open>converge M2 \<pi> \<alpha>\<close> \<open>vm \<in> LS M2 (after_initial M2 \<pi>)\<close> \<open>w2 \<in> set (prefixes vm)\<close> converge.elims(2) language_prefix prefixes_set_ob)
        moreover have "w2 \<in> LS M2 (after_initial M2 \<beta>)"
          using \<open>w2 \<in> set (prefixes vm)\<close> unfolding prefixes_set
          by (metis \<open>converge M2 \<tau> \<beta>\<close> \<open>vm \<in> LS M2 (after_initial M2 \<tau>)\<close> \<open>w2 \<in> set (prefixes vm)\<close> converge.elims(2) language_prefix prefixes_set_ob)
        ultimately have "w1@w2 \<in> L M2"
          using \<open>w1 \<in> {\<alpha>,\<beta>}\<close>
          by (metis \<open>converge M2 \<pi> \<alpha>\<close> \<open>converge M2 \<tau> \<beta>\<close> after_language_iff assms(2) converge.simps empty_iff insert_iff) 
        then have "converge M2 (V q) (w1@w2)"
          using unreached_V[OF \<open>q \<in> unreached_states\<close>]
          using \<open>after_initial M2 (V q) = after_initial M2 (w1 @ w2)\<close> assms(2) assms(4) convergence_minimal by blast
        moreover have "\<not>converge M1 (V q) (w1@w2)"
        proof -
          have "after M1 (after_initial M1 \<alpha>) w2 = after M1 (after_initial M1 \<beta>) w2"
            by (metis \<open>converge M1 \<alpha> \<beta>\<close> assms(1) assms(3) converge.simps convergence_minimal)
          then have "q \<noteq> (after M1 (after_initial M1 w1) w2)"
            using \<open>q \<in> unreached_states\<close>  \<open>w1 \<in> {\<alpha>,\<beta>}\<close>
            unfolding unreached_states
            by (metis DiffD2 \<open>w2 \<in> set (prefixes vm)\<close> image_eqI insert_iff singletonD)
          moreover have "(after M1 (after_initial M1 w1) w2) = (after_initial M1 (w1@w2))"
            by (metis (no_types, lifting) Int_iff \<open>SC \<subseteq> T\<close> \<open>w1 @ w2 \<in> L M2\<close> \<open>w1 @ w2 \<in> SC\<close> after_split assms(1) assms(10) in_mono)
          moreover have "q = after_initial M1 (V q)"
            using is_state_cover_assignment_observable_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>] \<open>q \<in> unreached_states\<close>
            unfolding unreached_states
            by (metis Diff_iff) 
          ultimately show ?thesis
            by (metis assms(1) assms(3) converge.elims(2) convergence_minimal)
        qed
        moreover have "V q \<in> L M1 \<inter> SC"
          using unreached_V[OF \<open>q \<in> unreached_states\<close>] by auto
        moreover have "w1@w2 \<in> L M1 \<inter> SC"
          using \<open>SC \<subseteq> T\<close> \<open>w1 @ w2 \<in> L M2\<close> \<open>w1 @ w2 \<in> SC\<close> assms(10) by auto
        ultimately show False
          using \<open>preserves_divergence M1 M2 SC\<close>
          unfolding preserves_divergence.simps 
          by blast
      qed
      then have *: "((\<lambda> q . after_initial M2 (V q)) ` unreached_states) \<inter> (after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}) = {}"
        by blast
      
      have **: "((\<lambda> q . after_initial M2 (V q)) ` unreached_states) \<subseteq> states M2"
        using unreached_V
        by (meson after_is_state assms(2) image_subset_iff)
      moreover note \<open>(after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}) \<subseteq> states M2\<close>

      show ?thesis 
        unfolding \<open>card unreached_states = card ((\<lambda> q . after_initial M2 (V q)) ` unreached_states)\<close> FSM.size_def
        using card_helper[OF * ** \<open>(after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}) \<subseteq> states M2\<close> fsm_states_finite[of M2] ]
        by linarith
    qed

    moreover have card_geq_unreached: "card (after_initial M2 ` {\<alpha>' @ \<gamma> |\<alpha>' \<gamma>. \<alpha>' \<in> {\<alpha>, \<beta>} \<and> \<gamma> \<in> set (prefixes vm)}) + card unreached_states \<ge> m + 1"
      using card_geq
      using \<open>size_r M1 \<le> m\<close>
      unfolding n
      unfolding \<open>size_r M1 = card (after M1 (after_initial M1 \<alpha>) ` set (prefixes vm)) + card unreached_states\<close>
      by linarith

    ultimately have "size M2 \<ge> m + 1"
      by linarith
    then show False
      using \<open>size M2 \<le> m\<close>
      by linarith
  qed
qed


(* A variation on the previous condition that does not require the existence of a particular state
   cover but instead requires passing of a certain set of traces. *) 
lemma establish_convergence_from_pass : 
  assumes "observable M1"
      and "observable M2"
      and "minimal M1"
      and "minimal M2"
      and "size_r M1 \<le> m"
      and "size M2 \<le> m"
      and "inputs M2 = inputs M1"
      and "outputs M2 = outputs M1"
      and "is_state_cover_assignment M1 V"
      and "L M1 \<inter> (V ` reachable_states M1) = L M2 \<inter> V ` reachable_states M1"
      and "converge M1 u v"
      and "u \<in> L M2"
      and "v \<in> L M2"
      and prop1: "\<And>\<gamma> x y.
                       length (\<gamma> @ [(x, y)]) \<le> (m - size_r M1) \<Longrightarrow>
                       \<gamma> \<in> LS M1 (after_initial M1 u) \<Longrightarrow>
                       x \<in> FSM.inputs M1 \<Longrightarrow>
                       y \<in> FSM.outputs M1 \<Longrightarrow>
                       L M1 \<inter> ((V ` reachable_states M1) \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) =
                       L M2 \<inter> ((V ` reachable_states M1) \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<and>
                       preserves_divergence M1 M2 ((V ` reachable_states M1) \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
      and prop2: "preserves_divergence M1 M2 ((V ` reachable_states M1) \<union> {u, v})"
shows "converge M2 u v"    
proof -

  define language_up_to_depth where language_up_to_depth: "language_up_to_depth = {\<gamma> . \<gamma> \<in> LS M1 (after_initial M1 u) \<and> length \<gamma> < (m - size_r M1)}"

  define T1 where T1: "T1 = \<Union>{((V ` reachable_states M1) \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) | \<gamma> x y . length (\<gamma> @ [(x, y)]) \<le> (m - size_r M1) \<and> \<gamma> \<in> LS M1 (after_initial M1 u) \<and> x \<in> inputs M1 \<and> y \<in> outputs M1}"
  define T2 where T2: "T2 = ((V ` reachable_states M1) \<union> {u, v})"

  define T where T: "T = T1 \<union> T2"

  have union_intersection_helper: "\<And> A B C . (A \<inter> \<Union>C = B \<inter> \<Union>C) = (\<forall>C' \<in> C . A \<inter> C' = B \<inter> C')"
    by blast

  have "L M1 \<inter> T = L M2 \<inter> T"
  proof -
    have "(L M1 \<inter> T1 = L M2 \<inter> T1)"
      unfolding T1 union_intersection_helper
      using prop1 by blast
    moreover have "L M1 \<inter> T2 = L M2 \<inter> T2"
    proof-
      have "u \<in> L M1" and "v \<in> L M1"
        using \<open>converge M1 u v\<close> by auto
      moreover note \<open>L M1 \<inter> (V ` reachable_states M1) = L M2 \<inter> V ` reachable_states M1\<close> \<open>u \<in> L M2\<close> \<open>v \<in> L M2\<close>
      ultimately show ?thesis
        unfolding T2 by blast
    qed
    ultimately show ?thesis 
      unfolding T by blast
  qed

  have prop1': "(\<And>\<gamma> x y.
    length (\<gamma> @ [(x, y)]) \<le> m - size_r M1 \<Longrightarrow>
    \<gamma> \<in> LS M1 (after_initial M1 u) \<Longrightarrow>
    x \<in> FSM.inputs M1 \<Longrightarrow>
    y \<in> FSM.outputs M1 \<Longrightarrow>
    \<exists>SC \<alpha> \<beta>.
       SC \<subseteq> T \<and>
       is_state_cover M1 SC \<and>
       {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha>, \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))} \<subseteq> SC \<and>
       converge M1 u \<alpha> \<and> converge M2 u \<alpha> \<and> converge M1 v \<beta> \<and> converge M2 v \<beta> \<and> preserves_divergence M1 M2 SC)"
  proof -
    fix \<gamma> x y

    define SC where SC: "SC = ((V ` reachable_states M1) \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"

    assume "length (\<gamma> @ [(x, y)]) \<le> m - size_r M1"
           "\<gamma> \<in> LS M1 (after_initial M1 u)"
           "x \<in> FSM.inputs M1"
           "y \<in> FSM.outputs M1"

    then have "L M1 \<inter> SC = L M2 \<inter> SC"
              "preserves_divergence M1 M2 SC"
      using prop1[of \<gamma> x y]
      unfolding SC
      by blast+

    have "SC \<subseteq> T"
      unfolding T T1 SC
      using \<open>length (\<gamma> @ [(x, y)]) \<le> m - size_r M1\<close> \<open>\<gamma> \<in> LS M1 (after_initial M1 u)\<close> \<open>x \<in> FSM.inputs M1\<close> \<open>y \<in> FSM.outputs M1\<close> 
      by blast
    moreover have "is_state_cover M1 SC"
    proof -
      have "is_state_cover M1 (V ` reachable_states M1)"
        using \<open>is_state_cover_assignment M1 V\<close>
        by (metis is_minimal_state_cover.simps minimal_state_cover_is_state_cover) 
      moreover have "(V ` reachable_states M1) \<subseteq> SC"
        unfolding SC
        by blast
      ultimately show ?thesis
        unfolding is_state_cover.simps by blast
    qed
    moreover have "{\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))} \<subseteq> SC"
      unfolding SC by auto
    moreover have "converge M1 u u"
      using \<open>converge M1 u v\<close> by auto
    moreover have "converge M1 v v"
      using \<open>converge M1 u v\<close> by auto
    moreover have "converge M2 u u"
      using \<open>u \<in> L M2\<close> by auto
    moreover have "converge M2 v v"
      using \<open>v \<in> L M2\<close> by auto
    moreover note \<open>preserves_divergence M1 M2 SC\<close>
    ultimately show "\<exists>SC \<alpha> \<beta>.
       SC \<subseteq> T \<and>
       is_state_cover M1 SC \<and>
       {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha>, \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))} \<subseteq> SC \<and>
       converge M1 u \<alpha> \<and> converge M2 u \<alpha> \<and> converge M1 v \<beta> \<and> converge M2 v \<beta> \<and> preserves_divergence M1 M2 SC"
      by blast
  qed

  have prop2': "\<exists>SC \<alpha> \<beta>.
   SC \<subseteq> T \<and>
   is_state_cover M1 SC \<and>
   \<alpha> \<in> SC \<and> \<beta> \<in> SC \<and> converge M1 u \<alpha> \<and> converge M2 u \<alpha> \<and> converge M1 v \<beta> \<and> converge M2 v \<beta> \<and> preserves_divergence M1 M2 SC"
  proof -
    define SC where SC: "SC = ((V ` reachable_states M1) \<union> {u, v})"
    have "SC \<subseteq> T"
      unfolding T T2 SC by auto
    moreover have "is_state_cover M1 SC"
    proof -
      have "is_state_cover M1 (V ` reachable_states M1)"
        using \<open>is_state_cover_assignment M1 V\<close>
        by (metis is_minimal_state_cover.simps minimal_state_cover_is_state_cover) 
      moreover have "(V ` reachable_states M1) \<subseteq> SC"
        unfolding SC
        by blast
      ultimately show ?thesis
        unfolding is_state_cover.simps by blast
    qed
    moreover have "u \<in> SC" and "v \<in> SC"
      unfolding SC by auto
    moreover have "converge M1 u u"
      using \<open>converge M1 u v\<close> by auto
    moreover have "converge M1 v v"
      using \<open>converge M1 u v\<close> by auto
    moreover have "converge M2 u u"
      using \<open>u \<in> L M2\<close> by auto
    moreover have "converge M2 v v"
      using \<open>v \<in> L M2\<close> by auto
    moreover have \<open>preserves_divergence M1 M2 SC\<close>
      using prop2 unfolding SC .
    ultimately show ?thesis 
      by blast
  qed
      
  show "converge M2 u v"
    using sufficient_condition_for_convergence[OF assms(1-8,11) \<open>L M1 \<inter> T = L M2 \<inter> T\<close> prop1' prop2']
    by blast
qed



subsection \<open>Proving Language Equivalence by Establishing a Convergence Preserving Initialised Transition Cover\<close>

(* adapted to partial nondeterministic FSMs - now requires all IO pairs to be applied after each reachable state *)
definition transition_cover :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "transition_cover M A = (\<forall> q \<in> reachable_states M . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . \<exists> \<alpha>. \<alpha> \<in> A \<and> \<alpha>@[(x,y)] \<in> A \<and> \<alpha> \<in> L M \<and> after_initial M \<alpha> = q)"   
  

lemma initialised_convergence_preserving_transition_cover_is_complete :
  fixes M1 :: "('a,'b,'c) fsm"
  fixes M2 :: "('d,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2" 
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
  and     "L M1 \<inter> T = L M2 \<inter> T"
  and     "A \<subseteq> T"
  and     "transition_cover M1 A"
  and     "[] \<in> A"
  and     "preserves_convergence M1 M2 A"
shows "L M1 = L M2"
proof -

  have convergence_right: "\<And> \<alpha> \<beta> . \<alpha> \<in> A \<Longrightarrow> converge M1 \<alpha> \<beta> \<Longrightarrow> converge M2 \<alpha> \<beta>"
  proof -
    fix \<alpha> \<beta>
    assume "\<alpha> \<in> A" and "converge M1 \<alpha> \<beta>"

    then show "converge M2 \<alpha> \<beta>"
    proof (induction \<beta> arbitrary: \<alpha> rule: rev_induct)
      case Nil
      then have "\<alpha> \<in> L M1 \<inter> A"
        by auto
      moreover have "[] \<in> L M1 \<inter> A"
        using \<open>[] \<in> A\<close> 
        by auto
      ultimately show ?case
        using \<open>preserves_convergence M1 M2 A\<close> \<open>converge M1 \<alpha> []\<close>
        unfolding preserves_convergence.simps
        by blast
    next
      case (snoc xy \<beta>)

      obtain x y where "xy = (x,y)"
        by force


      have "\<alpha> \<in> L M1" 
      and  "\<beta> @ [(x,y)] \<in> L M1"
      and  "LS M1 (after_initial M1 \<alpha>) = LS M1 (after_initial M1 (\<beta> @ [(x,y)]))"
        using snoc unfolding \<open>xy = (x,y)\<close>
        by auto
      then have "\<beta> \<in> L M1"
        using language_prefix by metis
      then have "after_initial M1 \<beta> \<in> reachable_states M1"
        using after_reachable[OF \<open>observable M1\<close> _ reachable_states_initial]
        by metis
      moreover have "x \<in> inputs M1" and "y \<in> outputs M1"
        using language_io[OF \<open>\<beta> @ [(x,y)] \<in> L M1\<close>] by auto
      ultimately obtain \<gamma> where "\<gamma> \<in> A"
                            and "\<gamma> @ [(x, y)] \<in> A" 
                            and "\<gamma> \<in> L M1" 
                            and "after_initial M1 \<gamma> = after_initial M1 \<beta>"
        using \<open>transition_cover M1 A\<close> 
        unfolding transition_cover_def
        by blast
      then have "converge M1 \<gamma> \<beta>"
        using \<open>\<beta> \<in> L M1\<close> 
        by auto
      then have "converge M2 \<gamma> \<beta>"
        using snoc.IH[OF \<open>\<gamma> \<in> A\<close>]
        by simp
      then have "\<beta> \<in> L M2"
        by auto

      have "converge M1 \<beta> \<gamma>"
        using \<open>converge M1 \<gamma> \<beta>\<close> by auto
      then have "converge M1 (\<beta> @ [(x, y)]) (\<gamma> @ [(x, y)])"
        using converge_append[OF assms(1) _ \<open>\<beta> @ [(x,y)] \<in> L M1\<close> \<open>\<gamma> \<in> L M1\<close>]
        by auto
      then have "\<gamma> @ [(x, y)] \<in> L M1"        
        by auto
      then have "\<gamma> @ [(x, y)] \<in> L M2"
        using \<open>\<gamma> @ [(x, y)] \<in> A\<close> assms(7,8)
        by blast
      then have "converge M2 (\<beta> @ [(x, y)]) (\<gamma> @ [(x, y)])"
        using converge_append[OF assms(2) \<open>converge M2 \<gamma> \<beta>\<close> _ \<open>\<beta> \<in> L M2\<close>]
        by auto
      
      have "converge M1 \<alpha> (\<gamma> @ [(x, y)])"
        using \<open>converge M1 (\<beta> @ [(x, y)]) (\<gamma> @ [(x, y)])\<close>
        using \<open>converge M1 \<alpha> (\<beta> @ [xy])\<close>
        unfolding \<open>xy = (x,y)\<close>
        by auto
      then have "converge M2 \<alpha> (\<gamma> @ [(x, y)])"
        using \<open>\<alpha> \<in> A\<close> \<open>\<gamma> @ [(x, y)] \<in> A\<close> \<open>preserves_convergence M1 M2 A\<close>
        unfolding preserves_convergence.simps
        by auto
      then show ?case 
        using \<open>converge M2 (\<beta> @ [(x, y)]) (\<gamma> @ [(x, y)])\<close> 
        unfolding \<open>xy = (x,y)\<close>
        by auto
    qed
  qed

  have reaching_sequence_ex : "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> \<exists> \<alpha> . \<alpha> \<in> A \<and> \<alpha> \<in> L M1 \<and> after_initial M1 \<alpha> = q"
  proof -
    fix q assume "q \<in> reachable_states M1"
    then show "\<exists> \<alpha> . \<alpha> \<in> A \<and> \<alpha> \<in> L M1 \<and> after_initial M1 \<alpha> = q"
    proof (induction rule: reachable_states_cases)
      case init
      then show ?case 
        using \<open>[] \<in> A\<close> 
        using language_contains_empty_sequence
        by (metis after.simps(1)) 
    next
      case (transition t)

      obtain \<gamma> where "\<gamma> \<in> A" and "\<gamma>@[(t_input t,t_output t)] \<in> A" and "\<gamma> \<in> L M1" and "after_initial M1 \<gamma> = t_source t"
        using \<open>transition_cover M1 A\<close>
              \<open>t_source t \<in> reachable_states M1\<close>
              fsm_transition_input[OF \<open>t \<in> transitions M1\<close>]
              fsm_transition_output[OF \<open>t \<in> transitions M1\<close>]
        unfolding transition_cover_def 
        by blast
      
      have "\<gamma>@[(t_input t,t_output t)] \<in> L M1"
        using after_language_iff[OF assms(1) \<open>\<gamma> \<in> L M1\<close>, of "[(t_input t,t_output t)]"] \<open>t \<in> transitions M1\<close>
        unfolding \<open>after_initial M1 \<gamma> = t_source t\<close> LS_single_transition 
        by auto
      moreover have "after M1 (after_initial M1 \<gamma>) [(t_input t,t_output t)] = t_target t"
        using after_transition[OF assms(1)] \<open>t \<in> transitions M1\<close>
        unfolding \<open>after_initial M1 \<gamma> = t_source t\<close>
        by auto
      ultimately have "after_initial M1 (\<gamma>@[(t_input t,t_output t)]) = t_target t"
        using after_split[OF assms(1)]
        by metis         
      then show ?case 
        using \<open>\<gamma>@[(t_input t,t_output t)] \<in> A\<close> \<open>\<gamma>@[(t_input t,t_output t)] \<in> L M1\<close>
        by blast
    qed
  qed

  have arbitrary_convergence: "\<And> \<alpha> \<beta> . converge M1 \<alpha> \<beta> \<Longrightarrow> converge M2 \<alpha> \<beta>"
  proof -
    fix \<alpha> \<beta>
    assume "converge M1 \<alpha> \<beta>"

    then have "\<alpha> \<in> L M1" and "\<beta> \<in> L M1"
      by auto
    then have "after_initial M1 \<alpha> \<in> reachable_states M1"
      using after_reachable[OF assms(1) _ reachable_states_initial]
      by auto
    then obtain \<gamma> where "\<gamma> \<in> A" and "\<gamma> \<in> L M1" and "after_initial M1 \<gamma> = after_initial M1 \<alpha>"
      using reaching_sequence_ex by blast
    moreover have "after_initial M1 \<alpha> = after_initial M1 \<beta>"
      using convergence_minimal[OF assms(3,1) \<open>\<alpha> \<in> L M1\<close> \<open>\<beta> \<in> L M1\<close>] \<open>converge M1 \<alpha> \<beta>\<close>
      by blast
    ultimately have "converge M1 \<gamma> \<alpha>" and "converge M1 \<gamma> \<beta>"
      using \<open>\<alpha> \<in> L M1\<close> \<open>\<beta> \<in> L M1\<close>
      by auto
    then have "converge M2 \<gamma> \<alpha>" and "converge M2 \<gamma> \<beta>"
      using convergence_right[OF \<open>\<gamma> \<in> A\<close>]
      by auto
    then show "converge M2 \<alpha> \<beta>"
      by auto
  qed

  
  have "L M1 \<subseteq> L M2"
  proof 
    fix \<alpha> assume "\<alpha> \<in> L M1"
    then have "converge M1 \<alpha> \<alpha>"
      by auto
    then have "converge M2 \<alpha> \<alpha>"
      using arbitrary_convergence
      by blast
    then show "\<alpha> \<in> L M2"
      by auto
  qed
  moreover have "L M2 \<subseteq> L M1"
  proof (rule ccontr)
    assume "\<not> L M2 \<subseteq> L M1"
    then obtain \<alpha>' where "\<alpha>' \<in> L M2 - L M1"
      by auto
    
    obtain \<alpha> xy \<beta> where "\<alpha>' = \<alpha> @ [xy] @ \<beta>" and "\<alpha> \<in> L M2 \<inter> L M1" and "\<alpha> @ [xy] \<in> L M2 - L M1"
      using minimal_failure_prefix_ob[OF assms(1,2) fsm_initial fsm_initial \<open>\<alpha>' \<in> L M2 - L M1\<close>]
      by blast
    moreover obtain x y where "xy = (x,y)"
      by force
    ultimately have "\<alpha> \<in> L M2" and "\<alpha> \<in> L M1" and "\<alpha> @ [(x,y)] \<in> L M2" and "\<alpha> @ [(x,y)] \<notin> L M1"
      by auto

    have "x \<in> inputs M1" and "y \<in> outputs M1"
      using language_io[OF \<open>\<alpha> @ [(x,y)] \<in> L M2\<close>]
      unfolding \<open>inputs M2 = inputs M1\<close> \<open>outputs M2 = outputs M1\<close>
      by auto
    moreover have "after_initial M1 \<alpha> \<in> reachable_states M1"
      using after_reachable[OF assms(1) \<open>\<alpha> \<in> L M1\<close> reachable_states_initial]
      by auto
    ultimately obtain \<gamma> where "\<gamma> \<in> A" and "\<gamma>@[(x,y)] \<in> A" and "\<gamma> \<in> L M1" and "after_initial M1 \<gamma> = after_initial M1 \<alpha>"
      using \<open>transition_cover M1 A\<close>
      unfolding transition_cover_def 
      by blast
    then have "converge M1 \<alpha> \<gamma>"
      using \<open>\<alpha> \<in> L M1\<close>
      by auto
    then have "converge M2 \<alpha> \<gamma>"
      using arbitrary_convergence
      by blast

    have "\<gamma> \<in> L M2"
      using \<open>\<gamma> \<in> A\<close> \<open>\<gamma> \<in> L M1\<close> assms(7,8)
      by blast
    
    have "\<gamma> @ [(x,y)] \<in> L M2"
      using \<open>\<alpha> @ [(x,y)] \<in> L M2\<close> \<open>converge M2 \<alpha> \<gamma>\<close>
      using after_language_iff[OF assms(2) \<open>\<alpha> \<in> L M2\<close> ]
      using after_language_iff[OF assms(2) \<open>\<gamma> \<in> L M2\<close> ]
      unfolding convergence_minimal[OF assms(4,2) \<open>\<alpha> \<in> L M2\<close> \<open>\<gamma> \<in> L M2\<close>]
      by auto
    
    have "\<gamma> @ [(x,y)] \<notin> L M1"
      using \<open>\<alpha> @ [(x,y)] \<notin> L M1\<close>
      using after_language_iff[OF assms(1) \<open>\<gamma> \<in> L M1\<close> ]
      using after_language_iff[OF assms(1) \<open>\<alpha> \<in> L M1\<close> ]
      unfolding \<open>after_initial M1 \<gamma> = after_initial M1 \<alpha>\<close>
      by auto
    then have "\<gamma> @ [(x,y)] \<notin> L M2"
      using \<open>\<gamma>@[(x,y)] \<in> A\<close> assms(7,8)
      by auto
    then show False
      using \<open>\<gamma> @ [(x,y)] \<in> L M2\<close>
      by auto
  qed
  ultimately show ?thesis
    by blast
qed
      
end