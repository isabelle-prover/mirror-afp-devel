(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some useful lemmas in topology\<close>

theory Missing_Topology imports "HOL-Analysis.Multivariate_Analysis"
begin

subsection \<open>Misc\<close>    
 
lemma open_times_image:
  fixes S::"'a::real_normed_field set"
  assumes "open S" "c\<noteq>0"
  shows "open (((*) c) ` S)" 
proof -
  let ?f = "\<lambda>x. x/c" and ?g="((*) c)"
  have "continuous_on UNIV ?f" using \<open>c\<noteq>0\<close> by (auto intro:continuous_intros)
  then have "open (?f -` S)" using \<open>open S\<close> by (auto elim:open_vimage)
  moreover have "?g ` S = ?f -` S" using \<open>c\<noteq>0\<close>
    using image_iff by fastforce
  ultimately show ?thesis by auto
qed   
 
lemma image_linear_greaterThan:
  fixes x::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "((\<lambda>x. c*x+b) ` {x<..}) = (if c>0 then {c*x+b <..} else {..< c*x+b})"
using \<open>c\<noteq>0\<close>
  apply (auto simp add:image_iff field_simps)    
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
done

lemma image_linear_lessThan:
  fixes x::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "((\<lambda>x. c*x+b) ` {..<x}) = (if c>0 then {..<c*x+b} else {c*x+b<..})"
using \<open>c\<noteq>0\<close>
  apply (auto simp add:image_iff field_simps)    
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
done    
 
lemma continuous_on_neq_split:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "\<forall>x\<in>s. f x\<noteq>y" "continuous_on s f" "connected s"
  shows "(\<forall>x\<in>s. f x>y) \<or> (\<forall>x\<in>s. f x<y)"
  by (smt (verit) assms connectedD_interval connected_continuous_image imageE image_eqI leI) 

lemma
  fixes f::"'a::linorder_topology \<Rightarrow> 'b::topological_space"
  assumes "continuous_on {a..b} f" "a<b"
  shows continuous_on_at_left:"continuous (at_left b) f" 
    and continuous_on_at_right:"continuous (at_right a) f"
  using assms continuous_on_Icc_at_leftD continuous_within apply blast
  using assms continuous_on_Icc_at_rightD continuous_within by blast
 
subsection \<open>More about @{term eventually}\<close>    
    
lemma eventually_comp_filtermap:
    "eventually (P o f) F \<longleftrightarrow> eventually P (filtermap f F)"
  unfolding comp_def using eventually_filtermap by auto
 
lemma eventually_at_infinityI:
  fixes P::"'a::real_normed_vector \<Rightarrow> bool"
  assumes "\<And>x. c \<le> norm x \<Longrightarrow> P x"
  shows "eventually P at_infinity"  
unfolding eventually_at_infinity using assms by auto
   
lemma eventually_at_bot_linorderI:
  fixes c::"'a::linorder"
  assumes "\<And>x. x \<le> c \<Longrightarrow> P x"
  shows "eventually P at_bot"
  using assms by (auto simp: eventually_at_bot_linorder)     

subsection \<open>More about @{term filtermap}\<close> 

lemma filtermap_linear_at_within:
  assumes "bij f" and cont: "isCont f a" and open_map: "\<And>S. open S \<Longrightarrow> open (f`S)"
  shows "filtermap f (at a within S) = at (f a) within f`S"
  unfolding filter_eq_iff
proof safe
  fix P
  assume "eventually P (filtermap f (at a within S))"
  then obtain T where "open T" "a \<in> T" and impP:"\<forall>x\<in>T. x\<noteq>a \<longrightarrow> x\<in>S\<longrightarrow> P (f x)"
    by (auto simp: eventually_filtermap eventually_at_topological)
  then show "eventually P (at (f a) within f ` S)"
    unfolding eventually_at_topological
    apply (intro exI[of _ "f`T"])
    using \<open>bij f\<close> open_map by (metis bij_pointE imageE imageI)  
next
  fix P
  assume "eventually P (at (f a) within f ` S)"
  then obtain T1 where "open T1" "f a \<in> T1" and impP:"\<forall>x\<in>T1. x\<noteq>f a \<longrightarrow> x\<in>f`S\<longrightarrow> P (x)"
    unfolding eventually_at_topological by auto
  then obtain T2 where "open T2" "a \<in> T2" "(\<forall>x'\<in>T2. f x' \<in> T1)" 
    using cont[unfolded continuous_at_open,rule_format,of T1] by blast 
  then have "\<forall>x\<in>T2. x\<noteq>a \<longrightarrow> x\<in>S\<longrightarrow> P (f x)"
    using impP by (metis assms(1) bij_pointE imageI)
  then show "eventually P (filtermap f (at a within S))" 
    unfolding eventually_filtermap eventually_at_topological 
    apply (intro exI[of _ T2])
    using \<open>open T2\<close> \<open>a \<in> T2\<close> by auto
qed
  
lemma filtermap_at_bot_linear_eq:
  fixes c::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "filtermap (\<lambda>x. x * c + b) at_bot = (if c>0 then at_bot else at_top)"
proof (cases "c>0")
  case True
  then have "filtermap (\<lambda>x. x * c + b) at_bot = at_bot" 
    apply (intro filtermap_fun_inverse[of "\<lambda>x. (x-b) / c"])
    subgoal unfolding eventually_at_bot_linorder filterlim_at_bot
      by (auto simp add: field_simps)
    subgoal unfolding eventually_at_bot_linorder filterlim_at_bot
      by (metis mult.commute real_affinity_le)
    by auto
  then show ?thesis using \<open>c>0\<close> by auto
next
  case False
  then have "c<0" using \<open>c\<noteq>0\<close> by auto
  then have "filtermap (\<lambda>x. x * c + b) at_bot = at_top"
    apply (intro filtermap_fun_inverse[of "\<lambda>x. (x-b) / c"])
    subgoal unfolding eventually_at_top_linorder filterlim_at_bot
      by (meson le_diff_eq neg_divide_le_eq)
    subgoal unfolding eventually_at_bot_linorder filterlim_at_top
      using \<open>c < 0\<close> by (meson False diff_le_eq le_divide_eq)
    by auto
  then show ?thesis using \<open>c<0\<close> by auto
qed  
  
lemma filtermap_linear_at_left:
  fixes c::"'a::{linordered_field,linorder_topology,real_normed_field}"
  assumes "c\<noteq>0"
  shows "filtermap (\<lambda>x. c*x+b) (at_left x) = (if c>0 then at_left (c*x+b) else at_right (c*x+b))"
proof -
  let ?f = "\<lambda>x. c*x+b"
  have "filtermap (\<lambda>x. c*x+b) (at_left x) = (at (?f x) within ?f ` {..<x})"
  proof (subst filtermap_linear_at_within)
    show "bij ?f" using \<open>c\<noteq>0\<close> 
      by (auto intro!: o_bij[of "\<lambda>x. (x-b)/c"])
    show "isCont ?f x" by auto
    show "\<And>S. open S \<Longrightarrow> open (?f ` S)" 
      using open_times_image[OF _ \<open>c\<noteq>0\<close>,THEN open_translation,of _ b]  
      by (simp add:image_image add.commute)
    show "at (?f x) within ?f ` {..<x} = at (?f x) within ?f ` {..<x}" by simp
  qed
  moreover have "?f ` {..<x} =  {..<?f x}" when "c>0" 
    using image_linear_lessThan[OF \<open>c\<noteq>0\<close>,of b x] that by auto
  moreover have "?f ` {..<x} =  {?f x<..}" when "\<not> c>0" 
    using image_linear_lessThan[OF \<open>c\<noteq>0\<close>,of b x] that by auto
  ultimately show ?thesis by auto
qed
    
lemma filtermap_linear_at_right:
  fixes c::"'a::{linordered_field,linorder_topology,real_normed_field}"
  assumes "c\<noteq>0"
  shows "filtermap (\<lambda>x. c*x+b) (at_right x) = (if c>0 then at_right (c*x+b) else at_left (c*x+b))" 
proof -
  let ?f = "\<lambda>x. c*x+b"
  have "filtermap ?f (at_right x) = (at (?f x) within ?f ` {x<..})"
  proof (subst filtermap_linear_at_within)
    show "bij ?f" using \<open>c\<noteq>0\<close> 
      by (auto intro!: o_bij[of "\<lambda>x. (x-b)/c"])
    show "isCont ?f x" by auto
    show "\<And>S. open S \<Longrightarrow> open (?f ` S)" 
      using open_times_image[OF _ \<open>c\<noteq>0\<close>,THEN open_translation,of _ b]  
      by (simp add:image_image add.commute)
    show "at (?f x) within ?f ` {x<..} = at (?f x) within ?f ` {x<..}" by simp
  qed
  moreover have "?f ` {x<..} =  {?f x<..}" when "c>0" 
    using image_linear_greaterThan[OF \<open>c\<noteq>0\<close>,of b x] that by auto
  moreover have "?f ` {x<..} =  {..<?f x}" when "\<not> c>0" 
    using image_linear_greaterThan[OF \<open>c\<noteq>0\<close>,of b x] that by auto
  ultimately show ?thesis by auto
qed
 
lemma filtermap_at_top_linear_eq:
  fixes c::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "filtermap (\<lambda>x. x * c + b) at_top = (if c>0 then at_top else at_bot)"
proof (cases "c>0")
  case True
  then have "filtermap (\<lambda>x. x * c + b) at_top = at_top" 
    apply (intro filtermap_fun_inverse[of "\<lambda>x. (x-b) / c"])
    subgoal unfolding eventually_at_top_linorder filterlim_at_top 
      by (meson le_diff_eq pos_le_divide_eq)
    subgoal unfolding eventually_at_top_linorder filterlim_at_top
      apply auto
      by (metis mult.commute real_le_affinity) 
    by auto
  then show ?thesis using \<open>c>0\<close> by auto
next
  case False
  then have "c<0" using \<open>c\<noteq>0\<close> by auto
  then have "filtermap (\<lambda>x. x * c + b) at_top = at_bot"
    apply (intro filtermap_fun_inverse[of "\<lambda>x. (x-b) / c"])
    subgoal unfolding eventually_at_bot_linorder filterlim_at_top
      by (auto simp add: field_simps)
    subgoal unfolding eventually_at_top_linorder filterlim_at_bot
      by (meson le_diff_eq neg_divide_le_eq)
    by auto
  then show ?thesis using \<open>c<0\<close> by auto
qed

subsection \<open>More about @{term filterlim}\<close>
  
lemma filterlim_at_top_linear_iff:
  fixes f::"'a::linordered_field \<Rightarrow> 'b"
  assumes "c\<noteq>0"
  shows "(LIM x at_top. f (x * c + b) :> F2) \<longleftrightarrow> (if c>0 then (LIM x at_top. f x :> F2) 
            else (LIM x at_bot. f x :> F2))"
  unfolding filterlim_def
  apply (subst filtermap_filtermap[of f "\<lambda>x. x * c + b",symmetric])
  using assms by (auto simp add:filtermap_at_top_linear_eq)
    
lemma filterlim_at_bot_linear_iff:
  fixes f::"'a::linordered_field \<Rightarrow> 'b"
  assumes "c\<noteq>0"
  shows "(LIM x at_bot. f (x * c + b) :> F2) \<longleftrightarrow> (if c>0 then (LIM x at_bot. f x :> F2) 
            else (LIM x at_top. f x :> F2)) "
  unfolding filterlim_def 
  apply (subst filtermap_filtermap[of f "\<lambda>x. x * c + b",symmetric])
  using assms by (auto simp add:filtermap_at_bot_linear_eq)      
  
  
lemma filterlim_tendsto_add_at_top_iff:
  assumes f: "(f \<longlongrightarrow> c) F"
  shows "(LIM x F. (f x + g x :: real) :> at_top) \<longleftrightarrow> (LIM x F. g x :> at_top)"
proof     
  assume "LIM x F. f x + g x :> at_top" 
  moreover have "((\<lambda>x. - f x) \<longlongrightarrow> - c) F"
    using f by (intro tendsto_intros,simp)
  ultimately show "filterlim g at_top F" using filterlim_tendsto_add_at_top 
    by fastforce
qed (auto simp add:filterlim_tendsto_add_at_top[OF f])    
    
  
lemma filterlim_tendsto_add_at_bot_iff:
  fixes c::real
  assumes f: "(f \<longlongrightarrow> c) F"
  shows "(LIM x F. f x + g x :> at_bot) \<longleftrightarrow> (LIM x F. g x :> at_bot)" 
proof -
  have "(LIM x F. f x + g x :> at_bot) 
        \<longleftrightarrow>  (LIM x F. - f x + (- g x)  :> at_top)"
    apply (subst filterlim_uminus_at_top)
    by (rule filterlim_cong,auto)
  also have "... = (LIM x F. - g x  :> at_top)"
    apply (subst filterlim_tendsto_add_at_top_iff[of _ "-c"])
    by (auto intro:tendsto_intros simp add:f)
  also have "... = (LIM x F. g x  :> at_bot)"
    apply (subst filterlim_uminus_at_top)
    by (rule filterlim_cong,auto)
  finally show ?thesis .
qed
  
lemma tendsto_inverse_0_at_infinity: 
    "LIM x F. f x :> at_infinity \<Longrightarrow> ((\<lambda>x. inverse (f x) :: real) \<longlongrightarrow> 0) F"
  by (metis filterlim_at filterlim_inverse_at_iff)

(*
lemma filterlim_at_top_tendsto[elim]:
  fixes f::"'a \<Rightarrow> 'b::{unbounded_dense_linorder,order_topology}" and F::"'a filter"
  assumes top:"filterlim f at_top F" and tendsto: "(f \<longlongrightarrow> c) F" 
          and "F\<noteq>bot"
  shows False
proof -
  obtain cc where "cc>c" using gt_ex by blast
  have "\<forall>\<^sub>F x in F. cc < f x" 
    using top unfolding filterlim_at_top_dense by auto
  moreover have "\<forall>\<^sub>F x in F. f x < cc" 
    using tendsto order_tendstoD(2)[OF _ \<open>cc>c\<close>] by auto
  ultimately have "\<forall>\<^sub>F x in F. cc < f x \<and> f x < cc" 
    using eventually_conj by auto
  then have "\<forall>\<^sub>F x in F. False" by (auto elim:eventually_mono)
  then show False using \<open>F\<noteq>bot\<close> by auto
qed

lemma filterlim_at_bot_tendsto[elim]:
  fixes f::"'a \<Rightarrow> 'b::{unbounded_dense_linorder,order_topology}" and F::"'a filter"
  assumes top:"filterlim f at_bot F" and tendsto: "(f \<longlongrightarrow> c) F" 
          and "F\<noteq>bot"
  shows False
proof -
  obtain cc where "cc<c" using lt_ex by blast
  have "\<forall>\<^sub>F x in F. cc > f x" 
    using top unfolding filterlim_at_bot_dense by auto
  moreover have "\<forall>\<^sub>F x in F. f x > cc" 
    using tendsto order_tendstoD(1)[OF _ \<open>cc<c\<close>] by auto
  ultimately have "\<forall>\<^sub>F x in F. cc < f x \<and> f x < cc" 
    using eventually_conj by auto
  then have "\<forall>\<^sub>F x in F. False" by (auto elim:eventually_mono)
  then show False using \<open>F\<noteq>bot\<close> by auto
qed
*)
  
end
