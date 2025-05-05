(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some useful lemmas in topology\<close>

theory Missing_Topology imports "HOL-Analysis.Multivariate_Analysis"
begin

subsection \<open>Misc\<close>    

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
 
subsection \<open>More about @{term filtermap}\<close> 

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
      using open_times_image[OF \<open>c\<noteq>0\<close>,THEN open_translation,of _ b]  
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
      using open_times_image[OF \<open>c\<noteq>0\<close>,THEN open_translation,of _ b]  
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
    
end
