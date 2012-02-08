header {* \isaheader{Transfer between Domains} *}
theory RefineG_Transfer
imports "../Refine_Misc"
begin
  text {* Currently, this theory is specialized to 
    transfers that include no data refinement.
    *}

ML {*
structure RefineG_Transfer = struct
  structure transfer = Named_Thms
    ( val name = "refine_transfer"
      val description = "Refinement Framework: " ^ 
        "Transfer rules" );

  fun transfer_tac thms ctxt i st = let 
    val thms = thms @ transfer.get ctxt;
    val ss = HOL_basic_ss addsimps @{thms nested_prod_case_simp}
  in
    REPEAT_DETERM1 (
      COND (has_fewer_prems (nprems_of st)) no_tac (
        FIRST [
          Method.assm_tac ctxt i,
          resolve_tac thms i,
          Refine_Misc.triggered_mono_tac ctxt i,
          CHANGED_PROP (simp_tac ss i)]
      )) st
  end
  
end
*}

setup {* RefineG_Transfer.transfer.setup *}
method_setup refine_transfer = 
  {* Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD'
    (RefineG_Transfer.transfer_tac thms ctxt)) 
  *} "Invoke transfer rules"


locale transfer = fixes \<alpha> :: "'c \<Rightarrow> 'a::complete_lattice"
begin

text {*
  In the following, we define some transfer lemmas for general
  HOL - constructs.
*}

lemma transfer_if[refine_transfer]:
  assumes "b \<Longrightarrow> \<alpha> s1 \<le> S1"
  assumes "\<not>b \<Longrightarrow> \<alpha> s2 \<le> S2"
  shows "\<alpha> (if b then s1 else s2) \<le> (if b then S1 else S2)"
  using assms by auto

lemma transfer_prod[refine_transfer]:
  assumes "\<And>a b. \<alpha> (f a b) \<le> F a b"
  shows "\<alpha> (prod_case f x) \<le> (prod_case F x)"
  using assms by (auto split: prod.split)

lemma transfer_Let[refine_transfer]:
  assumes "\<And>x. \<alpha> (f x) \<le> F x"
  shows "\<alpha> (Let x f) \<le> Let x F"
  using assms by auto

lemma transfer_option[refine_transfer]:
  assumes "\<alpha> fa \<le> Fa"
  assumes "\<And>x. \<alpha> (fb x) \<le> Fb x"
  shows "\<alpha> (option_case fa fb x) \<le> option_case Fa Fb x"
  using assms by (auto split: option.split)

end

text {* Transfer into complete lattice structure *}
locale ordered_transfer = transfer + 
  constrains \<alpha> :: "'c::complete_lattice \<Rightarrow> 'a::complete_lattice"

text {* Transfer into complete lattice structure with distributive
  transfer function. *}
locale dist_transfer = ordered_transfer + 
  constrains \<alpha> :: "'c::complete_lattice \<Rightarrow> 'a::complete_lattice"
  assumes \<alpha>_dist: "\<And>A. is_chain A \<Longrightarrow> \<alpha> (Sup A) = Sup (\<alpha>`A)"
begin
  lemma \<alpha>_mono[simp, intro!]: "mono \<alpha>"
    apply rule
    apply (subgoal_tac "is_chain {x,y}")
    apply (drule \<alpha>_dist)
    apply (auto simp: le_iff_sup) []
    apply (rule chainI)
    apply auto
    done

  lemma \<alpha>_strict[simp]: "\<alpha> bot = bot"
    using \<alpha>_dist[of "{}"] by simp
end


text {* Transfer into ccpo *}
locale ccpo_transfer = transfer \<alpha> for
  \<alpha> :: "'c::ccpo \<Rightarrow> 'a::complete_lattice" 

text {* Transfer into ccpo with distributive
  transfer function. *}
locale dist_ccpo_transfer = ccpo_transfer \<alpha>
  for \<alpha> :: "'c::ccpo \<Rightarrow> 'a::complete_lattice" + 
  assumes \<alpha>_dist: "\<And>A. is_chain A \<Longrightarrow> \<alpha> (Complete_Partial_Order.lub A) = Sup (\<alpha>`A)"
begin

  lemma \<alpha>_mono[simp, intro!]: "mono \<alpha>"
  proof
    fix x y :: 'c
    assume LE: "x\<le>y"
    hence C[simp, intro!]: "is_chain {x,y}" by (auto intro: chainI)
    from LE have "\<alpha> x \<le> sup (\<alpha> x) (\<alpha> y)" by simp
    also have "\<dots> = Sup (\<alpha>`{x,y})" by simp
    also have "\<dots> = \<alpha> (Complete_Partial_Order.lub {x,y})"
      by (rule \<alpha>_dist[symmetric]) simp
    also have "Complete_Partial_Order.lub {x,y} = y"
      apply (rule antisym)
      apply (rule lub_least[OF C]) using LE apply auto []
      apply (rule lub_upper[OF C]) by auto
    finally show "\<alpha> x \<le> \<alpha> y" .
  qed

  lemma \<alpha>_strict[simp]: "\<alpha> (Complete_Partial_Order.lub {}) = bot"
    using \<alpha>_dist[of "{}"] by simp
end

end
