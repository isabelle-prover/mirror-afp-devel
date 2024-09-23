section \<open>Preliminaries\<close>

theory Preliminaries
imports Main LatticeProperties.Complete_Lattice_Prop 
  LatticeProperties.Conj_Disj
begin

notation
  less_eq (infix \<open>\<sqsubseteq>\<close> 50) and
  less (infix \<open>\<sqsubset>\<close> 50) and
  inf (infixl \<open>\<sqinter>\<close> 70) and
  sup (infixl \<open>\<squnion>\<close> 65) and
  top (\<open>\<top>\<close>) and
  bot (\<open>\<bottom>\<close>) and
  Inf (\<open>\<Sqinter>_\<close> [900] 900) and
  Sup (\<open>\<Squnion>_\<close> [900] 900)

subsection \<open>Simplification Lemmas\<close>

declare fun_upd_idem[simp]

lemma simp_eq_emptyset:
  "(X = {}) = (\<forall> x. x \<notin> X)"
  by blast

lemma mono_comp: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f o g)" 
  by (unfold mono_def) auto

text \<open>Some lattice simplification rules\<close>

lemma inf_bot_bot: (* FIXME *)
  "(x::'a::{semilattice_inf,order_bot}) \<sqinter> \<bottom> = \<bottom>"
  apply (rule antisym)
  by auto

end
