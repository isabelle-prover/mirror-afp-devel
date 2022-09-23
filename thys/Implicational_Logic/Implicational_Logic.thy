(*
  Authors: Asta Halkjær From & Jørgen Villadsen, DTU Compute
*)

section \<open>Formalization of the Bernays-Tarski Axiom System for Classical Implicational Logic\<close>

(* Uncomment for Full Classical Propositional Logic *)

subsection \<open>Syntax, Semantics and Axiom System\<close>

theory Implicational_Logic imports Main begin

datatype form =
  (*Falsity (\<open>\<bottom>\<close>) |*)
  Pro nat (\<open>\<cdot>\<close>) |
  Imp form form (infixr \<open>\<rightarrow>\<close> 55)

primrec semantics (infix \<open>\<Turnstile>\<close> 50) where
  (*\<open>I \<Turnstile> \<bottom> = False\<close> |*)
  \<open>I \<Turnstile> \<cdot> n = I n\<close> |
  \<open>I \<Turnstile> p \<rightarrow> q = (I \<Turnstile> p \<longrightarrow> I \<Turnstile> q)\<close>

inductive Ax (\<open>\<turnstile> _\<close> 50) where
  (*Expl: \<open>\<turnstile> \<bottom> \<rightarrow> p\<close> |*)
  Simp: \<open>\<turnstile> p \<rightarrow> q \<rightarrow> p\<close> |
  Tran: \<open>\<turnstile> (p \<rightarrow> q) \<rightarrow> (q \<rightarrow> r) \<rightarrow> p \<rightarrow> r\<close> |
  MP: \<open>\<turnstile> p \<rightarrow> q \<Longrightarrow> \<turnstile> p \<Longrightarrow> \<turnstile> q\<close> |
  PR: \<open>\<turnstile> (p \<rightarrow> q) \<rightarrow> p \<Longrightarrow> \<turnstile> p\<close>

subsection \<open>Soundness and Derived Formulas\<close>

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct p rule: Ax.induct) auto

lemma Swap: \<open>\<turnstile> (p \<rightarrow> q \<rightarrow> r) \<rightarrow> q \<rightarrow> p \<rightarrow> r\<close>
proof -
  have \<open>\<turnstile> q \<rightarrow> (q \<rightarrow> r) \<rightarrow> r\<close>
    using MP PR Simp Tran by metis
  then show ?thesis
    using MP Tran by meson
qed

lemma Peirce: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> p) \<rightarrow> p\<close>
  using MP PR Simp Swap Tran by meson

lemma Hilbert: \<open>\<turnstile> (p \<rightarrow> p \<rightarrow> q) \<rightarrow> p \<rightarrow> q\<close>
  using MP MP Tran Tran Peirce .

lemma Id: \<open>\<turnstile> p \<rightarrow> p\<close>
  using MP Hilbert Simp .

lemma Tran': \<open>\<turnstile> (q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q) \<rightarrow> p \<rightarrow> r\<close>
  using MP Swap Tran .

lemma Frege: \<open>\<turnstile> (p \<rightarrow> q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q) \<rightarrow> p \<rightarrow> r\<close>
  using MP MP Tran MP MP Tran Swap Tran' MP Tran' Hilbert .

lemma Imp1: \<open>\<turnstile> (q \<rightarrow> s) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
  using MP Peirce Tran Tran' by meson

lemma Imp2: \<open>\<turnstile> ((r \<rightarrow> s) \<rightarrow> s) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
  using MP Tran MP Tran Simp .

lemma Imp3: \<open>\<turnstile> ((q \<rightarrow> s) \<rightarrow> s) \<rightarrow> (r \<rightarrow> s) \<rightarrow> (q \<rightarrow> r) \<rightarrow> s\<close>
  using MP Swap Tran by meson

subsection \<open>Completeness and Main Theorem\<close>

fun pros where
  \<open>pros (p \<rightarrow> q) = remdups (pros p @ pros q)\<close> |
  \<open>pros p = (case p of (\<cdot> n) \<Rightarrow> [n] | _ \<Rightarrow> [])\<close>

lemma distinct_pros: \<open>distinct (pros p)\<close>
  by (induct p) simp_all

primrec imply (infixr \<open>\<leadsto>\<close> 56) where
  \<open>[] \<leadsto> q = q\<close> |
  \<open>p # ps \<leadsto> q = p \<rightarrow> ps \<leadsto> q\<close>

lemma imply_append: \<open>ps @ qs \<leadsto> r = ps \<leadsto> qs \<leadsto> r\<close>
  by (induct ps) simp_all

abbreviation Ax_assms (infix \<open>\<turnstile>\<close> 50) where \<open>ps \<turnstile> q \<equiv> \<turnstile> ps \<leadsto> q\<close>

lemma imply_Cons: \<open>ps \<turnstile> q \<Longrightarrow> p # ps \<turnstile> q\<close>
proof -
  assume \<open>ps \<turnstile> q\<close>
  with MP Simp have \<open>\<turnstile> p \<rightarrow> ps \<leadsto> q\<close> .
  then show ?thesis
    by simp
qed

lemma imply_head: \<open>p # ps \<turnstile> p\<close>
  by (induct ps) (use MP Frege Simp imply.simps in metis)+

lemma imply_mem: \<open>p \<in> set ps \<Longrightarrow> ps \<turnstile> p\<close>
  by (induct ps) (use imply_Cons imply_head in auto)

lemma imply_MP: \<open>\<turnstile> ps \<leadsto> (p \<rightarrow> q) \<rightarrow> ps \<leadsto> p \<rightarrow> ps \<leadsto> q\<close>
proof (induct ps)
  case (Cons r ps)
  then have \<open>\<turnstile> (r \<rightarrow> ps \<leadsto> (p \<rightarrow> q)) \<rightarrow> (r \<rightarrow> ps \<leadsto> p) \<rightarrow> r \<rightarrow> ps \<leadsto> q\<close>
    using MP Frege Simp by meson
  then show ?case
    by simp
qed (auto intro: Id)

lemma MP': \<open>ps \<turnstile> p \<rightarrow> q \<Longrightarrow> ps \<turnstile> p \<Longrightarrow> ps \<turnstile> q\<close>
  using MP imply_MP by metis

lemma imply_swap_append: \<open>ps @ qs \<turnstile> r \<Longrightarrow> qs @ ps \<turnstile> r\<close>
  by (induct qs arbitrary: ps) (simp, metis MP' imply_append imply_Cons imply_head imply.simps(2))

lemma imply_deduct: \<open>p # ps \<turnstile> q \<Longrightarrow> ps \<turnstile> p \<rightarrow> q\<close>
  using imply_append imply_swap_append imply.simps by metis

lemma add_imply [simp]: \<open>\<turnstile> p \<Longrightarrow> ps \<turnstile> p\<close>
proof -
  note MP
  moreover have \<open>\<turnstile> p \<rightarrow> ps \<leadsto> p\<close>
    using imply_head by simp
  moreover assume \<open>\<turnstile> p\<close>
  ultimately show ?thesis .
qed

lemma imply_weaken: \<open>ps \<turnstile> p \<Longrightarrow> set ps \<subseteq> set ps' \<Longrightarrow> ps' \<turnstile> p\<close>
  by (induct ps arbitrary: p) (simp, metis MP' imply_deduct imply_mem insert_subset list.set(2))

abbreviation \<open>lift t s p \<equiv> if t then (p \<rightarrow> s) \<rightarrow> s else p \<rightarrow> s\<close>

abbreviation \<open>lifts I s \<equiv> map (\<lambda>n. lift (I n) s (\<cdot> n))\<close>

lemma lifts_weaken: \<open>lifts I s l \<turnstile> p \<Longrightarrow> set l \<subseteq> set l' \<Longrightarrow> lifts I s l' \<turnstile> p\<close>
  using imply_weaken by (metis (no_types, lifting) image_mono set_map)

lemma lifts_pros_lift: \<open>lifts I s (pros p) \<turnstile> lift (I \<Turnstile> p) s p\<close>
proof (induct p)
  case (Imp q r)
  consider \<open>\<not> I \<Turnstile> q\<close> | \<open>I \<Turnstile> r\<close> | \<open>I \<Turnstile> q\<close> \<open>\<not> I \<Turnstile> r\<close>
    by blast
  then show ?case
  proof cases
    case 1
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<turnstile> q \<rightarrow> s\<close>
      using Imp(1) lifts_weaken[where l' = \<open>pros (q \<rightarrow> r)\<close>] by simp
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<turnstile> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
      using Imp1 MP' add_imply by blast
    with 1 show ?thesis
      by simp
  next
    case 2
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<turnstile> (r \<rightarrow> s) \<rightarrow> s\<close>
      using Imp(2) lifts_weaken[where l' = \<open>pros (q \<rightarrow> r)\<close>] by simp
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<turnstile> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
      using Imp2 MP' add_imply by blast
    with 2 show ?thesis
      by simp
  next
    case 3
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<turnstile> (q \<rightarrow> s) \<rightarrow> s\<close> \<open>lifts I s (pros (q \<rightarrow> r)) \<turnstile> r \<rightarrow> s\<close>
      using Imp lifts_weaken[where l' = \<open>pros (q \<rightarrow> r)\<close>] by simp_all
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<turnstile> (q \<rightarrow> r) \<rightarrow> s\<close>
      using Imp3 MP' add_imply by blast
    with 3 show ?thesis
      by simp
  qed
qed (auto intro: Id Ax.intros)

lemma lifts_pros: \<open>I \<Turnstile> p \<Longrightarrow> lifts I p (pros p) \<turnstile> p\<close>
proof -
  assume \<open>I \<Turnstile> p\<close>
  then have \<open>lifts I p (pros p) \<turnstile> (p \<rightarrow> p) \<rightarrow> p\<close>
    using lifts_pros_lift[of I p p] by simp
  then show ?thesis
    using Id MP' add_imply by blast
qed

theorem completeness: \<open>\<forall>I. I \<Turnstile> p \<Longrightarrow> \<turnstile> p\<close>
proof -
  let ?A = \<open>\<lambda>l I. lifts I p l \<turnstile> p\<close>
  let ?B = \<open>\<lambda>l. \<forall>I. ?A l I \<and> distinct l\<close>
  assume \<open>\<forall>I. I \<Turnstile> p\<close>
  moreover have \<open>?B l \<Longrightarrow> (\<And>n l. ?B (n # l) \<Longrightarrow> ?B l) \<Longrightarrow> ?B []\<close> for l
    by (induct l) blast+
  moreover have \<open>?B (n # l) \<Longrightarrow> ?B l\<close> for n l
  proof -
    assume *: \<open>?B (n # l)\<close>
    show \<open>?B l\<close>
    proof
      fix I
      from * have \<open>?A (n # l) (I(n := True))\<close> \<open>?A (n # l) (I(n := False))\<close>
        by blast+
      moreover from * have \<open>\<forall>m \<in> set l. \<forall>t. (I(n := t)) m = I m\<close>
        by simp
      ultimately have \<open>((\<cdot> n \<rightarrow> p) \<rightarrow> p) # lifts I p l \<turnstile> p\<close> \<open>(\<cdot> n \<rightarrow> p) # lifts I p l \<turnstile> p\<close>
        by (simp_all cong: map_cong)
      then have \<open>?A l I\<close>
        using MP' imply_deduct by blast
      moreover from * have \<open>distinct (n # l)\<close>
        by blast
      ultimately show \<open>?A l I \<and> distinct l\<close>
        by simp
    qed
  qed
  ultimately have \<open>?B []\<close>
    using lifts_pros distinct_pros by blast
  then show ?thesis
    by simp
qed

theorem main: \<open>(\<turnstile> p) = (\<forall>I. I \<Turnstile> p)\<close>
  using soundness completeness by blast

subsection \<open>Reference\<close>

text \<open>Wikipedia \<^url>\<open>https://en.wikipedia.org/wiki/Implicational_propositional_calculus\<close> July 2022\<close>

end
