(*
  Authors: Asta Halkjær From & Jørgen Villadsen, DTU Compute
*)

section \<open>Formalization of Łukasiewicz's Axiom System from 1924 for Classical Propositional Logic\<close>

subsection \<open>Syntax, Semantics and Axiom System\<close>

theory Implicational_Logic_Appendix imports Main begin

datatype form =
  Pro nat (\<open>\<cdot>\<close>) |
  Neg form (\<open>\<sim>\<close>) |
  Imp form form (infixr \<open>\<rightarrow>\<close> 55)

primrec semantics (infix \<open>\<Turnstile>\<close> 50) where
  \<open>I \<Turnstile> \<cdot> n = I n\<close> |
  \<open>I \<Turnstile> \<sim> p = (\<not> I \<Turnstile> p)\<close> |
  \<open>I \<Turnstile> p \<rightarrow> q = (I \<Turnstile> p \<longrightarrow> I \<Turnstile> q)\<close>

inductive Ax (\<open>\<turnstile> _\<close> 50) where
  01: \<open>\<turnstile> (p \<rightarrow> q) \<rightarrow> (q \<rightarrow> r) \<rightarrow> p \<rightarrow> r\<close> |
  02: \<open>\<turnstile> (\<sim> p \<rightarrow> p) \<rightarrow> p\<close> |
  03: \<open>\<turnstile> p \<rightarrow> \<sim> p \<rightarrow> q\<close> |
  MP: \<open>\<turnstile> p \<rightarrow> q \<Longrightarrow> \<turnstile> p \<Longrightarrow> \<turnstile> q\<close>

subsection \<open>Soundness and Derived Formulas\<close>

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct p rule: Ax.induct) simp_all

lemma 04: \<open>\<turnstile> (((q \<rightarrow> r) \<rightarrow> p \<rightarrow> r) \<rightarrow> s) \<rightarrow> (p \<rightarrow> q) \<rightarrow> s\<close>
  using MP 01 01 .

lemma 05: \<open>\<turnstile> (p \<rightarrow> q \<rightarrow> r) \<rightarrow> (s \<rightarrow> q) \<rightarrow> p \<rightarrow> s \<rightarrow> r\<close>
  using MP 04 04 .

lemma 06: \<open>\<turnstile> (p \<rightarrow> q) \<rightarrow> ((p \<rightarrow> r) \<rightarrow> s) \<rightarrow> (q \<rightarrow> r) \<rightarrow> s\<close>
  using MP 04 01 .

lemma 07: \<open>\<turnstile> (t \<rightarrow> (p \<rightarrow> r) \<rightarrow> s) \<rightarrow> (p \<rightarrow> q) \<rightarrow> t \<rightarrow> (q \<rightarrow> r) \<rightarrow> s\<close>
  using MP 05 06 .

lemma 09: \<open>\<turnstile> ((\<sim> p \<rightarrow> q) \<rightarrow> r) \<rightarrow> p \<rightarrow> r\<close>
  using MP 01 03 .

lemma 10: \<open>\<turnstile> p \<rightarrow> ((\<sim> p \<rightarrow> p) \<rightarrow> p) \<rightarrow> (q \<rightarrow> p) \<rightarrow> p\<close>
  using MP 09 06 .

lemma 11: \<open>\<turnstile> (q \<rightarrow> (\<sim> p \<rightarrow> p) \<rightarrow> p) \<rightarrow> (\<sim> p \<rightarrow> p) \<rightarrow> p\<close>
  using MP MP 10 02 02 .

lemma 12: \<open>\<turnstile> t \<rightarrow> (\<sim> p \<rightarrow> p) \<rightarrow> p\<close>
  using MP 09 11 .

lemma 13: \<open>\<turnstile> (\<sim> p \<rightarrow> q) \<rightarrow> t \<rightarrow> (q \<rightarrow> p) \<rightarrow> p\<close>
  using MP 07 12 .

lemma 14: \<open>\<turnstile> ((t \<rightarrow> (q \<rightarrow> p) \<rightarrow> p) \<rightarrow> r) \<rightarrow> (\<sim> p \<rightarrow> q) \<rightarrow> r\<close>
  using MP 01 13 .

lemma 15: \<open>\<turnstile> (\<sim> p \<rightarrow> q) \<rightarrow> (q \<rightarrow> p) \<rightarrow> p\<close>
  using MP 14 02 .

lemma 16: \<open>\<turnstile> p \<rightarrow> p\<close>
  using MP 09 02 .

lemma 17: \<open>\<turnstile> p \<rightarrow> (q \<rightarrow> p) \<rightarrow> p\<close>
  using MP 09 15 .

lemma 18: \<open>\<turnstile> q \<rightarrow> p \<rightarrow> q\<close>
  using MP MP 05 17 03 .

lemma 19: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> q \<rightarrow> r\<close>
  using MP 01 18 .

lemma 20: \<open>\<turnstile> p \<rightarrow> (p \<rightarrow> q) \<rightarrow> q\<close>
  using MP 19 15 .

lemma 21: \<open>\<turnstile> (p \<rightarrow> q \<rightarrow> r) \<rightarrow> q \<rightarrow> p \<rightarrow> r\<close>
  using MP 05 20 .

lemma 22: \<open>\<turnstile> (q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q) \<rightarrow> p \<rightarrow> r\<close>
  using MP 21 01 .

lemma 23: \<open>\<turnstile> ((q \<rightarrow> p \<rightarrow> r) \<rightarrow> s) \<rightarrow> (p \<rightarrow> q \<rightarrow> r) \<rightarrow> s\<close>
  using MP 01 21 .

lemma 24: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> p) \<rightarrow> p\<close>
  using MP MP 23 15 03 .

lemma 25: \<open>\<turnstile> ((p \<rightarrow> r) \<rightarrow> s) \<rightarrow> (p \<rightarrow> q) \<rightarrow> (q \<rightarrow> r) \<rightarrow> s\<close>
  using MP 21 06 .

lemma 26: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> (r \<rightarrow> p) \<rightarrow> p\<close>
  using MP 25 24 .

lemma 28: \<open>\<turnstile> (((r \<rightarrow> p) \<rightarrow> p) \<rightarrow> s) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> s\<close>
  using MP 01 26 .

lemma 29: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> (p \<rightarrow> r) \<rightarrow> r\<close>
  using MP 28 26 .

lemma 31: \<open>\<turnstile> (p \<rightarrow> s) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> (s \<rightarrow> r) \<rightarrow> r\<close>
  using MP 07 29 .

lemma 32: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> (p \<rightarrow> s) \<rightarrow> (s \<rightarrow> r) \<rightarrow> r\<close>
  using MP 21 31 .

lemma 33: \<open>\<turnstile> (p \<rightarrow> s) \<rightarrow> (s \<rightarrow> q \<rightarrow> p \<rightarrow> r) \<rightarrow> q \<rightarrow> p \<rightarrow> r\<close>
  using MP 32 18 .

lemma 34: \<open>\<turnstile> (s \<rightarrow> q \<rightarrow> p \<rightarrow> r) \<rightarrow> (p \<rightarrow> s) \<rightarrow> q \<rightarrow> p \<rightarrow> r\<close>
  using MP 21 33 .

lemma 35: \<open>\<turnstile> (p \<rightarrow> q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q) \<rightarrow> p \<rightarrow> r\<close>
  using MP 34 22 .

lemma 36: \<open>\<turnstile> \<sim> p \<rightarrow> p \<rightarrow> q\<close>
  using MP 21 03 .

lemmas
  Tran = 01 and
  Clavius = 02 and
  Expl = 03 and
  Frege' = 05 and
  Clavius' = 15 and
  Id = 16 and
  Simp = 18 and
  Swap = 21 and
  Tran' = 22 and
  Peirce = 24 and
  Frege = 35 and
  Expl' = 36

lemma Neg1: \<open>\<turnstile> (q \<rightarrow> s) \<rightarrow> (\<sim> q \<rightarrow> s) \<rightarrow> s\<close>
  using MP Clavius' Expl' Frege' Swap by meson

lemma Neg2: \<open>\<turnstile> ((q \<rightarrow> s) \<rightarrow> s) \<rightarrow> \<sim> q \<rightarrow> s\<close>
  using MP Tran MP Swap Expl .

lemma Imp1: \<open>\<turnstile> (q \<rightarrow> s) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
  using MP Peirce Tran Tran' by meson

lemma Imp2: \<open>\<turnstile> ((r \<rightarrow> s) \<rightarrow> s) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
  using MP Tran MP Tran Simp .

lemma Imp3: \<open>\<turnstile> ((q \<rightarrow> s) \<rightarrow> s) \<rightarrow> (r \<rightarrow> s) \<rightarrow> (q \<rightarrow> r) \<rightarrow> s\<close>
  using MP Swap Tran by meson

subsection \<open>Completeness and Main Theorem\<close>

primrec pros where
  \<open>pros (\<cdot> n) = [n]\<close> |
  \<open>pros (\<sim> p) = pros p\<close> |
  \<open>pros (p \<rightarrow> q) = remdups (pros p @ pros q)\<close>

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
  case (Neg q)
  consider \<open>\<not> I \<Turnstile> q\<close> | \<open>I \<Turnstile> q\<close>
    by blast
  then show ?case
  proof cases
    case 1
    then have \<open>lifts I s (pros (\<sim> q)) \<turnstile> q \<rightarrow> s\<close>
      using Neg by simp
    then have \<open>lifts I s (pros (\<sim> q)) \<turnstile> (\<sim> q \<rightarrow> s) \<rightarrow> s\<close>
      using MP' Neg1 add_imply by blast
    with 1 show ?thesis
      by simp
  next
    case 2
    then have \<open>lifts I s (pros (\<sim> q)) \<turnstile> (q \<rightarrow> s) \<rightarrow> s\<close>
      using Neg by simp
    then have \<open>lifts I s (pros (\<sim> q)) \<turnstile> \<sim> q \<rightarrow> s\<close>
      using MP' Neg2 add_imply by blast
    with 2 show ?thesis
      by simp
  qed
next
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
qed (auto intro: Id)

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

text \<open>Numbered lemmas are from Jan Łukasiewicz: Elements of Mathematical Logic (English Tr. 1963)\<close>

end
