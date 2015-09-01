
(* Author: Florian Haftmann, TU Muenchen *)

section {* Some basic facts about discrete summation *}

theory Summation
imports Main
begin

subsection {* Auxiliary *}

lemma add_setsum_orient:
  "setsum f {k..<j} + setsum f {l..<k} = setsum f {l..<k} + setsum f {k..<j}"
  by (fact add.commute)

lemma add_setsum_int:
  fixes j k l :: int
  shows "j < k \<Longrightarrow> k < l \<Longrightarrow>
    setsum f {j..<k} + setsum f {k..<l} = setsum f {j..<l}"
  by (simp_all add: setsum.union_inter [symmetric] ivl_disj_un)


subsection {* The shift operator *}

definition \<Delta> :: "('b::ring_1 \<Rightarrow> 'a::ab_group_add) \<Rightarrow> int \<Rightarrow> 'a"
where
  "\<Delta> f k = f (of_int (k + 1)) - f (of_int k)"

lemma \<Delta>_shift:
  "\<Delta> (\<lambda>k. l + f k) = \<Delta> f"
  by (simp add: \<Delta>_def fun_eq_iff)

lemma \<Delta>_same_shift:
  assumes "\<Delta> f = \<Delta> g"
  shows "\<exists>l. plus l \<circ> f \<circ> of_int = g \<circ> of_int"
proof -
  let ?F = "\<lambda>k. f (of_int k)"
  let ?G = "\<lambda>k. g (of_int k)"
  from assms have "\<And>k. \<Delta> f (of_int k) = \<Delta> g (of_int k)" by simp
  then have k_incr: "\<And>k. ?F (k + 1) - ?G (k + 1) = ?F k - ?G k"
    by (simp add: \<Delta>_def algebra_simps)
  then have "\<And>k. ?F ((k - 1) + 1) - ?G ((k - 1) + 1) =
    ?F (k - 1) - ?G (k - 1)"
    by blast
  then have k_decr: "\<And>k. ?F (k - 1) - ?G (k - 1) = ?F k - ?G k"
    by simp
  have "\<And>k. ?F k - ?G k = ?F 0 - ?G 0"
  proof -
    fix k
    show "?F k - ?G k = ?F 0 - ?G 0"
      by (induct k rule: int_induct)
        (simp_all add: k_incr k_decr del: of_int_add of_int_diff of_int_0)
  qed
  then have "\<And>k. (plus (?G 0 - ?F 0) \<circ> ?F) k = ?G k"
    by (simp add: algebra_simps)
  then have "plus (?G 0 - ?F 0) \<circ> ?F = ?G" ..
  then have "plus (?G 0 - ?F 0) \<circ> f \<circ> of_int = g \<circ> of_int"
    by (simp only: comp_def)
  then show ?thesis ..
qed

lemma \<Delta>_add:
  "\<Delta> (\<lambda>k. f k + g k) k = \<Delta> f k + \<Delta> g k"
  by (simp add: \<Delta>_def)

lemma \<Delta>_factor:
  "\<Delta> (\<lambda>k. c * k) k = c"
  by (simp add: \<Delta>_def algebra_simps)


subsection {* The formal sum operator *}

definition \<Sigma> :: "('b::ring_1 \<Rightarrow> 'a::ab_group_add) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a"
where
  "\<Sigma> f j l = (if j < l then setsum (f \<circ> of_int) {j..<l}
    else if j > l then - setsum (f \<circ> of_int) {l..<j}
    else 0)"

lemma \<Sigma>_same [simp]:
  "\<Sigma> f j j = 0"
  by (simp add: \<Sigma>_def)

lemma \<Sigma>_positive:
  "j < l \<Longrightarrow> \<Sigma> f j l = setsum (f \<circ> of_int) {j..<l}"
  by (simp add: \<Sigma>_def)

lemma \<Sigma>_negative:
  "j > l \<Longrightarrow> \<Sigma> f j l = - \<Sigma> f l j"
  by (simp add: \<Sigma>_def)

lemma \<Sigma>_comp_of_int:
  "\<Sigma> (f \<circ> of_int) = \<Sigma> f"
  by (simp add: \<Sigma>_def fun_eq_iff)

lemma \<Sigma>_const:
  "\<Sigma> (\<lambda>k. c) j l = of_int (l - j) * c"
  by (simp add: \<Sigma>_def algebra_simps of_nat_nat)

lemma \<Sigma>_add:
  "\<Sigma> (\<lambda>k. f k + g k) j l = \<Sigma> f j l + \<Sigma> g j l"
  by (simp add: \<Sigma>_def setsum.distrib)

lemma \<Sigma>_factor:
  "\<Sigma> (\<lambda>k. c * f k) j l = (c::'a::ring) * \<Sigma> (\<lambda>k. f k) j l"
  by (simp add: \<Sigma>_def setsum_right_distrib)

lemma \<Sigma>_concat:
  "\<Sigma> f j k + \<Sigma> f k l = \<Sigma> f j l"
  by (simp add: \<Sigma>_def algebra_simps add_setsum_int)
    (simp_all add: add_setsum_orient [of "\<lambda>k. f (of_int k)" k j l]
      add_setsum_orient [of "\<lambda>k. f (of_int k)" j l k]
      add_setsum_orient [of "\<lambda>k. f (of_int k)" j k l] add_setsum_int)

lemma \<Sigma>_incr_upper:
  "\<Sigma> f j (l + 1) = \<Sigma> f j l + f (of_int l)"
proof -
  have "{l..<l+1} = {l}" by auto
  then have "\<Sigma> f l (l + 1) = f (of_int l)" by (simp add: \<Sigma>_def)
  moreover have "\<Sigma> f j (l + 1) = \<Sigma> f j l + \<Sigma> f l (l + 1)" by (simp add: \<Sigma>_concat)
  ultimately show ?thesis by simp
qed


subsection {* Fundamental lemmas: The relation between @{term \<Delta>} and @{term \<Sigma>} *}

lemma \<Delta>_\<Sigma>:
  "\<Delta> (\<Sigma> f j) = f"
proof
  fix k
  show "\<Delta> (\<Sigma> f j) k = f k"
    by (simp add: \<Delta>_def \<Sigma>_incr_upper)
qed

lemma \<Sigma>_\<Delta>:
  "\<Sigma> (\<Delta> f) j l = f (of_int l) - f (of_int j)"
proof -
  from \<Delta>_\<Sigma> have "\<Delta> (\<Sigma> (\<Delta> f) j) = \<Delta> f" .
  then obtain k where "plus k \<circ> \<Sigma> (\<Delta> f) j \<circ> of_int = f \<circ> of_int"
    by (blast dest: \<Delta>_same_shift)
  then have "\<And>q. f (of_int q) = k + \<Sigma> (\<Delta> f) j q"
    by (simp add: fun_eq_iff)
  then show ?thesis by simp
qed

end

