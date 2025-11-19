theory MLSSmf_to_MLSS_Auxiliary
  imports Main
begin

lemma card_Union_bounded_above:
  assumes "\<forall>e \<in> S. (card \<circ> f) e \<le> k"
      and "finite S"
    shows "card (\<Union> (f ` S)) \<le> (card S) * k"
proof -
  from assms have "sum (card \<circ> f) S \<le> (card S) * k"
    using sum_bounded_above [where ?A = S and ?f = "card \<circ> f" and ?K = k]
    by simp
  moreover
  have "(\<Sum>e\<in>S. card (f e)) = sum (card \<circ> f) S" by simp
  moreover
  from \<open>finite S\<close> have "card (\<Union> (f ` S)) \<le> (\<Sum>e\<in>S. card (f e))"
    using card_UN_le [where ?A = f and ?I = S] by blast
  ultimately
  show ?thesis by linarith
qed

lemma mem_set_map: "x \<in> set xs \<Longrightarrow> f x \<in> set (map f xs)"
  by simp

lemma filter_subseq: "filter P xs \<in> set (subseqs xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have cons_filter_mem: "x # filter P xs \<in> set (map (Cons x) (subseqs xs))"
    by auto
  have set_subseqs_cons: "set (subseqs (x # xs)) = set (map (Cons x) (subseqs xs)) \<union> set (subseqs xs)"
    by (metis set_append subseqs.simps(2))
  from Cons set_subseqs_cons have "filter P xs \<in> set (subseqs (x # xs))" by blast
  moreover
  from cons_filter_mem set_subseqs_cons have "x # filter P xs \<in> set (subseqs (x # xs))" by blast
  ultimately
  show ?case by force
qed

lemma length_subseq_le: "xs \<in> set (subseqs ys) \<Longrightarrow> length xs \<le> length ys"
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  {assume "xs \<in> set (subseqs (y # ys)) - set (subseqs ys)"
    then have "xs \<in> set (map ((#) y) (subseqs ys))"
      apply (simp only: subseqs.simps)
      using set_append[where ?xs = "map ((#) y) (subseqs ys)" and ?ys = "subseqs ys"]
      by (metis Diff_iff Un_iff)
    then obtain xs' where "xs' \<in> set (subseqs ys)" "xs = y # xs'"
      by fastforce
    with Cons.IH have "length xs' \<le> length ys" by blast
    with \<open>xs = y # xs'\<close> have "length xs \<le> length (y # ys)" by simp
  }
  with Cons.IH show ?case
    by (metis Cons.prems Diff_iff le_Suc_eq length_Cons)
qed

lemma distinct_subseqs: "distinct xs \<Longrightarrow> distinct (subseqs xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have 1: "distinct (subseqs xs)" by auto
  then have 2: "distinct (map ((#) x) (subseqs xs))"
    by (simp add: distinct_conv_nth)
  
  from \<open>distinct (x # xs)\<close> have "x \<notin> set xs" by simp
  then have "\<forall>ys \<in> set (subseqs xs). x \<notin> set ys"
    by (metis PowD imageI in_mono subseqs_powset)
  moreover
  have "\<forall>ys \<in> set (map ((#) x) (subseqs xs)). x \<in> set ys" by fastforce
  ultimately
  have 3: "set (map ((#) x) (subseqs xs)) \<inter> set (subseqs xs) = {}"
    by blast

  show ?case
    apply simp
    using distinct_append[where ?xs = "map ((#) x) (subseqs xs)" and ?ys = "subseqs xs"]
    using 1 2 3 by metis
qed

lemma Sum_le_times:
  "finite s \<Longrightarrow> \<forall>x \<in> s. f x \<le> n \<Longrightarrow> (\<Sum>x \<in> s. f x) \<le> n * card s"
  by (induction s rule: finite_induct) auto

lemma mult_le_power_2: "2 * n \<le> 2 ^ n"
proof -
  have "n \<le> 2 ^ (n - 1)"
    by (induction n) (simp_all add: Suc_leI)
  then show ?thesis
    by (cases n) auto
qed

end
