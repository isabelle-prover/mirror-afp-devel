header {* \isaheader{Auxiliary lemmas} *}

theory Aux imports Main begin

text {* Lemmas about left- and rightmost elements in lists *}

lemma leftmost_element_property:
  assumes ex:"\<exists>x \<in> set xs. P x"
  obtains x' zs ys where "xs = zs@x'#ys" and "P x'" and "\<forall>z \<in> set zs. \<not> P z"
proof -
  from ex have "\<exists>x' zs ys. xs = zs@x'#ys \<and> P x' \<and> (\<forall>z \<in> set zs. \<not> P z)"
  proof(induct xs)
    case Nil thus ?case by simp
  next
    case (Cons x' xs')
    have isin:"\<exists>y\<in>set (x' # xs'). P y"
      and IH:"\<exists>y\<in>set xs'. P y 
              \<Longrightarrow> \<exists>x' zs ys. xs' = zs@x'#ys \<and> P x' \<and> (\<forall>z\<in>set zs. \<not> P z)" .
    show ?case
    proof(cases "P x'")
      case True
      thus ?thesis
	by (metis mem_iff member.simps(1) self_append_conv2)
    next
      case False
      with isin have "\<exists>y\<in>set xs'. P y" by simp
      from IH[OF this] obtain y ys zs where list:"xs' = zs@y#ys"
	and P:"P y" and all:"\<forall>z\<in>set zs. \<not> P z" by blast
      from all False have "\<forall>z\<in>set (x'#zs). \<not> P z" by simp
      with list P show ?thesis by (metis Cons_eq_append_conv)
    qed
  qed
  with that show ?thesis by fastsimp
qed



lemma rightmost_element_property:
  assumes ex:"\<exists>x \<in> set xs. P x"
  obtains x' ys zs where "xs = ys@x'#zs" and "P x'" and "\<forall>z \<in> set zs. \<not> P z"
proof -
  from ex have "\<exists>x' ys zs. xs = ys@x'#zs \<and> P x' \<and> (\<forall>z \<in> set zs. \<not> P z)"
  proof(induct xs)
    case Nil thus ?case by simp
  next
    case (Cons x' xs')
    have isin:"\<exists>y\<in>set (x' # xs'). P y"
      and IH:"\<exists>y\<in>set xs'. P y 
              \<Longrightarrow> \<exists>x' ys zs. xs' = ys @ x' # zs \<and> P x' \<and> (\<forall>z\<in>set zs. \<not> P z)" .
    show ?case
    proof(cases "\<exists>y\<in>set xs'. P y")
      case True
      from IH[OF this] obtain y ys zs where "xs' = ys @ y # zs"
	and "P y" and "\<forall>z\<in>set zs. \<not> P z" by blast
      thus ?thesis by (metis Cons_eq_append_conv)
    next
      case False
      with isin have "P x'" by simp
      with False show ?thesis by (metis eq_Nil_appendI)
    qed
  qed
  with that show ?thesis by fastsimp
qed


text {* Lemma concerning maps and @{text @} *}

lemma map_append_append_maps:
  assumes map:"map f xs = ys@zs"
  obtains xs' xs'' where "map f xs' = ys" and "map f xs'' = zs" and "xs=xs'@xs''"
by (metis append_eq_conv_conj append_take_drop_id assms drop_map take_map that)


text {* Lemma concerning splitting of @{term list}s *}

lemma  path_split_general:
assumes all:"\<forall>zs. xs \<noteq> ys@zs"
obtains j zs where "xs = (take j ys)@zs" and "j < length ys"
  and "\<forall>k > j. \<forall>zs'. xs \<noteq> (take k ys)@zs'"
proof -
  from all have "\<exists>j zs. xs = (take j ys)@zs \<and> j < length ys \<and>
                        (\<forall>k > j. \<forall>zs'. xs \<noteq> (take k ys)@zs')"
  proof(induct ys arbitrary:xs)
    case Nil
    have "\<forall>zs. xs \<noteq> [] @ zs" .
    thus ?case by auto
  next
    case (Cons y' ys')
    have all:"\<forall>zs. xs \<noteq> (y' # ys') @ zs"
      and IH:"\<And>xs. \<forall>zs. xs \<noteq> ys' @ zs \<Longrightarrow>
      \<exists>j zs. xs = take j ys' @ zs \<and> j < length ys' \<and> 
           (\<forall>k. j < k \<longrightarrow> (\<forall>zs'. xs \<noteq> take k ys' @ zs'))" .
    show ?case
    proof(cases xs)
      case Nil thus ?thesis by simp
    next
      case (Cons x' xs')
      with all have disj:"x' \<noteq> y' \<or> (\<forall>zs. xs' \<noteq> ys' @ zs)"
	by simp
      thus ?thesis
      proof(cases "x' = y'")
	case True
	with disj have "\<forall>zs. xs' \<noteq> ys' @ zs" by simp
	from IH[OF this] have "\<exists>j zs. xs' = take j ys' @ zs \<and> j < length ys' \<and>
	  (\<forall>k. j < k \<longrightarrow> (\<forall>zs'. xs' \<noteq> take k ys' @ zs'))" .
	then obtain j zs where xs':"xs' = take j ys' @ zs"
	  and length:"j < length ys'"
	  and all_sub:"\<forall>k. j < k \<longrightarrow> (\<forall>zs'. xs' \<noteq> take k ys' @ zs')"
	  by blast
	from xs' True have take:"(x'#xs') = take (Suc j) (y' # ys') @ zs"
	  by simp
	from all_sub True have all_imp:"\<forall>k. j < k \<longrightarrow> 
	  (\<forall>zs'. (x'#xs') \<noteq> take (Suc k) (y' # ys') @ zs')"
	  by auto
	{ fix l assume less:"(Suc j) < l"
	  then obtain k where l:"l = Suc k" by(cases l) auto
	  with less have "j < k" by simp
	  with all_imp 
	  have "\<forall>zs'. (x'#xs') \<noteq> take (Suc k) (y' # ys') @ zs'"
	    by simp
	  with l have "\<forall>zs'. (x'#xs') \<noteq> take l (y' # ys') @ zs'"
	    by simp }
	with take Cons length show ?thesis
	  by (metis Suc_length_conv less_Suc_eq_0_disj)
      next
	case False
	with Cons have "\<forall>i zs'. i > 0 \<longrightarrow> xs \<noteq> take i (y' # ys') @ zs'"
	  by auto(case_tac i,auto)
	moreover
	have "\<exists>zs. xs = take 0 (y' # ys') @ zs" by simp
	ultimately show ?thesis by(rule_tac x="0" in exI,auto)
      qed
    qed
  qed
  with that show ?thesis by fastsimp
qed


end
