(*<*)
theory Partition
  imports "HOL-Library.Disjoint_Sets"
begin
(*>*)

section \<open>Valued Partitions\<close>

lemma part_list_set_eq_aux1:
  assumes
    "\<forall>i<length xs. \<forall>j<length xs. i \<noteq> j \<longrightarrow>  fst (xs ! i) \<inter> fst (xs ! j) = {}"
    "{} \<notin> fst ` set xs"
  shows "disjoint (fst ` set xs) \<and> distinct (map fst xs)"
proof -
  from assms(1) have "disjoint (fst ` set xs)"
    by (metis disjnt_def in_set_conv_nth pairwise_imageI)
  moreover have "distinct (map fst xs)"
    using assms
    by (smt (verit) distinct_conv_nth image_iff inf.idem 
        length_map nth_map nth_mem) 
  ultimately show ?thesis
    by blast
qed

lemma part_list_set_eq_aux2:
  assumes
    "disjoint (fst ` set xs)"
    "distinct (map fst xs)"
    "i < length xs"
    "j < length xs"
    "i \<noteq> j"
  shows "fst (xs ! i) \<inter> fst (xs ! j) = {}"
proof -
  from assms have "fst (xs ! i) \<in> fst ` set xs"
    and "fst (xs ! j) \<in> fst ` set xs"
    by auto
  moreover have "fst (xs ! i) \<noteq> fst (xs ! j)"
    using assms(2-) nth_eq_iff_index_eq 
    by fastforce 
  ultimately show ?thesis
    using assms(1) unfolding disjoint_def
    by blast
qed

lemma part_list_eq: 
  "(\<Union>X \<in> fst ` set xs. X) = UNIV
    \<and> (\<forall>i < length xs. \<forall>j < length xs. i \<noteq> j 
      \<longrightarrow> fst (xs ! i) \<inter> fst (xs ! j) = {}) \<and> {} \<notin> fst ` set xs
  \<longleftrightarrow> partition_on UNIV (set (map fst xs)) \<and> distinct (map fst xs)"
  using part_list_set_eq_aux1 part_list_set_eq_aux2
  unfolding partition_on_def by (auto 5 0)

text \<open>@{typ 'd}: domain (such that the union of @{typ 'd} sets form a partition)\<close>
typedef ('d, 'a) part = "{xs :: ('d set \<times> 'a) list. partition_on UNIV (set (map fst xs)) \<and> distinct (map fst xs)}"
  by (rule exI[of _ "[(UNIV, undefined)]"]) (auto simp: partition_on_def)

setup_lifting type_definition_part

lift_bnf (no_warn_wits, no_warn_transfer) (dead 'd, Vals: 'a) part
  unfolding part_list_eq[symmetric]
  by (auto simp: image_iff)

subsection \<open>\<^const>\<open>size\<close> setup\<close>

lift_definition subs :: "('d, 'a) part \<Rightarrow> 'd set list" is "map fst" .

lift_definition Subs :: "('d, 'a) part \<Rightarrow> 'd set set" is "set o map fst" .

lift_definition vals :: "('d, 'a) part \<Rightarrow> 'a list" is "map snd" .

lift_definition SubsVals :: "('d, 'a) part \<Rightarrow> ('d set \<times> 'a) set" is "set" .

lift_definition subsvals :: "('d, 'a) part \<Rightarrow> ('d set \<times> 'a) list" is "id" .

lift_definition size_part :: "('d \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('d, 'a) part \<Rightarrow> nat" is "\<lambda>f g. size_list (\<lambda>(x, y). sum f x + g y)" .

instantiation part :: (type, type) size begin

definition size_part where
size_part_overloaded_def: "size_part = Partition.size_part (\<lambda>_. 0) (\<lambda>_. 0)"

instance ..

end

lemma size_part_overloaded_simps[simp]: "size x = size (vals x)"
  unfolding size_part_overloaded_def
  by transfer (auto simp: size_list_conv_sum_list)

lemma part_size_o_map: "inj h \<Longrightarrow> size_part f g \<circ> map_part h = size_part f (g \<circ> h)"
  by (rule ext, transfer)
    (auto simp: fun_eq_iff map_prod_def o_def split_beta case_prod_beta[abs_def])

setup \<open>
BNF_LFP_Size.register_size_global \<^type_name>\<open>part\<close> \<^const_name>\<open>size_part\<close>
  @{thm size_part_overloaded_def} @{thms size_part_def size_part_overloaded_simps}
  @{thms part_size_o_map}
\<close>

lemma is_measure_size_part[measure_function]: "is_measure f \<Longrightarrow> is_measure g \<Longrightarrow> is_measure (size_part f g)"
  by (rule is_measure_trivial)

lemma size_part_estimation[termination_simp]: "x \<in> Vals xs \<Longrightarrow> y < g x \<Longrightarrow> y < size_part f g xs"
  by transfer (auto simp: termination_simp)

lemma size_part_estimation'[termination_simp]: "x \<in> Vals xs \<Longrightarrow> y \<le> g x \<Longrightarrow> y \<le> size_part f g xs"
  by transfer (auto simp: termination_simp)

lemma size_part_pointwise[termination_simp]: "(\<And>x. x \<in> Vals xs \<Longrightarrow> f x \<le> g x) \<Longrightarrow> size_part h f xs \<le> size_part h g xs"
  by transfer (force simp: image_iff intro!: size_list_pointwise)

subsection \<open>Functions on Valued Partitions\<close>

lemma Vals_code[code]: "Vals x = set (map snd (Rep_part x))"
  by (force simp: Vals_def)

lemma Vals_transfer[transfer_rule]: "rel_fun (pcr_part (=) (=)) (=) (set \<circ> map snd) Vals"
  by (force simp: Vals_def rel_fun_def pcr_part_def cr_part_def rel_set_eq prod.rel_eq list.rel_eq)

lemma set_vals[simp]: "set (vals xs) = Vals xs"
  by transfer simp

lift_definition part_hd :: "('d, 'a) part \<Rightarrow> 'a" is "snd \<circ> hd" .

lift_definition tabulate :: "'d list \<Rightarrow> ('d \<Rightarrow> 'n) \<Rightarrow> 'n \<Rightarrow> ('d, 'n) part" is
  "\<lambda>ds f z. if distinct ds then if set ds = UNIV then map (\<lambda>d. ({d}, f d)) ds else (- set ds, z) # map (\<lambda>d. ({d}, f d)) ds else [(UNIV, z)]"
  by (auto simp: o_def distinct_map inj_on_def partition_on_def disjoint_def)

lift_definition lookup_part :: "('d, 'a) part \<Rightarrow> 'd \<Rightarrow> 'a" is "\<lambda>xs d. snd (the (find (\<lambda>(D, _). d \<in> D) xs))" .

lemma Vals_tabulate[simp]: "Vals (tabulate xs f z) =
  (if distinct xs then if set xs = UNIV then f ` set xs else {z} \<union> f ` set xs else {z})"
  by transfer (auto simp: image_iff)

lemma lookup_part_tabulate[simp]: "lookup_part (tabulate xs f z) x =
  (if distinct xs \<and> x \<in> set xs then f x else z)"
  by (transfer fixing: x xs f z)
    (auto simp: find_dropWhile dropWhile_eq_Cons_conv map_eq_append_conv split: list.splits)

lemma part_hd_Vals[simp]: "part_hd part \<in> Vals part"
  by transfer (auto simp: partition_on_def image_iff intro!: hd_in_set)

lemma lookup_part_Vals[simp]: "lookup_part part d \<in> Vals part"
proof (transfer, goal_cases part)
  case (part xs d)
  then have unique: "(\<forall>i<length xs. \<forall>j<length xs. i \<noteq> j \<longrightarrow> fst (xs ! i) \<inter> fst (xs ! j) = {})"
    using part_list_eq[of xs]
    by simp
  from part obtain D x where D: "(D, x) \<in> set xs" "d \<in> D"
    unfolding partition_on_def
    by fastforce
  with unique have "find (\<lambda>(D, _). d \<in> D) xs = Some (D, x)"
    unfolding set_eq_iff
    by (auto simp: find_Some_iff in_set_conv_nth split_beta)
  with D show ?case
    by (force simp: image_iff)
qed

lemma lookup_part_SubsVals: "\<exists>D. d \<in> D \<and> (D, lookup_part part d) \<in> SubsVals part"
proof (transfer, goal_cases part)
  case (part d xs)
  then have unique: "(\<forall>i<length xs. \<forall>j<length xs. i \<noteq> j \<longrightarrow> fst (xs ! i) \<inter> fst (xs ! j) = {})"
    using part_list_eq[of xs]
    by simp
  from part obtain D x where D: "(D, x) \<in> set xs" "d \<in> D"
    unfolding partition_on_def
    by fastforce
  with unique have "find (\<lambda>(D, _). d \<in> D) xs = Some (D, x)"
    unfolding set_eq_iff
    by (auto simp: find_Some_iff in_set_conv_nth split_beta)
  with D show ?case
    by (force simp: image_iff)
qed

lemma lookup_part_from_subvals: "(D, e) \<in> set (subsvals part) \<Longrightarrow> d \<in> D \<Longrightarrow> lookup_part part d = e"
proof (transfer fixing: D e d, goal_cases)
  case (1 part)
  then show ?case 
  proof (cases "find (\<lambda>(D, _). d \<in> D) part")
    case (Some De)
    from 1 show ?thesis 
      unfolding partition_on_def set_eq_iff Some using Some unfolding find_Some_iff
      by (fastforce dest!: spec[of _ d] simp: in_set_conv_nth split_beta dest: part_list_set_eq_aux2)
  qed (auto simp: partition_on_def image_iff find_None_iff)
qed

lemma size_lookup_part_estimation[termination_simp]: "size (lookup_part part d) < Suc (size_part (\<lambda>_. 0) size part)"
  unfolding less_Suc_eq_le
  by (rule size_part_estimation'[OF _ order_refl]) simp

lemma subsvals_part_estimation[termination_simp]: "(D, e) \<in> set (subsvals part) \<Longrightarrow> size e < Suc (size_part (\<lambda>_. 0) size part)"
  unfolding less_Suc_eq_le
  by (rule size_part_estimation'[OF _ order_refl], transfer)
    (force simp: image_iff)

lemma size_part_hd_estimation[termination_simp]: "size (part_hd part) < Suc (size_part (\<lambda>_. 0) size part)"
  unfolding less_Suc_eq_le
  by (rule size_part_estimation'[OF _ order_refl]) simp

lemma size_last_estimation[termination_simp]: "xs \<noteq> [] \<Longrightarrow> size (last xs) < size_list size xs"
  by (induct xs) auto

lift_definition lookup :: "('d, 'a) part \<Rightarrow> 'd \<Rightarrow> ('d set \<times> 'a)" is "\<lambda>xs d. the (find (\<lambda>(D, _). d \<in> D) xs)" .

lemma snd_lookup[simp]: "snd (lookup part d) = lookup_part part d"
  by transfer auto

lemma distinct_disjoint_uniq: "distinct xs \<Longrightarrow> disjoint (set xs) \<Longrightarrow>
  i < j \<Longrightarrow> j < length xs \<Longrightarrow> d \<in> xs ! i \<Longrightarrow> d \<in> xs ! j \<Longrightarrow> False"
  unfolding disjoint_def disjoint_iff
  by (metis (no_types, lifting) order.strict_trans min.strict_order_iff nth_eq_iff_index_eq nth_mem)

lemma partition_on_UNIV_find_Some:
  "partition_on UNIV (set (map fst part)) \<Longrightarrow> distinct (map fst part) \<Longrightarrow>
  \<exists>y. find (\<lambda>(D, _). d \<in> D) part = Some y"
  unfolding partition_on_def set_eq_iff
  by (auto simp: find_Some_iff in_set_conv_nth
      Ball_def image_iff Bex_def split_beta dest: distinct_disjoint_uniq dest!: spec[of _ d]
      intro!: exI[where P="\<lambda>x. \<exists>y z. P x y z \<and> Q x y z" for P Q, OF exI, OF exI, OF conjI])

lemma fst_lookup: "d \<in> fst (lookup part d)"
proof (transfer fixing: d, goal_cases)
  case (1 part)
  then obtain y where "find (\<lambda>(D, _). d \<in> D) part = Some y" using partition_on_UNIV_find_Some
    by fastforce
  then show ?case
    by (auto dest: find_Some_iff[THEN iffD1])
qed

lemma lookup_subsvals: "lookup part d \<in> set (subsvals part)"
proof (transfer fixing: d, goal_cases)
  case (1 part)
  then obtain y where "find (\<lambda>(D, _). d \<in> D) part = Some y" using partition_on_UNIV_find_Some
    by fastforce
  then show ?case
    by (auto simp: in_set_conv_nth dest: find_Some_iff[THEN iffD1])
qed

lift_definition trivial_part :: "'pt \<Rightarrow> ('d, 'pt) part" is "\<lambda>pt. [(UNIV, pt)]"
  by (simp add: partition_on_space)

lemma part_hd_trivial[simp]: "part_hd (trivial_part pt) = pt"
  unfolding part_hd_def
  by (transfer) simp

lemma SubsVals_trivial[simp]: "SubsVals (trivial_part pt) = {(UNIV, pt)}"
  unfolding SubsVals_def
  by (transfer) simp

section \<open>Partitioned Decision Trees\<close>

(* 'd: domain; 'l: leaf, 'n: variable *)
datatype (dead 'd, leaves: 'l, vars: 'n) pdt = Leaf (unleaf: 'l) | Node 'n "('d, ('d, 'l, 'n) pdt) part"

inductive vars_order :: "'n list \<Rightarrow> ('d, 'l, 'n) pdt \<Rightarrow> bool" where
  "vars_order vs (Leaf _)"
| "\<forall>expl \<in> Vals part1. vars_order vs expl \<Longrightarrow> vars_order (x # vs) (Node x part1)"
| "vars_order vs (Node x part1) \<Longrightarrow> x \<noteq> z \<Longrightarrow> vars_order (z # vs) (Node x part1)"

lemma vars_order_Node:
  assumes "distinct xs"
  shows "vars_order xs (Node x part) = (\<exists>ys zs. xs = ys @ x # zs \<and> (\<forall>e \<in> Vals part. vars_order zs e))"
proof (safe, goal_cases LR RL)
  case LR
  then show ?case 
    by (induct xs "Node x part" rule: vars_order.induct)
      (auto 4 3 intro: exI[of _ "_ # _"])
next
  case (RL ys zs)
  with assms show ?case 
    by (induct ys arbitrary: xs)
      (auto intro: vars_order.intros)
qed

fun distinct_paths where
  "distinct_paths (Leaf _) = True"
| "distinct_paths (Node x part) = (\<forall>e \<in> Vals part. x \<notin> vars e \<and> distinct_paths e)"

fun eval_pdt where
  "eval_pdt v (Leaf l) = l"
| "eval_pdt v (Node x part) = eval_pdt v (lookup_part part (v x))"

lemma eval_pdt_cong: "\<forall>x \<in> vars e. v x = v' x \<Longrightarrow>  eval_pdt v e = eval_pdt v' e"
  by (induct e) auto

lemma vars_order_vars: "vars_order vs e \<Longrightarrow> vars e \<subseteq> set vs"
  by (induct vs e rule: vars_order.induct) auto

lemma vars_order_distinct_paths: "vars_order vs e \<Longrightarrow> distinct vs \<Longrightarrow> distinct_paths e"
  by (induct vs e rule: vars_order.induct) (auto dest!: vars_order_vars)

lemma eval_pdt_fun_upd: "vars_order vs e \<Longrightarrow> x \<notin> set vs \<Longrightarrow> eval_pdt (v(x := d)) e = eval_pdt v e"
  by (induct vs e rule: vars_order.induct) auto

(*<*)
end
(*>*)