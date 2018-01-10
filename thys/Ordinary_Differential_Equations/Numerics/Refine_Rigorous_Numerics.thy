theory Refine_Rigorous_Numerics
imports
  "HOL-Library.Parallel"
  Transfer_Euclidean_Space_Vector
begin

subsection \<open>Planes\<close>

definition "shows_sctn (sctn::real list sctn) =
  shows ''Sctn '' o shows_paren (shows_words (normal sctn)) o shows_space o
    shows_paren (shows (pstn sctn))"

text \<open>TODO: move!!\<close>

lemma \<comment>"TODO: needed  because @{thm dres.transfer_rec_list} expects one argument,
  but functions with more arguments defined by primrec take several arguments"
  uncurry_rec_list: "rec_list (\<lambda>a b. fn a b) (\<lambda>x xs rr a b. fs x xs rr a b) xs a b =
         rec_list (\<lambda>(a,b). fn a b) (\<lambda>x xs rr (a,b). fs x xs (\<lambda>a b. rr (a,b)) a b) xs (a,b)"
  apply (induction xs arbitrary: a b)
   apply (auto split: prod.splits)
  apply metis
  done

lemma
  sum_list_zip_map:
  assumes "distinct bs"
  assumes "length xs = length bs"
  shows "(\<Sum>(x, y)\<leftarrow>zip xs bs. f x y) = (\<Sum>x\<in>set bs. f (the (map_of (zip bs xs) x)) x)"
  apply (subst sum_list_distinct_conv_sum_set)
   apply (rule distinct_zipI2, fact)
  apply (rule sum.reindex_cong[where l="\<lambda>x. ((the (map_of (zip bs xs) x)), x)"])
    apply (auto simp: in_set_zip in_set_conv_nth)
  subgoal for n
    apply (rule image_eqI[where x="bs!n"])
     apply auto
    apply (cases "map_of (zip bs xs) (bs ! n)")
    using assms
     apply (auto simp: map_of_eq_None_iff in_set_zip map_of_eq_Some_iff)
    using in_set_zip apply fastforce
    using nth_eq_iff_index_eq by blast
  subgoal for i
    apply (rule exI[where x=i])
    apply (auto simp: in_set_conv_nth assms)
    apply (cases "map_of (zip bs xs) (bs ! i)")
    using assms
     apply (auto simp: map_of_eq_None_iff in_set_zip map_of_eq_Some_iff)
    using in_set_zip apply fastforce
    using nth_eq_iff_index_eq by blast
  done


attribute_setup le = \<open>Scan.succeed (Thm.rule_attribute [] (fn context => fn thm => thm RS @{thm order_trans}))\<close>
  "transitive version of inequality (useful for intro)"
attribute_setup ge = \<open>Scan.succeed (Thm.rule_attribute [] (fn context => fn thm => thm RS @{thm order_trans[rotated]}))\<close>
  "transitive version of inequality (useful for intro)"


lemma Id_br: "Id = br (\<lambda>x. x) top"
  by (auto simp: br_def)

lemma br_rel_prod: "br a I \<times>\<^sub>r br b J = br (\<lambda>(x, y). (a x, b y)) (\<lambda>(x, y). I x \<and> J y)"
  by (auto simp: br_def)

lemma list_wset_rel_br_eq: "\<langle>br a I\<rangle>list_wset_rel = br (\<lambda>xs. a ` set xs) (\<lambda>xs. \<forall>x \<in> set xs. I x)"
  by (auto simp: list_wset_rel_def br_def set_rel_def)

lemma mem_br_list_wset_rel_iff:
  "(xs, X) \<in> \<langle>br a I\<rangle>list_wset_rel \<longleftrightarrow> (X = (a ` set xs) \<and> (\<forall>x \<in> set xs. I x))"
  by (auto simp: list_wset_rel_def set_rel_def br_def)

lemma br_list_rel: "\<langle>br a I\<rangle>list_rel = br (map a) (list_all I)"
  apply (auto simp: br_def list_rel_def list_all_iff list_all2_iff split_beta' Ball_def
      in_set_zip intro!: nth_equalityI)
   apply force
  by (metis index_less_size_conv nth_index)

lemma brD: "(c,a)\<in>br \<alpha> I \<Longrightarrow> a = \<alpha> c \<and> I c"
  by (simp add: br_def)


definition [refine_vcg_def]: "list_spec X = SPEC (\<lambda>xs. set xs = X)"

lemma list_spec_impl[autoref_rules]:
  "(\<lambda>x. RETURN x, list_spec) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>\<langle>A\<rangle>list_rel\<rangle>nres_rel"
  if "PREFER single_valued A"
  using that
  apply (auto simp: list_spec_def nres_rel_def RETURN_RES_refine_iff list_wset_rel_br_eq
      br_list_rel intro!: brI dest!: brD
      elim!: single_valued_as_brE)
  subgoal for a I xs
    apply (rule exI[where x="map a xs"])
    by (auto simp: br_def list_all_iff)
  done

primrec nres_of_nress :: "('b \<Rightarrow> bool) \<Rightarrow> 'b nres list \<Rightarrow> 'b list nres"
  where "nres_of_nress P [] = RETURN []"
  | "nres_of_nress P (x#xs) = do {r \<leftarrow> x; rs \<leftarrow> nres_of_nress P xs; RETURN (r#rs)}"

lemma nres_of_nress_SPEC[le, refine_vcg]:
  assumes [refine_vcg]: "\<And>x. x \<in> set xs \<Longrightarrow> x \<le> SPEC P"
  shows "nres_of_nress P xs \<le> SPEC (list_all P)"
  using assms
  apply (induction xs)
    apply (simp add: )
  apply (simp add:)
  apply (intro refine_vcg)
  subgoal for x xs
    apply (rule order_trans[of _ "SPEC P"])
       apply auto
    apply refine_vcg
    done
  done
context begin interpretation autoref_syn .
lemma [autoref_op_pat_def]: "nres_of_nress P x \<equiv> (OP (nres_of_nress P) $ x)"
  by auto
lemma nres_of_nress_alt_def[abs_def]:
  "nres_of_nress P xs = rec_list (RETURN []) (\<lambda>x xs xsa. x \<bind> (\<lambda>r. xsa \<bind> (\<lambda>rs. RETURN (r # rs)))) xs"
  by (induction xs) auto

schematic_goal nres_of_nress_impl:
  "(?r, nres_of_nress P $ x) \<in> \<langle>\<langle>A\<rangle>list_rel\<rangle>nres_rel"
  if [autoref_rules]: "(xi, x) \<in> \<langle>\<langle>A\<rangle>nres_rel\<rangle>list_rel"
  unfolding nres_of_nress_alt_def
  by autoref
concrete_definition nres_of_nress_impl uses nres_of_nress_impl
lemmas [autoref_rules] = nres_of_nress_impl.refine

lemma nres_of_nress_impl_map:
  "nres_of_nress_impl (map f x) =
  rec_list (RETURN []) (\<lambda>x xs r. do { fx \<leftarrow> f x; r \<leftarrow> r; RETURN (fx # r)}) x"
  by (induction x) (auto simp: nres_of_nress_impl_def)

lemma dres_of_dress_impl:
  "nres_of (rec_list (dRETURN []) (\<lambda>x xs r. do { fx \<leftarrow> x; r \<leftarrow> r; dRETURN (fx # r)}) (Parallel.map f x)) \<le>
    nres_of_nress_impl (Parallel.map f' x)"
  if [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  unfolding Parallel.map_def nres_of_nress_impl_map
  apply (induction x)
   apply (auto simp: )
  apply refine_transfer
  done
concrete_definition dres_of_dress_impl uses dres_of_dress_impl
lemmas [refine_transfer] = dres_of_dress_impl.refine

definition PAR_IMAGE::"('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c nres) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'c) set nres" where
  "PAR_IMAGE P f X = do {
    xs \<leftarrow> list_spec X;
    fxs \<leftarrow>nres_of_nress (\<lambda>(x, y). P x y) (Parallel.map (\<lambda>x. do { y \<leftarrow> f x; RETURN (x, y)}) xs);
    RETURN (set fxs)
  }"

lemma [autoref_op_pat_def]: "PAR_IMAGE P \<equiv> OP (PAR_IMAGE P)" by auto
lemma [autoref_rules]: "(Parallel.map, Parallel.map) \<in> (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>B\<rangle>list_rel"
  unfolding Parallel.map_def
  by parametricity
schematic_goal PAR_IMAGE_nres:
  "(?r, PAR_IMAGE P $ f $ X) \<in> \<langle>\<langle>A\<times>\<^sub>rB\<rangle>list_wset_rel\<rangle>nres_rel"
  if [autoref_rules]: "(fi, f) \<in> A \<rightarrow> \<langle>B\<rangle>nres_rel" "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
  and [THEN PREFER_sv_D, relator_props]:
  "PREFER single_valued A"  "PREFER single_valued B"
  unfolding PAR_IMAGE_def
  including art
  by autoref
concrete_definition PAR_IMAGE_nres uses PAR_IMAGE_nres
lemma PAR_IMAGE_nres_impl_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow>
  PREFER single_valued B \<Longrightarrow>
  (\<lambda>fi Xi. Refine_Rigorous_Numerics.PAR_IMAGE_nres fi Xi, PAR_IMAGE P)
    \<in> (A \<rightarrow> \<langle>B\<rangle>nres_rel) \<rightarrow> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>\<langle>A\<times>\<^sub>rB\<rangle>list_wset_rel\<rangle>nres_rel"
  using PAR_IMAGE_nres.refine by force
schematic_goal PAR_IMAGE_dres:
  assumes [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  shows "nres_of (?f) \<le> Refine_Rigorous_Numerics.PAR_IMAGE_nres f' X'"
  unfolding PAR_IMAGE_nres_def
  by refine_transfer
concrete_definition PAR_IMAGE_dres for f X' uses PAR_IMAGE_dres
lemmas [refine_transfer] = PAR_IMAGE_dres.refine

lemma nres_of_nress_Parallel_map_SPEC[le, refine_vcg]:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> SPEC (I x)"
  shows
    "nres_of_nress (\<lambda>(x, y). I x y) (Parallel.map (\<lambda>x. f x \<bind> (\<lambda>y. RETURN (x, y))) xs) \<le>
      SPEC (\<lambda>xrs. map fst xrs = xs \<and> (\<forall>(x, r) \<in> set xrs. I x r))"
  using assms
  apply (induction xs)
  subgoal by (simp add: )
  apply clarsimp
  apply (rule refine_vcg)
  subgoal for x xs
    apply (rule order_trans[of _ "SPEC (I x)"]) apply force
    apply (rule refine_vcg)
    apply (rule refine_vcg)
    apply (rule order_trans, assumption)
    apply refine_vcg
    done
  done

lemma PAR_IMAGE_SPEC[le, refine_vcg]:
  "PAR_IMAGE I f X \<le> SPEC (\<lambda>R. X = fst ` R \<and> (\<forall>(x,r) \<in> R. I x r))"
  if [le, refine_vcg]: "\<And>x. x \<in> X \<Longrightarrow> f x \<le> SPEC (I x)"
  unfolding PAR_IMAGE_def
  by refine_vcg


definition WEAK_ALL:: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> bool nres) \<Rightarrow> bool nres" ("WEAK'_ALL\<^bsup>_\<^esup>") where
  "WEAK_ALL I X P = do {
    (_, b) \<leftarrow> WHILE\<^bsup>\<lambda>(Y, b). b \<longrightarrow> (\<forall>x \<in> X - Y. I x)\<^esup> (\<lambda>(X, b). b \<and> X \<noteq> {}) (\<lambda>(X, b). do {
      ASSERT (X \<noteq> {});
      (x, X') \<leftarrow> op_set_npick_remove X;
      b' \<leftarrow> P x;
      RETURN (X', b' \<and> b)
    }) (X, True); RETURN b}"
schematic_goal WEAK_ALL_list[autoref_rules]:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
      "(P_impl, P) \<in> A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  shows "(?r, WEAK_ALL I X P) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding WEAK_ALL_def
  including art
  by (autoref)
concrete_definition WEAK_ALL_list for Xi P_impl uses WEAK_ALL_list
lemma WEAK_ALL_list_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow> (WEAK_ALL_list, WEAK_ALL I) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> (A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using WEAK_ALL_list.refine by force

schematic_goal WEAK_ALL_transfer_nres:
  assumes [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  shows "nres_of (?f) \<le> WEAK_ALL_list xs f'"
  unfolding WEAK_ALL_list_def
  by refine_transfer
concrete_definition dWEAK_ALL for xs f uses WEAK_ALL_transfer_nres
lemmas [refine_transfer] = dWEAK_ALL.refine

definition WEAK_EX:: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> bool nres) \<Rightarrow> bool nres" ("WEAK'_EX\<^bsup>_\<^esup>") where
  "WEAK_EX I X P = do {
    (_, b) \<leftarrow> WHILE\<^bsup>\<lambda>(Y, b). Y \<subseteq> X \<and> (b \<longrightarrow> (\<exists>x \<in> X. I x))\<^esup> (\<lambda>(X, b). \<not>b \<and> X \<noteq> {}) (\<lambda>(X, b). do {
      ASSERT (X \<noteq> {});
      (x, X') \<leftarrow> op_set_npick_remove X;
      b' \<leftarrow> P x;
      RETURN (X', b' \<or> b)
    }) (X, False); RETURN b}"
schematic_goal WEAK_EX_list[autoref_rules]:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
      "(P_impl, P) \<in> A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  shows "(?r, WEAK_EX I X P) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding WEAK_EX_def
  including art
  by (autoref)
concrete_definition WEAK_EX_list for Xi P_impl uses WEAK_EX_list
lemma WEAK_EX_list_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow> (WEAK_EX_list, WEAK_EX I) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> (A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using WEAK_EX_list.refine by force

schematic_goal WEAK_EX_transfer_nres:
  assumes [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  shows "nres_of (?f) \<le> WEAK_EX_list xs f'"
  unfolding WEAK_EX_list_def
  by refine_transfer
concrete_definition dWEAK_EX for xs f uses WEAK_EX_transfer_nres
lemmas [refine_transfer] = dWEAK_EX.refine

lemma WEAK_EX[le, refine_vcg]:
  assumes [le, refine_vcg]: "\<And>x. F x \<le> SPEC (\<lambda>r. r \<longrightarrow> I x)"
  shows "WEAK_EX I X F \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<exists>x\<in>X. I x))"
  unfolding WEAK_EX_def
  by (refine_vcg ) (auto simp: )

lemma WEAK_ALL[le, refine_vcg]:
  assumes [le, refine_vcg]: "\<And>x. F x \<le> SPEC (\<lambda>r. r \<longrightarrow> I x)"
  shows "WEAK_ALL I X F \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<forall>x\<in>X. I x))"
  unfolding WEAK_ALL_def
  by (refine_vcg) auto

context begin
interpretation autoref_syn .

lemma [autoref_op_pat_def]:
  "WEAK_ALL I \<equiv> OP (WEAK_ALL I)"
  "WEAK_EX I \<equiv> OP (WEAK_EX I)"
  by auto

end

subsection \<open>intersection from given coordinates?!\<close>

(*
definition inter_aform_plane_ortho::
  "nat \<Rightarrow> 'a::executable_euclidean_space aform \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a aform option"
  where
  "inter_aform_plane_ortho p Z n g = do {
    mMs \<leftarrow> those (map (\<lambda>b. bound_intersect_2d_ud p (inner2_aform Z n b) g) Basis_list);
    let l = (\<Sum>(b, m)\<leftarrow>zip Basis_list (map fst mMs). m *\<^sub>R b);
    let u = (\<Sum>(b, M)\<leftarrow>zip Basis_list (map snd mMs). M *\<^sub>R b);
    Some (aform_of_ivl l u)
  }"

lemma
  those_eq_SomeD:
  assumes "those (map f xs) = Some ys"
  shows "ys = map (the o f) xs \<and> (\<forall>i.\<exists>y. i < length xs \<longrightarrow> f (xs ! i) = Some y)"
  using assms
  by (induct xs arbitrary: ys) (auto split: option.split_asm simp: o_def nth_Cons split: nat.split)

lemma
  sum_list_zip_map:
  assumes "distinct xs"
  shows "(\<Sum>(x, y)\<leftarrow>zip xs (map g xs). f x y) = (\<Sum>x\<in>set xs. f x (g x))"
  by (force simp add: sum_list_distinct_conv_sum_set assms distinct_zipI1 split_beta'
    in_set_zip in_set_conv_nth inj_on_convol_ident
    intro!: sum.reindex_cong[where l="\<lambda>x. (x, g x)"])

lemma
  inter_aform_plane_ortho_overappr:
  assumes "inter_aform_plane_ortho p Z n g = Some X"
  shows "{x. \<forall>i \<in> Basis. x \<bullet> i \<in> {y. (g, y) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> i)) ` Affine Z}} \<subseteq> Affine X"
proof -
  let ?inter = "(\<lambda>b. bound_intersect_2d_ud p (inner2_aform Z n b) g)"
  obtain xs
  where xs: "those (map ?inter Basis_list) = Some xs"
    using assms by (cases "those (map ?inter Basis_list)") (auto simp: inter_aform_plane_ortho_def)

  from those_eq_SomeD[OF this]
  obtain y' where xs_eq: "xs = map (the \<circ> ?inter) Basis_list"
    and y': "\<And>i. i < length (Basis_list::'a list) \<Longrightarrow> ?inter (Basis_list ! i) = Some (y' i)"
    by metis
  have "\<forall>(i::'a) \<in> Basis. \<exists>j<length (Basis_list::'a list). i = Basis_list ! j"
    by (metis Basis_list in_set_conv_nth)
  then obtain j where j:
    "\<And>i::'a. i\<in>Basis \<Longrightarrow> j i < length (Basis_list::'a list)"
    "\<And>i::'a. i\<in>Basis \<Longrightarrow> i = Basis_list ! j i"
    by metis
  define y where "y = y' o j"
  with y' j have y: "\<And>i. i \<in> Basis \<Longrightarrow> ?inter i = Some (y i)"
    by (metis comp_def)
  hence y_le: "\<And>i. i \<in> Basis \<Longrightarrow> fst (y i) \<le> snd (y i)"
    by (auto intro!: bound_intersect_2d_ud_segments_of_aform_le)
  hence "(\<Sum>b\<in>Basis. fst (y b) *\<^sub>R b) \<le> (\<Sum>b\<in>Basis. snd (y b) *\<^sub>R b)"
    by (auto simp: eucl_le[where 'a='a])
  with assms have X: "Affine X = {\<Sum>b\<in>Basis. fst (y b) *\<^sub>R b..\<Sum>b\<in>Basis. snd (y b) *\<^sub>R b}"
    by (auto simp: inter_aform_plane_ortho_def sum_list_zip_map xs xs_eq y Affine_aform_of_ivl)
  show ?thesis
  proof safe
    fix x assume x: "\<forall>i\<in>Basis. x \<bullet> i \<in> {y. (g, y) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> i)) ` Affine Z}"
    {
      fix i::'a assume i: "i \<in> Basis"
      from x i have x_in2: "(g, x \<bullet> i) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> i)) ` Affine Z"
        by auto
      from x_in2 obtain e
      where e: "e \<in> UNIV \<rightarrow> {- 1..1}"
        and g: "g = aform_val e Z \<bullet> n"
        and x: "x \<bullet> i = aform_val e Z \<bullet> i"
        by (auto simp: Affine_def valuate_def)
      have "{aform_val e (inner2_aform Z n i)} = {aform_val e (inner2_aform Z n i)} \<inter> {x. fst x = g}"
        by (auto simp: g inner2_def)
      also
      from y[OF \<open>i \<in> Basis\<close>]
      have "?inter i = Some (fst (y i), snd (y i))" by simp
      note bound_intersect_2d_ud_segments_of_aform[OF this e]
      finally have "x \<bullet> i \<in> {fst (y i) .. snd (y i)}"
        by (auto simp: x inner2_def)
    } thus "x \<in> Affine X"
      unfolding X
      by (auto simp: eucl_le[where 'a='a])
  qed
qed

lemma inter_proj_eq:
  fixes n g l
  defines "G \<equiv> {x. x \<bullet> n = g}"
  shows "(\<lambda>x. x \<bullet> l) ` (Z \<inter> G) =
    {y. (g, y) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> l)) ` Z}"
  by (auto simp: G_def)

lemma
  inter_overappr:
  fixes n \<gamma> l
  shows "Z \<inter> {x. x \<bullet> n = g} \<subseteq> {x. \<forall>i \<in> Basis. x \<bullet> i \<in> {y. (g, y) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> i)) ` Z}}"
  by auto

lemma inter_inter_aform_plane_ortho:
  assumes "inter_aform_plane_ortho p Z n g = Some X"
  shows "Affine Z \<inter> {x. x \<bullet> n = g} \<subseteq> Affine X"
proof -
  note inter_overappr[of "Affine Z" n g]
  also note inter_aform_plane_ortho_overappr[OF assms]
  finally show ?thesis .
qed
*)

section \<open>TODO: move\<close>


lemma nres_rel_comp: "\<langle>A\<rangle>nres_rel O \<langle>B\<rangle>nres_rel = \<langle>A O B\<rangle> nres_rel"
  unfolding nres_rel_def
  apply (auto simp: nres_rel_def conc_fun_def converse_relcomp relcomp_Image split: )
  apply (subst converse_relcomp)
  apply (subst relcomp_Image)
  apply (auto split: nres.splits)
  apply (meson Image_mono RES_leof_RES_iff equalityE le_RES_nofailI leofD leof_lift leof_trans)
  apply (rule relcompI)
   defer apply force
  apply (auto simp: converse_relcomp relcomp_Image)
  done

lemma nres_rel_mono: "A \<subseteq> B \<Longrightarrow> \<langle>A\<rangle>nres_rel \<subseteq> \<langle>B\<rangle>nres_rel"
  apply (auto simp: nres_rel_def conc_fun_def)
  apply (split nres.splits)+
  apply auto
  by (meson Image_mono RES_leof_RES_iff converse_mono equalityE le_RES_nofailI leofD leof_lift leof_trans)

end


section \<open>move: multivariate approximation and derivatives\<close>
text \<open>TODO: rename!\<close>

locale second_derivative_within' =
  fixes f f' f'' a G
  assumes first_fderiv[derivative_intros]:
    "\<And>a. a \<in> G \<Longrightarrow> (f has_derivative f' a) (at a within G)"
  assumes in_G: "a \<in> G"
  assumes second_fderiv[derivative_intros]:
    "\<And>i. ((\<lambda>x. f' x i) has_derivative f'' i) (at a within G)"
begin

lemma symmetric_second_derivative_within:
  assumes "a \<in> G"  "open G"
  assumes "\<And>s t. s \<in> {0..1} \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> a + s *\<^sub>R i + t *\<^sub>R j \<in> G"
  shows "f'' i j = f'' j i"
proof (cases "i = j \<or> i = 0 \<or> j = 0")
  case True
  interpret bounded_linear "f'' k" for k
    by (rule has_derivative_bounded_linear) (rule second_fderiv)
  have z1: "f'' j 0 = 0" "f'' i 0 = 0" by (simp_all add: zero)
  have f'z: "f' x 0 = 0" if "x \<in> G" for x
  proof -
    interpret bounded_linear "f' x"
      by (rule has_derivative_bounded_linear) (rule first_fderiv that)+
    show ?thesis by (simp add: zero)
  qed
  note aw = at_within_open[OF \<open>a \<in> G\<close> \<open>open G\<close>]
  have "((\<lambda>x. f' x 0) has_derivative (\<lambda>_. 0)) (at a within G)"
    apply (rule has_derivative_transform_within)
       apply (rule has_derivative_const[where c=0])
      apply (rule zero_less_one)
     apply fact
    by (simp add: f'z)
  from has_derivative_unique[OF second_fderiv[unfolded aw] this[unfolded aw]]
  have "f'' 0 = (\<lambda>_. 0)" .
  with True z1 show ?thesis
    by (auto)
next
  case False
  show ?thesis
    using first_fderiv _ _ _ _ assms(1,3-)
    by (rule symmetric_second_derivative_aux[])
       (use False in \<open>auto intro!: derivative_eq_intros simp: blinfun.bilinear_simps assms\<close>)
qed

end

locale second_derivative_on_open =
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::banach"
    and f' :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
    and f'' :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
    and a :: 'a
    and G :: "'a set"
  assumes first_fderiv[derivative_intros]:
    "\<And>a. a \<in> G \<Longrightarrow> (f has_derivative f' a) (at a)"
  assumes in_G: "a \<in> G" and open_G: "open G"
  assumes second_fderiv[derivative_intros]:
    "((\<lambda>x. f' x i) has_derivative f'' i) (at a)"
begin

lemma symmetric_second_derivative:
  assumes "a \<in> G"
  shows "f'' i j = f'' j i"
proof -
  interpret second_derivative_within'
    by unfold_locales
      (auto intro!: derivative_intros intro: has_derivative_at_within \<open>a \<in> G\<close>)
  from \<open>a \<in> G\<close> open_G
  obtain e where e: "e > 0" "\<And>y. dist y a < e \<Longrightarrow> y \<in> G"
    by (force simp: open_dist)
  define e' where "e' = e / 3"
  define i' j' where "i' = e' *\<^sub>R i /\<^sub>R norm i" and "j' = e' *\<^sub>R j /\<^sub>R norm j"
  hence "norm i' \<le> e'" "norm j' \<le> e'"
    by (auto simp: field_simps e'_def \<open>0 < e\<close> less_imp_le)
  hence "\<bar>s\<bar> \<le> 1 \<Longrightarrow> \<bar>t\<bar> \<le> 1 \<Longrightarrow> norm (s *\<^sub>R i' + t *\<^sub>R j') \<le> e' + e'" for s t
    by (intro norm_triangle_le[OF add_mono])
      (auto intro!: order_trans[OF mult_left_le_one_le])
  also have "\<dots> < e" by (simp add: e'_def \<open>0 < e\<close>)
  finally
  have "f'' i' j' = f'' j' i'"
    by (intro symmetric_second_derivative_within \<open>a \<in> G\<close> e)
      (auto simp add: dist_norm open_G)
  moreover
  interpret f'': bounded_linear "f'' k" for k
    by (rule has_derivative_bounded_linear) (rule second_fderiv)
  note aw = at_within_open[OF \<open>a \<in> G\<close> \<open>open G\<close>]
  have z1: "f'' j 0 = 0" "f'' i 0 = 0" by (simp_all add: f''.zero)
  have f'z: "f' x 0 = 0" if "x \<in> G" for x
  proof -
    interpret bounded_linear "f' x"
      by (rule has_derivative_bounded_linear) (rule first_fderiv that)+
    show ?thesis by (simp add: zero)
  qed
  have "((\<lambda>x. f' x 0) has_derivative (\<lambda>_. 0)) (at a within G)"
    apply (rule has_derivative_transform_within)
       apply (rule has_derivative_const[where c=0])
      apply (rule zero_less_one)
     apply fact
    by (simp add: f'z)
  from has_derivative_unique[OF second_fderiv[unfolded aw] this[unfolded aw]]
  have z2: "f'' 0 = (\<lambda>_. 0)" .
  have "((\<lambda>a. f' a (r *\<^sub>R x)) has_derivative f'' (r *\<^sub>R x)) (at a within G)"
    "((\<lambda>a. f' a (r *\<^sub>R x)) has_derivative (\<lambda>y. r *\<^sub>R f'' x y)) (at a within G)"
    for r x
    subgoal by (rule second_fderiv)
    subgoal
    proof -
      have "((\<lambda>a. r *\<^sub>R f' a (x)) has_derivative (\<lambda>y. r *\<^sub>R f'' x y)) (at a within G)"
        by (auto intro!: derivative_intros)
      then show ?thesis
        apply (rule has_derivative_transform[rotated 2])
         apply (rule in_G)
        subgoal premises prems for a'
        proof -
          interpret bounded_linear "f' a'"
            apply (rule has_derivative_bounded_linear)
            by (rule first_fderiv[OF prems])
          show ?thesis
            by (simp add: scaleR)
        qed
        done
    qed
    done
  then have "((\<lambda>a. f' a (r *\<^sub>R x)) has_derivative f'' (r *\<^sub>R x)) (at a)"
    "((\<lambda>a. f' a (r *\<^sub>R x)) has_derivative (\<lambda>y. r *\<^sub>R f'' x y)) (at a)" for r x
    unfolding aw by auto
  then have f'z: "f'' (r *\<^sub>R x) = (\<lambda>y. r *\<^sub>R f'' x y)" for r x
    by (rule has_derivative_unique[where f="(\<lambda>a. f' a (r *\<^sub>R x))"])
  ultimately show ?thesis
    using e(1)
    by (auto simp: i'_def j'_def e'_def f''.scaleR z1 z2
      blinfun.zero_right blinfun.zero_left
      blinfun.scaleR_left blinfun.scaleR_right algebra_simps)
qed

end


subsection \<open>Derivatives\<close>

section \<open>move\<close>


lemma halfspaces_union:
  "sbelow_halfspaces (a \<union> b) = sbelow_halfspaces a \<inter> sbelow_halfspaces b"
  "below_halfspaces (a \<union> b) = below_halfspaces a \<inter> below_halfspaces b"
  by (auto simp: halfspace_simps)

lemma plane_of_subset_halfspace: "plane_of sctn \<subseteq> below_halfspace sctn"
  by (auto simp: plane_of_def below_halfspace_def le_halfspace_def)

lemma halfspace_subsets: "sbelow_halfspaces sctns \<subseteq> below_halfspaces sctns"
  and halfspace_subset: "sbelow_halfspace sctn \<subseteq> below_halfspace sctn"
  by (force simp: plane_of_def halfspace_simps)+

lemma sbelow_halfspaces_insert:
  "sbelow_halfspaces (insert x2 stop_sctns) = sbelow_halfspace x2 \<inter> sbelow_halfspaces stop_sctns"
  by (auto simp: sbelow_halfspaces_def)

lemma sbelow_halfspaces_antimono:
  assumes "A \<subseteq> B"
  shows "sbelow_halfspaces B \<subseteq> sbelow_halfspaces A"
  using assms
  by (auto simp: halfspace_simps)

lemma plane_in_halfspace[intro, simp]:
  "x \<in> plane_of sctn \<Longrightarrow> x \<in> below_halfspace sctn"
  "x \<in> plane_of sctn \<Longrightarrow> x \<in> above_halfspace sctn"
  by (auto simp: halfspace_simps plane_of_def)

lemma closure_shalfspace[intro, simp]:
  assumes "normal sctn \<noteq> 0"
  shows "closure (sbelow_halfspace sctn) = below_halfspace sctn"
    and "closure (sabove_halfspace sctn) = above_halfspace sctn"
  using closure_halfspace_lt[OF assms] closure_halfspace_gt[OF assms]
  by (auto simp: halfspace_simps inner_commute)

lemma closure_sbelow_halfspaces[intro, simp]:
  assumes "\<And>sctn. sctn \<in> sctns \<Longrightarrow> normal sctn \<noteq> 0"
  shows "closure (sbelow_halfspaces sctns) \<subseteq> below_halfspaces sctns"
proof -
  have *: "{closure S |S. S \<in> sbelow_halfspace ` sctns} = {S |S. S \<in> below_halfspace ` sctns}"
    by (auto simp: assms intro!: closure_shalfspace(1)[symmetric] exI)
  show ?thesis
    unfolding sbelow_halfspaces_def
    by (rule order_trans[OF closure_Int]) (auto simp: halfspace_simps *)
qed

lemma halfspaces_empty[simp]: "sbelow_halfspaces {} = UNIV" "below_halfspaces {} = UNIV"
  by (auto simp: halfspace_simps)

lemma halfspaces_planeI:
  assumes "x \<in> below_halfspaces (s)"
  assumes "x \<notin> UNION (s) plane_of"
  shows "x \<in> sbelow_halfspaces (s)"
  using assms
  by (force simp: halfspace_simps plane_of_def)


subsection \<open>Section\<close>

definition sctn_rel where sctn_rel_internal: "sctn_rel A = {(a, b). rel_sctn (in_rel A) a b}"
lemma sctn_rel_def: "\<langle>A\<rangle>sctn_rel = {(a, b). rel_sctn (in_rel A) a b}"
  by (auto simp: sctn_rel_internal relAPP_def)

lemma single_valued_sctn_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>sctn_rel)"
  using sctn.right_unique_rel[of "in_rel A"]
  by (auto simp: single_valued_def right_unique_def sctn_rel_def)

consts i_sctn :: "interface \<Rightarrow> interface" \<comment> \<open>section datatype\<close>
lemmas [autoref_rel_intf] = REL_INTFI[of sctn_rel i_sctn]

section \<open>\<close>

context begin interpretation autoref_syn .
lemma finite_list_set_rel[autoref_rules]: "(\<lambda>_. True, finite) \<in> \<langle>A\<rangle>list_set_rel \<rightarrow> bool_rel"
  by (auto simp: list_set_rel_def br_def)
end

lemma list_set_rel_finiteD: "(xs, X) \<in> \<langle>A\<rangle>list_set_rel \<Longrightarrow> finite X"
  by (auto simp: list_set_rel_def br_def)

lemma
  insert_mem_set_rel_iff:
  assumes "single_valued A"
  shows "(insert x (set xs), XXS) \<in> \<langle>A\<rangle>set_rel \<longleftrightarrow> (\<exists>X XS. (x, X) \<in> A \<and> (set xs, XS) \<in> \<langle>A\<rangle>set_rel \<and> XXS = insert X XS)"
  using assms
  apply (auto simp: set_rel_def single_valuedD)
  subgoal for a
    apply (cases "x \<in> set xs")
    subgoal by (rule exI[where x=a]) auto
    subgoal
      apply (rule exI[where x=a])
      apply auto
      apply (rule exI[where x="{y\<in>XXS. (\<exists>x\<in>set xs. (x, y) \<in> A)}"])
      apply auto
      subgoal by (drule bspec, assumption) auto
      subgoal by (meson single_valuedD)
      done
    done
  done

lemma image_mem_set_rel_iff:
  shows "(f ` x, y) \<in> \<langle>R\<rangle>set_rel \<longleftrightarrow> (x, y) \<in> \<langle>br f top O R\<rangle>set_rel"
proof -
  have "z \<in> Domain ({(c, a). a = f c} O R)"
    if "f ` x \<subseteq> Domain R" "z \<in> x"
    for z
  proof -
    have "(f z, fun_of_rel R (f z)) \<in> R"
      using that
      by (auto intro!: for_in_RI)
    then show ?thesis
      by (auto intro!: Domain.DomainI[where b="fun_of_rel R (f z)"] relcompI[where b="f z"])
  qed
  then show ?thesis
    by (auto simp: set_rel_def relcomp.simps br_def)
qed

definition cfuncset where "cfuncset l u X = funcset {l .. u} X \<inter> Collect (continuous_on {l .. u})"
lemma cfuncset_iff: "f \<in> cfuncset l u X \<longleftrightarrow> (\<forall>i\<in>{l .. u}. f i \<in> X) \<and> continuous_on {l .. u} f"
  unfolding cfuncset_def by auto

lemma cfuncset_continuous_onD: "f \<in> cfuncset 0 h X \<Longrightarrow> continuous_on {0..h} f"
  by (simp add: cfuncset_iff)


section \<open>interfaces\<close>

consts i_appr :: interface \<comment> \<open>reachable set\<close>

consts i_coll :: "interface \<Rightarrow> interface \<Rightarrow> interface" \<comment> \<open>collection of reachable sets\<close>

section \<open>hyperplanes\<close>

section \<open>Operations on Enclosures (Sets)\<close>

definition [refine_vcg_def]: "split_spec X = SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"

definition [refine_vcg_def]: "split_spec_param (n::nat) X = SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"
definition [refine_vcg_def]: "split_spec_params d n X = SPEC (\<lambda>(A, B). env_len A d \<and> env_len B d \<and> X \<subseteq> A \<union> B)"

definition [refine_vcg_def]: "split_spec_exact x = SPEC (\<lambda>(a, b). x = a \<union> b)"

definition [refine_vcg_def]: "Inf_specs d X = SPEC (\<lambda>r::real list. length r = d \<and> (\<forall>x \<in> X. list_all2 (\<le>) r x))"
definition [refine_vcg_def]: "Inf_spec X = SPEC (\<lambda>r. \<forall>x \<in> X. r \<le> x)"

definition [refine_vcg_def]: "Sup_specs d X = SPEC (\<lambda>r::real list. length r = d \<and> (\<forall>x \<in> X. list_all2 (\<le>) x r))"
definition [refine_vcg_def]: "Sup_spec X = SPEC (\<lambda>r. \<forall>x \<in> X. x \<le> r)"

definition [refine_vcg_def]: "Inf_inners X y = SPEC (\<lambda>r::real. (\<forall>x \<in> X. r \<le> inner_lv_rel x y))" \<comment>"TODO: generic image of aforms, then Inf"
definition [refine_vcg_def]: "Inf_inner X y = SPEC (\<lambda>r. \<forall>x \<in> X. r \<le> x \<bullet> y)" \<comment>"TODO: generic image of aforms, then Inf"

definition [refine_vcg_def]: "Sup_inners X y = SPEC (\<lambda>r::real. (\<forall>x \<in> X. r \<ge> inner_lv_rel x y))" \<comment>"TODO: generic image of aforms, then Inf"
definition [refine_vcg_def]: "Sup_inner X y = SPEC (\<lambda>r. \<forall>x \<in> X. x \<bullet> y \<le> r)" \<comment>"TODO: generic image of aforms. then Sup"

definition "plane_ofs sctn = {x. inner_lv_rel x (normal sctn) = pstn sctn}"
definition [refine_vcg_def]: "inter_sctn_specs d X sctn = SPEC (\<lambda>R. env_len R d \<and> X \<inter> plane_ofs sctn \<subseteq> R \<and> R \<subseteq> plane_ofs sctn)"
definition [refine_vcg_def]: "inter_sctn_spec X sctn = SPEC (\<lambda>R. X \<inter> plane_of sctn \<subseteq> R \<and> R \<subseteq> plane_of sctn)"

definition [refine_vcg_def]: "intersects_spec X sctn = SPEC (\<lambda>b. b \<or> X \<inter> plane_of sctn = {})"

definition [refine_vcg_def]: "intersects_sctns_spec X sctns = SPEC (\<lambda>b. b \<or> X \<inter> UNION sctns plane_of = {})"

definition [refine_vcg_def]: "reduce_spec (C::'b list \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> bool) X = SPEC (\<lambda>R. X \<subseteq> R)"
definition [refine_vcg_def]: "reduce_specs d (C::'b list \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> bool) X = SPEC (\<lambda>R. env_len R d \<and> X \<subseteq> R)"

definition [refine_vcg_def]: "width_spec X = SPEC (top::real\<Rightarrow>_)"

definition [refine_vcg_def]: "ivl_rep_of_set X = SPEC (\<lambda>(i, s). i \<le> s \<and> X \<subseteq> {i .. s})"

definition "strongest_direction T =
  (let
    b = fold (\<lambda>b' b. if abs (T \<bullet> b') \<ge> abs (T \<bullet> b) then b' else b) (Basis_list::'a::executable_euclidean_space list) 0
  in
    (sgn (T \<bullet> b) *\<^sub>R b, abs (T \<bullet> b)))"

subsubsection \<open>interval approximation of many\<close>

definition ivl_rep_of_sets::"'a::lattice set set \<Rightarrow> ('a \<times> 'a) nres" where
  "ivl_rep_of_sets (XS::'a set set) = SPEC (\<lambda>(i, s). i \<le> s \<and> (\<forall>X\<in>XS. X \<subseteq> {i..s}))"
lemmas [refine_vcg] = ivl_rep_of_sets_def[THEN eq_refl, THEN order.trans]


subsection \<open>subset approximation\<close>

definition[refine_vcg_def]:  "subset_spec X Y = SPEC (\<lambda>b. b \<longrightarrow> X \<subseteq> Y)"

definition [refine_vcg_def]: "above_sctn X sctn = SPEC (\<lambda>b. b \<longrightarrow> (X \<subseteq> sabove_halfspace sctn))"

lemma above_sctn_nres: "do { ii \<leftarrow> Inf_inner X (normal sctn); RETURN (ii > pstn sctn)} \<le> above_sctn X sctn"
  by (auto simp: above_sctn_def Inf_inner_def sabove_halfspace_def gt_halfspace_def intro!: refine_vcg)

definition [refine_vcg_def]: "below_sctn X sctn = SPEC (\<lambda>b. b \<longrightarrow> (X \<subseteq> below_halfspace sctn))"

lemma below_sctn_nres:
  "do { si \<leftarrow> Sup_inner X (normal sctn); RETURN (si \<le> pstn sctn)} \<le> below_sctn X sctn"
  by (auto simp: below_sctn_def Sup_inner_def below_halfspace_def le_halfspace_def intro!: refine_vcg)

definition [refine_vcg_def]: "sbelow_sctn X sctn = SPEC (\<lambda>b. b \<longrightarrow> (X \<subseteq> sbelow_halfspace sctn))"

lemma sbelow_sctn_nres:
  "do { si \<leftarrow> Sup_inner X (normal sctn); RETURN (si < pstn sctn)} \<le> sbelow_sctn X sctn"
  by (auto simp: sbelow_sctn_def Sup_inner_def sbelow_halfspace_def lt_halfspace_def intro!: refine_vcg)

definition [refine_vcg_def]: "sbelow_sctns X sctn = SPEC (\<lambda>b. b \<longrightarrow> (X \<subseteq> sbelow_halfspaces sctn))"

lemma sbelow_sctns_nres:
  assumes "finite sctns"
  shows "FOREACH\<^bsup>(\<lambda>it b. b \<longrightarrow> (\<forall>sctn \<in> sctns - it. X \<subseteq> sbelow_halfspace sctn))\<^esup> sctns  (\<lambda>sctn b.
    do {
      b' \<leftarrow> sbelow_sctn X sctn;
      RETURN (b' \<and> b)}) True \<le> sbelow_sctns X sctns"
  unfolding sbelow_sctns_def
  by (refine_vcg assms) (auto simp: sbelow_halfspaces_def)


definition [refine_vcg_def]: "disjoint_sets X Y = SPEC (\<lambda>b. b \<longrightarrow> X \<inter> Y = {})"


section \<open>Dependencies (Set of vectors)\<close>

subsection \<open>singleton projection\<close>

definition [refine_vcg_def]: "nth_image_precond X n \<longleftrightarrow> X \<noteq> {} \<and> (\<forall>xs\<in>X. n < length xs \<and> env_len X (length xs))"

definition [refine_vcg_def]: "nth_image X n = SPEC (\<lambda>R. nth_image_precond X n \<and> (R = (\<lambda>x. x ! n) ` X))"


subsection \<open>projection\<close>

definition "project_env_precond env is \<equiv> (\<forall>i \<in> set is. \<forall>xs\<in>env. i < length xs \<and> env_len env (length xs))"

definition project_env where [refine_vcg_def]:
  "project_env env is = SPEC (\<lambda>R. project_env_precond env is \<and> env_len R (length is) \<and> (\<lambda>xs. map (\<lambda>i. xs ! i) is) ` env \<subseteq> R)"

subsection \<open>expressions\<close>

definition approx_slp_spec::"floatarith list \<Rightarrow> nat \<Rightarrow> slp \<Rightarrow> real list set \<Rightarrow> real list set option nres"
  where [refine_vcg_def]: "approx_slp_spec fas l slp env =
    (ASSERT (slp_of_fas fas = slp \<and> length fas = l)) \<bind>
    (\<lambda>_. SPEC (\<lambda>R. case R of Some R \<Rightarrow> \<exists>e. env_len env e \<and> env_len R l \<and>
        (\<forall>e\<in>env. interpret_floatariths fas e \<in> R) | None \<Rightarrow> True))"

definition approx_form_spec::"form \<Rightarrow> real list set \<Rightarrow> bool nres"
where "approx_form_spec ea E = SPEC (\<lambda>r. r \<longrightarrow> (\<forall>e\<in>E. interpret_form ea e))"

definition isFDERIV_spec
  :: "nat \<Rightarrow> nat list \<Rightarrow> floatarith list \<Rightarrow> real list set \<Rightarrow> bool nres"
  where "isFDERIV_spec N xs fas VS = SPEC (\<lambda>r. r \<longrightarrow> (\<forall>vs \<in> VS. isFDERIV N xs fas vs))"

subsection \<open>singleton environment\<close>

definition sings_spec where [refine_vcg_def]:
  "sings_spec X = SPEC (\<lambda>env. env_len env 1 \<and> X \<noteq> {} \<and> (env = (\<lambda>x. [x]) ` X))"


section \<open>Implementations\<close>

context begin
interpretation autoref_syn .

lemma list_ex_rec_list: "list_ex P xs = rec_list False (\<lambda>x xs b. P x \<or> b) xs"
  by (induct xs) simp_all

lemma list_ex_param[autoref_rules, param]:
  "(list_ex, list_ex) \<in> (A \<rightarrow> bool_rel) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"
  unfolding list_ex_rec_list
  by parametricity

lemma zip_param[autoref_rules, param]:
  "(zip, zip) \<in> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A \<times>\<^sub>r A\<rangle>list_rel"
  by (rule param_zip)

lemma [autoref_rules]:
  "((=), (=)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> bool_rel"
  "((\<le>), (\<le>)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> bool_rel"
  "((<), (<)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> bool_rel"
  "(min, min) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(max, max) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((+), (+)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((-), (-)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((/), (/)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(( * ), ( * )) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((^), (^)) \<in> rnv_rel \<rightarrow> nat_rel \<rightarrow> rnv_rel"
  "(int, int) \<in> nat_rel \<rightarrow> int_rel"
  "(Float, Float) \<in> int_rel \<rightarrow> int_rel \<rightarrow> Id"
  "(real_of_float, real_of_float) \<in> Id \<rightarrow> rnv_rel"
  "(upto, upto) \<in> int_rel \<rightarrow> int_rel \<rightarrow> \<langle>int_rel\<rangle>list_rel"
  "(upt, upt) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel"
  "(product_lists, product_lists) \<in> \<langle>\<langle>int_rel\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>int_rel\<rangle>list_rel\<rangle>list_rel"
  "(floor, floor) \<in> rnv_rel \<rightarrow> int_rel"
  by auto

end

subsection \<open>composed set relations\<close>

definition Union_rel::"('l \<times> 'a set) set \<Rightarrow> ('a \<times> 'b set) set \<Rightarrow> ('l \<times> 'b set) set"
  where Union_rel_internal: "Union_rel L S = L O \<langle>S\<rangle>set_rel O br Union top"
lemmas [autoref_rel_intf] = REL_INTFI[of "Union_rel" "i_coll" for L S R]

lemma Union_rel_def: "\<langle>L, S\<rangle>Union_rel = L O \<langle>S\<rangle>set_rel O br Union top"
  unfolding relAPP_def Union_rel_internal ..

lemma single_valued_Union_rel[relator_props]:
  "single_valued L \<Longrightarrow> single_valued R \<Longrightarrow> single_valued (\<langle>L, R\<rangle>Union_rel)"
  unfolding relAPP_def
  by (auto simp: Union_rel_internal intro!: relator_props intro: single_valuedI)

lemma Union_rel_br: "\<langle>(br l lI), (br s sI)\<rangle>Union_rel = br (\<lambda>a. \<Union>(s ` (l a))) (\<lambda>a. lI a \<and> (\<forall>c \<in> l a. sI c))"
  unfolding Union_rel_def br_def
  apply (safe)
  subgoal by (force simp: set_rel_def)
  subgoal by (fastforce simp: set_rel_def)
  subgoal by (force simp: set_rel_def)
  subgoal for a
    by (auto intro!: relcompI[where b="l a"] relcompI[where b="s ` l a"] simp: set_rel_def)
  done

consts i_default::"interface \<Rightarrow> interface"

definition default_rel_internal: "default_rel d X = insert (None, d) ((\<lambda>(x, y). (Some x, y)) ` X)"
lemma default_rel_def: "\<langle>X\<rangle>default_rel d = insert (None, d) ((\<lambda>(x, y). (Some x, y)) ` X)"
  by (auto simp: relAPP_def default_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of "default_rel d" i_default for d]

lemma single_valued_default_rel[relator_props]:
  "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>default_rel d)"
  by (auto simp: default_rel_def intro!: relator_props) (auto simp: single_valued_def)

lemma
  mem_default_relI:
  assumes "a = None \<Longrightarrow> b = d"
  assumes "\<And>x. a = Some x \<Longrightarrow> (x, b) \<in> R"
  shows "(a, b) \<in> \<langle>R\<rangle>default_rel d"
  using assms image_iff
  by (force simp: default_rel_def)

lemma Some_mem_default_rel: "(Some x, y) \<in> \<langle>X\<rangle>default_rel d\<longleftrightarrow> (x, y) \<in> X"
  by (auto simp: default_rel_def)

lemma option_rel_inverse[simp]: "(\<langle>R\<rangle>option_rel)\<inverse> = \<langle>R\<inverse>\<rangle>option_rel"
  by (auto simp: option_rel_def)

consts i_inter::"interface \<Rightarrow> interface \<Rightarrow> interface"
hide_const (open) inter_rel
definition inter_rel_internal: "inter_rel AA BB = {((a, b), A \<inter> B)|a b A B. (a, A) \<in> AA \<and> (b, B) \<in> BB}"
lemma inter_rel_def: "\<langle>AA, BB\<rangle>inter_rel = {((a, b), A \<inter> B)|a b A B. (a, A) \<in> AA \<and> (b, B) \<in> BB}"
  by (auto simp: inter_rel_internal relAPP_def)
lemmas [autoref_rel_intf] = REL_INTFI[of inter_rel i_inter]

context autoref_syn begin

no_notation funcset (infixr "\<rightarrow>" 60)

end

context begin interpretation autoref_syn .
lemma [autoref_rules]:
  shows
  "(Sctn, Sctn) \<in> A \<rightarrow> rnv_rel \<rightarrow> \<langle>A\<rangle>sctn_rel"
  "(normal, normal) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> A"
  "(pstn, pstn) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> rnv_rel"
  by (auto simp: sctn_rel_def sctn.rel_sel)

lemma gen_eq_sctn[autoref_rules]:
  assumes "GEN_OP eq (=) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>sctn1 sctn2. eq (normal sctn1) (normal sctn2) \<and> pstn sctn1 = pstn sctn2, (=)) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> \<langle>A\<rangle>sctn_rel \<rightarrow> bool_rel"
  apply safe
  subgoal for a b c d
    using assms
    by (cases a; cases b; cases c; cases d) (auto simp: sctn_rel_def dest: fun_relD)
  subgoal for a b c d
    using assms
    by (cases a; cases b; cases c; cases d) (auto simp: sctn_rel_def dest: fun_relD)
  subgoal for a b c d
    using assms
    by (cases a; cases b; cases c; cases d) (auto simp: sctn_rel_def dest: fun_relD)
  done

end

abbreviation "sctns_rel \<equiv> \<langle>\<langle>lv_rel\<rangle>sctn_rel\<rangle>list_set_rel"

definition plane_rel_internal: "plane_rel A = \<langle>A\<rangle>sctn_rel O br plane_of top"
lemma plane_rel_def: "\<langle>A\<rangle>plane_rel = \<langle>A\<rangle>sctn_rel O br plane_of top"
  by (simp add: plane_rel_internal relAPP_def)
consts i_plane::"interface\<Rightarrow>interface"
lemmas [autoref_rel_intf] = REL_INTFI[of plane_rel i_plane]

definition below_rel_internal: "below_rel A = \<langle>A\<rangle>sctn_rel O br below_halfspace top"
lemma below_rel_def: "\<langle>A\<rangle>below_rel = \<langle>A\<rangle>sctn_rel O br below_halfspace top"
  by (simp add: below_rel_internal relAPP_def)
consts i_below::"interface\<Rightarrow>interface"
lemmas [autoref_rel_intf] = REL_INTFI[of below_rel i_below]

definition sbelow_rel_internal: "sbelow_rel A = \<langle>A\<rangle>sctn_rel O br sbelow_halfspace top"
lemma sbelow_rel_def: "\<langle>A\<rangle>sbelow_rel = \<langle>A\<rangle>sctn_rel O br sbelow_halfspace top"
  by (simp add: sbelow_rel_internal relAPP_def)
consts i_sbelow::"interface\<Rightarrow>interface"
lemmas [autoref_rel_intf] = REL_INTFI[of sbelow_rel i_sbelow]

definition sbelows_rel_internal: "sbelows_rel A = \<langle>\<langle>A\<rangle>sctn_rel\<rangle>list_set_rel O br sbelow_halfspaces top"
lemma sbelows_rel_def: "\<langle>A\<rangle>sbelows_rel = \<langle>\<langle>A\<rangle>sctn_rel\<rangle>list_set_rel O br sbelow_halfspaces top"
  by (simp add: sbelows_rel_internal relAPP_def)
consts i_sbelows::"interface\<Rightarrow>interface"
lemmas [autoref_rel_intf] = REL_INTFI[of sbelows_rel i_sbelows]

lemma inter_rel_br: "\<langle>(br a I), (br b J)\<rangle>inter_rel = br (\<lambda>(x, y). a x \<inter> b y) (\<lambda>x. I (fst x) \<and> J (snd x))"
  by (auto simp: inter_rel_def br_def)

context begin interpretation autoref_syn .

lemma plane_of_autoref[autoref_rules]:
  "(\<lambda>x. x, plane_of) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> \<langle>A\<rangle>plane_rel"
  by (auto simp: plane_rel_def intro!: brI)

lemma below_halfspace_autoref[autoref_rules]:
  "(\<lambda>x. x, below_halfspace) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> \<langle>A\<rangle>below_rel"
  by (auto simp: below_rel_def intro!: brI)

lemma sbelow_halfspace_autoref[autoref_rules]:
  "(\<lambda>x. x, sbelow_halfspace) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> \<langle>A\<rangle>sbelow_rel"
  by (auto simp: sbelow_rel_def intro!: brI)

lemma sbelow_halfspaces_autoref[autoref_rules]:
  "(\<lambda>x. x, sbelow_halfspaces) \<in> \<langle>\<langle>A\<rangle>sctn_rel\<rangle>list_set_rel \<rightarrow> \<langle>A\<rangle>sbelows_rel"
  by (auto simp: sbelows_rel_def intro!: brI)


end


consts i_info::"interface\<Rightarrow>interface\<Rightarrow>interface"

subsubsection \<open>Implementation of set as union of sets\<close>

context begin
interpretation autoref_syn .

definition [simp]: "op_union_coll = (\<union>)"
lemma [autoref_op_pat]: "(\<union>) \<equiv> OP op_union_coll"
  by simp
lemma coll_union12[autoref_rules]:
  assumes unI[unfolded autoref_tag_defs]: "GEN_OP uni (\<union>) (L \<rightarrow> L \<rightarrow> L)"
  shows "(uni, op_union_coll) \<in> \<langle>L, S\<rangle>Union_rel \<rightarrow> \<langle>L, S\<rangle>Union_rel \<rightarrow> \<langle>L, S\<rangle>Union_rel"
  unfolding Union_rel_def
  by (auto simp: br_def intro!: relcompI[OF unI[param_fo]]
      relcompI[OF param_union[param_fo]])

definition "Id_arbitrary_interface = Id"
abbreviation "lw_rel \<equiv> \<langle>Id_arbitrary_interface\<rangle>list_wset_rel"
lemmas [autoref_rel_intf] = REL_INTFI[of Id_arbitrary_interface S for S::interface]

lemma lw_rel_def: "lw_rel = br set top"
  by (simp add: list_wset_rel_def Id_arbitrary_interface_def)

abbreviation "clw_rel A \<equiv> \<langle>lw_rel, A\<rangle>Union_rel"

lemma clw_rel_def: "clw_rel A = lw_rel O \<langle>A\<rangle>set_rel O br Union top"
  unfolding Union_rel_def
  by simp

lemma op_wset_isEmpty_clw_rel[autoref_rules]:
  "(\<lambda>x. RETURN (x = []), isEmpty_spec) \<in> clw_rel A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def lw_rel_def Union_rel_def br_def set_rel_def)

lemma lift_clw_rel_map:
  assumes "single_valued A"
  assumes "single_valued B"
  assumes "(fi, f) \<in> A \<rightarrow> B"
  assumes f_distrib: "\<And>X. X \<subseteq> Range A \<Longrightarrow> f (\<Union>X) = \<Union>(f ` X)"
  shows "(map fi, f) \<in> clw_rel A \<rightarrow> clw_rel B"
  using assms(1-2)
  apply (auto simp: clw_rel_def)
  subgoal for xs X YY Z
    apply (rule relcompI[where b="fi ` X"])
     apply (force simp: lw_rel_def br_def)
    apply (rule relcompI[where b="f `  YY"])
     prefer 2
     apply (rule brI)
      apply (subst f_distrib[symmetric])
      apply (force simp: br_def set_rel_def)
      apply (force simp add: br_def)
    apply force
    using assms(3)
    apply parametricity
    done
  done

lemma list_rel_comp_Union_rel:
  "single_valued R \<Longrightarrow> (\<langle>R\<rangle>list_rel O \<langle>(\<langle>Id\<rangle>list_wset_rel), S\<rangle>Union_rel) =
    \<langle>(\<langle>Id\<rangle>list_wset_rel), (R O S)\<rangle>Union_rel"
  unfolding Union_rel_def default_rel_def
  unfolding O_assoc[symmetric]
  apply (subst list_rel_comp_list_wset_rel) apply simp apply (simp)
  by (simp add: O_assoc list_wset_rel_def set_rel_compp)

lemma Cons_mem_clw_rel_iff:
  assumes "single_valued A"
  shows "(x # xs, X) \<in> clw_rel A \<longleftrightarrow> (\<exists>Y YS. (x, Y) \<in> A \<and> (set xs, YS) \<in> \<langle>A\<rangle>set_rel \<and> X = Y \<union> \<Union>YS)"
  using assms
  unfolding clw_rel_def
  apply safe
  subgoal by (force simp add: br_def lw_rel_def insert_mem_set_rel_iff[OF assms])
  subgoal for Y YS
    apply (auto intro!: relcompI[where b="insert x (set xs)"] relcompI[where b="insert Y YS"]
        param_insert[param_fo]
        simp: lw_rel_def br_def)
    done
  done

definition "split_spec_coll = split_spec"
lemma clw_rel_split[autoref_rules]:
  assumes "PREFER single_valued A"
  shows "(\<lambda>xs. case xs of [] \<Rightarrow> SUCCEED | (x # xs) \<Rightarrow> RETURN (x, xs), split_spec_coll) \<in>
    clw_rel A \<rightarrow> \<langle>A \<times>\<^sub>r clw_rel A\<rangle>nres_rel"
proof -
  have "\<exists>a. (x, a) \<in> A \<and> (\<exists>b. (y, b) \<in> clw_rel A \<and> xs \<subseteq> a \<union> b \<and> \<Union>YS \<subseteq> a \<union> b)"
    if "(x, xs) \<in> A" "(set y, YS) \<in> \<langle>A\<rangle>set_rel"
    for x y xs YS
    using that
    by (auto intro: exI[where x=xs] exI[where x="\<Union>YS"] simp: Union_rel_def lw_rel_def br_def)
  then show ?thesis
    using assms
    by (auto simp: split_spec_coll_def split_spec_def Cons_mem_clw_rel_iff
        intro!: nres_relI RETURN_SPEC_refine
        split: list.splits)
qed

lemma default_rel_split[autoref_rules]:
  assumes split_impl: "(split_impl, split_spec) \<in> A \<rightarrow> \<langle>B \<times>\<^sub>r A\<rangle>nres_rel"
  shows "(\<lambda>xs.
    case xs of None \<Rightarrow> SUCCEED
    | Some x \<Rightarrow> do {(r, s) \<leftarrow> split_impl x; RETURN (r, Some s)},
    split_spec) \<in>
    \<langle>A\<rangle>default_rel d \<rightarrow> \<langle>B \<times>\<^sub>r \<langle>A\<rangle>default_rel d\<rangle>nres_rel"
proof -
  have "split_impl a \<bind> (\<lambda>(r, s). RETURN (r, Some s))
    \<le> \<Down> (B \<times>\<^sub>r insert (None, d) ((\<lambda>(x, y). (Some x, y)) ` A)) (SPEC (\<lambda>(A, B). b \<subseteq> A \<union> B))"
    if "(a, b) \<in> A"
    for a b
  proof -
    have split_inresD:
      "\<exists>a. (c, a) \<in> B \<and> (\<exists>bb. (Some d, bb) \<in> (\<lambda>(x, y). (Some x, y)) ` A \<and> b \<subseteq> a \<union> bb)"
      if "inres (split_impl a) (c, d)"
      for c d
    proof -
      have "RETURN (c, d) \<le> \<Down> (B \<times>\<^sub>r A) (split_spec b)"
        using \<open>(a, b) \<in> A\<close> that split_impl
        by (auto simp: inres_def nres_rel_def dest!: fun_relD)
      then show ?thesis
        using \<open>(a, b) \<in> A\<close> that split_impl
        by (fastforce simp: split_spec_def elim!: RETURN_ref_SPECD)
    qed
    have "nofail (split_impl a)"
      using split_impl[param_fo, OF \<open>(a, b) \<in> A\<close>] le_RES_nofailI
      by (auto simp: split_spec_def nres_rel_def conc_fun_def)
    then show ?thesis
      using that split_impl
      by (fastforce simp: refine_pw_simps dest!: split_inresD intro!: pw_leI)
  qed
  then show ?thesis
    by (auto simp: split_spec_def default_rel_def
        intro!: nres_relI)
qed

lemma split_spec_exact_with_stepsize_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  shows "(\<lambda>xs. case xs of [] \<Rightarrow> SUCCEED | (x # xs) \<Rightarrow> RETURN (x, xs), split_spec_exact) \<in>
    clw_rel A \<rightarrow> \<langle>A \<times>\<^sub>r clw_rel A\<rangle>nres_rel"
proof -
  have "\<exists>a. (x, a) \<in> A \<and> (\<exists>b. (y, b) \<in> clw_rel A \<and> xs \<union> \<Union>YS = a \<union> b)"
    if "(x, xs) \<in> A" "(set y, YS) \<in> \<langle>A\<rangle>set_rel"
    for x y xs YS
    using that
    by (auto intro: exI[where x=xs] exI[where x="\<Union>YS"] simp: Union_rel_def lw_rel_def br_def)
  then show ?thesis
    using assms
    by (auto simp: split_spec_exact_def Cons_mem_clw_rel_iff
        intro!: nres_relI RETURN_SPEC_refine
        split: list.splits)
qed

lemma br_Some_O_default_rel_eq: "br Some top O \<langle>A\<rangle>default_rel d = A"
  by (auto simp: br_def default_rel_def)

definition [simp]: "op_Union_default = Union"
lemma [autoref_op_pat]: "Union \<equiv> OP op_Union_default"
  by simp

lemma default_rel_Union[autoref_rules]:
  assumes sv: "PREFER single_valued A"
  assumes safe: "SIDE_PRECOND (\<forall>x \<in> X. x \<subseteq> d)"
  assumes xs: "(xs, X) \<in> \<langle>\<langle>A\<rangle>default_rel d\<rangle>list_wset_rel"
  assumes Union_A: "(concat, Union) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> A"
  shows "(map_option concat (those xs), op_Union_default $ X) \<in> \<langle>A\<rangle>default_rel d"
  using xs
  apply (safe dest!: list_wset_relD intro!: mem_default_relI)
  subgoal using safe by (auto simp: default_rel_def)
  subgoal by (auto simp: default_rel_def those_eq_None_set_iff dest!: set_relD)[]
  subgoal
    by (auto simp: those_eq_Some_map_Some_iff image_mem_set_rel_iff br_Some_O_default_rel_eq list_wset_rel_def
        intro!: relcompI brI Union_A[param_fo])
  done

definition [simp]: "op_Union_coll = Union"
lemma [autoref_op_pat]: "Union \<equiv> OP op_Union_coll"
  by simp
lemma clw_rel_Union[autoref_rules]:
  assumes [unfolded autoref_tag_defs, relator_props]: "PREFER single_valued A"
  shows "(concat, op_Union_coll) \<in> \<langle>clw_rel A\<rangle>list_wset_rel \<rightarrow> clw_rel A"
proof -
  have "(concat, concat) \<in> \<langle>\<langle>A\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" (is "_ \<in> ?L1 \<rightarrow> ?L2")
    by parametricity
  moreover have "(concat, op_Union_coll) \<in> \<langle>clw_rel Id\<rangle>list_wset_rel \<rightarrow> clw_rel Id"  (is "_ \<in> ?R1 \<rightarrow> ?R2")
    apply (auto simp: list_wset_rel_def Id_arbitrary_interface_def Union_rel_def
        br_chain o_def)
    apply (auto simp: br_def set_rel_def)
    apply force
    done
  ultimately have "(concat, op_Union_coll) \<in> (?L1 \<rightarrow> ?L2) O (?R1 \<rightarrow> ?R2)"
    by auto
  also have "\<dots> \<subseteq> (?L1 O ?R1) \<rightarrow> (?L2 O ?R2)" by (rule fun_rel_comp_dist)
  also have "?L1 O ?R1 = \<langle>clw_rel A\<rangle>list_wset_rel"
    apply (subst list_rel_comp_list_wset_rel)
    subgoal by (simp add: relator_props)
    subgoal using assms by (simp add: list_rel_comp_Union_rel Id_arbitrary_interface_def)
    done
  also have "?L2 O ?R2 = clw_rel A" using assms
    unfolding Id_arbitrary_interface_def
    by (subst list_rel_comp_Union_rel) simp_all
  finally show ?thesis .
qed

definition [simp]: "is_empty \<equiv> \<lambda>x. x = {}"
lemma [autoref_itype]: "is_empty ::\<^sub>i A \<rightarrow>\<^sub>i i_bool"
  by simp

definition [simp]: "op_coll_is_empty \<equiv> is_empty"
lemma [autoref_op_pat]:  "is_empty \<equiv> OP op_coll_is_empty"
  by simp
lemma op_set_isEmpty_Union_rel[autoref_rules]:
  assumes "GEN_OP is_empty_i is_empty (A \<rightarrow> bool_rel)"
  shows "(\<lambda>xs. xs = [] \<or> list_all is_empty_i xs, op_coll_is_empty) \<in> clw_rel A \<rightarrow> bool_rel"
  using assms
  apply (auto simp: Union_rel_def lw_rel_def br_def set_rel_def op_set_isEmpty_def[abs_def]
      op_coll_is_empty_def
    list_all_iff dest: fun_relD)
  apply (fastforce dest: fun_relD)
  using fun_relD by fastforce

definition info_rel_internal: "info_rel I S = (I \<times>\<^sub>r S) O br snd top"
lemma info_rel_def: "\<langle>I, S\<rangle>info_rel = (I \<times>\<^sub>r S) O br snd top"
  by (auto simp: relAPP_def info_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of "info_rel" i_info]

lemma info_rel_br: "\<langle>br a I, (br b J)\<rangle>info_rel = br (\<lambda>y. b (snd y)) (\<lambda>x. I (fst x) \<and> J (snd x))"
  by (auto simp: info_rel_def br_def prod_rel_def)

lemma sv_info_rel[relator_props]:
  "single_valued S \<Longrightarrow>single_valued I \<Longrightarrow> single_valued (\<langle>I, S\<rangle>info_rel)"
  by (auto simp: info_rel_def intro!: relator_props)

definition [simp]: "op_info_is_empty = is_empty"
lemma [autoref_op_pat]:  "is_empty \<equiv> OP op_info_is_empty"
  by simp

lemma op_set_isEmpty_info_rel_set[autoref_rules]:
  "GEN_OP empty_i (is_empty) (A \<rightarrow> bool_rel) \<Longrightarrow> (\<lambda>x. empty_i (snd x), op_info_is_empty) \<in> \<langle>I, A\<rangle>info_rel \<rightarrow> bool_rel"
  by (auto simp: info_rel_def br_def op_set_isEmpty_def[abs_def] dest: fun_relD)

definition [refine_vcg_def]: "get_info X = SPEC (\<lambda>(h, Y). Y = X)"
lemma get_info_autoref[autoref_rules]:
  shows "(\<lambda>x. RETURN x, get_info) \<in> \<langle>I, A\<rangle>info_rel \<rightarrow> \<langle>I \<times>\<^sub>r A\<rangle>nres_rel"
  by (force simp: get_info_def info_rel_def nres_rel_def br_def intro!: RETURN_SPEC_refine)

definition with_info::"'b \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where [simp, refine_vcg_def]: "with_info h x = x"

lemma with_stepsize_autoref[autoref_rules]:
  "((\<lambda>h x. (h, x)), with_info) \<in> R \<rightarrow> A \<rightarrow> \<langle>R, A\<rangle>info_rel"
  by (auto simp: info_rel_def br_def intro!: prod_relI)

definition with_half_stepsizes::"'a set \<Rightarrow> 'a set"
  where [simp, refine_vcg_def]: "with_half_stepsizes x = x"
lemma with_half_stepsize_autoref[autoref_rules]:
  "((map (\<lambda>(h, x). (h/2, x))), with_half_stepsizes) \<in>
  clw_rel (\<langle>rnv_rel, A\<rangle>info_rel) \<rightarrow> clw_rel (\<langle>rnv_rel, A\<rangle>info_rel)"
  if  [unfolded autoref_tag_defs, relator_props]: "single_valued A"
  unfolding with_half_stepsizes_def
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)+
  by (auto simp: info_rel_def br_def prod_rel_def)

definition with_infos::"'b \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where [simp, refine_vcg_def]: "with_infos h x = x"
lemma with_infos_autoref[autoref_rules]:
  "(\<lambda>h. map (Pair h), with_infos) \<in> R \<rightarrow> clw_rel A \<rightarrow> clw_rel (\<langle>R, A\<rangle>info_rel)"
  if [unfolded autoref_tag_defs, relator_props]: "PREFER single_valued A" "PREFER single_valued R"
  unfolding with_infos_def
  apply (rule fun_relI)
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)+
  by (auto simp: info_rel_def br_def prod_rel_def)

abbreviation "with_stepsize \<equiv> (with_info::real\<Rightarrow>_)"

definition [simp]: "op_empty_coll = {}"
lemma Union_rel_empty[autoref_rules]:
  shows "([], op_empty_coll) \<in> clw_rel R"
  by (auto simp: br_def Union_rel_def
      intro!: relcompI[OF param_empty] relcompI[OF list_wset_autoref_empty])

definition [simp]: "op_empty_default = {}"
lemma default_rel_empty[autoref_rules]:
  assumes "GEN_OP ei {} A"
  shows "(Some ei, op_empty_default) \<in> \<langle>A\<rangle>default_rel d"
  using assms by (auto simp: default_rel_def)

definition mk_coll::"'a set \<Rightarrow> 'a set" where [refine_vcg_def, simp]: "mk_coll x = x"
lemma mk_coll[autoref_rules]:
  "PREFER single_valued R \<Longrightarrow> (\<lambda>x. [x], mk_coll) \<in> R \<rightarrow> clw_rel R"
  apply (rule fun_relI)
  subgoal for x x'
    by (auto simp: Union_rel_def list_wset_rel_def br_def set_rel_def single_valued_def
      Id_arbitrary_interface_def
      intro!: relcompI[where b="{xa. (x, xa) \<in> R}"] relcompI[where b="{x}"])
  done

definition mk_default::"'a set \<Rightarrow> 'a set" where [refine_vcg_def, simp]: "mk_default x = x"

lemma mk_default[autoref_rules]:
  "(Some, mk_default) \<in> R \<rightarrow> \<langle>R\<rangle>default_rel d"
  by (auto simp: default_rel_def)

end
consts i_invar::"interface \<Rightarrow> interface \<Rightarrow> interface"
context begin
interpretation autoref_syn .

definition invar_rel_internal:
  "invar_rel a X S = {((x, s'), y). \<exists>s. (s', s) \<in> X \<and> (x, y) \<in> S \<and> y \<subseteq> a s}"
lemma invar_rel_def: "\<langle>X, S\<rangle>invar_rel a = {((x, s'), y). \<exists>s. (s', s) \<in> X \<and> (x, y) \<in> S \<and> y \<subseteq> a s}"
  by (auto simp: invar_rel_internal relAPP_def)
lemmas [autoref_rel_intf] = REL_INTFI[of "invar_rel a" i_invar for a]

lemma invar_rel_br: "\<langle>(br a' I'), (br a I)\<rangle>invar_rel b =
  br (\<lambda>(x, s). a x) (\<lambda>(x, s). I x \<and> I' s \<and> (a x \<subseteq> b (a' s)))"
  by (auto simp: invar_rel_def br_def)

lemma sv_appr_invar_rel[relator_props]: "single_valued S \<Longrightarrow> single_valued (\<langle>X, S\<rangle>invar_rel a)"
  and sv_inter_rel[relator_props]: "single_valued S \<Longrightarrow> single_valued T \<Longrightarrow> single_valued (\<langle>T, S\<rangle>inter_rel)"
  unfolding relAPP_def
   apply (auto simp: invar_rel_internal inter_rel_internal single_valued_def set_rel_def)
     apply blast
    apply blast
  done

definition with_invar::"'invar \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where [simp]: "with_invar sctn X = X"

lemma with_invar_impl[autoref_rules]:
  assumes "(sctni, sctn) \<in> S"
  assumes "(Xi, X) \<in> clw_rel A"
  assumes "PREFER single_valued A"
  assumes "SIDE_PRECOND (X \<subseteq> a sctn)"
  shows "(map (\<lambda>x. (x, sctni)) Xi, with_invar $ sctn $ X) \<in> clw_rel (\<langle>S,A\<rangle>invar_rel a)"
  unfolding autoref_tag_defs
  using assms
  apply (auto simp: clw_rel_def elim!: single_valued_as_brE)
  subgoal for a i Y Z
    apply (rule relcompI)
    apply (force simp: lw_rel_def br_def)
    apply (rule relcompI[where b=Z])
    apply (auto simp: set_rel_def lw_rel_def invar_rel_def br_def)
    apply (metis Sup_le_iff)
    apply (metis Sup_le_iff)
    done
  done

definition get_invar::"('invar \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'invar) nres"
  where [refine_vcg_def]: "get_invar a X = SPEC (\<lambda>(Y, invar). Y = X \<and> Y \<subseteq> a invar)"

lemma [autoref_op_pat_def]: "get_invar p \<equiv> OP (get_invar p)"
  by simp

lemma get_invar_autoref[autoref_rules]:
  "(\<lambda>x. RETURN x, get_invar a) \<in> \<langle>X, S\<rangle>invar_rel a \<rightarrow> \<langle>S \<times>\<^sub>r X\<rangle>nres_rel"
  by (force simp: get_invar_def invar_rel_def nres_rel_def intro!: RETURN_SPEC_refine)

definition mk_inter::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
where [simp]: "mk_inter \<equiv> \<lambda>X Y. X \<inter> Y"
definition mk_inter_coll::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
where [simp]: "mk_inter_coll \<equiv> \<lambda>X Y. X \<inter> Y"

lemma [autoref_op_pat]: "mk_inter \<equiv> OP (mk_inter)"
  by simp
lemma [autoref_op_pat]: "mk_inter \<equiv> OP (mk_inter_coll)"
  by simp

lemma map_mem_clw_rel_br:
  assumes "\<Union>((\<lambda>x. a (f x)) ` set xs) = X"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> I (f x)"
  shows "(map f xs, X) \<in> clw_rel (br a I)"
  using assms
  by (auto simp: lw_rel_def Union_rel_br intro!: brI)

lemma inter_plane_clw_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>xs sctni. map (\<lambda>x. (x, sctni)) xs, mk_inter_coll) \<in> clw_rel A \<rightarrow> B \<rightarrow> clw_rel (\<langle>A,B\<rangle>inter_rel)"
  using assms
  by (fastforce
      intro!: nres_relI RETURN_SPEC_refine brI
      dest!: brD
      elim!: single_valued_as_brE
      simp: RETURN_RES_refine_iff inter_rel_br Union_rel_br lw_rel_def)

lemma inter_plane_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>x sctn. (x, sctn), mk_inter) \<in> A \<rightarrow> B \<rightarrow> \<langle>A,B\<rangle>inter_rel"
  using assms
  by (fastforce
      intro!: nres_relI RETURN_SPEC_refine brI
      dest!: brD
      elim!: single_valued_as_brE
      simp: RETURN_RES_refine_iff inter_rel_br Union_rel_br lw_rel_def)

definition unintersect::"'a set \<Rightarrow> 'a set nres"
  where [refine_vcg_def]: "unintersect X = SPEC (\<lambda>R. X \<subseteq> R)"

definition unintersect_coll::"'a set \<Rightarrow> 'a set nres"
  where [refine_vcg_def]: "unintersect_coll X = SPEC (\<lambda>R. X \<subseteq> R)"

definition unintersect2::"'a set \<Rightarrow> 'a set nres"
  where [refine_vcg_def]: "unintersect2 X = SPEC (\<lambda>R. X \<subseteq> R)"

definition unintersect_coll2::"'a set \<Rightarrow> 'a set nres"
  where [refine_vcg_def]: "unintersect_coll2 X = SPEC (\<lambda>R. X \<subseteq> R)"

lemma unintersect_clw_impl[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>xs. RETURN ((map fst) xs), unintersect_coll) \<in> clw_rel (\<langle>A,B\<rangle>inter_rel) \<rightarrow> \<langle>clw_rel A\<rangle>nres_rel"
  using assms
  by (auto intro!: nres_relI RETURN_SPEC_refine elim!: single_valued_as_brE
      simp: unintersect_coll_def inter_rel_br Union_rel_br lw_rel_def)
    (auto simp: br_def)

lemma unintersect_impl[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>x. RETURN (fst x), unintersect) \<in> (\<langle>A,B\<rangle>inter_rel) \<rightarrow> \<langle>A\<rangle>nres_rel"
  using assms
  by (auto intro!: nres_relI RETURN_SPEC_refine elim!: single_valued_as_brE
      simp: unintersect_def inter_rel_br Union_rel_br lw_rel_def)
    (auto simp: br_def)

lemma unintersect_clw2_impl[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>xs. RETURN ((map snd) xs), unintersect_coll2) \<in> clw_rel (\<langle>A,B\<rangle>inter_rel) \<rightarrow> \<langle>clw_rel B\<rangle>nres_rel"
  using assms
  by (auto intro!: nres_relI RETURN_SPEC_refine elim!: single_valued_as_brE
      simp: unintersect_coll2_def inter_rel_br Union_rel_br lw_rel_def)
    (auto simp: br_def)

lemma unintersect2_impl[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>x. RETURN (snd x), unintersect2) \<in> (\<langle>A,B\<rangle>inter_rel) \<rightarrow> \<langle>B\<rangle>nres_rel"
  using assms
  by (auto intro!: nres_relI RETURN_SPEC_refine elim!: single_valued_as_brE
      simp: unintersect2_def inter_rel_br Union_rel_br lw_rel_def)
    (auto simp: br_def)

definition get_inter::"'a set \<Rightarrow> ('a set \<times> 'a set) nres"
  where [refine_vcg_def]: "get_inter X = SPEC (\<lambda>(Y, Z). X = Y \<inter> Z)"

lemma get_inter_autoref[autoref_rules]:
  "(\<lambda>x. RETURN x, get_inter) \<in> \<langle>X,S\<rangle>inter_rel \<rightarrow> \<langle>X \<times>\<^sub>r S\<rangle>nres_rel"
  by (force simp: get_inter_def inter_rel_def nres_rel_def intro!: RETURN_SPEC_refine)

end

lemma set_rel_br: "\<langle>br a I\<rangle>set_rel = br ((`) a) (\<lambda>X. Ball X I)"
  by (auto simp: set_rel_def br_def)

subsection \<open>Interval representation\<close>

consts i_ivl::"interface \<Rightarrow> interface"

context begin interpretation autoref_syn .

definition "set_of_ivl x = {fst x .. snd x}"

definition "set_of_lvivl ivl = (set_of_ivl (map_prod eucl_of_list eucl_of_list ivl)::'a::executable_euclidean_space set)"

definition ivl_rel::"('a \<times> 'b::ordered_euclidean_space) set \<Rightarrow> (('a \<times> 'a) \<times> 'b set) set" where
  ivl_rel_internal: "ivl_rel S = (S \<times>\<^sub>r S) O br set_of_ivl top"
lemma ivl_rel_def: "\<langle>S\<rangle>ivl_rel = (S \<times>\<^sub>r S) O br set_of_ivl top"
  unfolding relAPP_def ivl_rel_internal ..

lemmas [autoref_rel_intf] = REL_INTFI[of "ivl_rel" "i_ivl"]

lemma ivl_rel_sv[relator_props]: "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>ivl_rel)"
  unfolding relAPP_def
  by (auto simp: ivl_rel_internal intro!: relator_props)

definition [simp]: "op_atLeastAtMost_ivl = atLeastAtMost"
lemma [autoref_op_pat]: "atLeastAtMost \<equiv> OP op_atLeastAtMost_ivl"
  by simp

lemma atLeastAtMost_ivlrel[autoref_rules]:
  "(Pair, op_atLeastAtMost_ivl) \<in> A \<rightarrow> A \<rightarrow> \<langle>A\<rangle>ivl_rel"
  by (auto simp: br_def set_of_ivl_def ivl_rel_def intro!: prod_relI)

definition [refine_vcg_def]: "ivl_rep X = SPEC (\<lambda>(l, u). X = {l .. u})"

lemma ivl_rep_autoref[autoref_rules]: "(RETURN, ivl_rep) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A \<times>\<^sub>r A\<rangle>nres_rel"
  by (force intro!: nres_relI RETURN_SPEC_refine simp: ivl_rep_def ivl_rel_def br_def set_of_ivl_def)

lemma Inf_ivl_rel[autoref_rules]:
  fixes X::"'a::ordered_euclidean_space set"
  assumes "SIDE_PRECOND (X \<noteq> {})"
  assumes "(Xi, X) \<in> \<langle>A\<rangle>ivl_rel"
  shows "(fst Xi, Inf $ X) \<in> A"
  using assms
  by (auto simp: ivl_rel_def br_def set_of_ivl_def)

lemma Sup_ivl_rel[autoref_rules]:
  fixes X::"'a::ordered_euclidean_space set"
  assumes "SIDE_PRECOND (X \<noteq> {})"
  assumes "(Xi, X) \<in> \<langle>A\<rangle>ivl_rel"
  shows "(snd Xi, Sup $ X) \<in> A"
  using assms
  by (auto simp: ivl_rel_def br_def set_of_ivl_def)

definition "filter_empty_ivls_impl le ivls = [(i, s) \<leftarrow> ivls. le i s]"

lemma filter_empty_ivls_impl_simps[simp]:
  shows
    "filter_empty_ivls_impl le [] = []"
    "filter_empty_ivls_impl le (a # xs) =
      (if le (fst a) (snd a) then a#filter_empty_ivls_impl le xs else filter_empty_ivls_impl le xs)"
  by (auto simp: filter_empty_ivls_impl_def)

definition [simp]: "filter_empty_ivls X = X"

lemma clw_rel_empty_iff:
  assumes "single_valued A"
  assumes "(x, {}) \<in> A" "(xs, X) \<in> clw_rel A"
  shows "(x#xs, X) \<in> clw_rel A"
  using assms
  by (auto simp: lw_rel_def Union_rel_br elim!: single_valued_as_brE) (auto simp: br_def)

lemma
  empty_ivl_relD:
  "(a, Y) \<in> \<langle>A\<rangle>ivl_rel \<Longrightarrow> single_valued A \<Longrightarrow> (le, (\<le>)) \<in> A \<rightarrow> A \<rightarrow> bool_rel \<Longrightarrow> \<not> le (fst a) (snd a) \<Longrightarrow> Y = {}"
  by (fastforce simp: ivl_rel_def br_def set_of_ivl_def dest: fun_relD )

lemma union_clw_relI: "(set xs, YS) \<in> \<langle>A\<rangle>set_rel \<Longrightarrow> (xs, \<Union>YS) \<in> clw_rel (A)"
  apply (auto simp: clw_rel_def br_def )
  apply (auto simp: lw_rel_def Union_rel_br set_rel_def )
  apply (auto simp: br_def)
  done

lemma filter_empty_ivls_impl_mem_clw_rel_ivl_rel_iff:
  "(filter_empty_ivls_impl (\<le>) xs, X) \<in> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel) \<longleftrightarrow> (xs, X) \<in> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)"
  by (force simp: lw_rel_def ivl_rel_def Union_rel_br filter_empty_ivls_impl_def
      set_of_ivl_def dest!: brD intro!: brI)

lemma filter_empty_ivls_eucl:
  "(filter_empty_ivls_impl (\<le>), filter_empty_ivls) \<in> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)"
  by (auto simp: filter_empty_ivls_impl_mem_clw_rel_ivl_rel_iff)

lemma filter_param[param]:
  "(filter, filter) \<in> (A \<rightarrow> bool_rel) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel"
  unfolding List.filter_def[abs_def]
  by parametricity

lemma prod_rel_comp_ivl_rel:
  assumes "single_valued A" "single_valued B"
  shows "(A \<times>\<^sub>r A) O \<langle>B\<rangle>ivl_rel = \<langle>A O B\<rangle>ivl_rel"
  using assms
  by (auto simp: ivl_rel_def set_of_ivl_def br_chain br_rel_prod
      elim!: single_valued_as_brE
      intro!:brI dest!: brD)

lemma filter_empty_ivls[autoref_rules]:
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes [THEN GEN_OP_D, param]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  assumes xs: "(xs, X) \<in> clw_rel (\<langle>A\<rangle>ivl_rel)"
  shows "(filter_empty_ivls_impl le xs, filter_empty_ivls $ X) \<in> clw_rel (\<langle>A\<rangle>ivl_rel)"
proof -
  have "(filter_empty_ivls_impl le, filter_empty_ivls_impl (\<le>)) \<in> \<langle>A\<times>\<^sub>rA\<rangle>list_rel \<rightarrow> \<langle>A\<times>\<^sub>rA\<rangle>list_rel"
    unfolding filter_empty_ivls_impl_def
    by parametricity
  moreover
  have "(filter_empty_ivls_impl (\<le>), filter_empty_ivls) \<in> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)"
    by (rule filter_empty_ivls_eucl)
  ultimately have "(filter_empty_ivls_impl le, filter_empty_ivls) \<in>
    (\<langle>A \<times>\<^sub>r A\<rangle>list_rel \<rightarrow> \<langle>A \<times>\<^sub>r A\<rangle>list_rel) O (clw_rel (\<langle>rnv_rel\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel))" ..
  also have "\<dots> \<subseteq> (\<langle>A \<times>\<^sub>r A\<rangle>list_rel O clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)) \<rightarrow> (\<langle>A \<times>\<^sub>r A\<rangle>list_rel O clw_rel (\<langle>rnv_rel\<rangle>ivl_rel))"
    by (rule fun_rel_comp_dist)
  also have "(\<langle>A \<times>\<^sub>r A\<rangle>list_rel O clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)) = clw_rel (\<langle>A\<rangle>ivl_rel)"
    unfolding Id_arbitrary_interface_def
    apply (subst list_rel_comp_Union_rel)
     apply (intro relator_props)
    apply (subst prod_rel_comp_ivl_rel)
     apply (intro relator_props)
     apply (intro relator_props)
    apply simp
    done
  finally show ?thesis using xs by (auto dest: fun_relD)
qed

definition [simp]: "op_inter_ivl = (\<inter>)"
lemma [autoref_op_pat]: "(\<inter>) \<equiv> OP op_inter_ivl"
  by simp
lemma inter_ivl_rel[autoref_rules]:
  assumes infi[THEN GEN_OP_D, param_fo]: "GEN_OP infi inf (A \<rightarrow> A \<rightarrow> A)"
  assumes supi[THEN GEN_OP_D, param_fo]:"GEN_OP supi sup (A \<rightarrow> A \<rightarrow> A)"
  shows "(\<lambda>(i, s). \<lambda>(i', s'). (supi i i', infi s s'), op_inter_ivl) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel"
  using assms
  by (fastforce simp: ivl_rel_def br_def set_of_ivl_def intro!: infi supi prod_relI)

definition [simp]: "op_inter_ivl_coll = (\<inter>)"
lemma [autoref_op_pat]: "(\<inter>) \<equiv> OP op_inter_ivl_coll"
  by simp
lemma inter_ivl_clw_aux:
  assumes sv: "single_valued A"
  assumes intr: "(intr, (\<inter>)) \<in> (\<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel)"
  shows "(\<lambda>xs y. map (intr y) xs, (\<inter>)) \<in> clw_rel (\<langle>A\<rangle>ivl_rel) \<rightarrow>  \<langle>A\<rangle>ivl_rel \<rightarrow> clw_rel (\<langle>A\<rangle>ivl_rel)"
  apply (rule fun_relI)
  apply (rule fun_relI)
  using sv
  apply (rule single_valued_as_brE)
  apply simp
  unfolding ivl_rel_def br_rel_prod br_chain prod_rel_id_simp Id_O_R
  apply (rule map_mem_clw_rel_br)
   apply (auto simp: set_of_ivl_def)
  subgoal for a b c d e f g h i j
    using intr[param_fo, of "(c, d)" "{f c .. f d}" "(i, j)" "{f i .. f j}"]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    apply (rule bexI) prefer 2 apply assumption
    apply simp
    by (metis (mono_tags, lifting) Int_iff atLeastAtMost_iff fst_conv snd_conv)
  subgoal for a b c d e f g h i j
    using intr[param_fo, of "(c, d)" "{f c .. f d}" "(i, j)" "{f i .. f j}"]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    by (metis (mono_tags, lifting) Int_iff atLeastAtMost_iff fst_conv snd_conv)+
  subgoal for a b c d e f g h
    using intr[param_fo, of "(c, d)" "{f c .. f d}" ]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    apply (rule bexI) prefer 2 apply assumption
    by (metis (mono_tags, lifting) Int_iff atLeastAtMost_iff fst_conv snd_conv)
  subgoal for a b c d e f g h
    using intr[param_fo, of "(c, d)" "{f c .. f d}" ]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    by (metis (mono_tags, lifting) fst_conv snd_conv)
  subgoal for a b c d e f g h
    using intr[param_fo, of "(c, d)" "{f c .. f d}" ]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    by (metis (mono_tags, lifting) fst_conv snd_conv)
  done

lemma inter_ivl_clw[autoref_rules]:
  assumes sv[THEN PREFER_sv_D]: "PREFER single_valued A"
  assumes intr[THEN GEN_OP_D]: "GEN_OP intr (\<inter>) (\<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel)"
  assumes "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>xs y. filter_empty_ivls_impl le (map (intr y) xs), op_inter_ivl_coll) \<in> clw_rel (\<langle>A\<rangle>ivl_rel) \<rightarrow> (\<langle>A\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>A\<rangle>ivl_rel)"
  apply safe
  subgoal premises prems
    using filter_empty_ivls[OF assms(1,3), param_fo, OF inter_ivl_clw_aux[OF sv intr, param_fo, OF prems]]
    by simp
  done

end

subsection \<open>Specs for Vectors\<close>

context begin interpretation autoref_syn .

lemma Inf_specs_Inf_spec:
  "(Inf_specs d, Inf_spec::_\<Rightarrow>'a::executable_euclidean_space nres) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  if "d = DIM('a)"
  apply (auto intro!: nres_relI RES_refine simp: Inf_specs_def Inf_spec_def set_rel_def that)
  subgoal for x y s
    apply (rule exI[where x="eucl_of_list s"])
    apply (auto simp: lv_rel_def br_def subset_iff)
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    subgoal for c
      using lv_rel_le[where 'a ='a, param_fo, OF lv_relI lv_relI, of s c]
      by auto
    done
  done

lemma Sup_specs_Sup_spec:
  "(Sup_specs d, Sup_spec::_\<Rightarrow>'a::executable_euclidean_space nres) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  if "d = DIM('a)"
 apply (auto intro!: nres_relI RES_refine simp: Sup_specs_def Sup_spec_def set_rel_def that)
  subgoal for x y s
    apply (rule exI[where x="eucl_of_list s"])
    apply (auto simp: lv_rel_def br_def subset_iff)
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    subgoal for c
      using lv_rel_le[where 'a ='a, param_fo, OF lv_relI lv_relI, of c s]
      by auto
    done
  done

lemma set_rel_sv:
  "\<langle>R\<rangle>set_rel = {(S,S'). S'=R``S \<and> S\<subseteq>Domain R}"
  if "single_valued R"
  using that
  by (auto simp: set_rel_def set_rel_br elim!: single_valued_as_brE)
     (auto simp: br_def)

lemma inter_sctn_specs_inter_sctn_spec:
  "(inter_sctn_specs d, inter_sctn_spec::'a::executable_euclidean_space set\<Rightarrow>_) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
  if "d = DIM('a)"
  apply (auto intro!: nres_relI RES_refine
      simp: inter_sctn_specs_def inter_sctn_spec_def set_rel_sv[OF lv_rel_sv] plane_ofs_def plane_of_def that)
  subgoal for a b c d e f
    apply (cases b; cases c)
    apply (rule ImageI, assumption)
    apply (auto simp: lv_rel_def br_def sctn_rel_def plane_of_def)
    apply (rule set_mp, assumption)
    apply auto
    subgoal for x1
      using lv_rel_inner[param_fo, OF lv_relI lv_relI, of f x1]
      by auto
    done
  subgoal for a b c d e f
    apply (cases b; cases c)
    apply (auto simp: sctn_rel_def lv_rel_def br_def)
    apply (drule set_rev_mp, assumption)
    subgoal for x1 x2
      using lv_rel_inner[where 'a = 'a, param_fo, OF lv_relI lv_relI, of f x1]
      by auto
    done
  by (auto simp: sctn_rel_def lv_rel_def br_def env_len_def)

lemma Sup_inners_Sup_inner: "(Sup_inners, Sup_inner) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  unfolding set_rel_sv[OF lv_rel_sv]
  apply (auto intro!: nres_relI RES_refine
      simp: Sup_inners_def Sup_inner_def  plane_ofs_def plane_of_def lv_rel_def br_def)
  subgoal for a b c d
    using lv_rel_inner[where 'a = 'a, param_fo, OF lv_relI lv_relI, of d b]
    by auto
  done

lemma Inf_inners_Inf_inner: "(Inf_inners, Inf_inner) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  unfolding set_rel_sv[OF lv_rel_sv]
  apply (auto intro!: nres_relI RES_refine
      simp: Inf_inners_def Inf_inner_def plane_ofs_def plane_of_def lv_rel_def br_def)
  subgoal for a b c d
    using lv_rel_inner[where 'a = 'a, param_fo, OF lv_relI lv_relI, of d b]
    by auto
  done

lemma split_spec_params_split_spec_param:
  "(split_spec_params d, split_spec_param::nat\<Rightarrow>'a::executable_euclidean_space set\<Rightarrow>_) \<in> nat_rel \<rightarrow> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>set_rel\<times>\<^sub>r\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
  if "d = DIM('a::executable_euclidean_space)"
  apply (auto intro!: nres_relI RES_refine simp: split_spec_param_def split_spec_params_def env_len_def that)
  unfolding set_rel_sv[OF lv_rel_sv]
  apply (auto intro!: nres_relI RES_refine simp: plane_ofs_def plane_of_def lv_rel_def br_def subset_iff)
  done

lemma reduce_specs_reduce_spec:
  "(reduce_specs d, reduce_spec::_\<Rightarrow>'a::executable_euclidean_space set\<Rightarrow>_) \<in> A \<rightarrow> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
  if "d = DIM('a::executable_euclidean_space)"
  apply (auto intro!: nres_relI RES_refine simp: reduce_spec_def reduce_specs_def env_len_def that)
  unfolding set_rel_sv[OF lv_rel_sv]
  apply (auto intro!: nres_relI RES_refine simp: plane_ofs_def plane_of_def lv_rel_def br_def subset_iff)
  done

end


subsection \<open>locale for sets\<close>

definition "product_listset xs ys = (\<lambda>(x, y). x @ y) ` ((xs::real list set) \<times> (ys::real list set))"

abbreviation "rl_rel \<equiv> \<langle>rnv_rel\<rangle>list_rel"

lemma bounded_subset_cboxE:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> bounded ((\<lambda>x. x \<bullet> i) ` X)"
  obtains a b where "X \<subseteq> cbox a b"
proof -
  from bounded_subset_open_interval[OF assms[rule_format]] obtain a b where
    bnds: "\<And>i. i \<in> Basis \<Longrightarrow> ((\<lambda>x. x \<bullet> i) ` X) \<subseteq> {a i .. b i}"
    by (metis box_real(2) box_subset_cbox subset_trans)
  then have "X \<subseteq> {x. \<forall>i\<in>Basis. x \<bullet> i \<in> {a i .. b i}}"
    by force
  also have "\<dots> = cbox (\<Sum>i\<in>Basis. a i *\<^sub>R i) (\<Sum>i\<in>Basis. b i *\<^sub>R i)"
    by (auto simp: cbox_def)
  finally show ?thesis ..
qed

lemma
  bounded_euclideanI:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> bounded ((\<lambda>x. x \<bullet> i) ` X)"
  shows "bounded X"
proof -
  from bounded_subset_cboxE[OF assms] obtain a b where "X \<subseteq> cbox a b" .
  with bounded_cbox show ?thesis by (rule bounded_subset)
qed

abbreviation "slp_rel \<equiv> \<langle>Id::floatarith rel\<rangle>list_rel"
abbreviation "fas_rel \<equiv> \<langle>Id::floatarith rel\<rangle>list_rel"

locale approximate_sets = autoref_syn +
  fixes appr_of_ivl::"real list \<Rightarrow> real list \<Rightarrow> 'b list"
  fixes product_appr::"'b list \<Rightarrow> 'b list \<Rightarrow> 'b list"
  fixes msum_appr::"'b list \<Rightarrow> 'b list \<Rightarrow> 'b list"
  fixes set_of_appr::"'b list \<Rightarrow> real list set"
  fixes inf_of_appr::"'options \<Rightarrow> 'b list \<Rightarrow> real list"
  fixes sup_of_appr::"'options \<Rightarrow> 'b list \<Rightarrow> real list"
  fixes split_appr::"'options \<Rightarrow> nat \<Rightarrow> 'b list \<Rightarrow> 'b list \<times> 'b list"
  fixes appr_inf_inner::"'options \<Rightarrow> 'b list \<Rightarrow> real list \<Rightarrow> real"
  fixes appr_sup_inner::"'options \<Rightarrow> 'b list \<Rightarrow> real list \<Rightarrow> real"
  fixes inter_appr_plane::"'options \<Rightarrow> 'b list \<Rightarrow> real list sctn \<Rightarrow> 'b list dres"
  fixes reduce_appr::"'options \<Rightarrow> ('b list \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> 'b list"
  fixes width_appr::"'options \<Rightarrow> 'b list \<Rightarrow> real"
  fixes approx_slp::"'options \<Rightarrow> nat \<Rightarrow> slp \<Rightarrow> 'b list \<Rightarrow> 'b list option dres"
  fixes approx_euclarithform::"'options \<Rightarrow> form \<Rightarrow> 'b list \<Rightarrow> bool dres"
  fixes approx_isFDERIV::"'options \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> floatarith list \<Rightarrow> 'b list \<Rightarrow>
    bool dres"
  fixes appr_rell
  fixes optns::"'options"
  assumes appr_rell_internal: "appr_rell \<equiv> br set_of_appr top"
  assumes transfer_operations_rl:
    "SIDE_PRECOND (list_all2 (\<le>) xrs yrs) \<Longrightarrow>
      (xri, xrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
      (yri, yrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
      (appr_of_ivl xri yri, lv_ivl $ xrs $ yrs) \<in> appr_rell"
    "(product_appr, product_listset) \<in> appr_rell \<rightarrow> appr_rell \<rightarrow> appr_rell"
    "(msum_appr, (\<lambda>xs ys. {map2 (+) x y |x y. x \<in> xs \<and> y \<in> ys})) \<in> appr_rell \<rightarrow> appr_rell \<rightarrow> appr_rell"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (inf_of_appr optns xi), Inf_specs d x) \<in> \<langle>rl_rel\<rangle>nres_rel"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (sup_of_appr optns xi), Sup_specs d x) \<in> \<langle>rl_rel\<rangle>nres_rel"
    "(ni, n) \<in> nat_rel \<Longrightarrow> (xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (split_appr optns ni xi), split_spec_params d n x) \<in> \<langle>appr_rell \<times>\<^sub>r appr_rell\<rangle>nres_rel"
    "(RETURN o2 appr_inf_inner optns, Inf_inners) \<in> appr_rell \<rightarrow> rl_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(RETURN o2 appr_sup_inner optns, Sup_inners) \<in> appr_rell \<rightarrow> rl_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow> length (normal si) = d \<Longrightarrow> d > 0 \<Longrightarrow> (si, s) \<in> \<langle>rl_rel\<rangle>sctn_rel \<Longrightarrow>
      (nres_of (inter_appr_plane optns xi si), inter_sctn_specs d x s) \<in> \<langle>appr_rell\<rangle>nres_rel"
    "(Ci, C) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> rl_rel \<rightarrow> bool_rel \<Longrightarrow> (xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (reduce_appr optns Ci xi), reduce_specs d C x) \<in> \<langle>appr_rell\<rangle>nres_rel"
    "(RETURN o width_appr optns, width_spec) \<in> appr_rell \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(nres_of o3 approx_slp optns, approx_slp_spec fas) \<in> nat_rel \<rightarrow> slp_rel \<rightarrow> appr_rell \<rightarrow> \<langle>\<langle>appr_rell\<rangle>option_rel\<rangle>nres_rel"
assumes approx_euclarithform[unfolded comps, autoref_rules]:
  "(nres_of o2 approx_euclarithform optns, approx_form_spec) \<in> Id \<rightarrow> appr_rell \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
assumes approx_isFDERIV[unfolded comps, autoref_rules]:
  "(\<lambda>N xs fas vs. nres_of (approx_isFDERIV optns N xs fas vs), isFDERIV_spec) \<in>
  nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow>  appr_rell \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
assumes set_of_appr_nonempty[simp]: "set_of_appr X \<noteq> {}"
assumes length_set_of_appr: "xrs \<in> set_of_appr xs \<Longrightarrow> length xrs = length xs"
assumes set_of_appr_project: "xrs \<in> set_of_appr xs \<Longrightarrow> (\<And>i. i \<in> set is \<Longrightarrow> i < length xs) \<Longrightarrow>
    map ((!) xrs) is \<in> set_of_appr (map ((!) xs) is)"
assumes set_of_apprs_ex_Cons: "xrs \<in> set_of_appr xs \<Longrightarrow> \<exists>r. r#xrs \<in> set_of_appr (b#xs)"
assumes set_of_apprs_Nil[simp]: "xrs \<in> set_of_appr [] \<longleftrightarrow> xrs = []"
begin

definition "appr_rel = appr_rell O \<langle>lv_rel\<rangle>set_rel"
lemmas [autoref_rel_intf] = REL_INTFI[of appr_rel i_appr]

lemma prod_rel_relcomp_distr: "(R \<times>\<^sub>r S) O (T \<times>\<^sub>r U) = (R O T) \<times>\<^sub>r (S O U)"
  by (auto simp: prod_rel_def)

lemma appr_relp_comp: "appr_rell O \<langle>lv_rel\<rangle>set_rel \<subseteq> appr_rel"
  "appr_rel \<subseteq> appr_rell O \<langle>lv_rel\<rangle>set_rel"
  by (auto simp: appr_rel_def)

lemma rnv_rel_comp2:
  "rnv_rel \<subseteq> rnv_rel O rnv_rel"
  "rnv_rel O rnv_rel \<subseteq> rnv_rel"
  by auto

lemma rl_comp_lv: "rl_rel O lv_rel \<subseteq> lv_rel"
  "lv_rel \<subseteq> rl_rel O lv_rel"
  by auto

lemma sctn_rel_comp: "\<langle>A\<rangle>sctn_rel O \<langle>B\<rangle>sctn_rel = \<langle>A O B\<rangle> sctn_rel"
  apply safe
  subgoal for a b c d e
    apply (cases c; cases d; cases d; cases e)
    by (auto simp: sctn_rel_def )
  subgoal for a b
    apply (cases a; cases b)
    apply (auto simp: sctn_rel_def )
    subgoal for c d e f
      apply (rule relcompI[where b="Sctn e c"])
       apply auto
      done
    done
  done

lemma sctn_rel: "\<langle>lv_rel\<rangle>sctn_rel \<subseteq> \<langle>rl_rel\<rangle>sctn_rel O \<langle>lv_rel\<rangle>sctn_rel"
  "\<langle>rl_rel\<rangle>sctn_rel O \<langle>lv_rel\<rangle>sctn_rel \<subseteq> \<langle>lv_rel\<rangle>sctn_rel"
  using sctn_rel_comp[of rl_rel lv_rel] by auto

lemmas rel_lemmas =
  fun_rel_comp_dist[THEN order_trans]
  fun_rel_mono nres_rel_comp[THEN eq_refl, THEN order_trans]
  nres_rel_mono prod_rel_mono prod_rel_relcomp_distr[THEN eq_refl, THEN order_trans]
  appr_relp_comp
  rnv_rel_comp2
  rl_comp_lv
  sctn_rel

lemma width_spec_width_spec: "(width_spec, width_spec) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  by (auto simp: width_spec_def nres_relI)

lemma [autoref_itype]:
  "width_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_nres"
  "Inf_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>B\<rangle>\<^sub>ii_nres"
  "Sup_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>B\<rangle>\<^sub>ii_nres"
  "inter_sctn_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>B\<rangle>\<^sub>ii_sctn \<rightarrow>\<^sub>i \<langle>C\<rangle>\<^sub>ii_nres"
  "split_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>\<langle>B, B\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  "split_spec_param ::\<^sub>i i_nat \<rightarrow>\<^sub>i A \<rightarrow>\<^sub>i \<langle>\<langle>B, B\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  "Inf_inner ::\<^sub>i A \<rightarrow>\<^sub>i B \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_nres"
  "Sup_inner ::\<^sub>i A \<rightarrow>\<^sub>i B \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_nres"
  by auto

lemma transfer_operations[unfolded comps, autoref_rules]:
  "SIDE_PRECOND (list_all2 (\<le>) xrs yrs) \<Longrightarrow>
    (xri, xrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
    (yri, yrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
    (appr_of_ivl xri yri, lv_ivl $ xrs $ yrs) \<in> appr_rell"
  "(product_appr, product_listset) \<in> appr_rell \<rightarrow> appr_rell \<rightarrow> appr_rell"
  "(msum_appr, (+)) \<in> appr_rel \<rightarrow> appr_rel \<rightarrow> appr_rel"
  "(RETURN o inf_of_appr optns, Inf_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  "(RETURN o sup_of_appr optns, Sup_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  "(RETURN o2 split_appr optns, split_spec_param) \<in> nat_rel \<rightarrow> appr_rel \<rightarrow> \<langle>appr_rel \<times>\<^sub>r appr_rel\<rangle>nres_rel"
  "(RETURN o2 appr_inf_inner optns, Inf_inner) \<in> appr_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  "(RETURN o2 appr_sup_inner optns, Sup_inner) \<in> appr_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  "(nres_of o2 inter_appr_plane optns, inter_sctn_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  "(RETURN o2 reduce_appr optns, reduce_spec) \<in> (\<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> rl_rel \<rightarrow> bool_rel) \<rightarrow> appr_rel \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  "(RETURN o width_appr optns, width_spec) \<in> appr_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  "(nres_of o3 approx_slp optns, approx_slp_spec fas) \<in> nat_rel \<rightarrow> slp_rel \<rightarrow> appr_rell \<rightarrow> \<langle>\<langle>appr_rell\<rangle>option_rel\<rangle>nres_rel"
  subgoal premises prems using transfer_operations_rl(1)[OF prems] by simp
  subgoal premises prems using transfer_operations_rl(2)[OF prems] by simp
  subgoal premises prems using transfer_operations_rl(3)[OF prems]
    unfolding appr_rel_def set_plus_def
    apply auto
    apply (drule fun_relD, assumption, drule fun_relD, assumption, rule relcompI, assumption)
    apply (auto simp: set_rel_sv[OF lv_rel_sv])
      apply (rule ImageI)
       apply (rule lv_rel_add[param_fo], assumption, assumption)
      apply force
    subgoal for a b c d e f g
      apply (rule bexI[where x="eucl_of_list f"])
       apply (rule bexI[where x="eucl_of_list g"])
      using lv_rel_add[param_fo, of f "eucl_of_list f", of g "eucl_of_list g::'a"]
      by (auto simp: lv_rel_def br_def subset_iff)
    subgoal
      by (auto simp: lv_rel_def br_def subset_iff)
    done
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 x y z)
    from transfer_operations_rl(4)[OF 1(1) refl]
    have Is: "(RETURN (inf_of_appr optns x), Inf_specs (length x) y) \<in> \<langle>rl_rel\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('c)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ Inf_specs_Inf_spec[param_fo], OF Is \<open>length x = _\<close> 1(2)]
    have "(RETURN (inf_of_appr optns x), Inf_spec z) \<in> \<langle>rl_rel\<rangle>nres_rel O \<langle>lv_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp)
  qed
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 x y z)
    from transfer_operations_rl(5)[OF 1(1) refl]
    have Is: "(RETURN (sup_of_appr optns x), Sup_specs (length x) y) \<in> \<langle>rl_rel\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('d)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ Sup_specs_Sup_spec[param_fo], OF Is \<open>length x = _\<close> 1(2)]
    have "(RETURN (sup_of_appr optns x), Sup_spec z) \<in> \<langle>rl_rel\<rangle>nres_rel O \<langle>lv_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp)
  qed
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 n x y z)
    from transfer_operations_rl(6)[OF _ 1(1) refl]
    have Is: "(RETURN (split_appr optns n x), split_spec_params (length x) n y) \<in> \<langle>appr_rell \<times>\<^sub>r appr_rell\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('e)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ split_spec_params_split_spec_param[param_fo], OF Is \<open>length x = _\<close> IdI 1(2)]
    have "(RETURN (split_appr optns n x), split_spec_param n z) \<in>
        \<langle>appr_rell \<times>\<^sub>r appr_rell\<rangle>nres_rel O \<langle>\<langle>lv_rel\<rangle>set_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp prod_rel_relcomp_distr comps)
  qed
  subgoal
    by (intro relcompI[OF transfer_operations_rl(7) Inf_inners_Inf_inner, THEN set_rev_mp] rel_lemmas)
  subgoal
    by (intro relcompI[OF transfer_operations_rl(8) Sup_inners_Sup_inner, THEN set_rev_mp] rel_lemmas)
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 r s x y z)
    from 1 have lens: "length (normal r) = length x"
      apply (cases r; cases s)
      apply (auto simp: sctn_rel_def)
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    have poslen: "0 < length x"
      using 1
      apply (cases r; cases s)
      apply (auto simp: sctn_rel_def)
      by (auto simp: lv_rel_def set_rel_def br_def appr_rell_internal)
    have rr: "(r, r) \<in> \<langle>rl_rel\<rangle>sctn_rel"
      by (cases r) (auto simp: sctn_rel_def)
    from transfer_operations_rl(9)[OF 1(2) refl lens poslen rr]
    have Is: "(nres_of (inter_appr_plane optns x r), inter_sctn_specs (length x) y r) \<in> \<langle>appr_rell\<rangle>nres_rel"
      by (auto dest!: fun_relD)
    from 1 have "length x = DIM('h)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ inter_sctn_specs_inter_sctn_spec[param_fo], OF Is, OF \<open>length x = _\<close> 1(3) 1(1)]
    have "(nres_of (inter_appr_plane optns x r), inter_sctn_spec z s) \<in> \<langle>appr_rell\<rangle>nres_rel O \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp prod_rel_relcomp_distr comps)
  qed
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 r x y z)
    from transfer_operations_rl(10)[OF _ 1(1) refl]
    have Is: "(RETURN (reduce_appr optns r x), reduce_specs (length x) r y) \<in> \<langle>appr_rell\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('i)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ reduce_specs_reduce_spec[param_fo], OF Is \<open>length x = _\<close> IdI 1(2)]
    have "(RETURN (reduce_appr optns r x), reduce_spec r z) \<in> \<langle>appr_rell\<rangle>nres_rel O \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp prod_rel_relcomp_distr comps)
  qed
  subgoal
    by (intro relcompI[OF transfer_operations_rl(11) width_spec_width_spec, THEN set_rev_mp] rel_lemmas)
  subgoal using transfer_operations_rl(12) by auto
  done

lemma approx_slp_spec[autoref_op_pat_def]: "approx_slp_spec fas \<equiv> OP (approx_slp_spec fas)"
  by auto

primrec concat_appr where
  "concat_appr [] = []"
| "concat_appr (x#xs) = product_appr x (concat_appr xs)"

definition [simp]: "op_concat_listset xs = concat ` listset xs"

lemma [autoref_op_pat_def]: "concat ` listset xs \<equiv> OP op_concat_listset $ xs"
  by simp

lemma length_listset: "xi \<in> listset xs \<Longrightarrow> length xi = length xs"
  by (induction xs arbitrary: xi) (auto simp: set_Cons_def)

lemma Nil_mem_listset[simp]: "[] \<in> listset list \<longleftrightarrow> list = []"
  by (induction list) (auto simp: set_Cons_def)

lemma sing_mem_listset_iff[simp]: "[b] \<in> listset ys \<longleftrightarrow> (\<exists>z. ys = [z] \<and> b \<in> z)"
  \<comment>\<open>TODO: generalize to Cons?\<close>
  by (cases ys) (auto simp: set_Cons_def)


lemma
  concat_appr:
  assumes "(xsi, xs) \<in> \<langle>appr_rell\<rangle>list_rel"
  shows "(concat_appr xsi, concat ` listset xs) \<in> appr_rell"
  using assms
  apply (auto simp: appr_rell_internal br_def)
  subgoal premises prems for xi
  proof -
    have "length xi = length xs" "length xs = length xsi"
      using prems
       by (auto simp: list_rel_def list_all2_iff length_listset)
    then show ?thesis using prems
    proof (induction rule: list_induct3)
      case Nil
      then show ?case by simp
    next
      case (Cons x xs y ys z zs)
      have "(z, set_of_appr z) \<in> appr_rell"
        "(concat_appr zs, set_of_appr (concat_appr zs)) \<in> appr_rell"
        by (auto simp: appr_rell_internal br_def)
      from transfer_operations(2)[param_fo, OF this]
      have *: "set_of_appr (product_appr z (concat_appr zs)) =
        (\<lambda>(x, y). x @ y) ` (set_of_appr z \<times> set_of_appr (concat_appr zs))"
        by (simp add: appr_rell_internal br_def product_listset_def)
      show ?case
        using Cons
        apply (auto simp: appr_rell_internal *)
        apply (rule image_eqI[where x="(x, concat xs)"])
         by (auto simp: set_Cons_def)
     qed
   qed
   subgoal premises prems for z
   proof -
     have "length xsi = length xs"
       using prems
       by (auto simp: list_rel_def list_all2_iff)
     then show ?thesis
       using prems
     proof (induction arbitrary: z rule: list_induct2 )
       case Nil
       then show ?case by simp
     next
       case (Cons x xs y ys)
       have "(x, set_of_appr x) \<in> appr_rell" "(concat_appr xs, set_of_appr (concat_appr xs)) \<in> appr_rell"
         by (auto simp: appr_rell_internal br_def)
       from transfer_operations(2)[param_fo, OF this]
       have *: "set_of_appr (product_appr x (concat_appr xs)) =
          product_listset (set_of_appr x) (set_of_appr (concat_appr xs))"
         by (auto simp: appr_rell_internal br_def)
       show ?case using Cons
         apply (auto simp: * product_listset_def list_rel_def set_Cons_def)
         subgoal premises prems for a b
           using prems(2)[OF prems(7)] prems(6)
           apply (auto )
           subgoal for ya
           apply (rule image_eqI[where x="a#ya"])
             by (auto simp: set_Cons_def)
           done
         done
     qed
   qed
   done

lemma op_concat_listset_autoref[autoref_rules]:
  "(concat_appr, op_concat_listset) \<in> \<langle>appr_rell\<rangle>list_rel \<rightarrow> appr_rell"
  using concat_appr by force

lemma appr_rel_br: "appr_rel = br (\<lambda>xs. eucl_of_list ` (set_of_appr xs)::'a set) (\<lambda>xs. length xs = DIM('a::executable_euclidean_space))"
  unfolding appr_rel_def lv_rel_def set_rel_br
  unfolding appr_rell_internal br_chain o_def
  using length_set_of_appr
  by (auto dest!: brD intro: brI)

lemma list_all2_replicate [simp]: "list_all2 (\<le>) xs xs" for xs::"'a::order list"
  by (auto simp: list_all2_iff in_set_zip)

lemma lv_ivl_self[simp]: "lv_ivl xs xs = {xs}" for xs::"'a::order list"
  by (force simp: lv_ivl_def list_all2_conv_all_nth
      intro!: nth_equalityI)

lemma set_of_appr_of_ivl_point'[simp]:
  "set_of_appr (appr_of_ivl (replicate E 0) (replicate E 0)) = {replicate E (0::real)}"
  using transfer_operations(1)[of "(replicate E (0::real))" "(replicate E (0::real))" "(replicate E (0::real))" "(replicate E 0)"]
  by (auto simp: appr_rell_internal br_def)

lemma set_of_appr_of_ivl_point:
  "set_of_appr (appr_of_ivl xs xs) = {xs}"
  using transfer_operations(1)[of xs xs xs xs]
  by (auto simp: appr_rell_internal br_def)


lemma
  take_set_of_apprI:
  assumes "xs \<in> set_of_appr XS" "tXS = take d XS" "d < length xs"
  shows "take d xs \<in> set_of_appr tXS"
  using set_of_appr_project[OF assms(1), of "[0..<d]"]
  apply (auto simp: assms take_eq_map_nth length_set_of_appr)
  using assms(1) assms(3) length_set_of_appr take_eq_map_nth by fastforce

lemma length_appr_of_ivl[simp]:
  "length (appr_of_ivl xs ys) = length xs"
  if "list_all2 (\<le>) xs ys"
  using transfer_operations(1)[of xs ys xs ys] that
    apply (simp add: appr_rell_internal br_def lv_ivl_def)
  apply (auto simp: appr_rell_internal br_def list_all2_lengthD dest!: length_set_of_appr)
  using length_set_of_appr by fastforce

lemma length_appr_of_ivl_point[simp]:
  "length (appr_of_ivl xs xs) = length xs"
  by (simp add: list_all2_refl)

definition [simp]: "op_atLeastAtMost_appr = atLeastAtMost"
lemma [autoref_op_pat]: "atLeastAtMost \<equiv> OP op_atLeastAtMost_appr"
  by simp

lemma transfer_operations1[autoref_rules]:
  assumes "SIDE_PRECOND (x \<le> y)" "(xi, x) \<in> lv_rel" "(yi, y) \<in> lv_rel"
  shows "(appr_of_ivl xi yi, op_atLeastAtMost_appr $ x $ y) \<in> appr_rel"
proof -
  have "(appr_of_ivl xi yi, lv_ivl (list_of_eucl x) (list_of_eucl y)) \<in> appr_rell"
    apply (rule transfer_operations[unfolded autoref_tag_defs])
    using assms lv_rel_le[param_fo, of xi x yi y]
    by (auto simp: lv_rel_def br_def)
  then have "(appr_of_ivl xi yi, eucl_of_list ` lv_ivl (list_of_eucl x) (list_of_eucl y)::'a set) \<in> appr_rel"
    unfolding appr_rel_br
    using assms[unfolded lv_rel_def]
    using lv_rel_le[param_fo, of xi x yi y]
    by (auto simp: appr_rell_internal br_def appr_rel_br)
       (auto simp: lv_rel_def br_def)
  also have "eucl_of_list ` lv_ivl (list_of_eucl x) (list_of_eucl y) = {x .. y}"
    by (subst eucl_of_list_image_lv_ivl) auto
  finally show ?thesis by simp
qed

lemma appr_of_ivl_point_appr_rel:
  "(appr_of_ivl x x, {eucl_of_list x::'a::executable_euclidean_space}) \<in> appr_rel"
  if "length x = DIM('a)"
  using transfer_operations1[OF _ lv_relI lv_relI, OF _ that that]
  by auto

lemmas [autoref_post_simps] = concat.simps append_Nil2 append.simps

lemma is_empty_appr_rel[autoref_rules]:
  "(\<lambda>_. False, is_empty) \<in> appr_rel \<rightarrow> bool_rel"
  by (auto simp: appr_rel_br br_def)

definition card_info::"_ set \<Rightarrow> nat nres" where [refine_vcg_def]: "card_info x = SPEC top" \<comment>\<open>\<open>op_set_wcard\<close>\<close>
sublocale autoref_op_pat_def card_info .

lemma card_info[autoref_rules]:
  "((\<lambda>x. RETURN (length x)), card_info) \<in> clw_rel R \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  by (auto simp: card_info_def nres_rel_def)

lemma appr_rel_nonempty: "(x, X) \<in> appr_rel \<Longrightarrow> X \<noteq> {}"
  by (auto simp: appr_rel_br br_def)

lemma [autoref_rules]: "(optns, optns) \<in> Id"
  by simp

lemma single_valued_appr_rel[relator_props]:
  "single_valued (appr_rel)"
  by (auto simp: appr_rel_br)

lemma nth_append_cond:
  "i < length xs \<Longrightarrow> (xs @ ys) ! i = xs ! i"
  "i \<ge> length xs \<Longrightarrow> (xs @ ys) ! i = ys ! (i - length xs)"
  by (auto simp: nth_append)

lemma ivl_rep_of_set_nres:
  fixes X::"'a::executable_euclidean_space set"
  shows "do { let X = ((X ::: A):::appr_rel); i \<leftarrow> Inf_spec X; s \<leftarrow> Sup_spec X; RETURN (inf i s, s)} \<le> ivl_rep_of_set X"
  unfolding ivl_rep_of_set_def Inf_spec_def Sup_spec_def
  by (refine_vcg) (auto simp: inf.coboundedI1)

schematic_goal ivl_rep_of_set_impl:
  fixes X::"'a::executable_euclidean_space set"
  assumes [autoref_rules]: "(ai, X) \<in> appr_rel"
  shows "(RETURN (?f::?'r), ivl_rep_of_set X) \<in> ?R"
  by (rule ivl_rep_of_set_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition ivl_rep_of_set_impl for  ai uses ivl_rep_of_set_impl
lemma ivl_rep_of_set_autoref[autoref_rules]:
  shows "(\<lambda>x. RETURN (ivl_rep_of_set_impl x), ivl_rep_of_set) \<in> appr_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  using ivl_rep_of_set_impl.refine
  by auto

lemma ivl_rep_of_sets_nres:
  "FORWEAK XS (RETURN (0, 0)) ivl_rep_of_set (\<lambda>(i, s) (i', s'). RETURN (inf i i':::lv_rel, sup s s':::lv_rel)) \<le> ivl_rep_of_sets XS"
  apply (cases "XS = {}")
  subgoal by (simp add: ivl_rep_of_sets_def)
  subgoal premises ne
  proof -
    have "FORWEAK XS (RETURN (0, 0)) ivl_rep_of_set (\<lambda>(i, s) (i', s'). RETURN (inf i i', sup s s')) \<le> SPEC (\<lambda>(i, s). (\<forall>X\<in>XS. X \<subseteq> {i..s} \<and> i \<le> s))"
      by (auto simp: subset_iff le_infI1 le_infI2 le_supI1 le_supI2 ivl_rep_of_set_def split_beta' intro!: FORWEAK_elementwise_rule)
    also have "\<dots> \<le> ivl_rep_of_sets XS"
      using ne by (auto simp add: ivl_rep_of_sets_def)
    finally show ?thesis by (simp add: ne)
  qed
  done

schematic_goal ivl_rep_of_sets_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(ai, a) \<in> \<langle>appr_rel\<rangle>list_wset_rel"
  notes [refine_transfer] = FORWEAK_LIST_plain.refine
  shows "(RETURN (?f), ivl_rep_of_sets a::('a \<times> 'a)nres) \<in> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  by (rule nres_rel_trans2[OF ivl_rep_of_sets_nres]) (autoref_monadic(plain))
concrete_definition ivl_rep_of_sets_impl for n ai uses ivl_rep_of_sets_impl
lemma ivl_rep_of_sets_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
  (\<lambda>ai. RETURN (ivl_rep_of_sets_impl n ai), ivl_rep_of_sets::_\<Rightarrow>('a \<times> 'a)nres) \<in> \<langle>appr_rel\<rangle>list_wset_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  using ivl_rep_of_sets_impl.refine by force

definition [refine_vcg_def]: "sets_of_coll X = SPEC (\<lambda>XS. X = \<Union>XS)"
sublocale autoref_op_pat_def sets_of_coll .

lemma sets_of_coll_autoref[autoref_rules]:
  shows "(\<lambda>x. RETURN x, sets_of_coll) \<in> clw_rel R \<rightarrow> \<langle>\<langle>R\<rangle>list_wset_rel\<rangle>nres_rel"
  by (auto simp: lw_rel_def Union_rel_def br_def set_rel_def list_wset_rel_def sets_of_coll_def
    Id_arbitrary_interface_def
      elim!: single_valued_as_brE
      intro!: nres_relI RETURN_SPEC_refine)
    auto

lemma Inf_spec_ivl_rel[autoref_rules]:
  "(\<lambda>x. RETURN (fst x), Inf_spec) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  and Sup_spec_ivl_rel[autoref_rules]:
  "(\<lambda>x. RETURN (snd x), Sup_spec) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  by (force simp: Inf_spec_def Sup_spec_def nres_rel_def ivl_rel_def br_def set_of_ivl_def
      intro!: RETURN_SPEC_refine)+

definition [simp]: "set_of_coll X = X"

definition [simp]: "ivl_rep_of_set_coll = ivl_rep_of_set"

lemma ivl_rep_of_set_coll:
  "do { Xs \<leftarrow> sets_of_coll (X:::clw_rel appr_rel); ivl_rep_of_sets Xs} \<le> ivl_rep_of_set_coll X"
  unfolding ivl_rep_of_set_def ivl_rep_of_set_coll_def
  by refine_vcg auto

schematic_goal ivl_rep_of_set_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  shows "(RETURN (?f), ivl_rep_of_set_coll a::('a\<times>'a) nres) \<in> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  by (rule nres_rel_trans2[OF ivl_rep_of_set_coll]) (autoref_monadic (plain))
concrete_definition ivl_rep_of_set_coll_impl for n ai uses ivl_rep_of_set_coll_impl
lemma ivl_rep_of_set_coll_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
  (\<lambda>ai. RETURN (ivl_rep_of_set_coll_impl n ai), ivl_rep_of_set_coll::_\<Rightarrow>('a\<times>'a) nres) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  using ivl_rep_of_set_coll_impl.refine by force

definition [refine_vcg_def]: "ivls_of_sets X = SPEC (\<lambda>R. X \<subseteq> R)"

abbreviation "lvivl_rel \<equiv> \<langle>lv_rel\<rangle>ivl_rel"

lemma ivls_of_set_FORWEAK:
  "do {
    XS \<leftarrow> (sets_of_coll (X:::clw_rel appr_rel) ::: \<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN (op_empty_coll:::clw_rel lvivl_rel))
      (\<lambda>X. do {
        (i, s) \<leftarrow> ivl_rep_of_set X;
        RETURN (mk_coll (op_atLeastAtMost_ivl i s:::\<langle>lv_rel\<rangle>ivl_rel))
      })
      (\<lambda>a b. RETURN (a \<union> b))
  } \<le> ivls_of_sets X"
  unfolding ivls_of_sets_def autoref_tag_defs
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>XS U. \<Union>XS \<subseteq> U"]) auto

schematic_goal ivls_of_sets_impl:
  assumes [autoref_rules]: "(xsi, xs) \<in> clw_rel appr_rel"
  shows "(nres_of (?f), ivls_of_sets $ xs) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule ivls_of_set_FORWEAK[THEN nres_rel_trans2]) autoref_monadic
concrete_definition ivls_of_sets_impl for xsi uses ivls_of_sets_impl
lemma ivls_of_set_impl_refine[autoref_rules]:
  "(\<lambda>ai. nres_of (ivls_of_sets_impl ai), ivls_of_sets) \<in> clw_rel appr_rel \<rightarrow> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  using ivls_of_sets_impl.refine by force

definition [simp]: "uninvar X = X"
sublocale autoref_op_pat_def uninvar .
lemma uninvar_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued X"
  shows "(map fst, uninvar) \<in> clw_rel (\<langle>X, A\<rangle>invar_rel b) \<rightarrow> clw_rel A"
  using assms
  by (force simp: lw_rel_def Union_rel_br invar_rel_br elim!: single_valued_as_brE
      dest!: brD
      intro!: brI)

definition [simp]: "ivl_to_set X = X"

lemma ivl_to_set[autoref_rules]:
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) ((lv_rel::(_ \<times> 'a::executable_euclidean_space)set) \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>(i, s). if le i s then [appr_of_ivl i s] else [], ivl_to_set::_\<Rightarrow>'a set) \<in> lvivl_rel \<rightarrow> clw_rel (appr_rel)"
  apply (clarsimp simp add: ivl_rel_def)
  subgoal premises prems for ls us l u X
    using le[OF \<open>(_, l) \<in> _\<close> \<open>(_, u) \<in> _\<close>] prems transfer_operations1[of l u ls us]
    apply (auto simp: Cons_mem_clw_rel_iff single_valued_appr_rel ivl_rel_def[symmetric] intro!: exI[where x=X])
    subgoal by (auto simp: set_of_ivl_def br_def)
    subgoal using Union_rel_empty by (auto simp: set_of_ivl_def br_def )
    done
  done

lemma clw_rel_br: "clw_rel (br a I) = br (\<lambda>xs. UNION (set xs) a) (\<lambda>xs. Ball (set xs) I)"
  unfolding lw_rel_def Union_rel_br by simp

lemma ivl_rel_br: "\<langle>br a I\<rangle>ivl_rel = br (\<lambda>(x, y). set_of_ivl (a x, a y)) (\<lambda>(x, y). I x \<and> I y)"
  unfolding ivl_rel_def br_rel_prod br_chain
  by (simp add: split_beta' o_def)

lemma set_of_lvivl: "length (l) = DIM('a::executable_euclidean_space) \<Longrightarrow>
    length u = DIM('a) \<Longrightarrow>
    ((l, u), set_of_lvivl (l, u)::'a set) \<in> lvivl_rel"
  by (force simp: set_of_lvivl_def ivl_rel_br ivl_rel_def lv_rel_def br_def)

lemma lvivl_rel_br: "lvivl_rel = br (\<lambda>(x, y). set_of_ivl (eucl_of_list x, eucl_of_list y::'a)) (\<lambda>(x, y). length x = DIM('a::executable_euclidean_space) \<and> length y = DIM('a))"
  unfolding lv_rel_def ivl_rel_br by (simp add: split_beta')

lemma lv_relI: "length c = DIM('c) \<Longrightarrow> (c, eucl_of_list c::'c::executable_euclidean_space) \<in> lv_rel"
  by (auto simp: lv_rel_def br_def)

definition [simp]: "sets_of_ivls X = X"
lemma sets_of_ivls[autoref_rules]:
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) ((lv_rel::(_ \<times> 'a::executable_euclidean_space)set) \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>xs. map (\<lambda>(i, s). appr_of_ivl i s) [(i,s) \<leftarrow> xs. le i s], sets_of_ivls::_\<Rightarrow>'a set) \<in> clw_rel lvivl_rel \<rightarrow> clw_rel (appr_rel)"
  apply (rule fun_relI)
  unfolding appr_rel_br ivl_rel_br clw_rel_br lvivl_rel_br
  apply (auto simp: br_def set_of_ivl_def)
  subgoal for a b c d
    apply (rule exI conjI le le[THEN IdD, THEN iffD2] lv_relI| assumption | force)+
    using transfer_operations1[where 'a='a, of "eucl_of_list c" "eucl_of_list d" c d]
    apply (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def)
    by (metis (mono_tags, lifting) atLeastAtMost_iff atLeastatMost_empty_iff case_prodD empty_iff)
  subgoal for a b c d
    using transfer_operations1[where 'a='a, of "eucl_of_list b" "eucl_of_list c" b c]
      le[of b _ c _, OF lv_relI lv_relI]
    by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def intro!: bexI)
  subgoal for a b c
    using transfer_operations1[where 'a='a, of "eucl_of_list b" "eucl_of_list c" b c]
      le[of b _ c _, OF lv_relI lv_relI]
    by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def intro!: bexI)
  done

schematic_goal above_sctn_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, above_sctn $ X $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule above_sctn_nres[THEN nres_rel_trans2]) autoref_monadic
concrete_definition above_sctn_impl for Xi sctni uses above_sctn_impl
lemma above_sctn_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (above_sctn_impl ai sctni), above_sctn) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using above_sctn_impl.refine by force

schematic_goal below_sctn_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, below_sctn $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule below_sctn_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition below_sctn_impl for ai sctni uses below_sctn_impl
lemma below_sctn_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (below_sctn_impl ai sctni), below_sctn) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using below_sctn_impl.refine by force

schematic_goal sbelow_sctn_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, sbelow_sctn $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule sbelow_sctn_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition sbelow_sctn_impl for ai sctni uses sbelow_sctn_impl
lemma sbelow_sctn_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (sbelow_sctn_impl ai sctni), sbelow_sctn) \<in>
    appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using sbelow_sctn_impl.refine by force

schematic_goal sbelow_sctns_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  shows "(?f::?'r, sbelow_sctns $ a $ sctns) \<in> ?R"
  unfolding autoref_tag_defs
  apply (rule sbelow_sctns_nres[THEN nres_rel_trans2])
  subgoal using list_set_rel_finiteD[of sctnsi sctns "\<langle>lv_rel\<rangle>sctn_rel"] \<open>(sctnsi, sctns) \<in> _\<close> by (simp add: relAPP_def)
  by (autoref_monadic (plain))
concrete_definition sbelow_sctns_impl for ai sctnsi uses sbelow_sctns_impl
lemma sbelow_sctns_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (sbelow_sctns_impl ai sctni), sbelow_sctns) \<in>
    appr_rel \<rightarrow> sctns_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using sbelow_sctns_impl.refine by force

lemma disjoint_sets_nres:
  fixes X Y::"'a::executable_euclidean_space set"
  shows "do {
    (iX, sX) \<leftarrow> ivl_rep X;
    (iY, sY) \<leftarrow> ivl_rep Y;
    RETURN (list_ex (\<lambda>i. sX \<bullet> i < iY \<bullet> i \<or> sY \<bullet> i < iX \<bullet> i) Basis_list)
  } \<le> disjoint_sets X Y"
  by (force simp: Inf_spec_def Sup_spec_def disjoint_sets_def list_ex_iff eucl_le[where 'a='a]
    intro!: refine_vcg)

schematic_goal disjoint_sets_impl:
  fixes A::"(_ * 'a::executable_euclidean_space set) set"
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(ai, a::'a set) \<in> lvivl_rel"
  assumes [autoref_rules]: "(bi, b) \<in> lvivl_rel"
  shows "(nres_of (?f::?'r dres), disjoint_sets $ a $ b) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule disjoint_sets_nres[THEN nres_rel_trans2])(autoref_monadic)
concrete_definition disjoint_sets_impl for n ai bi uses disjoint_sets_impl
lemma disjoint_sets_impl_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
  (\<lambda>ai bi. nres_of (disjoint_sets_impl n ai bi), disjoint_sets::'a set \<Rightarrow> _) \<in> lvivl_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using disjoint_sets_impl.refine by force

lemma intersects_nres:
  shows "(do {
    ii \<leftarrow> Inf_inner X (normal sctn);
    si \<leftarrow> Sup_inner X (normal sctn);
    RETURN (ii \<le> pstn sctn \<and> si \<ge> pstn sctn)
  }) \<le> intersects_spec X sctn"
  unfolding intersects_spec_def Inf_inner_def Sup_inner_def
  by refine_vcg (force simp: plane_of_def)

schematic_goal intersects_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, intersects_spec $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule intersects_nres[THEN nres_rel_trans2])
    (autoref_monadic (plain))
concrete_definition intersects_impl for ai sctni uses intersects_impl
lemma intersects_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (intersects_impl ai sctni), intersects_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using intersects_impl.refine by force


definition [simp]: "intersects_clw = intersects_spec"

lemma intersects_clw:
  shows "(do {
    XS \<leftarrow> sets_of_coll (X:::clw_rel appr_rel);
    FORWEAK XS (RETURN False) (\<lambda>X. intersects_spec X sctn) (\<lambda>a b. RETURN (a \<or> b))
  }) \<le> intersects_clw X sctn"
  unfolding intersects_spec_def intersects_clw_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>XS b. b \<or> \<Union>XS \<inter> plane_of sctn = {}"]) auto

schematic_goal intersects_clw_impl:
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, intersects_clw $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule intersects_clw[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition intersects_clw_impl for ai sctni uses intersects_clw_impl
lemma intersects_clw_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (intersects_clw_impl ai sctni), intersects_clw) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using intersects_clw_impl.refine by force

definition split_intersecting
  where [refine_vcg_def]: "split_intersecting X Y = SPEC (\<lambda>(R, S). X = R \<union> S \<and> X \<inter> Y \<subseteq> R \<and> S \<inter> Y = {})"

definition intersecting_sets where
  "intersecting_sets X Z = do {
    ZS \<leftarrow> sets_of_coll (Z);
    XS \<leftarrow> sets_of_coll (X);
    FORWEAK XS (RETURN (op_empty_coll, op_empty_coll)) (\<lambda>X. do {
      d \<leftarrow> FORWEAK ZS (RETURN True) (disjoint_sets X) (\<lambda>a b. RETURN (a \<and> b));
      RETURN (if d then (op_empty_coll, mk_coll X) else (mk_coll X, op_empty_coll))
    }) (\<lambda>(R, S). \<lambda>(R', S'). RETURN (R' \<union> R, S' \<union> S))
  }"
sublocale autoref_op_pat_def intersecting_sets .

lemma intersecting_sets_spec:
  shows "intersecting_sets X Y \<le> split_intersecting X Y"
  unfolding intersecting_sets_def split_intersecting_def
    autoref_tag_defs
  apply (refine_vcg)
  apply (rule FORWEAK_mono_rule[where I="\<lambda>XS. \<lambda>(R, S). 
        R \<union> S \<subseteq> X \<and> \<Union>XS \<subseteq> R \<union> S \<and> \<Union>XS \<inter> Y \<subseteq> R \<and> S \<inter> Y = {}"])
  subgoal by (refine_vcg)
  subgoal for a b c
    by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>ZS d. d \<longrightarrow> \<Union>ZS \<inter> c = {}"]) (auto split: if_splits)
  subgoal by (auto; blast)
  subgoal for a b c d e
    by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>ZS d. d \<longrightarrow> \<Union>ZS \<inter> c = {}"]) (auto split: if_splits)
  subgoal by auto
  done

schematic_goal split_intersecting_impl:
  fixes A::"(_ \<times> 'a::executable_euclidean_space set) set"
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(Xi,X::'a set)\<in>clw_rel lvivl_rel"
  assumes [autoref_rules]: "(Zi,Z)\<in>clw_rel lvivl_rel"
  shows "(nres_of ?f, split_intersecting $ X $ Z)\<in>\<langle>clw_rel lvivl_rel \<times>\<^sub>r clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  apply (rule nres_rel_trans2[OF intersecting_sets_spec])
  unfolding intersecting_sets_def
  by autoref_monadic

concrete_definition split_intersecting_impl for Xi Zi uses split_intersecting_impl
lemmas [autoref_rules] = split_intersecting_impl.refine

definition inter_overappr where [refine_vcg_def]: "inter_overappr X Y = SPEC (\<lambda>R. X \<inter> Y \<subseteq> R \<and> R \<subseteq> X)"

lemma inter_overappr_impl: "do {(X, _) \<leftarrow> split_intersecting X Y; RETURN X} \<le> inter_overappr X Y"
  unfolding split_intersecting_def inter_overappr_def autoref_tag_defs
  by (refine_vcg) auto

schematic_goal inter_overappr_autoref[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a::executable_euclidean_space)) n"
  assumes [autoref_rules]: "(Xi,X)\<in>clw_rel lvivl_rel"
  assumes [autoref_rules]: "(Zi,Z)\<in>clw_rel lvivl_rel"
  shows "(nres_of ?f, inter_overappr $ X $ Z::'a set nres)\<in>\<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule nres_rel_trans2[OF inter_overappr_impl]) (autoref_monadic)

lemma subset_spec_ivl_impl:
  shows
  "do {
      (i', s') \<leftarrow> ((ivl_rep ((ivl))));
      (i, s) \<leftarrow> (ivl_rep_of_set ((X::'a::executable_euclidean_space set)));
      RETURN (((i' \<le> i):::bool_rel) \<and> ((s \<le> s'):::bool_rel))
    } \<le> subset_spec X ivl"
    unfolding subset_spec_def autoref_tag_defs
    by (refine_vcg) force
schematic_goal subset_spec_ivlc:
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> appr_rel"
      "(ivli, ivl) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  notes [autoref_post_simps] = Let_def
  shows "(RETURN (?f), subset_spec $ X $ ivl) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule subset_spec_ivl_impl[THEN nres_rel_trans2]) autoref_monadic
concrete_definition subset_spec_ivlc for Xi ivli uses subset_spec_ivlc

lemma subset_spec_ivl_refine[autoref_rules]:
  "(\<lambda>Xi Yi. RETURN (subset_spec_ivlc Xi Yi), subset_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  for A::"(_ \<times> 'a::executable_euclidean_space set) set"
  using subset_spec_ivlc.refine
  by auto

definition [simp]: "subset_spec_coll = subset_spec"

lemma subset_spec_ivl_coll_impl:
  "do {
    XS \<leftarrow> (sets_of_coll X:::\<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN True)
      (\<lambda>X. subset_spec X ivl)
      (\<lambda>x y. RETURN (x \<and> y))
  } \<le> subset_spec_coll X ivl"
  unfolding autoref_tag_defs subset_spec_def subset_spec_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>x b. b \<longrightarrow> \<Union>x \<subseteq> ivl"])
     (auto simp: subset_iff set_of_ivl_def)
schematic_goal subset_spec_ivl_collc:
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> clw_rel appr_rel"
    "(ivli, ivl) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  notes [autoref_post_simps] = Let_def
  shows "(RETURN (?f), subset_spec_coll $ X $ ivl) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule subset_spec_ivl_coll_impl[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition subset_spec_ivl_collc for Xi ivli uses subset_spec_ivl_collc
lemma subset_spec_ivl_collc_refine[autoref_rules]:
  "(\<lambda>Xi Yi. RETURN (subset_spec_ivl_collc Xi Yi), subset_spec_coll) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using subset_spec_ivl_collc.refine by force

definition [refine_vcg_def]: "project_set X b y = SPEC (\<lambda>ivl. X \<inter> {x. x \<bullet> b = y} \<subseteq> ivl \<and> ivl \<subseteq> {x. x \<bullet> b = y})"
sublocale autoref_op_pat_def project_set .

lemma project_set_appr_le:
  "inter_sctn_spec X (Sctn b y) \<le> project_set X b y"
  unfolding project_set_def
  by (refine_vcg) (force simp: plane_of_def)+

schematic_goal project_set_appr:
  fixes b::"'a::executable_euclidean_space" and y
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel"
  assumes [autoref_rules]: "(bi, b) \<in> lv_rel"
  assumes [autoref_rules]: "(yi, y) \<in> rnv_rel"
  shows "(nres_of (?f::?'r dres), project_set X b y) \<in> ?R"
  by (rule nres_rel_trans2[OF project_set_appr_le]) autoref_monadic
concrete_definition project_set_appr for Xi bi yi uses project_set_appr
lemma project_set_appr_refine[autoref_rules]:
  "(\<lambda>Xi bi yi. nres_of (project_set_appr Xi bi yi), project_set) \<in> appr_rel \<rightarrow> lv_rel \<rightarrow> rnv_rel \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  using project_set_appr.refine by force

definition [simp]: "project_set_ivl X b y = do {
    CHECK (\<lambda>_. ()) (b \<in> set Basis_list \<or> -b \<in> set Basis_list);
    (i, s) \<leftarrow> ivl_rep X;
    RETURN (op_atLeastAtMost_ivl (i + (y - i \<bullet> b) *\<^sub>R b) (s + (y - s \<bullet> b) *\<^sub>R b):::\<langle>lv_rel\<rangle>ivl_rel)
  }"

schematic_goal project_set_ivl:
  fixes b::"'a::executable_euclidean_space" and y
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  assumes [autoref_rules]: "(bi, b) \<in> lv_rel"
  assumes [autoref_rules]: "(yi, y) \<in> rnv_rel"
  shows "(nres_of (?f::?'r dres), project_set_ivl X b y) \<in> ?R"
  unfolding project_set_ivl_def
  by autoref_monadic
concrete_definition project_set_ivl_impl for n Xi bi yi uses project_set_ivl
lemma project_set_ivl_refine[autoref_rules]:
  "DIM_precond (TYPE('a)) n \<Longrightarrow>
    (\<lambda>Xi bi yi. nres_of (project_set_ivl_impl n Xi bi yi), project_set_ivl) \<in>
    \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> (lv_rel::(_\<times>'a::executable_euclidean_space) set) \<rightarrow> rnv_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>ivl_rel\<rangle>nres_rel"
  using project_set_ivl_impl.refine by force

lemma project_set_ivl_spec[le, refine_vcg]: "project_set_ivl X b y \<le>
  SPEC (\<lambda>R. abs b \<in> Basis \<and> (\<exists>i s. X = {i .. s} \<and> R = {i + (y - i \<bullet> b) *\<^sub>R b .. s + (y - s \<bullet> b) *\<^sub>R b}))"
proof -
  define b' where "b' \<equiv> abs b"
  then have "b \<in> Basis \<Longrightarrow> b' \<in> Basis"
    "- b \<in> Basis \<Longrightarrow> b' \<in> Basis"
    "b \<in> Basis \<Longrightarrow> b = b'"
    "-b \<in> Basis \<Longrightarrow> b = - b'"
    using Basis_nonneg by (fastforce)+
  then show ?thesis
    unfolding project_set_def project_set_ivl_def
    by refine_vcg
      (auto 0 4 simp: subset_iff eucl_le[where 'a='a] algebra_simps inner_Basis)
qed

definition [simp]: "project_set_clw = project_set"
lemma project_set_clw_le:
  shows
  "do {
    XS \<leftarrow> (sets_of_coll (X:::clw_rel A));
    FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. do {
      P \<leftarrow> (project_set:::A \<rightarrow> lv_rel \<rightarrow> rnv_rel \<rightarrow> \<langle>A\<rangle>nres_rel) X b y;
      RETURN (mk_coll P)
    }) (\<lambda>X Y. RETURN (Y \<union> X))
  } \<le> project_set_clw X b y"
  unfolding autoref_tag_defs project_set_def project_set_clw_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X P. \<Union>X \<inter> {x. x \<bullet> b = y} \<subseteq> P \<and> P \<subseteq> {x. x \<bullet> b = y}"])
      auto

schematic_goal project_set_clw_impl:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel A"
  assumes [autoref_rules]: "(bi, b) \<in> lv_rel"
  assumes [autoref_rules]: "(yi, y) \<in> rnv_rel"
  assumes [autoref_rules(overloaded)]: "(ps, project_set) \<in> A \<rightarrow> lv_rel \<rightarrow> rnv_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  assumes [refine_transfer]: "\<And>a b c. nres_of (psd a b c) \<le> ps a b c"
  shows "(nres_of (?f::?'r dres), project_set_clw X b y) \<in> ?R"
  by (rule nres_rel_trans2[OF project_set_clw_le[where A=A]]) autoref_monadic
concrete_definition project_set_clw_impl for psd Xi bi yi uses project_set_clw_impl
lemma project_set_clw_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow>
  GEN_OP ps project_set (A \<rightarrow> lv_rel \<rightarrow> rnv_rel \<rightarrow> \<langle>A\<rangle>nres_rel) \<Longrightarrow>
  (\<And>a b c. TRANSFER (nres_of (psd a b c) \<le> ps a b c)) \<Longrightarrow>
  (\<lambda>Xi bi yi. nres_of (project_set_clw_impl psd Xi bi yi), project_set_clw) \<in>
    clw_rel A \<rightarrow> lv_rel \<rightarrow> rnv_rel \<rightarrow> \<langle>clw_rel A\<rangle>nres_rel"
  using project_set_clw_impl.refine[of A] by force

lemma projection_notempty:
  fixes b::"'a::executable_euclidean_space"
  assumes "b \<in> Basis \<or> -b \<in> Basis"
  assumes "x \<le> z"
  shows "x + (y - x \<bullet> b) *\<^sub>R b \<le> z + (y - z \<bullet> b) *\<^sub>R b"
proof -
  define b' where "b' \<equiv> - b"
  then have b_dest: "-b \<in> Basis \<Longrightarrow> b = -b' \<and> b' \<in> Basis"
    by simp
  show ?thesis using assms
    by (auto simp: eucl_le[where 'a='a] algebra_simps inner_Basis dest!: b_dest)
qed

definition restrict_to_halfspace::"'a::executable_euclidean_space sctn \<Rightarrow> 'a set \<Rightarrow> 'a set nres"
where
  "restrict_to_halfspace sctn X = do {
    CHECK (\<lambda>_. ()) (normal sctn \<in> set Basis_list \<or> - normal sctn \<in> set Basis_list);
    let y = pstn sctn;
    let b = normal sctn;
    (i, s) \<leftarrow> ivl_rep X;
    let i' = (if b \<le> 0 then (i + (min (y - i \<bullet> b) 0) *\<^sub>R b) else i);
    let s' = (if b \<ge> 0 then (s + (min (y - s \<bullet> b) 0) *\<^sub>R b) else s);
    RETURN ({i' .. s'}:::\<^sub>i\<langle>i_rnv\<rangle>\<^sub>ii_ivl)
  }"
sublocale autoref_op_pat_def restrict_to_halfspace .
schematic_goal restrict_to_halfspace_impl:
  fixes b y
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a::executable_euclidean_space)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  assumes [autoref_rules]: "(sctni, sctn::'a sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(nres_of (?f::?'r dres), restrict_to_halfspace sctn X) \<in> ?R"
  unfolding restrict_to_halfspace_def[abs_def]
  by (autoref_monadic)
concrete_definition restrict_to_halfspace_impl for n sctni Xi uses restrict_to_halfspace_impl
lemma restrict_to_halfspace_impl_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
    (\<lambda>sctni Xi. nres_of (restrict_to_halfspace_impl n sctni Xi), restrict_to_halfspace::'a sctn\<Rightarrow>_) \<in>
      \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>ivl_rel\<rangle>nres_rel"
  using restrict_to_halfspace_impl.refine by force
lemma restrict_to_halfspace[THEN order_trans, refine_vcg]:
  "restrict_to_halfspace sctn X \<le> SPEC (\<lambda>R. R = X \<inter> below_halfspace sctn)"
  unfolding restrict_to_halfspace_def
  apply (refine_vcg)
  subgoal premises prems for x a b
  proof -
    from prems obtain i where i: "i \<in> Basis" and disj: "normal sctn = i \<or> normal sctn = - i"
      by (auto simp: )
    note nn = Basis_nonneg[OF i]
    note nz = nonzero_Basis[OF i]
    have ne: "- i \<noteq> i" using nn nz
      by (metis antisym neg_le_0_iff_le)
    have nn_iff: "0 \<le> normal sctn \<longleftrightarrow> normal sctn = i"
      using disj nn
      by (auto)
    from prems have X: "X = {a .. b}" by auto
    from disj show ?thesis
      unfolding nn_iff
      apply (rule disjE)
      using nn nz ne
       apply (simp_all add: below_halfspace_def le_halfspace_def[abs_def])
      unfolding X using i
      by (auto simp: eucl_le[where 'a='a] min_def algebra_simps inner_Basis
          split: if_splits)
        (auto simp: algebra_simps not_le)
  qed
  done

definition [refine_vcg_def]: "restrict_to_halfspaces sctns X = SPEC (\<lambda>R. R = X \<inter> below_halfspaces sctns)"
sublocale autoref_op_pat_def restrict_to_halfspaces .

lemma restrict_to_halfspaces_impl:
  "do {
    ASSUME (finite sctns);
    FOREACH\<^bsup>\<lambda>sctns' Y. Y = X \<inter> below_halfspaces (sctns - sctns')\<^esup> sctns restrict_to_halfspace X
  } \<le> restrict_to_halfspaces sctns X"
  unfolding restrict_to_halfspaces_def
  by (refine_vcg) (auto simp: halfspace_simps)

schematic_goal restrict_to_halfspaces_ivl:
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a::executable_euclidean_space)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  assumes sctns[autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  notes [simp] = list_set_rel_finiteD[OF sctns]
  shows "(nres_of (?f::?'r dres), restrict_to_halfspaces sctns X::'a set nres) \<in> ?R"
  by (rule nres_rel_trans2[OF restrict_to_halfspaces_impl]) autoref_monadic
concrete_definition restrict_to_halfspaces_ivl for n sctnsi Xi uses restrict_to_halfspaces_ivl
lemma restrict_to_halfspaces_impl_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
  (\<lambda>sctni Xi. nres_of (restrict_to_halfspaces_ivl n sctni Xi), restrict_to_halfspaces) \<in>
      sctns_rel \<rightarrow> \<langle>(lv_rel::(_\<times>'a) set)\<rangle>ivl_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>ivl_rel\<rangle>nres_rel"
  using restrict_to_halfspaces_ivl.refine[of n] by force

definition [simp]: "restrict_to_halfspaces_clw = restrict_to_halfspaces"
lemma restrict_to_halfspaces_clw:
  "do {
    XS \<leftarrow> sets_of_coll X;
    FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. do {R \<leftarrow> restrict_to_halfspaces sctns X; RETURN (filter_empty_ivls (mk_coll R))})
      (\<lambda>X Y. RETURN (Y \<union> X))
  } \<le> restrict_to_halfspaces_clw sctns X"
  unfolding restrict_to_halfspaces_def restrict_to_halfspaces_clw_def
  by (refine_vcg FORWEAK_mono_rule[where
        I="\<lambda>XS R. \<Union>XS \<inter> below_halfspaces sctns \<subseteq> R \<and> R \<subseteq> X \<inter> below_halfspaces sctns"])
    auto
schematic_goal restrict_to_halfspaces_clw_rel:
  fixes X::"'a::executable_euclidean_space set"
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel (\<langle>lv_rel\<rangle>ivl_rel)"
  assumes sctns[autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  notes [simp] = list_set_rel_finiteD[OF sctns]
  shows "(nres_of (?f::?'r dres), restrict_to_halfspaces_clw sctns X) \<in> ?R"
  by (rule nres_rel_trans2[OF restrict_to_halfspaces_clw]) autoref_monadic
concrete_definition restrict_to_halfspaces_clw_rel for n sctnsi Xi uses restrict_to_halfspaces_clw_rel
lemma restrict_to_halfspaces_clw_rel_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
    (\<lambda>sctni Xi. nres_of (restrict_to_halfspaces_clw_rel n sctni Xi), restrict_to_halfspaces_clw) \<in>
      sctns_rel \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>clw_rel (\<langle>(lv_rel::(_\<times>'a) set)\<rangle>ivl_rel)\<rangle>nres_rel"
  using restrict_to_halfspaces_clw_rel.refine by force

definition [simp]: "restrict_to_halfspaces_invar_clw = restrict_to_halfspaces"
lemma restrict_to_halfspaces_invar_clw_ref:
  "do {
    XS \<leftarrow> (sets_of_coll X);
    FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. do {
        (X, i) \<leftarrow> get_invar a X;
        R \<leftarrow> restrict_to_halfspaces sctns X;
        ASSERT (R \<subseteq> a i);
        RETURN (with_invar i (filter_empty_ivls (mk_coll R)):::clw_rel (\<langle>I, lvivl_rel\<rangle>invar_rel a))
      }) (\<lambda>X Y. RETURN (Y \<union> X))
  } \<le> restrict_to_halfspaces_invar_clw sctns X"
  unfolding restrict_to_halfspaces_def restrict_to_halfspaces_invar_clw_def
  by (refine_vcg FORWEAK_mono_rule[where
        I="\<lambda>XS R. \<Union>XS \<inter> below_halfspaces sctns \<subseteq> R \<and> R \<subseteq> X \<inter> below_halfspaces sctns"])
    auto
schematic_goal restrict_to_halfspaces_invar_clw_impl:
  fixes X::"'a::executable_euclidean_space set"
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel (\<langle>I, lvivl_rel\<rangle>invar_rel a)"
  assumes sctns[autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  notes [simp] = list_set_rel_finiteD[OF sctns]
  shows "(nres_of (?f::?'r dres), restrict_to_halfspaces_invar_clw sctns X) \<in> ?R"
  by (rule nres_rel_trans2[OF restrict_to_halfspaces_invar_clw_ref[where a=a and I=I]])
    (autoref_monadic)

concrete_definition restrict_to_halfspaces_invar_clw_impl for n sctnsi Xi uses restrict_to_halfspaces_invar_clw_impl
lemma restrict_to_halfspaces_invar_clw_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
    (\<lambda>sctnsi Xi. nres_of (restrict_to_halfspaces_invar_clw_impl n sctnsi Xi), restrict_to_halfspaces_invar_clw::'a sctn set \<Rightarrow> _) \<in>
      sctns_rel \<rightarrow> clw_rel (\<langle>I, lvivl_rel\<rangle>invar_rel a) \<rightarrow> \<langle>clw_rel (\<langle>I, lvivl_rel\<rangle>invar_rel a)\<rangle>nres_rel"
  using restrict_to_halfspaces_invar_clw_impl.refine[of n _ _ a I] by force

abbreviation "below_invar_rel \<equiv> \<lambda>A. \<langle>\<langle>lv_rel\<rangle>sctn_rel, A\<rangle>invar_rel below_halfspace"
abbreviation "sbelow_invar_rel \<equiv> \<lambda>A. \<langle>\<langle>lv_rel\<rangle>sctn_rel, A\<rangle>invar_rel sbelow_halfspace"
abbreviation "plane_invar_rel \<equiv> \<lambda>A. \<langle>\<langle>lv_rel\<rangle>sctn_rel, A\<rangle>invar_rel plane_of"
abbreviation "belows_invar_rel \<equiv> \<lambda>A. \<langle>sctns_rel, A\<rangle>invar_rel below_halfspaces"
abbreviation "sbelows_invar_rel \<equiv> \<lambda>A. \<langle>sctns_rel, A\<rangle>invar_rel sbelow_halfspaces"

definition [simp]: "with_invar_on_invar = with_invar"
lemma with_invar_on_invar_impl[autoref_rules]:
  assumes "PREFER single_valued S"
  assumes "PREFER single_valued A"
  assumes "(sctni, sctn) \<in> S"
  assumes "GEN_OP uni (\<union>) (S \<rightarrow> S \<rightarrow> S)"
  assumes "(Xi, X) \<in> clw_rel (\<langle>S, A\<rangle>invar_rel a)"
  assumes "SIDE_PRECOND (X \<subseteq> a sctn)"
  assumes a_distrib: "SIDE_PRECOND (\<forall>x y. a (x \<union> y) = a x \<inter> a y)"
  shows "(map (\<lambda>(x, y). (x, uni sctni y)) Xi, with_invar_on_invar $ sctn $ X) \<in> clw_rel (\<langle>S, A\<rangle>invar_rel a)"
  using assms(1-6) a_distrib[unfolded autoref_tag_defs, rule_format]
  apply (auto simp: invar_rel_br intro!: map_mem_clw_rel_br elim!: single_valued_as_brE)
      apply (auto simp: lw_rel_def Union_rel_br)
      apply (auto simp: br_def)
    apply (metis (no_types, lifting) case_prod_conv)
   apply (drule_tac x=sctni and x' = sctn in fun_relD, force)
   apply (drule_tac x=b and x' = "\<alpha> b" in fun_relD, force)
   apply force
  apply (drule_tac x=sctni and x' = sctn in fun_relD, force)
  apply (drule_tac x=b and x' = "\<alpha> b" in fun_relD, force)
  apply safe
proof -
  fix \<alpha> :: "'a \<Rightarrow> 'c set" and invar :: "'a \<Rightarrow> bool" and \<alpha>' :: "'d \<Rightarrow> 'e set" and invara :: "'d \<Rightarrow> bool" and aa :: 'd and b :: 'a and x :: 'e
  assume a1: "x \<in> \<alpha>' aa"
  assume a2: "(aa, b) \<in> set Xi"
  assume a3: "(\<Union>x\<in>set Xi. case x of (x, s) \<Rightarrow> \<alpha>' x) \<subseteq> a (\<alpha> sctni)"
  assume a4: "\<forall>x\<in>set Xi. case x of (x, s) \<Rightarrow> invara x \<and> invar s \<and> \<alpha>' x \<subseteq> a (\<alpha> s)"
  assume a5: "\<And>x y. a (x \<union> y) = a x \<inter> a y"
  assume a6: "\<alpha> sctni \<union> \<alpha> b = \<alpha> (uni sctni b)"
  have f7: "invara aa \<and> invar b \<and> \<alpha>' aa \<subseteq> a (\<alpha> b)"
    using a4 a2 by fastforce
  have "x \<in> a (\<alpha> sctni)"
    using a3 a2 a1 by blast
  then show "x \<in> a (\<alpha> (uni sctni b))"
    using f7 a6 a5 a1 by (metis (full_types) Int_iff subsetCE)
qed

lemma
  set_of_ivl_union:
  fixes i1 i2 s1 s2::"'a::executable_euclidean_space"
  shows "set_of_ivl (i1, s1) \<union> set_of_ivl (i2, s2) \<subseteq> set_of_ivl (inf i1 i2, sup s1 s2)"
  by (auto simp: set_of_ivl_def)

lemma fold_set_of_ivl:
  fixes i s::"'a::executable_euclidean_space"
  assumes "\<And>i s. (i, s) \<in> set xs \<Longrightarrow> i \<le> s"
  assumes "i \<le> s"
  shows "UNION (insert (i,s) (set xs)) set_of_ivl \<subseteq>
      set_of_ivl (fold (\<lambda>(i1, s1) (i2, s2). (inf i1 i2, sup s1 s2)) xs (i, s))"
  using assms
proof (induction xs arbitrary: i s)
  case (Cons x xs i s)
  then show ?case
    apply (auto simp: set_of_ivl_def
        simp: split_beta' le_infI2 le_supI2 le_infI1 le_supI1)
    apply (metis (no_types, lifting) inf.absorb_iff2 inf_sup_ord(2) le_infE le_supI2)
    apply (metis (no_types, lifting) inf.absorb_iff2 inf_sup_ord(2) le_infE le_supI2)
     apply (metis (no_types, lifting) inf.absorb_iff2 inf_sup_ord(2) le_infE le_supI2)
    by (metis (no_types, lifting) inf_sup_absorb le_infI2 le_supI2)
qed simp

lemma fold_infsup_le:
  fixes i s::"'a::executable_euclidean_space"
  assumes "\<And>i s. (i, s) \<in> set xs \<Longrightarrow> i \<le> s"
  assumes "i \<le> s"
  shows "case (fold (\<lambda>(i1, s1) (i2, s2). (inf i1 i2, sup s1 s2)) xs (i, s)) of (i, s) \<Rightarrow> i \<le> s"
  using assms
proof (induction xs arbitrary: i s)
  case (Cons x xs i s)
  then show ?case
    by (auto simp: set_of_ivl_def
        simp: split_beta' le_infI2 le_supI2 le_infI1 le_supI1)
qed simp

definition "max_coord M (x::'a::executable_euclidean_space) =
  snd (fold (\<lambda>a (b, c). let d = abs x \<bullet> a in if d \<ge> b then (d, a) else (b, c)) (take M Basis_list) (0, 0))"

schematic_goal max_coord_autoref:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(Xi, X::'a) \<in> lv_rel"
  assumes [autoref_rules]: "(Mi, M) \<in> nat_rel"
  shows "(?r, max_coord M X) \<in> lv_rel"
  unfolding max_coord_def
  by autoref
concrete_definition max_coord_lv_rel for n Mi Xi uses max_coord_autoref
lemma max_coord_lv_rel_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow> (\<lambda>Mi Xi. max_coord_lv_rel n Mi Xi, max_coord::nat\<Rightarrow>'a\<Rightarrow>_) \<in> nat_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  using max_coord_lv_rel.refine by force

definition "split_ivl_at_halfspace sctn1 x =
  do {
    (i, s) \<leftarrow> ivl_rep x;
    let sctn2 = Sctn (- normal sctn1) (- pstn sctn1);
    x1 \<leftarrow> restrict_to_halfspace sctn1 x;
    x2 \<leftarrow> restrict_to_halfspace sctn2 x;
    RETURN (x1, x2)
  }"

lemma split_ivl_at_halfspace[THEN order_trans, refine_vcg]:
  "split_ivl_at_halfspace sctn x \<le> split_spec_exact x"
  unfolding split_ivl_at_halfspace_def split_spec_exact_def
  by refine_vcg (auto simp: halfspace_simps)

schematic_goal split_ivl_at_halfspace_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(Xi, X) \<in> lvivl_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(nres_of ?X, split_ivl_at_halfspace sctn (X::'a set)) \<in> \<langle>lvivl_rel \<times>\<^sub>r lvivl_rel\<rangle>nres_rel"
  unfolding split_ivl_at_halfspace_def
  by (autoref_monadic)
concrete_definition split_ivl_at_halfspace_impl for n sctni Xi uses split_ivl_at_halfspace_impl
lemma split_ivl_at_halfspace_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
    (\<lambda>sctni Xi. nres_of (split_ivl_at_halfspace_impl n sctni Xi), split_ivl_at_halfspace::_ \<Rightarrow> 'a set \<Rightarrow> _) \<in>
    \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>lvivl_rel \<times>\<^sub>r lvivl_rel\<rangle>nres_rel"
  using split_ivl_at_halfspace_impl.refine
  by force

definition "split_spec_ivl M x =
  do {
    (i, s) \<leftarrow> ivl_rep x;
    let d = s - i;
    let b = max_coord M d;
    let m = (i \<bullet> b + s \<bullet> b)/2;
    split_ivl_at_halfspace (Sctn b m) x
  }"

lemma split_spec_ivl_split_spec_exact[THEN order_trans, refine_vcg]:
  "split_spec_ivl M x \<le> split_spec_exact x"
  unfolding split_spec_ivl_def split_spec_exact_def
  by refine_vcg

schematic_goal split_spec_exact_ivl_rel:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(Xi, X) \<in> lvivl_rel"
  assumes [autoref_rules]: "(Mi, M) \<in> nat_rel"
  shows "(nres_of ?X, split_spec_ivl M (X::'a set)) \<in> \<langle>lvivl_rel \<times>\<^sub>r lvivl_rel\<rangle>nres_rel"
  unfolding split_spec_ivl_def
  by (autoref_monadic)
concrete_definition split_spec_exact_ivl_rel for n Mi Xi uses split_spec_exact_ivl_rel
lemma split_spec_exact_ivl_rel_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
    (\<lambda>Mi Xi. nres_of (split_spec_exact_ivl_rel n Mi Xi), split_spec_ivl::nat \<Rightarrow> 'a set \<Rightarrow> _) \<in>
    nat_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>lvivl_rel \<times>\<^sub>r lvivl_rel\<rangle>nres_rel"
  using split_spec_exact_ivl_rel.refine
  by force

lemma [autoref_itype]: "op_set_isEmpty ::\<^sub>i \<langle>L, \<langle>A\<rangle>\<^sub>ii_ivl\<rangle>\<^sub>ii_coll \<rightarrow>\<^sub>i i_bool"
  by simp

lemma op_set_isEmpty_clw_rel_ivl_rel[autoref_rules]:
  assumes sv[THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>xs. filter_empty_ivls_impl le xs = [], op_set_isEmpty) \<in> clw_rel (\<langle>A\<rangle>ivl_rel) \<rightarrow> bool_rel"
  apply (rule fun_relI)
  subgoal premises prems for a b
    using filter_empty_ivls[OF assms prems] sv
    apply (auto simp: list_wset_rel_def ivl_rel_br Union_rel_br filter_empty_ivls_impl_def filter_empty_conv
        set_of_ivl_def split_beta' Id_arbitrary_interface_def
        dest!: brD elim!: single_valued_as_brE)
    subgoal for \<alpha> I x y
      using le[of x "\<alpha> x"  y "\<alpha> y"]
      apply (auto simp: br_def)
      done
    done
  done

definition [refine_vcg_def]: "project_sets X b y = SPEC (\<lambda>ivl. X \<inter> {x. x \<bullet> b = y} \<subseteq> ivl \<and> ivl \<subseteq> {x. x \<bullet> b = y})"
sublocale autoref_op_pat_def project_sets .

lemma project_sets_FOREACH_refine:
  "do {
    Xs \<leftarrow> (sets_of_coll X ::: \<langle>\<langle>A\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK Xs (RETURN {}) (\<lambda>X. do { ivl \<leftarrow> project_set X b y; RETURN (mk_coll ivl)}) (\<lambda>a b. RETURN (a \<union> b))
  } \<le> project_sets X b y"
  unfolding project_sets_def autoref_tag_defs
  by (refine_vcg FORWEAK_mono_rule'[where I="\<lambda>S s. \<Union>S \<inter> {x. x \<bullet> b = y} \<subseteq> s \<and> s \<subseteq> {x. x \<bullet> b = y}"])
    auto

definition [simp]: "sbelow_sctns_coll = sbelow_sctns"
lemma sbelow_sctns_coll_refine:
  "do {
    XS \<leftarrow> (sets_of_coll XS ::: \<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN True) (\<lambda>X. sbelow_sctns X sctns) (\<lambda>a b. RETURN (a \<and> b))
  } \<le> sbelow_sctns_coll XS sctns"
  unfolding sbelow_sctns_def autoref_tag_defs sbelow_sctns_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X b. b \<longrightarrow> (\<Union>X \<subseteq> sbelow_halfspaces sctns)"]) auto
schematic_goal sbelow_sctns_coll_impl:
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  shows "(?f::?'r, sbelow_sctns_coll $ a $ sctns) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule sbelow_sctns_coll_refine[THEN nres_rel_trans2]) autoref
concrete_definition sbelow_sctns_coll_impl for ai sctnsi uses sbelow_sctns_coll_impl
lemma sbelow_sctns_coll_impl_refine[autoref_rules]:
  "(sbelow_sctns_coll_impl, sbelow_sctns_coll) \<in> clw_rel appr_rel \<rightarrow> sctns_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using sbelow_sctns_coll_impl.refine by force

schematic_goal sbelow_sctns_coll_dres:
  "nres_of ?r \<le> sbelow_sctns_coll_impl a sctns"
  unfolding sbelow_sctns_coll_impl_def
  by refine_transfer
concrete_definition sbelow_sctns_coll_dres for a sctns uses sbelow_sctns_coll_dres
lemmas [refine_transfer] = sbelow_sctns_coll_dres.refine

definition [simp]: "below_sctn_coll = below_sctn"
lemma below_sctn_coll_refine:
  "do {
    XS \<leftarrow> (sets_of_coll XS ::: \<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN True) (\<lambda>X. below_sctn X sctn) (\<lambda>a b. RETURN (a \<and> b))
  } \<le> below_sctn_coll XS sctn"
  unfolding below_sctn_def autoref_tag_defs below_sctn_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X b. b \<longrightarrow> (\<Union>X \<subseteq> below_halfspace sctn)"]) auto
schematic_goal below_sctn_coll_impl:
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, below_sctn_coll $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule below_sctn_coll_refine[THEN nres_rel_trans2]) autoref
concrete_definition below_sctn_coll_impl for ai sctni uses below_sctn_coll_impl
lemma below_sctn_coll_impl_refine[autoref_rules]:
  "(below_sctn_coll_impl, below_sctn_coll) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using below_sctn_coll_impl.refine by force
schematic_goal below_sctn_coll_dres:
  "nres_of ?r \<le> below_sctn_coll_impl a sctn"
  unfolding below_sctn_coll_impl_def
  by refine_transfer
concrete_definition below_sctn_coll_dres for a sctn uses below_sctn_coll_dres
lemmas [refine_transfer] = below_sctn_coll_dres.refine

definition split_with_invar::"('c \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> (('a set \<times> 'c) \<times> 'a set) nres"
  where [refine_vcg_def]: "split_with_invar i X = SPEC (\<lambda>((Y, sctn), YS). X = Y \<union> YS \<and> Y \<subseteq> i sctn)"
sublocale autoref_op_pat_def "split_with_invar i" for i .

abbreviation "splitbysndimpl xs \<equiv> do {
  let s = snd (hd xs);
  let (ys, zs) = List.partition (\<lambda>(_, sctn). sctn = s) xs;
  RETURN ((map fst ys, s), zs)
}"

lemma Nil_mem_clw_rel_iff[simp]: "([], X) \<in> clw_rel W \<longleftrightarrow> X = {}"
  by (auto simp: Union_rel_def br_def set_rel_def lw_rel_def)

lemma ex_br_conj_iff:
  "(\<exists>x. (y, x) \<in> br a I \<and> P x) \<longleftrightarrow> I y \<and> P (a y)"
  by (auto intro!: brI dest!: brD)
lemma split_with_invar_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued S"
  assumes "(xs, X) \<in> clw_rel (\<langle>S, A\<rangle>invar_rel a)"
  shows
    "(if xs \<noteq> [] then do { ((xs, sctn), ys) \<leftarrow> splitbysndimpl xs; RETURN ((xs, sctn), ys) } else SUCCEED,
    split_with_invar a $ X) \<in>
    \<langle>(clw_rel A \<times>\<^sub>r S) \<times>\<^sub>r clw_rel (\<langle>S, A\<rangle>invar_rel a)\<rangle>nres_rel"
  using assms
  by (fastforce simp: Let_def split_with_invar_def split_beta'
      lw_rel_def Union_rel_br ex_br_conj_iff invar_rel_br
      elim!: single_valued_as_brE
      intro!: nres_relI RETURN_SPEC_refine
      dest!: brD)

definition split_by_inter::"'a set \<Rightarrow> ('a set \<times> 'a set) nres"
  where [refine_vcg_def]: "split_by_inter X = SPEC (\<lambda>(Y, YS). X = Y \<union> YS)"

lemma split_by_inter_appr_plane_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued S"
  assumes "(xs, X) \<in> clw_rel (\<langle>A,S\<rangle>inter_rel)"
  shows
    "(let (a, b) = List.partition (\<lambda>(_, sctn). sctn = snd (hd xs)) xs in RETURN (a, b),
    split_by_inter $ X) \<in>
    \<langle>clw_rel (\<langle>A, S\<rangle>inter_rel) \<times>\<^sub>r clw_rel (\<langle>A, S\<rangle>inter_rel)\<rangle>nres_rel"
  using assms
  by (fastforce simp: Let_def split_by_inter_def split_beta'
      lw_rel_def Union_rel_br inter_rel_br ex_br_conj_iff Id_br[where 'a="'a sctn"]
      elim!: single_valued_as_brE
      intro!: nres_relI RETURN_SPEC_refine
      dest!: brD)

definition split_with_info::"'a set \<Rightarrow> ('c \<times> 'a set \<times> 'a set) nres"
  where [refine_vcg_def]: "split_with_info X = SPEC (\<lambda>(S, Y, YS). X = Y \<union> YS)"

lemma split_with_info_appr_plane_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued S"
  assumes "(xs, X) \<in> clw_rel (\<langle>A,S\<rangle>info_rel)"
  shows
    "(if xs = [] then SUCCEED else let s = fst (hd xs); (a, b) = List.partition (\<lambda>(sctn, _). sctn = s) xs in RETURN (s, map snd a, b),
    split_with_info $ X) \<in>
    \<langle>A \<times>\<^sub>r clw_rel S \<times>\<^sub>r clw_rel (\<langle>A, S\<rangle>info_rel)\<rangle>nres_rel"
  using assms
  by (fastforce simp: Let_def split_with_info_def split_beta'
      lw_rel_def Union_rel_br info_rel_br ex_br_conj_iff Id_br[where 'a="'a sctn"]
      split: if_splits
      elim!: single_valued_as_brE
      intro!: nres_relI RETURN_SPEC_refine brI hd_in_set
      dest!: brD )

definition
  "explicit_info_set X0 =
    do {
      e \<leftarrow> isEmpty_spec X0;
      (_, _, Xis) \<leftarrow> WHILE\<^bsup>\<lambda>(e, X, Y).
          (e \<longrightarrow> X = {}) \<and>
          X0 = X \<union> (\<Union>(sctn, IS)\<in>Y. IS)\<^esup>
        (\<lambda>(e, X, Y). \<not>e)
        (\<lambda>(e, X, Y).
          do {
            (sctn, S, X') \<leftarrow> split_with_info X;
            e \<leftarrow> isEmpty_spec X';
            RETURN (e, X', insert (sctn, S) Y)
          }
        )
        (e, X0, {});
      RETURN Xis
    }"
sublocale autoref_op_pat_def explicit_info_set .

lemma single_valued_Id_arbitrary_interface[relator_props]: "single_valued Id_arbitrary_interface"
  by (auto simp: Id_arbitrary_interface_def)

schematic_goal explicit_info_setc:
  fixes po :: "'d \<Rightarrow> 'a::executable_euclidean_space set"
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued S"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel (\<langle>S, A\<rangle>info_rel)"
  shows "(nres_of ?f, explicit_info_set $ XS) \<in> \<langle>\<langle>S \<times>\<^sub>r clw_rel A\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding explicit_info_set_def
  including art
  by autoref_monadic
concrete_definition explicit_info_setc for XSi uses explicit_info_setc
lemmas [autoref_rules] = explicit_info_setc.refine

lemma explicit_info_set[THEN order_trans, refine_vcg]:
  "explicit_info_set X \<le> SPEC (\<lambda>R. X = (\<Union>(sctn, IS) \<in> R. IS))"
  unfolding explicit_info_set_def
  by (refine_vcg) (auto simp: split_beta' subset_iff)

definition
  "explicit_sctn_set po X0 =
    do {
      e \<leftarrow> isEmpty_spec X0;
      (_, _, Xis) \<leftarrow> WHILE\<^bsup>\<lambda>(e, X, Y).
          (e \<longrightarrow> X = {}) \<and>
          X0 = X \<union> (\<Union>(sctn, IS)\<in>Y. IS) \<and>
          (\<forall>(sctn, IS) \<in> Y. IS \<subseteq> po sctn)\<^esup>
        (\<lambda>(e, X, Y). \<not>e)
        (\<lambda>(e, X, Y).
          do {
            ((S, sctn), X') \<leftarrow> split_with_invar po X;
            e \<leftarrow> isEmpty_spec X';
            RETURN (e, X', insert (sctn, S) Y)
          }
        )
        (e,
          X0,
          {});
      RETURN Xis
    }"
sublocale autoref_op_pat_def "explicit_sctn_set po" for po .

schematic_goal explicit_sctn_setc:
  fixes po :: "'d \<Rightarrow> 'a::executable_euclidean_space set"
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued S"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel (\<langle>S, A\<rangle>invar_rel po)"
  shows "(nres_of ?f, explicit_sctn_set po $ XS) \<in> \<langle>\<langle>S \<times>\<^sub>r clw_rel A\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding explicit_sctn_set_def
  including art
  by autoref_monadic
concrete_definition explicit_sctn_setc for XSi uses explicit_sctn_setc
lemmas [autoref_rules] = explicit_sctn_setc.refine

lemma explicit_sctn_set[THEN order_trans, refine_vcg]:
  "explicit_sctn_set po X \<le> SPEC (\<lambda>R. X = (\<Union>(sctn, IS) \<in> R. IS) \<and> (\<forall>(sctn, IS) \<in> R. IS \<subseteq> po sctn))"
  unfolding explicit_sctn_set_def
  by (refine_vcg) (auto simp: split_beta' subset_iff)

definition "sctnbounds_of_ivl M X = do {
    (l, u) \<leftarrow> ivl_rep X;
    let ls = (\<lambda>b. Sctn (- b) (- l \<bullet> b)) ` (set (take M Basis_list)::'a::executable_euclidean_space set);
    let us = (\<lambda>b. Sctn (b) (u \<bullet> b)) ` (set (take M Basis_list)::'a set);
    RETURN (ls \<union> us)
  }"
sublocale autoref_op_pat_def sctnbounds_of_ivl .

lemma sctnbounds_of_ivl[THEN order_trans, refine_vcg]:
  "sctnbounds_of_ivl M X \<le> SPEC (\<lambda>sctns. finite sctns \<and> (\<forall>sctn \<in> sctns. normal sctn \<noteq> 0))"
  unfolding sctnbounds_of_ivl_def
  by refine_vcg (auto dest!: in_set_takeD)

schematic_goal sctnbounds_of_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> lvivl_rel" "(Mi, M) \<in> nat_rel"
  shows "(?f, sctnbounds_of_ivl $ M $ X) \<in> \<langle>sctns_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding sctnbounds_of_ivl_def
  by autoref_monadic
concrete_definition sctnbounds_of_ivl_impl for Mi Xi uses sctnbounds_of_ivl_impl
lemma sctnbounds_of_ivl_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow>
  (\<lambda>Mi Xi. RETURN (sctnbounds_of_ivl_impl D Mi Xi), sctnbounds_of_ivl::nat \<Rightarrow> 'a set \<Rightarrow> _)
    \<in> nat_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>sctns_rel\<rangle>nres_rel"
  using sctnbounds_of_ivl_impl.refine by force

lemma SPEC_True_mono: "b \<le> c \<Longrightarrow> SPEC (\<lambda>_. True) \<bind> (\<lambda>_. b) \<le> c"
  by (auto simp: bind_le_nofailI)

definition "split_ivls_at_halfspace sctn XS = do {
    XS \<leftarrow> sets_of_coll XS;
    FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. do {
      (A, B) \<leftarrow> split_ivl_at_halfspace sctn X;
      RETURN (filter_empty_ivls (mk_coll A \<union> mk_coll B))
    }) (\<lambda>X X'. RETURN (X' \<union> X))
  }"
sublocale autoref_op_pat_def split_ivls_at_halfspace .

lemma split_ivls_at_halfspace[THEN order_trans, refine_vcg]:
  "split_ivls_at_halfspace sctn X \<le> SPEC (\<lambda>R. R = X)"
  unfolding split_ivls_at_halfspace_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xi XS. \<Union>Xi \<subseteq> XS \<and> XS \<subseteq> X"]) auto

schematic_goal split_ivls_at_halfspace_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f, split_ivls_at_halfspace $ sctn $ X) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_ivls_at_halfspace_def
  by autoref_monadic
concrete_definition split_ivls_at_halfspace_impl for sctni Xi uses split_ivls_at_halfspace_impl
lemma split_ivls_at_halfspace_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow>
  (\<lambda>Xi sctni. nres_of (split_ivls_at_halfspace_impl D Xi sctni), split_ivls_at_halfspace::'a sctn \<Rightarrow> _)
  \<in>  \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>clw_rel (\<langle>lv_rel\<rangle>ivl_rel)\<rangle>nres_rel"
  using split_ivls_at_halfspace_impl.refine
  by force

definition "split_along_ivls M X IS = do {
    IS \<leftarrow> sets_of_coll IS;
    sctns \<leftarrow> FORWEAK IS (RETURN {}) (sctnbounds_of_ivl M) (\<lambda>sctns sctns'. RETURN (sctns' \<union> sctns));
    FOREACH\<^bsup>\<lambda>_ R. R = X\<^esup> sctns split_ivls_at_halfspace X
  }"
sublocale autoref_op_pat_def split_along_ivls .

lemma split_along_ivls[THEN order_trans, refine_vcg]:"split_along_ivls M X IS \<le> SPEC (\<lambda>R. R = X)"
  unfolding split_along_ivls_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>_ r. finite r"])

schematic_goal split_along_ivls_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(ISi, IS) \<in> clw_rel lvivl_rel"
      "(Mi, M) \<in> nat_rel"
  shows "(?f, split_along_ivls $ M $ X $ IS) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_along_ivls_def
  by autoref_monadic
concrete_definition split_along_ivls_impl uses split_along_ivls_impl
lemmas [autoref_rules] = split_along_ivls_impl.refine

definition "subset_spec_ivls X Y = do {
    Ys \<leftarrow> sets_of_coll Y; FORWEAK Ys (RETURN False) (\<lambda>Y. subset_spec X Y) (\<lambda>a b. RETURN (a \<or> b))
  }"
sublocale autoref_op_pat_def subset_spec_ivls .

schematic_goal subset_spec_ivls_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(Yi, Y) \<in> clw_rel lvivl_rel"
  shows "(RETURN ?f, subset_spec_ivls X Y) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_ivls_def
  by (autoref_monadic (plain))
concrete_definition subset_spec_ivls_impl for Xi Yi uses subset_spec_ivls_impl
lemmas [autoref_rules] = subset_spec_ivls_impl.refine[autoref_higher_order_rule]

lemma subset_spec_ivls[THEN order_trans, refine_vcg]:
  "subset_spec_ivls X Y \<le> subset_spec X Y"
  unfolding subset_spec_ivls_def subset_spec_def
  by (refine_vcg FORWEAK_mono_rule'[where I="\<lambda>Ys b. b \<longrightarrow> X - \<Union>Ys \<subseteq> Y"]) auto

definition "subset_spec_ivls_clw M X Y = do {
    X \<leftarrow> split_along_ivls M X Y;
    X \<leftarrow> sets_of_coll (sets_of_ivls X);
    FORWEAK X (RETURN True) (\<lambda>X. subset_spec_ivls X Y) (\<lambda>a b. RETURN (a \<and> b))
  }"
sublocale autoref_op_pat_def subset_spec_ivls_clw .

schematic_goal subset_spec_ivls_clw_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(Yi, Y) \<in> clw_rel lvivl_rel"
    "(Mi, M) \<in> nat_rel"
  shows "(nres_of ?f, subset_spec_ivls_clw M X Y) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_ivls_clw_def
  including art
  by (autoref_monadic)
concrete_definition subset_spec_ivls_clw_impl for Mi Xi Yi uses subset_spec_ivls_clw_impl
lemma [autoref_rules]:
"DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow>
  (\<lambda>Mi Xi Yi. nres_of (subset_spec_ivls_clw_impl D Mi Xi Yi),
   subset_spec_ivls_clw::nat \<Rightarrow> 'a set \<Rightarrow> _)
  \<in> nat_rel \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using subset_spec_ivls_clw_impl.refine by force

definition [simp]: "REMDUPS x = x"
sublocale autoref_op_pat_def REMDUPS .
lemma REMDUPS_impl[autoref_rules]: "(remdups, REMDUPS) \<in> clw_rel A \<rightarrow> clw_rel A"
  if "PREFER single_valued A"
  using that
  by (force simp: clw_rel_br dest!: brD intro!: brI elim!: single_valued_as_brE)

definition "split_along_ivls2 M X Y = do {
    Xs \<leftarrow> sets_of_coll X;
    Rs \<leftarrow>FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. do {
      (I, N) \<leftarrow> split_intersecting Y (mk_coll X);
      split_along_ivls M (mk_coll X) I
    }) (\<lambda>x y. RETURN (y \<union> x));
    RETURN (REMDUPS Rs)
  }"
sublocale autoref_op_pat_def split_along_ivls2 .

lemma split_along_ivls2[THEN order_trans, refine_vcg]:"split_along_ivls2 M X IS \<le> SPEC (\<lambda>R. R = X)"
  unfolding split_along_ivls2_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>x xi. \<Union>x \<subseteq> xi \<and> xi \<subseteq> X"]) auto

schematic_goal split_along_ivls2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(ISi, IS) \<in> clw_rel lvivl_rel"
      "(Mi, M) \<in> nat_rel"
  shows "(nres_of ?f, split_along_ivls2 $ M $ X $ IS) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_along_ivls2_def
  by autoref_monadic
concrete_definition split_along_ivls2_impl uses split_along_ivls2_impl
lemmas [autoref_rules] = split_along_ivls2_impl.refine

definition [simp]: "op_list_of_eucl_image X = list_of_eucl ` X"
lemma [autoref_op_pat_def]: "list_of_eucl ` X \<equiv> OP op_list_of_eucl_image $ X" by simp

lemma op_list_of_eucl_image_autoref[autoref_rules]:
  shows "(\<lambda>xs. xs, op_list_of_eucl_image) \<in> appr_rel \<rightarrow> appr_rell"
  by (auto simp: length_set_of_appr appr_rel_def lv_rel_def image_image set_rel_br
      cong: image_cong
      dest!: brD)

definition [simp]: "op_eucl_of_list_image X = (eucl_of_list ` X::'a::executable_euclidean_space set)"
lemma [autoref_op_pat_def]: "eucl_of_list ` X \<equiv> OP op_eucl_of_list_image $ X" by simp

lemma op_eucl_of_list_image_autoref[autoref_rules]:
  assumes "(xsi, xs) \<in> appr_rell"
  assumes "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes "SIDE_PRECOND (env_len xs D)"
  shows "(xsi, op_eucl_of_list_image $ (xs)::'a set) \<in> appr_rel"
  using assms
  unfolding appr_rel_br
  by (auto simp: length_set_of_appr appr_rel_br br_def image_image env_len_def appr_rell_internal)

definition [simp]: "op_take_image n X = take n ` X"
lemma [autoref_op_pat_def]: "take n ` X \<equiv> OP op_take_image $ n $ X" by simp

lemma take_set_of_apprD: "xs \<in> set_of_appr XS \<Longrightarrow> take n xs \<in> set_of_appr (take n XS)"
  apply (cases "n < length xs")
   apply (subst take_eq_map_nth)
    apply simp
   apply (subst take_eq_map_nth)
    apply (simp add: length_set_of_appr)
   apply (rule set_of_appr_project)
  by (auto simp: length_set_of_appr)

lemma set_of_appr_ex_append1:
  "xrs \<in> set_of_appr xs \<Longrightarrow> \<exists>r. r @ xrs \<in> set_of_appr (b @ xs)"
proof (induction b)
  case Nil
  then show ?case by (auto intro!: exI[where x=Nil])
next
  case (Cons a b)
  then show ?case
    apply (auto)
    subgoal for r
      apply (drule set_of_apprs_ex_Cons[where b=a and xs="b@xs"])
      apply auto
      by (metis Cons_eq_appendI)
    done
qed

lemma set_of_appr_ex_append2:
  assumes "xrs \<in> set_of_appr xs" shows "\<exists>r. xrs @ r \<in> set_of_appr (xs @ b)"
proof -
  from set_of_appr_ex_append1[OF assms, of b]
  obtain r where r: "r @ xrs \<in> set_of_appr (b @ xs)" by auto
  have "map ((!) (r @ xrs)) ([length b..<length b + length xs] @ [0..<length b])
    \<in> set_of_appr (map ((!) (b @ xs)) ([length b..<length b + length xs] @ [0..<length b]))"
    by (rule set_of_appr_project[OF r, of "[length b..<length b + length xs] @ [0..<length b]"])
      auto
  also have "map ((!) (b @ xs)) ([length b..<length b + length xs] @ [0..<length b]) = xs @ b"
    by (auto intro!: nth_equalityI simp: nth_append)
  also have "map ((!) (r @ xrs)) ([length b..<length b + length xs] @ [0..<length b]) = xrs @ r"
    using length_set_of_appr[OF r] assms length_set_of_appr
    by (auto intro!: nth_equalityI simp: nth_append)
  finally show ?thesis by rule
qed

lemma drop_all_conc: "drop (length a) (a@b) = b"
  by (simp)

lemma set_of_appr_takeD: "xs \<in> set_of_appr (take n XS) \<Longrightarrow> xs \<in> take n ` set_of_appr XS"
  apply (frule set_of_appr_ex_append2[where b="map ((!) XS) [n..<length XS]"])
  apply (auto simp: take_append_take_minus_idem)
  apply (rule image_eqI)
   prefer 2 apply assumption
  by (metis append_eq_append_conv append_take_drop_id drop_all_conc length_drop length_set_of_appr)

lemma op_take_image_autoref[autoref_rules]:
  shows "(\<lambda>ni xs. take ni xs, op_take_image) \<in> nat_rel \<rightarrow> appr_rell \<rightarrow> appr_rell"
  apply (auto simp: appr_rell_internal br_def )
  subgoal by (rule take_set_of_apprD)
  subgoal by (rule set_of_appr_takeD)
  done

definition [simp]: "op_drop_image n X = drop n ` X"
lemma [autoref_op_pat_def]: "drop n ` X \<equiv> OP op_drop_image $ n $ X" by simp

lemma drop_eq_map_nth: "drop n xs = map ((!) xs) [n..<length xs]"
  by (auto intro!: nth_equalityI simp: nth_append)

lemma drop_set_of_apprD: "xs \<in> set_of_appr XS \<Longrightarrow> drop n xs \<in> set_of_appr (drop n XS)"
   apply (subst drop_eq_map_nth)
   apply (subst drop_eq_map_nth)
    apply (simp add: length_set_of_appr)
   apply (rule set_of_appr_project)
  by (auto simp: length_set_of_appr)

lemma drop_append_drop_minus_idem: "n < length XS \<Longrightarrow> map ((!) XS) [0..<n] @ drop n XS = XS"
  by (auto intro!: nth_equalityI simp: nth_append)

lemma set_of_appr_dropD: "xs \<in> set_of_appr (drop n XS) \<Longrightarrow> xs \<in> drop n ` set_of_appr XS"
  apply (cases "n < length XS")
  subgoal
    apply (frule set_of_appr_ex_append1[where b="map ((!) XS) [0..<n]"])
    apply (auto simp: drop_append_drop_minus_idem)
    apply (rule image_eqI)
    prefer 2 apply assumption
    by (metis (mono_tags, lifting) diff_add_inverse2 diff_diff_cancel drop_all_conc length_append
        length_drop length_set_of_appr less_imp_le)
  subgoal
    using set_of_appr_nonempty[of XS]
    by (auto simp: length_set_of_appr image_iff simp del: set_of_appr_nonempty)
  done

lemma op_drop_image_autoref[autoref_rules]:
  shows "(\<lambda>ni xs. drop ni xs, op_drop_image) \<in> nat_rel \<rightarrow> appr_rell \<rightarrow> appr_rell"
  apply (auto simp: appr_rell_internal br_def )
  subgoal by (rule drop_set_of_apprD)
  subgoal by (rule set_of_appr_dropD)
  done

lemma inj_on_nat_add_square: "inj_on (\<lambda>a::nat. a + a * a) S"
  by (rule strict_mono_imp_inj_on) (auto intro!: strict_monoI add_strict_mono mult_strict_mono)

lemma add_sq_eq[simp]: "a + a * a = b + b * b \<longleftrightarrow> a = b" for a b::nat
  using inj_on_nat_add_square[of UNIV, unfolded inj_on_def, rule_format, of a b]
  by auto

lemma mem_set_of_appr_appendE:
  assumes "zs \<in> set_of_appr (XS @ YS)"
  obtains xs ys where "zs = xs @ ys" "xs \<in> set_of_appr XS" "ys \<in> set_of_appr YS"
proof -
  have "zs = map ((!) zs) [0..<length XS] @ map ((!) zs) [length XS..<length XS + length YS]"
    using assms
    by (auto intro!: nth_equalityI simp: nth_append dest!: length_set_of_appr)
  moreover
  from
    set_of_appr_project[OF assms, of "[0..<length XS]"]
    set_of_appr_project[OF assms, of "[length XS..<length XS + length YS]"]
  have "map ((!) zs) [0..<length XS] \<in> set_of_appr XS"
    "map ((!) zs) [length XS..<length XS + length YS] \<in> set_of_appr YS"
    by (auto simp : map_nth_append2 map_nth_append1)
  ultimately show ?thesis ..
qed

lemma set_of_appr_of_ivl_append_point:
  "set_of_appr (xs @ appr_of_ivl p p) = (\<lambda>x. x @ p) ` set_of_appr xs"
  apply auto
   apply (frule length_set_of_appr)
  subgoal for x
    apply (rule image_eqI[where x="take (length xs) x"])
     apply (auto intro!: nth_equalityI simp: min_def)
     apply (simp add: nth_append)
    subgoal for i
      apply (frule set_of_appr_project[where ?is="[length xs..<length xs + length p]"])
       apply simp
      apply (auto simp: map_nth_append2 set_of_appr_of_ivl_point)
      subgoal premises prems
      proof -
        from prems
        have "map ((!) x) [length xs..<length xs + length p] ! (i - length xs) =
          p ! (i - length xs)"
          by simp
        also have "map ((!) x) [length xs..<length xs + length p] ! (i - length xs) = x ! i"
          using prems
          apply (auto simp: map_nth)
          by (metis add_diff_cancel_left' add_diff_inverse_nat add_less_cancel_left nth_map_upt)
        finally show ?thesis
          using prems by (simp add: min_def)
      qed
      done
    subgoal
      apply (frule set_of_appr_project[where ?is="[0..<length xs]"])
       apply (auto simp: map_nth_append1 take_eq_map_nth
          elim!: mem_set_of_appr_appendE
          dest: length_set_of_appr)
      done
    done
  subgoal premises prems for x
  proof -
    from set_of_appr_ex_append2[where b="appr_of_ivl p p", OF \<open>x \<in> set_of_appr xs\<close>]
    obtain r where r: "x @ r \<in> set_of_appr (xs @ appr_of_ivl p p)"
      by auto
    have "map ((!) (x @ r)) [length xs..<length xs + (length p)]
        \<in> set_of_appr
            (map ((!) (xs @ appr_of_ivl p p))
              [length xs..<length xs + (length p)])"
      by (rule set_of_appr_project[OF r, of "[length xs..<length xs+(length p)]"])
         auto
    also have "map ((!) (x @ r)) [length xs..<length xs + (length p)] = r"
      using length_set_of_appr prems r
      by (auto intro!: nth_equalityI simp: nth_append dest!: length_set_of_appr)
    also have "map ((!) (xs @ appr_of_ivl p p))
        [length xs..<length xs + (length p)] = appr_of_ivl p p"
      by (auto intro!: nth_equalityI)
    finally have "r = p"
      by (auto simp: set_of_appr_of_ivl_point)
    with r show ?thesis by simp
  qed
  done

lemma set_of_appr_of_ivl_point_append:
  "set_of_appr (appr_of_ivl p p @ xs) = (\<lambda>x. p @ x) ` set_of_appr xs"
  apply auto
   apply (frule length_set_of_appr)
  subgoal for x
    apply (rule image_eqI[where x="drop (length p) x"])
     apply (auto intro!: nth_equalityI simp: min_def)
     apply (simp add: nth_append)
    subgoal for i
      apply (frule set_of_appr_project[where ?is="[0..<(length p)]"])
       apply simp
      apply (auto simp: map_nth_append1 dest: length_set_of_appr)
      by (metis insertE mem_set_of_appr_appendE memb_imp_not_empty nth_append_cond(1) set_of_appr_of_ivl_point)
    by (metis add_right_imp_eq drop_all_conc drop_set_of_apprD length_append length_set_of_appr)
  subgoal premises prems for x
  proof -
    from set_of_appr_ex_append1[where b="appr_of_ivl p p",
        OF \<open>x \<in> set_of_appr xs\<close>]
    obtain r where r: "r @ x \<in> set_of_appr (appr_of_ivl p p @ xs)"
      by auto
    have "map ((!) (r @ x)) [0..<(length p)]
        \<in> set_of_appr
            (map ((!) (appr_of_ivl p p @ xs))
              [0..<(length p)])"
      by (rule set_of_appr_project[OF r, of "[0..<(length p)]"])
         (auto simp: )
    also have "map ((!) (r @ x)) [0..<(length p)] = r"
      using length_set_of_appr prems r
      by (auto intro!: nth_equalityI simp: nth_append dest!: length_set_of_appr)
    also have "map ((!) (appr_of_ivl p p @ xs))
        [0..<(length p)] = appr_of_ivl p p"
      by (auto intro!: nth_equalityI simp: nth_append)
    finally have "r = p"
      by (auto simp: set_of_appr_of_ivl_point)
    with r show ?thesis by simp
  qed
  done

lemma op_eucl_of_list_image_pad:
  assumes "(xsi, xs) \<in> appr_rell" "DIM_precond TYPE('a::executable_euclidean_space) E"
  shows "(take E xsi @ (let z = replicate (E - length xsi) 0 in appr_of_ivl z z),
    op_eucl_of_list_image $ xs::'a set) \<in> appr_rel"
  using assms
  unfolding appr_rel_br
  apply (auto simp: length_set_of_appr appr_rel_br br_def image_image env_len_def appr_rell_internal)
    apply (auto simp: Let_def set_of_appr_of_ivl_append_point length_set_of_appr)
   apply (rule image_eqI)
    prefer 2
    apply (rule image_eqI)
     apply (rule refl)
    apply (rule take_set_of_apprD)
    apply assumption
   apply auto
  apply (drule set_of_appr_takeD)
  apply auto
  done
concrete_definition op_eucl_of_list_image_pad for E xsi uses op_eucl_of_list_image_pad
lemma op_eucl_of_list_image_pad_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) E \<Longrightarrow>
  (op_eucl_of_list_image_pad E, op_eucl_of_list_image::_\<Rightarrow>'a set) \<in> appr_rell \<rightarrow> appr_rel"
  using op_eucl_of_list_image_pad.refine
  by force

definition "approx_slp_appr fas slp X = do {
    cfp \<leftarrow> approx_slp_spec fas DIM('a::executable_euclidean_space) slp X;
    (case cfp of
      Some cfp \<Rightarrow> do {
        RETURN ((eucl_of_list ` cfp::'a set):::appr_rel)
      }
      | None \<Rightarrow> do {
        SUCCEED
      }
    )
  }"
sublocale autoref_op_pat_def approx_slp_appr .
lemma [autoref_op_pat_def]: "approx_slp_appr fas \<equiv> OP (approx_slp_appr fas)"
  by auto
schematic_goal approx_slp_appr_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(slpi, slp) \<in> slp_rel" "(Xi, X) \<in> appr_rell"
    notes [autoref_rules] = IdI[of E]
  shows "(nres_of ?r, approx_slp_appr fas $ slp $ X::'a set nres) \<in> \<langle>appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding approx_slp_appr_def assms(1)[unfolded DIM_eq_def]
  including art
  by autoref_monadic

concrete_definition approx_slp_appr_impl for E slpi Xi uses approx_slp_appr_impl
lemma approx_slp_appr_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) E \<Longrightarrow>
(\<lambda>slpi Xi. nres_of (approx_slp_appr_impl E slpi Xi), approx_slp_appr fas::_\<Rightarrow>_\<Rightarrow>'a set nres) \<in>
    slp_rel \<rightarrow> appr_rell \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  using approx_slp_appr_impl.refine[where 'a='a, of E]
  by force

end

context begin interpretation autoref_syn .

lemma [autoref_rules]:
  "(slp_of_fas, slp_of_fas) \<in> fas_rel \<rightarrow> slp_rel"
  "(Norm, Norm) \<in> fas_rel \<rightarrow> Id"
  by auto

lemma length_slp_of_fas_le: "length fas \<le> length (slp_of_fas fas)"
  by (auto simp: slp_of_fas_def split: prod.splits)

lemma list_of_eucl_eqD: "list_of_eucl x = xs \<Longrightarrow> x = eucl_of_list xs"
  by auto

lemma slp_of_fasI:
  "d = (length fas) \<Longrightarrow>
    take d (interpret_slp (slp_of_fas fas) xs) =
    interpret_floatariths fas xs"
  using slp_of_fas by force

lemma [autoref_rules]: "(norm2_slp, norm2_slp) \<in> nat_rel \<rightarrow> Id"
  by auto
definition [simp]: "rnv_of_lv x = x"

lemma rnv_of_lv_impl[autoref_rules]: "(hd, rnv_of_lv) \<in> lv_rel \<rightarrow> rnv_rel"
  by (auto simp: lv_rel_def br_def length_Suc_conv)

lemma
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  shows snd_lv_rel[autoref_rules(overloaded)]: "(drop D, snd::('a \<times> _) \<Rightarrow> _) \<in> lv_rel \<rightarrow> lv_rel"
    and fst_lv_rel[autoref_rules(overloaded)]: "(take D, fst::('a \<times> _) \<Rightarrow> _) \<in> lv_rel \<rightarrow> lv_rel"
  using assms by (auto simp: lv_rel_def br_def eucl_of_list_prod)

definition [simp]: "Pair_lv_rel = Pair"

lemma Pair_lv_rel[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  shows "((@), Pair_lv_rel::'a \<Rightarrow> _) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  using assms
  by (auto simp: lv_rel_def br_def intro!: eucl_of_list_eqI)

definition [simp]: "split_lv_rel X = (fst X, snd X)"

schematic_goal split_lv_rel_impl[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  shows "(?r, split_lv_rel::'a\<times>_\<Rightarrow>_) \<in> lv_rel \<rightarrow> lv_rel \<times>\<^sub>r lv_rel"
  unfolding split_lv_rel_def
  by autoref

lemma [autoref_rules]:
  "(floatarith.Var, floatarith.Var) \<in> nat_rel \<rightarrow> Id"
  "(slp_of_fas, slp_of_fas) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel"
  "(fold_const_fa, fold_const_fa) \<in> Id \<rightarrow> Id"
  "(open_form, open_form) \<in> Id \<rightarrow> bool_rel"
  "(max_Var_floatariths, max_Var_floatariths) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel"
  "(max_Var_form, max_Var_form) \<in> Id \<rightarrow> nat_rel"
  "(length, length) \<in> \<langle>A\<rangle>list_rel \<rightarrow> nat_rel"
  by (auto simp: list_rel_imp_same_length)

end

context approximate_sets begin

lemma approx_fas[le, refine_vcg]:
  "approx_slp_appr fas slp X \<le> SPEC (\<lambda>R. \<forall>x \<in> X. einterpret fas x \<in> (R::'a set))"
  if "slp_of_fas fas = slp" "length fas = DIM('a::executable_euclidean_space)"
  unfolding approx_slp_appr_def
  by (refine_vcg that)

definition "mig_set D (X::'a::executable_euclidean_space set) = do {
    (i, s) \<leftarrow> ivl_rep_of_set (X:::appr_rel);
    let migc = mig_componentwise i s;
    ASSUME (D = DIM('a));
    let norm_fas = ([Norm (map Var [0..<D])]:::\<langle>Id\<rangle>list_rel);
    let env = (list_of_eucl ` ({migc .. migc}:::appr_rel):::appr_rell);
    (n::real set) \<leftarrow> approx_slp_appr  norm_fas (slp_of_fas norm_fas) env;
    (ni::real) \<leftarrow> Inf_spec (n:::appr_rel);
    RETURN (rnv_of_lv ni::real)
  }"

lemma DIM_precond_real[autoref_rules_raw]: "DIM_precond TYPE(real) 1" by simp

schematic_goal mig_set_impl: "(nres_of ?r, mig_set $ D $ X) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X::'a set) \<in> appr_rel"  "(Di, D) \<in> nat_rel"
  and [autoref_rules_raw, simplified, simp]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  unfolding autoref_tag_defs
  unfolding mig_set_def
  including art
  by autoref_monadic
concrete_definition mig_set_impl for Di Xi uses mig_set_impl
lemma mig_set_impl_refine[autoref_rules]:
  "(\<lambda>x. nres_of (mig_set_impl D x), mig_set $ D::'a set\<Rightarrow>_) \<in> appr_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  if "DIM_precond TYPE('a::executable_euclidean_space) D" "(Di, D) \<in> nat_rel"
  using mig_set_impl.refine that by force

lemma mig_set[le, refine_vcg]: "mig_set D X \<le> SPEC (\<lambda>m. \<forall>x \<in> X. m \<le> norm x)"
  unfolding mig_set_def
  apply refine_vcg
  apply (auto simp: dest!: bspec)
  apply (rule order_trans, assumption)
  apply (rule norm_mig_componentwise_le)
  by auto

end

consts i_alt::"interface \<Rightarrow> interface \<Rightarrow> interface"
context begin
interpretation autoref_syn .
definition alt_rel_internal: "alt_rel A B = {(x, y). case x of Inl x \<Rightarrow> (x, y) \<in> A | Inr x \<Rightarrow> (x, y) \<in> B}"

lemma alt_rel_def: "\<langle>A, B\<rangle>alt_rel = {(x, y). case x of Inl x \<Rightarrow> (x, y) \<in> A | Inr x \<Rightarrow> (x, y) \<in> B}"
  by (auto simp: relAPP_def alt_rel_internal)

primrec mk_alt::"'a + 'a \<Rightarrow> 'a" where
  "mk_alt (Inl X) = X"
| "mk_alt (Inr X) = X"

lemma alt_rel_const[autoref_rules]: "(\<lambda>x. x, mk_alt) \<in> \<langle>A, B\<rangle>sum_rel \<rightarrow> \<langle>A, B\<rangle>alt_rel"
  by (auto simp: mk_alt_def alt_rel_def split: sum.splits)

lemma unop_alt_rel:
  assumes "GEN_OP fa f (A \<rightarrow> C)"
  assumes "GEN_OP fb f (B \<rightarrow> D)"
  shows "(map_sum fa fb, f) \<in> \<langle>A, B\<rangle>alt_rel \<rightarrow> \<langle>C, D\<rangle>alt_rel"
  using assms
  by (auto simp: alt_rel_def map_sum_def split: sum.splits dest: fun_relD)

end

lemma prod_relI': "\<lbrakk>(a,fst ab')\<in>R1; (b,snd ab')\<in>R2\<rbrakk> \<Longrightarrow> ((a,b),ab')\<in>\<langle>R1,R2\<rangle>prod_rel"
  by  (auto simp: prod_rel_def)

lemma lv_relivl_relI:
  "((xs', ys'), {eucl_of_list xs..eucl_of_list ys::'a::executable_euclidean_space}) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  if [simp]: "xs' = xs" "ys' = ys" "DIM('a) = length xs" "length ys = length xs"
  by (force simp: ivl_rel_def set_of_ivl_def
      intro!:  brI lv_relI prod_relI[of _ "eucl_of_list xs" _ _ "eucl_of_list ys"])

end
