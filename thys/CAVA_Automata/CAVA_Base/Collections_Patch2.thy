theory Collections_Patch2
imports 
  Collections_Patch1
  "~~/src/HOL/Library/Infinite_Set"
begin
text {*
  This theory contains patches to the  Autoref, Refinement, 
  and Collections Framework that have not yet been integrated into CAVA's
  versions of these libraries.

  These patches are separated from Collections_Patch1, to make update simpler:
    Patch1 has been extracted a posteriori, and the libraries in 
    afp-devel will be replaced by the ported versions from the CAVA-repo, not
    using Patch1 at all.

    After that, Patch2 will be applied in afp-devel, to get the final versions 
    of the libraries fro afp-devel.
*}

(* Automatic_Refinement/Misc: Addition of lemmas *)
subsection {* Rules *}

(* for some reason, there is no such rule *)
lemma iffI2: "\<lbrakk>P \<Longrightarrow> Q; \<not> P \<Longrightarrow> \<not> Q\<rbrakk> \<Longrightarrow> P \<longleftrightarrow> Q"
by metis

lemma iffExI:
  "\<lbrakk> \<And>x. P x \<Longrightarrow> Q x; \<And>x. Q x \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> (\<exists>x. P x) \<longleftrightarrow> (\<exists>x. Q x)"
by metis

lemma bex2I[intro?]: "\<lbrakk> (a,b)\<in>S; (a,b)\<in>S \<Longrightarrow> P a b \<rbrakk> \<Longrightarrow> \<exists>a b. (a,b)\<in>S \<and> P a b"
  by blast

subsection {* Option Type *}

lemma the_Some_eq_id[simp]: "(the o Some) = id" by auto

lemma not_Some_eq2[simp]: "(\<forall>x y. v \<noteq> Some (x,y)) = (v = None)"
  by (cases v) auto

subsection {* Product Type *}

fun pairself where 
  "pairself f (a,b) = (f a, f b)"

lemma pairself_image_eq[simp]: 
  "pairself f ` {(a,b). P a b} = {(f a, f b)| a b. P a b}"
  by force

lemma pairself_image_cart[simp]: "pairself f ` (A\<times>B) = f`A \<times> f`B"
  by (auto simp: image_def)

lemma in_prod_fst_sndI: "fst x \<in> A \<Longrightarrow> snd x \<in> B \<Longrightarrow> x\<in>A\<times>B"
  by (cases x) auto

lemma inj_Pair[simp]: 
  "inj_on (\<lambda>x. (x,c x)) S"
  "inj_on (\<lambda>x. (c x,x)) S"
  by (auto intro!: inj_onI)

declare Product_Type.swap_inj_on[simp]

lemma img_fst [intro]:
  assumes "(a,b) \<in> S"
  shows "a \<in> fst ` S"
by (rule image_eqI[OF _ assms]) simp

lemma img_snd [intro]:
  assumes "(a,b) \<in> S"
  shows "b \<in> snd ` S"
by (rule image_eqI[OF _ assms]) simp

lemma range_prod:
  "range f \<subseteq> (range (fst \<circ> f)) \<times> (range (snd \<circ> f))"
proof
  fix y
  assume "y \<in> range f"
  then obtain x where y: "y = f x" by auto
  hence "y = (fst(f x), snd(f x))"
    by simp
  thus "y \<in> (range (fst \<circ> f)) \<times> (range (snd \<circ> f))"
    by (fastforce simp add: image_def)
qed

lemma finite_range_prod:
  assumes fst: "finite (range (fst \<circ> f))"
  and     snd: "finite (range (snd \<circ> f))"
  shows "finite (range f)"
proof -
  from fst snd have "finite (range (fst \<circ> f) \<times> range (snd \<circ> f))"
    by (rule finite_SigmaI)
  thus ?thesis
    by (rule finite_subset[OF range_prod])
qed

lemma fstE:
  "x = (a,b) \<Longrightarrow> P (fst x) \<Longrightarrow> P a"
by (metis fst_conv)

lemma sndE:
  "x = (a,b) \<Longrightarrow> P (snd x) \<Longrightarrow> P b"
by (metis snd_conv)



subsection {* Functions *}
lemma fun_comp_eq_conv: "f o g = fg \<longleftrightarrow> (\<forall>x. f (g x) = fg x)"
  by auto


subsection {* Lists *}

lemma not_hd_in_tl:
  "x \<noteq> hd xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> set (tl xs)"
by (induct xs) simp_all

lemma distinct_hd_tl:
  "distinct xs \<Longrightarrow> x = hd xs \<Longrightarrow> x \<notin> set (tl (xs))"
by (induct xs) simp_all

lemma in_set_tlD: "x \<in> set (tl xs) \<Longrightarrow> x \<in> set xs"
by (induct xs) simp_all

lemma nth_tl: "xs \<noteq> [] \<Longrightarrow> tl xs ! n = xs ! Suc n"
by (induct xs) simp_all

lemma tl_subset:
  "xs \<noteq> [] \<Longrightarrow> set xs \<subseteq> A \<Longrightarrow> set (tl xs) \<subseteq> A"
by (metis in_set_tlD set_rev_mp subsetI)

lemma tl_last:
  "tl xs \<noteq> [] \<Longrightarrow> last xs = last (tl xs)"
by (induct xs) simp_all

lemma tl_obtain_elem:
  assumes "xs \<noteq> []" "tl xs = []"
  obtains e where "xs = [e]"
using assms
by (induct xs rule: list_nonempty_induct) simp_all

lemma butlast_subset:
  "xs \<noteq> [] \<Longrightarrow> set xs \<subseteq> A \<Longrightarrow> set (butlast xs) \<subseteq> A"
by (metis in_set_butlastD set_rev_mp subsetI)

lemma butlast_rev_tl:
  "xs \<noteq> [] \<Longrightarrow> butlast (rev xs) = rev (tl xs)"
by (induct xs rule: rev_induct) simp_all

lemma hd_butlast:
  "length xs > 1 \<Longrightarrow> hd (butlast xs) = hd xs"
by (induct xs) simp_all

lemma list_take_induct_tl2:
  "length xs = length ys \<Longrightarrow> \<forall>n<length xs. P (ys ! n) (xs ! n) \<Longrightarrow> \<forall>n < length (tl xs). P ((tl ys) ! n) ((tl xs) ! n)"
by (induct xs ys rule: list_induct2) auto

lemma not_distinct_split_distinct:
  assumes "\<not> distinct xs"
  obtains y ys zs where "distinct ys" "y \<in> set ys" "xs = ys@[y]@zs"
using assms
proof (induct xs rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x xs) thus ?case by (cases "distinct xs") auto
qed

lemma distinct_length_le:
  assumes d: "distinct ys"
  and eq: "set ys = set xs"
  shows "length ys \<le> length xs"
proof -
  from d have "length ys = card (set ys)" by (simp add: distinct_card)
  also from eq List.card_set have "card (set ys) = length (remdups xs)" by simp
  also have "... \<le> length xs" by simp
  finally show ?thesis .
qed


lemma butlast_upd_last_eq[simp]: "length l \<ge> 2 \<Longrightarrow> 
  butlast l [ length l - 2 := x ] = take (length l - 2) l @ [x]"
  apply (case_tac l rule: rev_cases)
  apply simp
  apply simp
  apply (case_tac ys rule: rev_cases)
  apply simp
  apply simp
  done

(* TODO: Move to Misc, replace lemma there! *)
lemma butlast_upt: "butlast [m..<n] = [m..<n - 1]"
  apply (cases "m<n")
  apply (rule Misc.butlast_upt, assumption)
  apply simp
  done


lemma distinct_sorted_strict_mono_iff:
  assumes "distinct l" "sorted l"
  assumes "i<length l" "j<length l"
  shows "l!i<l!j \<longleftrightarrow> i<j"
  using assms
  by (metis distinct_sorted_mono leI less_le_not_le 
    order.strict_iff_order)

lemma distinct_sorted_mono_iff:
  assumes "distinct l" "sorted l"
  assumes "i<length l" "j<length l"
  shows "l!i\<le>l!j \<longleftrightarrow> i\<le>j"
  by (metis assms distinct_sorted_strict_mono_iff leD le_less_linear)

lemma find_SomeD:
  "List.find P xs = Some x \<Longrightarrow> P x"
  "List.find P xs = Some x \<Longrightarrow> x\<in>set xs"
  by (auto simp add: find_Some_iff)

subsection {* Sets *}
text {*
  Decompose general union over sum types.
*}

lemma Union_plus:
  "(\<Union> x \<in> A <+> B. f x) = (\<Union> a \<in> A. f (Inl a)) \<union> (\<Union>b \<in> B. f (Inr b))"
by auto

lemma Union_sum:
  "(\<Union>x. f (x::'a+'b)) = (\<Union>l. f (Inl l)) \<union> (\<Union>r. f (Inr r))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Union>x \<in> UNIV <+> UNIV. f x)"
    by simp
  thus ?thesis
    by (simp only: Union_plus)
qed

lemma card_Plus:
  assumes fina: "finite (A::'a set)" and finb: "finite (B::'b set)"
  shows "card (A <+> B) = (card A) + (card B)"
proof -
  from fina finb
  have "card ((Inl ` A) \<union> (Inr ` B)) =
        (card ((Inl ` A)::('a+'b)set)) + (card ((Inr ` B)::('a+'b)set))"
    by (auto intro: card_Un_disjoint finite_imageI)
  thus ?thesis
    by (simp add: Plus_def card_image inj_on_def)
qed

text {*
  The standard library proves that a generalized union is finite
  if the index set is finite and if for every index the component
  set is itself finite. Conversely, we show that every component
  set must be finite when the union is finite.
*}

lemma finite_UNION_then_finite:
  assumes hyp: "finite (UNION A B)" and a: "a \<in> A"
  shows "finite (B a)"
proof (rule ccontr)
  assume cc: "\<not>finite (B a)"
  from a have "B a \<subseteq> UNION A B" by auto
  from this cc have "\<not>finite (UNION A B)" by (auto intro: finite_subset)
  from this hyp show "False" ..
qed

lemma finite_if_eq_beyond_finite: "finite S \<Longrightarrow> finite {s. s - S = s' - S}"
proof (rule finite_subset[where B="(\<lambda>s. s \<union> (s' - S)) ` Pow S"], clarsimp)
  fix s
  have "s = (s \<inter> S) \<union> (s - S)"
    by auto
  also assume "s - S = s' - S"
  finally show "s \<in> (\<lambda>s. s \<union> (s' - S)) ` Pow S" by blast
qed blast

lemma distinct_finite_subset:
  assumes "finite x"
  shows "finite {ys. set ys \<subseteq> x \<and> distinct ys}" (is "finite ?S")
proof (rule finite_subset)
  from assms show "?S \<subseteq> {ys. set ys \<subseteq> x \<and> length ys \<le> card x}"
    by clarsimp (metis distinct_card card_mono) 
  from assms show "finite ..." by (rule finite_lists_length_le)
qed
  
lemma distinct_finite_set:
  shows "finite {ys. set ys = x \<and> distinct ys}" (is "finite ?S")
proof (cases "finite x")
  case False hence "{ys. set ys = x} = {}" by auto
  thus ?thesis by simp
next
  case True show ?thesis
  proof (rule finite_subset)
    show "?S \<subseteq> {ys. set ys \<subseteq> x \<and> length ys \<le> card x}"
      using distinct_card by force
    from True show "finite ..." by (rule finite_lists_length_le)
  qed
qed

lemma finite_set_image:
  assumes f: "finite (set ` A)"
  and dist: "\<And>xs. xs \<in> A \<Longrightarrow> distinct xs"
  shows "finite A"
proof (rule finite_subset)
  from f show "finite (set -` (set ` A) \<inter> {xs. distinct xs})"
  proof (induct rule: finite_induct)
    case (insert x F)
    from distinct_finite_set have "finite (set -` {x} \<inter> {xs. distinct xs})" by (force simp add: vimage_def)
    with insert show ?case
      apply (subst vimage_insert) 
      apply (subst Int_Un_distrib2)
      apply (rule finite_UnI) 
        apply simp_all
      done
  qed simp
  moreover from dist show "A \<subseteq> ..."
    by (auto simp add: vimage_image_eq)
qed

lemma finite_Assoc_List_set_image:
  assumes "finite (Assoc_List.set ` A)"
  shows "finite A"
proof -
  have "Assoc_List.set ` A = set ` Assoc_List.impl_of ` A"
    by (auto simp add: Assoc_List.set_def)
  with assms finite_set_image have "finite (Assoc_List.impl_of ` A)" by auto
  with assoc_list_ext show ?thesis by (metis inj_onI finite_imageD)
qed




subsection {* Relations *}
lemma trancl_image_by_rtrancl: "(E\<^sup>+)``Vi \<union> Vi = (E\<^sup>*)``Vi"
  by (metis Image_Id Un_Image rtrancl_trancl_reflcl)

lemma rtrancl_mono_mp: "U\<subseteq>V \<Longrightarrow> x\<in>U\<^sup>* \<Longrightarrow> x\<in>V\<^sup>*" by (metis in_mono rtrancl_mono)
lemma trancl_mono_mp: "U\<subseteq>V \<Longrightarrow> x\<in>U\<^sup>+ \<Longrightarrow> x\<in>V\<^sup>+" by (metis trancl_mono)

lemma rtrancl_mapI: "(a,b)\<in>E\<^sup>* \<Longrightarrow> (f a, f b)\<in>(pairself f `E)\<^sup>*"
  apply (induction rule: rtrancl_induct)
  apply (force intro: rtrancl.intros)+
  done

lemma rtrancl_image_advance_rtrancl:
  assumes "q \<in> R\<^sup>*``Q0"
  assumes "(q,x) \<in> R\<^sup>*"
  shows "x \<in> R\<^sup>*``Q0"
  using assms
  by (metis rtrancl_idemp rtrancl_image_advance)

lemma nth_step_trancl:
  "\<And>n m. \<lbrakk> \<And> n. n < length xs - 1 \<Longrightarrow> (xs ! Suc n, xs ! n) \<in> R \<rbrakk> \<Longrightarrow> n < length xs \<Longrightarrow> m < n \<Longrightarrow> (xs ! n, xs ! m) \<in> R\<^sup>+"
proof (induction xs)
  case (Cons x xs)
  hence "\<And>n. n < length xs - 1 \<Longrightarrow> (xs ! Suc n, xs ! n) \<in> R" 
    apply clarsimp
    by (metis One_nat_def diff_Suc_eq_diff_pred nth_Cons_Suc zero_less_diff) 
  note IH = this[THEN Cons.IH]

  from Cons obtain n' where n': "Suc n' = n" by (cases n) blast+

  show ?case
  proof (cases m)
    case "0" with Cons have "xs \<noteq> []" by auto
    with "0" Cons.prems(1)[of m] have "(xs ! 0, x) \<in> R" by simp
    moreover from IH[where m = 0] have "\<And>n. n < length xs \<Longrightarrow> n > 0 \<Longrightarrow> (xs ! n, xs ! 0) \<in> R\<^sup>+" by simp
    ultimately have "\<And>n. n < length xs \<Longrightarrow> (xs ! n, x) \<in> R\<^sup>+" by (metis trancl_into_trancl gr0I r_into_trancl')
    with Cons "0" show ?thesis by auto
  next
    case (Suc m') with Cons.prems n' have "n' < length xs" "m' < n'" by auto
    with IH have "(xs ! n', xs ! m') \<in> R\<^sup>+" by simp
    with Suc n' show ?thesis by auto
  qed
qed simp

lemma Image_empty_trancl_Image_empty:
  "R `` {v} = {} \<Longrightarrow> R\<^sup>+ `` {v} = {}"
  unfolding Image_def
  by (auto elim: converse_tranclE)

lemma Image_empty_rtrancl_Image_id:
  "R `` {v} = {} \<Longrightarrow> R\<^sup>* `` {v} = {v}"
  unfolding Image_def
  by (auto elim: converse_rtranclE)

lemma trans_rtrancl_eq_reflcl:
  "trans A \<Longrightarrow> A^* = A^="
  by (simp add: rtrancl_trancl_reflcl)

lemma refl_on_reflcl_Image:
  "refl_on B A \<Longrightarrow> C \<subseteq> B \<Longrightarrow> A^= `` C = A `` C"
  by (auto simp add: Image_def dest: refl_onD)

lemma Image_absorb_rtrancl:
  "\<lbrakk> trans A; refl_on B A; C \<subseteq> B \<rbrakk> \<Longrightarrow> A^* `` C = A `` C"
  by (simp add: trans_rtrancl_eq_reflcl refl_on_reflcl_Image)

lemma fst_in_Field: "fst ` R \<subseteq> Field R"
  by (simp add: Field_def fst_eq_Domain)

lemma snd_in_Field: "snd ` R \<subseteq> Field R"
  by (simp add: Field_def snd_eq_Range)

lemma R_subset_Field: "R \<subseteq> Field R \<times> Field R"
  unfolding Field_def
  by auto

lemma ran_map_of:
  "ran (map_of xs) \<subseteq> snd ` set (xs)"
by (induct xs) (auto simp add: ran_def)




lemma Image_subset_snd_image:
  "A `` B \<subseteq> snd ` A"
unfolding Image_def image_def
by force

lemma finite_Image_subset:
  "finite (A `` B) \<Longrightarrow> C \<subseteq> A \<Longrightarrow> finite (C `` B)"
by (metis Image_mono order_refl rev_finite_subset)


definition rel_restrict :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set"
where
  "rel_restrict R A \<equiv> {(v,w). (v,w) \<in> R \<and> v \<notin> A \<and> w \<notin> A}"

lemma rel_restrict_alt_def:
  "rel_restrict R A = R \<inter> (-A) \<times> (-A)"
unfolding rel_restrict_def
by auto

lemma rel_restrict_empty[simp]:
  "rel_restrict R {} = R"
by (simp add: rel_restrict_def)

lemma rel_restrict_notR:
  assumes "(x,y) \<in> rel_restrict A R"
  shows "x \<notin> R" and "y \<notin> R"
using assms
unfolding rel_restrict_def
by auto

lemma rel_restrict_sub:
  "rel_restrict R A \<subseteq> R"
unfolding rel_restrict_def 
by auto

lemma rel_restrict_Int_empty:
  "A \<inter> Field R = {} \<Longrightarrow> rel_restrict R A = R"
unfolding rel_restrict_def Field_def
by auto

lemma Domain_rel_restrict:
  "Domain (rel_restrict R A) \<subseteq> Domain R - A"
unfolding rel_restrict_def
by auto

lemma Range_rel_restrict:
  "Range (rel_restrict R A) \<subseteq> Range R - A"
unfolding rel_restrict_def
by auto

lemma Field_rel_restrict:
  "Field (rel_restrict R A) \<subseteq> Field R - A"
unfolding rel_restrict_def Field_def
by auto

lemma rel_restrict_compl:
  "rel_restrict R A \<inter> rel_restrict R (-A) = {}"
unfolding rel_restrict_def
by auto

lemma finite_rel_restrict:
  "finite R \<Longrightarrow> finite (rel_restrict R A)"
by (metis finite_subset rel_restrict_sub)

lemma homo_rel_restrict_mono:
  "R \<subseteq> B \<times> B \<Longrightarrow> rel_restrict R A \<subseteq> (B - A) \<times> (B - A)"
proof -
  assume A: "R \<subseteq> B \<times> B"
  hence "Field R \<subseteq> B" unfolding Field_def by auto
  with Field_rel_restrict have "Field (rel_restrict R A) \<subseteq> B - A" 
    by (metis Diff_mono order_refl order_trans)
  with R_subset_Field show ?thesis by blast
qed

lemma rel_restrict_union:
  "rel_restrict R (A \<union> B) = rel_restrict (rel_restrict R A) B"
unfolding rel_restrict_def
by auto

lemma rel_restrictI:
  "x \<notin> R \<Longrightarrow> y \<notin> R \<Longrightarrow> (x,y) \<in> E \<Longrightarrow> (x,y) \<in> rel_restrict E R"
unfolding rel_restrict_def
by auto

lemma rel_restrict_lift:
  "(x,y) \<in> rel_restrict E R \<Longrightarrow> (x,y) \<in> E"
unfolding rel_restrict_def
by simp

lemma rel_restrict_trancl_mem:
  "(a,b) \<in> (rel_restrict A R)\<^sup>+ \<Longrightarrow> (a,b) \<in> rel_restrict (A\<^sup>+) R"
by (induction rule: trancl_induct) (auto simp add: rel_restrict_def)

lemma rel_restrict_trancl_sub:
  "(rel_restrict A R)\<^sup>+ \<subseteq> rel_restrict (A\<^sup>+) R"
by (metis subrelI rel_restrict_trancl_mem)

lemma rel_restrict_mono:
  "A \<subseteq> B \<Longrightarrow> rel_restrict A R \<subseteq> rel_restrict B R"
unfolding rel_restrict_def by auto

lemma rel_restrict_mono2:
  "R \<subseteq> S \<Longrightarrow> rel_restrict A S \<subseteq> rel_restrict A R"
unfolding rel_restrict_def by auto

lemma rel_restrict_Sigma_sub:
  "rel_restrict ((A\<times>A)\<^sup>+) R \<subseteq> ((A - R) \<times> (A - R))\<^sup>+" 
unfolding rel_restrict_def
by auto (metis DiffI converse_tranclE mem_Sigma_iff r_into_trancl tranclE)


lemma finite_reachable_restrictedI:
  assumes F: "finite Q"
  assumes I: "I\<subseteq>Q"
  assumes R: "Range E \<subseteq> Q"
  shows "finite (E\<^sup>*``I)"
proof -
  from I R have "E\<^sup>*``I \<subseteq> Q"
    by (force elim: rtrancl.cases)
  also note F
  finally (finite_subset) show ?thesis .
qed



subsection {* Maps *}

lemma ran_is_image:
  "ran M = (the \<circ> M) ` (dom M)"
unfolding ran_def dom_def image_def
by auto

lemma map_card_eq_iff:
  assumes finite: "finite (dom M)"
  and card_eq: "card (dom M) = card (ran M)"
  and indom: "x \<in> dom M"
  shows "(M x = M y) \<longleftrightarrow> (x = y)"
proof -
  from ran_is_image finite card_eq have *: "inj_on (the \<circ> M) (dom M)" using eq_card_imp_inj_on by metis
  thus ?thesis
  proof (cases "y \<in> dom M")
    case False with indom show ?thesis by auto
  next
    case True with indom have "the (M x) = the (M y) \<longleftrightarrow> (x = y)" using inj_on_eq_iff[OF *] by auto
    thus ?thesis by auto
  qed
qed

lemma map_dom_ran_finite:
  "finite (dom M) \<Longrightarrow> finite (ran M)"
by (simp add: ran_is_image)

definition "dflt_None_set S \<equiv> if S={} then None else Some S"
lemma the_dflt_None_set[simp]: "the_default {} (dflt_None_set x) = x"
  unfolding dflt_None_set_def by auto

subsection {* Natural Numbers *}
text {*
  The standard library contains theorem @{text less_iff_Suc_add}

  @{thm less_iff_Suc_add [no_vars]}

  that can be used to reduce ``less than'' to addition and successor.
  The following lemma is the analogous result for ``less or equal''.
*}

lemma le_iff_add:
  "(m::nat) \<le> n = (\<exists> k. n = m+k)"
proof
  assume le: "m \<le> n"
  thus "\<exists> k. n = m+k"
  proof (auto simp add: order_le_less)
    assume "m<n"
    then obtain k where "n = Suc(m+k)"
      by (auto simp add: less_iff_Suc_add)
    thus ?thesis by auto
  qed
next
  assume "\<exists> k. n = m+k"
  thus "m \<le> n" by auto
qed

lemma exists_leI:
  assumes hyp: "(\<forall>n' < n. \<not> P n') \<Longrightarrow> P (n::nat)"
  shows "\<exists>n' \<le> n. P n'"
proof (rule classical)
  assume contra: "\<not> (\<exists>n'\<le>n. P n')"
  hence "\<forall>n' < n. \<not> P n'" by auto
  hence "P n" by (rule hyp)
  thus "\<exists>n'\<le>n. P n'" by auto
qed



subsection {* Mod *}
text {*
  An ``induction'' law for modulus arithmetic: if $P$ holds for some
  $i<p$ and if $P(i)$ implies $P((i+1) \bmod p)$, for all $i<p$, then
  $P(i)$ holds for all $i<p$.
*}

lemma mod_induct_0:
  assumes step: "\<forall>i<p. P i \<longrightarrow> P ((Suc i) mod p)"
  and base: "P i" and i: "i<p"
  shows "P 0"
proof (rule ccontr)
  assume contra: "\<not>(P 0)"
  from i have p: "0<p" by simp
  have "\<forall>k. 0<k \<longrightarrow> \<not> P (p-k)" (is "\<forall>k. ?A k")
  proof
    fix k
    show "?A k"
    proof (induct k)
      show "?A 0" by simp  -- "by contradiction"
    next
      fix n
      assume ih: "?A n"
      show "?A (Suc n)"
      proof (clarsimp)
	assume y: "P (p - Suc n)"
	have n: "Suc n < p"
	proof (rule ccontr)
	  assume "\<not>(Suc n < p)"
	  hence "p - Suc n = 0"
	    by simp
	  with y contra show "False"
	    by simp
	qed
	hence n2: "Suc (p - Suc n) = p-n" by arith
	from p have "p - Suc n < p" by arith
	with y step have z: "P ((Suc (p - Suc n)) mod p)"
	  by blast
	show "False"
	proof (cases "n=0")
	  case True
	  with z n2 contra show ?thesis by simp
	next
	  case False
	  with p have "p-n < p" by arith
	  with z n2 False ih show ?thesis by simp
	qed
      qed
    qed
  qed
  moreover
  from i obtain k where "0<k \<and> i+k=p"
    by (blast dest: less_imp_add_positive)
  hence "0<k \<and> i=p-k" by auto
  moreover
  note base
  ultimately
  show "False" by blast
qed

lemma mod_induct:
  assumes step: "\<forall>i<p. P i \<longrightarrow> P ((Suc i) mod p)"
  and base: "P i" and i: "i<p" and j: "j<p"
  shows "P j"
proof -
  have "\<forall>j<p. P j"
  proof
    fix j
    show "j<p \<longrightarrow> P j" (is "?A j")
    proof (induct j)
      from step base i show "?A 0"
	by (auto elim: mod_induct_0)
    next
      fix k
      assume ih: "?A k"
      show "?A (Suc k)"
      proof
	assume suc: "Suc k < p"
	hence k: "k<p" by simp
	with ih have "P k" ..
	with step k have "P (Suc k mod p)"
	  by blast
	moreover
	from suc have "Suc k mod p = Suc k"
	  by simp
	ultimately
	show "P (Suc k)" by simp
      qed
    qed
  qed
  with j show ?thesis by blast
qed

lemma mod_le:
  "(a::'a::semiring_numeral_div) \<le> b \<Longrightarrow> 0 < a \<Longrightarrow> x mod (a + 1) \<le> b"
  by (metis add_pos_nonneg discrete not_less order.strict_trans2 
    semiring_numeral_div_class.pos_mod_bound zero_le_one)

lemma mod_ge:
  "(b::'a::semiring_numeral_div) \<le> 0 \<Longrightarrow> 0 < a \<Longrightarrow> b \<le> x mod (a+1)"
  by (metis dual_order.trans less_add_one order.strict_trans 
    semiring_numeral_div_class.pos_mod_sign)

subsection {* Integer *}
text {* Some setup from @{text "int"} transferred to @{text "integer"} *}

lemma atLeastLessThanPlusOne_atLeastAtMost_integer: "{l..<u+1} = {l..(u::integer)}"
  apply (auto simp add: atLeastAtMost_def atLeastLessThan_def)
  apply transfer
  apply simp
  done

lemma atLeastPlusOneAtMost_greaterThanAtMost_integer: "{l+1..u} = {l<..(u::integer)}"
  by (auto simp add: atLeastAtMost_def greaterThanAtMost_def, transfer, simp)

lemma atLeastPlusOneLessThan_greaterThanLessThan_integer:
    "{l+1..<u} = {l<..<u::integer}"
  by (auto simp add: atLeastLessThan_def greaterThanLessThan_def, transfer, simp)

lemma image_atLeastZeroLessThan_integer: "0 \<le> u \<Longrightarrow>
    {(0::integer)..<u} = of_nat ` {..<nat_of_integer u}"
  apply (unfold image_def lessThan_def)
  apply auto
  apply (rule_tac x = "nat_of_integer x" in exI)
  apply transfer
  apply (auto simp add: zless_nat_eq_int_zless [THEN sym])
  apply transfer
  apply simp
  done

lemma image_add_integer_atLeastLessThan:
    "(%x. x + (l::integer)) ` {0..<u-l} = {l..<u}"
  apply (auto simp add: image_def)
  apply (rule_tac x = "x - l" in bexI)
  apply auto
  done

lemma finite_atLeastZeroLessThan_integer: "finite {(0::integer)..<u}"
  apply (cases "0 \<le> u")
  apply (subst image_atLeastZeroLessThan_integer, assumption)
  apply (rule finite_imageI)
  apply auto
  done

lemma finite_atLeastLessThan_integer [iff]: "finite {l..<u::integer}"
  apply (subgoal_tac "(%x. x + l) ` {0..<u-l} = {l..<u}")
  apply (erule subst)
  apply (rule finite_imageI)
  apply (rule finite_atLeastZeroLessThan_integer)
  apply (rule image_add_integer_atLeastLessThan)
  done

lemma finite_atLeastAtMost_integer [iff]: "finite {l..(u::integer)}"
  by (subst atLeastLessThanPlusOne_atLeastAtMost_integer [THEN sym], simp)

lemma finite_greaterThanAtMost_integer [iff]: "finite {l<..(u::integer)}"
  by (subst atLeastPlusOneAtMost_greaterThanAtMost_integer [THEN sym], simp)

lemma finite_greaterThanLessThan_integer [iff]: "finite {l<..<u::integer}"
  by (subst atLeastPlusOneLessThan_greaterThanLessThan_integer [THEN sym], simp)


subsection {* Infinite Set *}
lemma INFM_nat_inductI: 
  assumes P0: "P (0::nat)"
  assumes PS: "\<And>i. P i \<Longrightarrow> \<exists>j>i. P j \<and> Q j"
  shows "\<exists>\<^sub>\<infinity>i. Q i"
proof -
  have "\<forall>i. \<exists>j>i. P j \<and> Q j" proof
    fix i
    show "\<exists>j>i. P j \<and> Q j"
      apply (induction i)
      using PS[OF P0] apply auto []
      by (metis PS Suc_lessI)
  qed
  thus ?thesis unfolding INFM_nat by blast
qed

subsection {* Multisets *}
definition multiset_of_set :: "'a set \<Rightarrow> 'a multiset" where
  "multiset_of_set S = Abs_multiset (\<lambda>x. if x \<in> S then 1 else 0)"

lemma count_multiset_of_set [simp]:
"finite S \<Longrightarrow> count (multiset_of_set S) a = (if a \<in> S then 1 else 0)"
proof -
  assume "finite S"
  hence "(\<lambda>x. if x \<in> S then 1 else 0) \<in> multiset"
    by (simp add: multiset_def)
  thus ?thesis 
    by (simp add: multiset_of_set_def Abs_multiset_inverse)
qed

lemma in_multiset_of_set :
"finite S \<Longrightarrow> x \<in># (multiset_of_set S) \<longleftrightarrow> x \<in> S"
by simp

lemma multiset_of_set_inv [simp] :
  "finite S \<Longrightarrow> set_of (multiset_of_set S) = S"
by (simp add: set_of_def)

lemma multiset_of_empty [simp]: "multiset_of_set {} = {#}"
  by (simp add: multiset_of_set_def zero_multiset_def)

lemma multiset_of_insert: "finite S \<Longrightarrow>
  multiset_of_set (insert e S) =
  multiset_of_set (S - {e}) + {#e#}"
by (simp add: multiset_eq_iff)

lemma multiset_of_single [simp]: "multiset_of_set {b} = {#b#}"
by (simp add: multiset_of_set_def single_def)

lemma multiset_of_set_set :
  "distinct l \<Longrightarrow>
   multiset_of_set (set l) = multiset_of l"
proof (induct l)
  case Nil thus ?case by simp
next
  case (Cons e l)
  from Cons(2) have e_nin_l : "e \<notin> set l" by simp
  from Cons(2) have dist_l: "distinct l" by simp
  note ind_hyp = Cons(1)[OF dist_l]

  from e_nin_l have "set l - {e} = set l" by auto
  with ind_hyp show ?case
    by (simp add: multiset_of_insert)
qed

lemma ex_Melem_conv: "(\<exists>x. x \<in># A) = (A \<noteq> {#})"
by (metis all_not_in_conv mem_set_of_iff set_of_eq_empty_iff)


(* Refine_Monadic: Added vc_solve method *)
text {*
  We establich a tactic called @{text "vc_solve"}, which is specialized to
  solve verification conditions. It first clarsimps all goals, then
  it tries to apply a set of safe introduction rules (vcs_rec, rec add).
  Finally, it applies introduction rules (vcs_solve, solve add) and tries
  to discharge all emerging subgoals by auto. If this does not succeed, it
  backtracks over the application of the solve-rule.
*}
ML {*
  structure vc_solver = struct
    structure rec_thms = Named_Thms ( 
      val name = @{binding vcs_rec}
      val description = "VC-Solver: Recursive intro rules"
    )

    structure solve_thms = Named_Thms ( 
      val name = @{binding vcs_solve}
      val description = "VC-Solver: Solve rules"
    )

    val rec_modifiers = [
      Args.$$$ "rec" -- Scan.option Args.add -- Args.colon 
        >> K ((I,rec_thms.add):Method.modifier),
      Args.$$$ "rec" -- Scan.option Args.del -- Args.colon 
        >> K ((I,rec_thms.del):Method.modifier)
    ];

    val solve_modifiers = [
      Args.$$$ "solve" -- Scan.option Args.add -- Args.colon 
        >> K ((I,solve_thms.add):Method.modifier),
      Args.$$$ "solve" -- Scan.option Args.del -- Args.colon 
        >> K ((I,solve_thms.del):Method.modifier)
    ];

    val vc_solve_modifiers = 
      clasimp_modifiers @ rec_modifiers @ solve_modifiers;

    fun vc_solve_tac ctxt no_pre = let
      val rthms = rec_thms.get ctxt
      val sthms = solve_thms.get ctxt
      val pre_tac = if no_pre then K all_tac else clarsimp_tac ctxt
      val tac = SELECT_GOAL (auto_tac ctxt)
    in
      TRY o pre_tac
      THEN_ALL_NEW_FWD (TRY o REPEAT_ALL_NEW_FWD (resolve_tac rthms))
      THEN_ALL_NEW_FWD (TRY o SOLVED' (resolve_tac sthms THEN_ALL_NEW_FWD tac))
    end

    val setup = I
      #> rec_thms.setup 
      #> solve_thms.setup

  end
*}
setup vc_solver.setup

method_setup vc_solve = 
  {* Scan.lift (Args.mode "nopre") 
      --| Method.sections vc_solver.vc_solve_modifiers >>
  (fn (nopre) => fn ctxt => SIMPLE_METHOD (
    CHANGED (ALLGOALS (vc_solver.vc_solve_tac ctxt nopre))
  )) *} "Try to solve verification conditions"


(* Refine_Monadic: Tweaking of rcg/vcg setup *)
(* TODO: Move, if that works *)
lemmas [refine0] = ASSUME_refine_right
lemmas [refine0] = ASSERT_refine_left
lemmas [refine0] = ASSUME_refine_left
lemmas [refine0] = ASSERT_refine_right

(* TODO: Move *)
lemma bind_Let_refine2[refine2]: "\<lbrakk> 
    m' \<le>\<Down>R' (RETURN x);
    \<And>x'. \<lbrakk>inres m' x'; (x',x)\<in>R'\<rbrakk> \<Longrightarrow> f' x' \<le> \<Down>R (f x) 
  \<rbrakk> \<Longrightarrow> m'\<guillemotright>=(\<lambda>x'. f' x') \<le> \<Down>R (Let x (\<lambda>x. f x))"
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

lemma if_RETURN_refine [refine2]:
  assumes "b \<longleftrightarrow> b'"
  assumes "\<lbrakk>b;b'\<rbrakk> \<Longrightarrow> RETURN S1 \<le> \<Down>R S1'"
  assumes "\<lbrakk>\<not>b;\<not>b'\<rbrakk> \<Longrightarrow> RETURN S2 \<le> \<Down>R S2'"
  shows "RETURN (if b then S1 else S2) \<le> \<Down>R (if b' then S1' else S2')"
  (* this is nice to have for small functions, hence keep it in refine2 *)
  using assms
  by (simp add: pw_le_iff refine_pw_simps)

lemmas [refine_hsimp] = prod_rel_id_simp option_rel_id_simp

lemma RETURN_to_SPEC_rule[refine_vcg]: "m\<le>SPEC (op = v) \<Longrightarrow> m\<le>RETURN v"
  by (simp add: ireturn_eq)

(* Automatic_Refinement: Additional setup for HOL *)
(* TODO: Move to param/autoref setup for HOL *)
term List.all_interval_nat
lemma [param, autoref_rules]: "(List.all_interval_nat, List.all_interval_nat) 
  \<in> (nat_rel \<rightarrow> bool_rel) \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
  unfolding List.all_interval_nat_def[abs_def]
  apply parametricity
  apply simp
  done

context begin interpretation autoref_syn .
lemma [autoref_op_pat]: 
  "(\<forall>i<u. P i) \<equiv> OP List.all_interval_nat P 0 u"
  "(\<forall>i\<le>u. P i) \<equiv> OP List.all_interval_nat P 0 (Suc u)"
  "(\<forall>i<u. l\<le>i \<longrightarrow> P i) \<equiv> OP List.all_interval_nat P l u"
  "(\<forall>i\<le>u. l\<le>i \<longrightarrow> P i) \<equiv> OP List.all_interval_nat P l (Suc u)"
  by (auto intro!: eq_reflection simp: List.all_interval_nat_def)
end

(* TODO: Move *)
lemma unit_param[param]: "((),())\<in>unit_rel" by auto


(* Refine_Monadic: Added convenience lemmas *)
lemma if_bind_cond_refine: 
  assumes "ci \<le> RETURN b"
  assumes "b \<Longrightarrow> ti\<le>\<Down>R t"
  assumes "\<not>b \<Longrightarrow> ei\<le>\<Down>R e"
  shows "do {b\<leftarrow>ci; if b then ti else ei} \<le> \<Down>R (if b then t else e)"
  using assms
  by (auto simp add: refine_pw_simps pw_le_iff)

lemma intro_RETURN_Let_refine:
  assumes "RETURN (f x) \<le> \<Down>R M'"
  shows "RETURN (Let x f) \<le> \<Down>R M'" 
  (* this should be needed very rarely - so don't add it *)
  using assms by auto

(* TODO: Move Refine_Basic/Convenience*)
lemma pull_out_RETURN_option_case: 
  "option_case (RETURN a) (\<lambda>v. RETURN (f v)) x = RETURN (option_case a f x)"
  by (auto split: option.splits)

lemma inres_if:
  "\<lbrakk> inres (if P then Q else R) x; \<lbrakk>P; inres Q x\<rbrakk> \<Longrightarrow> S; \<lbrakk>\<not> P; inres R x\<rbrakk> \<Longrightarrow> S \<rbrakk> \<Longrightarrow> S"
by (metis (full_types))

lemma inres_SPEC:
  "inres M x \<Longrightarrow> M \<le> SPEC \<Phi> \<Longrightarrow> \<Phi> x"
by (auto dest: pwD2)

lemma SPEC_nofail:
  "X \<le> SPEC \<Phi> \<Longrightarrow> nofail X"
by (auto dest: pwD1)

lemma SPEC_iff:
  assumes "P \<le> SPEC (\<lambda>s. Q s \<longrightarrow> R s)"
  and "P \<le> SPEC (\<lambda>s. \<not> Q s \<longrightarrow> \<not> R s)"
  shows "P \<le> SPEC (\<lambda>s. Q s \<longleftrightarrow> R s)"
  using assms[THEN pw_le_iff[THEN iffD1]]
  by (auto intro!: pw_leI)

lemma SPEC_rule_conjI:
  assumes "A \<le> SPEC P" and "A \<le> SPEC Q"
    shows "A \<le> SPEC (\<lambda>v. P v \<and> Q v)"
proof -
  have "A \<le> inf (SPEC P) (SPEC Q)" using assms by (rule_tac inf_greatest) assumption
  thus ?thesis by (auto simp add:Collect_conj_eq)
qed

lemma SPEC_rule_conjunct1:
  assumes "A \<le> SPEC (\<lambda>v. P v \<and> Q v)"
    shows "A \<le> SPEC P"
proof -
  note assms
  also have "\<dots> \<le> SPEC P" by (rule SPEC_rule) auto
  finally show ?thesis .
qed

lemma SPEC_rule_conjunct2:
  assumes "A \<le> SPEC (\<lambda>v. P v \<and> Q v)"
    shows "A \<le> SPEC Q"
proof -
  note assms
  also have "\<dots> \<le> SPEC Q" by (rule SPEC_rule) auto
  finally show ?thesis .
qed

(* This rule establishes equality between RECT and REC, using an additional 
    invariant. Note that the default way is to prove termination in
    first place, instead of re-proving parts of the invariant just for the
    termination proof. *)
lemma RECT_eq_REC':
  assumes WF: "wf V'"
  assumes I0: "I x"
  assumes IS: "\<And>f x. I x \<Longrightarrow> (\<And>x. f x \<le> RECT body x) \<Longrightarrow>
    body (\<lambda>x'. if (I x' \<and> (x',x)\<in>V') then f x' else top) x \<le> body f x"
  shows "RECT body x = REC body x"
proof (cases "mono body")
  assume "\<not>mono body"
  thus ?thesis unfolding REC_def RECT_def by simp
next
  assume MONO: "mono body"

  have lfp_ubound: "\<And>x. lfp body x \<le> RECT body x"
  proof -
    fix x
    from REC_le_RECT[of body x, unfolded REC_def] MONO
    show "lfp body x \<le> RECT body x" by auto
  qed

  from lfp_le_gfp' MONO have "lfp body x \<le> gfp body x" .
  moreover have "I x \<longrightarrow> gfp body x \<le> lfp body x"
    using WF
    apply (induct rule: wf_induct[consumes 1])
    apply (rule impI)
    apply (subst lfp_unfold[OF MONO])
    apply (subst gfp_unfold[OF MONO])
    apply (rule order_trans[OF _ IS])
    apply (rule monoD[OF MONO,THEN le_funD])
    apply (rule le_funI)
    apply simp
    apply simp
    apply (rule lfp_ubound)
    done
  ultimately show ?thesis
    unfolding REC_def RECT_def
    apply (rule_tac antisym)
    using I0 MONO by auto
qed

(* Refine_Monadic: Rules for nfoldli *)
(* TODO: Move *)
lemma nfoldli_rule:
  assumes I0: "I [] l0 \<sigma>0"
  assumes IS: "\<And>x l1 l2 \<sigma>. \<lbrakk> l0=l1@x#l2; I l1 (x#l2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (l1@[x]) l2)"
  assumes FNC: "\<And>l1 l2 \<sigma>. \<lbrakk> l0=l1@l2; I l1 l2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I l0 [] \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "nfoldli l0 c f \<sigma>0 \<le> SPEC P"
  apply (rule order_trans[OF nfoldli_while[
    where I="\<lambda>(l2,\<sigma>). \<exists>l1. l0=l1@l2 \<and> I l1 l2 \<sigma>"]])
  unfolding FOREACH_cond_def FOREACH_body_def
  apply (refine_rcg WHILEIT_rule[where R="measure (length o fst)"] refine_vcg)
  apply simp
  using I0 apply simp

  apply (case_tac a, simp)
  apply simp
  apply (elim exE conjE)
  apply (rule order_trans[OF IS], assumption+)
  apply auto []

  apply simp
  apply (elim exE disjE2)
  using FC apply auto []
  using FNC apply auto []
  done

(* TODO: Move *)
lemma autoref_nfoldli[autoref_rules]:
  assumes "PREFER single_valued Rb"
  shows "(nfoldli, nfoldli)
  \<in> \<langle>Ra\<rangle>list_rel \<rightarrow> (Rb \<rightarrow> bool_rel) \<rightarrow> (Ra \<rightarrow> Rb \<rightarrow> \<langle>Rb\<rangle>nres_rel) \<rightarrow> Rb \<rightarrow> \<langle>Rb\<rangle>nres_rel"
  using assms param_nfoldli by simp

(* Refine_Monadic: Improved autoref-setup for foreach-loops *)
(* TODO: Move, modify pat-lemmas for foreach *)
lemma [autoref_op_pat]:
  "FOREACH\<^bsup>I\<^esup> \<equiv> \<lambda>s f \<sigma>. FOREACH\<^sub>O\<^sub>C\<^bsup>\<lambda>_ _. True,I\<^esup> s (\<lambda>_. True) f \<sigma>"
  "FOREACHci I \<equiv> FOREACHoci (\<lambda>_ _. True) I"
  "FOREACH\<^sub>O\<^sub>C\<^bsup>R,\<Phi>\<^esup> \<equiv> \<lambda>s c f \<sigma>. do {
    ASSERT (finite s);
    Autoref_Tagging.OP (LIST_FOREACH \<Phi>) (it_to_sorted_list R s) c f \<sigma>
  }"
  apply (intro eq_reflection ext)
  apply (subst FOREACH_patterns, force)
  apply (intro eq_reflection ext)
  apply (subst FOREACH_patterns, force)
  apply (intro eq_reflection ext)
  apply (subst FOREACH_patterns, force)
  done
(* TODO: There are different op_pats for FOREACH, with various amount of eta-expansion. Fix that! *)
lemma [autoref_op_pat]: "FOREACH \<equiv> \<lambda>s. FOREACHoci (\<lambda>_ _. True) (\<lambda>_ _. True) s (\<lambda>_. True)"
  by (simp add: FOREACH_def[abs_def] FOREACHc_def[abs_def] FOREACHci_def[abs_def])


(* Automatic_Refinement/Collections: Corrected itype-setup for bool/sets *)
(* TODO: Correct setup in Intf_Set, and remove the following patch *)

local_setup {*
  @{thms autoref_itype}
  |> filter (fn thm => case concl_of thm |> HOLogic.dest_Trueprop of 
        @{mpat "op = ::\<^sub>i \<langle>_\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i _"} => true 
      | @{mpat "op - ::\<^sub>i \<langle>_\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i _"} => true 
      | @{mpat "mpaq_STRUCT (mpaq_Var _ _) ::\<^sub>i i_bool"} => true 
      | _ => false
    )
  |> (fn thms => snd o Local_Theory.note ((@{binding rmp_del_itypes},[]), thms))
  *}

declare rmp_del_itypes[autoref_itype del]

ML_val {*
  tag_list 1 @{thms autoref_itype}
  |> filter (fn (_,thm) => case concl_of thm |> HOLogic.dest_Trueprop of 
      @{mpat "op - ::\<^sub>i _"} => true | _ => false
  )
  *}

lemma [autoref_itype]:
  "(op - :: 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set) ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "(op = :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool) ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  by auto

lemma [autoref_itype]:
  "True ::\<^sub>i i_bool"
  "False ::\<^sub>i i_bool"
  by auto

(* Collections: Added set-to-list patterns *)
(* TODO: Move: Set-Spec *)
(*lemma [autoref_op_pat]: "SPEC (\<lambda>l. distinct l \<and> set l = s) 
  \<equiv> it_to_sorted_list (\<lambda>_ _. True) s"
  unfolding it_to_sorted_list_def
  apply (rule eq_reflection)
  by auto*)

(* TODO: Move to GenCF *)

definition [simp]: "op_set_to_sorted_list ordR s 
  \<equiv> SPEC (\<lambda>l. set l = s \<and> distinct l \<and> sorted_by_rel ordR l)"

definition [simp]: "op_set_to_list s \<equiv> SPEC (\<lambda>l. set l = s \<and> distinct l)"


context begin interpretation autoref_syn .
  lemma [autoref_op_pat]:
    "SPEC (\<lambda>l. set l = s \<and> distinct l \<and> sorted_by_rel ordR l) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. set l = s \<and> sorted_by_rel ordR l \<and> distinct l) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. distinct l \<and> set l = s \<and> sorted_by_rel ordR l) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. distinct l \<and> sorted_by_rel ordR l \<and> set l = s) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. sorted_by_rel ordR l \<and> distinct l \<and> set l = s) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. sorted_by_rel ordR l \<and> set l = s \<and> distinct l) \<equiv> OP (op_set_to_sorted_list ordR)$s"

    "SPEC (\<lambda>l. s = set l \<and> distinct l \<and> sorted_by_rel ordR l) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. s = set l \<and> sorted_by_rel ordR l \<and> distinct l) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. distinct l \<and> s = set l \<and> sorted_by_rel ordR l) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. distinct l \<and> sorted_by_rel ordR l \<and> s = set l) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. sorted_by_rel ordR l \<and> distinct l \<and> s = set l) \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. sorted_by_rel ordR l \<and> s = set l \<and> distinct l) \<equiv> OP (op_set_to_sorted_list ordR)$s"

    "SPEC (\<lambda>l. set l = s \<and> distinct l) \<equiv> op_set_to_list$s"
    "SPEC (\<lambda>l. distinct l \<and> set l = s) \<equiv> op_set_to_list$s"

    "SPEC (\<lambda>l. s = set l \<and> distinct l) \<equiv> op_set_to_list$s"
    "SPEC (\<lambda>l. distinct l \<and> s = set l) \<equiv> op_set_to_list$s"
    by (auto intro!: eq_reflection)

  lemma op_set_to_sorted_list_autoref[autoref_rules]:
    assumes "PREFER single_valued Rk"
    assumes "SIDE_GEN_ALGO (is_set_to_sorted_list ordR Rk Rs tsl)"
    shows "(\<lambda>si. RETURN (tsl si),  OP (op_set_to_sorted_list ordR)) \<in> \<langle>Rk\<rangle>Rs \<rightarrow> \<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel"
    using assms
    apply (intro fun_relI nres_relI)
    apply simp
    apply (rule RETURN_SPEC_refine_sv)
    apply tagged_solver
    apply (auto simp: is_set_to_sorted_list_def it_to_sorted_list_def)
    done

  lemma op_set_to_list_autoref[autoref_rules]:
    assumes "PREFER single_valued Rk"
    assumes "SIDE_GEN_ALGO (is_set_to_sorted_list ordR Rk Rs tsl)"
    shows "(\<lambda>si. RETURN (tsl si), op_set_to_list) \<in> \<langle>Rk\<rangle>Rs \<rightarrow> \<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel"
    using assms
    apply (intro fun_relI nres_relI)
    apply simp
    apply (rule RETURN_SPEC_refine_sv)
    apply tagged_solver
    apply (auto simp: is_set_to_sorted_list_def it_to_sorted_list_def)
    done

end


(* Collections: Added select-function that selects element from set *)
(* TODO: Move *)
(* TODO: Is select properly integrated into autoref? *)
definition select where
  "select S \<equiv> if S={} then RETURN None else RES {Some s | s. s\<in>S}"

(* Collections: Added optimized impl for inj_image on list_set *)
(* TODO: Move: list-set-impl *)
context begin interpretation autoref_syn .
lemma list_set_autoref_inj_image[autoref_rules]:
  assumes "PRIO_TAG_OPTIMIZATION"
  assumes INJ: "SIDE_PRECOND_OPT (inj_on f s)"
  assumes [param]: "(fi,f)\<in>Ra\<rightarrow>Rb"
  assumes LP: "(l,s)\<in>\<langle>Ra\<rangle>list_set_rel"
  shows "(map fi l, (OP op ` ::: (Ra\<rightarrow>Rb) \<rightarrow> \<langle>Ra\<rangle>list_set_rel \<rightarrow> \<langle>Rb\<rangle>list_set_rel)$f$s) 
    \<in> \<langle>Rb\<rangle>list_set_rel"
proof -
  from LP obtain l' where [param]: "(l,l')\<in>\<langle>Ra\<rangle>list_rel" and L'S: "(l',s)\<in>br set distinct"
    unfolding list_set_rel_def by auto
    
  have "(map fi l, map f l')\<in>\<langle>Rb\<rangle>list_rel" by parametricity
  also from INJ L'S have "(map f l',f`s)\<in>br set distinct"
    apply (induction l' arbitrary: s)
    apply (auto simp: br_def dest: injD)
    done
  finally (relcompI) show ?thesis 
    unfolding autoref_tag_defs list_set_rel_def .
qed
  
end

(* Collections/Impl_Fun_Set: Extended relator_props setup for fun_set_rel *)
(* TODO: Move to FunSet-Impl *)
lemma fun_set_rel_RUNIV[relator_props]:
  assumes SV: "single_valued R" 
  shows "Range (\<langle>R\<rangle>fun_set_rel) = UNIV"
proof -
  {
    fix b
    have "\<exists>a. (a,b)\<in>\<langle>R\<rangle>fun_set_rel" unfolding fun_set_rel_def
      apply (rule exI)
      apply (rule relcompI)
    proof -
      show "((\<lambda>x. x\<in>b),b)\<in>br Collect (\<lambda>_. True)" by (auto simp: br_def)
      show "(\<lambda>x'. \<exists>x. (x',x)\<in>R \<and> x\<in>b,\<lambda>x. x \<in> b)\<in>R \<rightarrow> bool_rel"
        by (auto dest: single_valuedD[OF SV])
    qed
  } thus ?thesis by blast
qed

(* Automatic_Refinement: Added theorems to generate tagged lemmas *)
lemma PREFER_I: "P x \<Longrightarrow> PREFER P x" by simp
lemma PREFER_D: "PREFER P x \<Longrightarrow> P x" by simp

lemmas PREFER_sv_D = PREFER_D[of single_valued]
lemma PREFER_id_D: "PREFER_id R \<Longrightarrow> R=Id" by simp

abbreviation "PREFER_RUNIV \<equiv> PREFER (\<lambda>R. Range R = UNIV)"
lemmas PREFER_RUNIV_D = PREFER_D[of "(\<lambda>R. Range R = UNIV)"]

lemma SIDE_GEN_ALGO_D: "SIDE_GEN_ALGO P \<Longrightarrow> P" by simp

lemma GEN_OP_D: "GEN_OP c a R \<Longrightarrow> (c,a)\<in>R"
  by simp

lemma MINOR_PRIO_TAG_I: "P \<Longrightarrow> (MINOR_PRIO_TAG p \<Longrightarrow> P)" by auto
lemma MAJOR_PRIO_TAG_I: "P \<Longrightarrow> (MAJOR_PRIO_TAG p \<Longrightarrow> P)" by auto
lemma PRIO_TAG_I: "P \<Longrightarrow> (PRIO_TAG ma mi \<Longrightarrow> P)" by auto

(* Automatic_Refinement: Added parametricity and autoref setup for sum-type *)
(* TODO: Move: Parametricity/Autoref HOL setup *)
primrec is_Inl where "is_Inl (Inl _) = True" | "is_Inl (Inr _) = False"
primrec is_Inr where "is_Inr (Inr _) = True" | "is_Inr (Inl _) = False"

lemma is_Inl_param[param, autoref_rules]: "(is_Inl,is_Inl) \<in> \<langle>Ra,Rb\<rangle>sum_rel \<rightarrow> bool_rel"
  unfolding is_Inl_def by parametricity
lemma is_Inr_param[param, autoref_rules]: "(is_Inr,is_Inr) \<in> \<langle>Ra,Rb\<rangle>sum_rel \<rightarrow> bool_rel"
  unfolding is_Inr_def by parametricity

lemma sum_Projl_param[param]: 
  "\<lbrakk>is_Inl s; (s',s)\<in>\<langle>Ra,Rb\<rangle>sum_rel\<rbrakk> \<Longrightarrow> (Sum_Type.Projl s',Sum_Type.Projl s) \<in> Ra"
  apply (cases s)
  apply (auto elim: sum_relE)
  done

lemma sum_Projr_param[param]: 
  "\<lbrakk>is_Inr s; (s',s)\<in>\<langle>Ra,Rb\<rangle>sum_rel\<rbrakk> \<Longrightarrow> (Sum_Type.Projr s',Sum_Type.Projr s) \<in> Rb"
  apply (cases s)
  apply (auto elim: sum_relE)
  done

context begin interpretation autoref_syn .
lemma autoref_sum_Projl[autoref_rules]: "\<lbrakk>SIDE_PRECOND (is_Inl s); (s',s)\<in>\<langle>Ra,Rb\<rangle>sum_rel\<rbrakk> \<Longrightarrow>
  (Sum_Type.Projl s', (OP Sum_Type.Projl ::: \<langle>Ra,Rb\<rangle>sum_rel \<rightarrow> Ra)$s)\<in>Ra"
  by simp parametricity

lemma autoref_sum_Projr[autoref_rules]: "\<lbrakk>SIDE_PRECOND (is_Inr s); (s',s)\<in>\<langle>Ra,Rb\<rangle>sum_rel\<rbrakk> \<Longrightarrow>
  (Sum_Type.Projr s', (OP Sum_Type.Projr ::: \<langle>Ra,Rb\<rangle>sum_rel \<rightarrow> Rb)$s)\<in>Rb"
  by simp parametricity

end

(* Collections: Added op_set_cart for cartesian product. Have
    generic implementation and optimized one for lists *)
(* TODO: Move to GenCF, {Intf,Impl,Gen}_Set *)
definition [simp]: "op_set_cart x y \<equiv> x \<times> y"

lemma cart_pat[autoref_op_pat]: "x \<times> y \<equiv> op_set_cart x y" by auto

context begin interpretation autoref_syn .
  lemma [autoref_itype]: "op_set_cart ::\<^sub>i \<langle>Ix\<rangle>\<^sub>iIsx \<rightarrow>\<^sub>i \<langle>Iy\<rangle>\<^sub>iIsy \<rightarrow>\<^sub>i \<langle>\<langle>Ix, Iy\<rangle>\<^sub>ii_prod\<rangle>\<^sub>iIsp"
    by simp
end

lemma list_set_cart_autoref[autoref_rules]:
  fixes Rx :: "('xi \<times> 'x) set"
  fixes Ry :: "('yi \<times> 'y) set"
  shows "(\<lambda>xl yl. [ (x,y). x\<leftarrow>xl, y\<leftarrow>yl], op_set_cart) 
  \<in> \<langle>Rx\<rangle>list_set_rel \<rightarrow> \<langle>Ry\<rangle>list_set_rel \<rightarrow> \<langle>Rx \<times>\<^sub>r Ry\<rangle>list_set_rel"
proof (intro fun_relI)
  fix xl xs yl ys
  assume "(xl, xs) \<in> \<langle>Rx\<rangle>list_set_rel" "(yl, ys) \<in> \<langle>Ry\<rangle>list_set_rel"
  then obtain xl' :: "'x list" and yl' :: "'y list" where 
    [param]: "(xl,xl')\<in>\<langle>Rx\<rangle>list_rel" "(yl,yl')\<in>\<langle>Ry\<rangle>list_rel"
    and XLS: "(xl',xs)\<in>br set distinct" and YLS: "(yl',ys)\<in>br set distinct"
    unfolding list_set_rel_def 
    by auto

  have "([ (x,y). x\<leftarrow>xl, y\<leftarrow>yl ], [ (x,y). x\<leftarrow>xl', y\<leftarrow>yl' ]) \<in> \<langle>Rx \<times>\<^sub>r Ry\<rangle>list_rel"
    by parametricity
  also have "([ (x,y). x\<leftarrow>xl', y\<leftarrow>yl' ], xs \<times> ys) \<in> br set distinct"
    using XLS YLS
    apply (auto simp: br_def)
    apply (induction xl')
    apply simp
    apply (induction yl')
    apply simp
    apply auto []
    apply (metis (lifting) concat_map_maps distinct.simps(2) distinct_singleton maps_simps(2))
    done
  finally (relcompI) 
  show "([ (x,y). x\<leftarrow>xl, y\<leftarrow>yl ], op_set_cart xs ys) \<in> \<langle>Rx \<times>\<^sub>r Ry\<rangle>list_set_rel"
    unfolding list_set_rel_def by simp
qed



lemma gen_cart:
  assumes PRIO_TAG_GEN_ALGO
  assumes [param]: "(sigma, Sigma) \<in> (\<langle>Rx\<rangle>Rsx \<rightarrow> (Rx \<rightarrow> \<langle>Ry\<rangle>Rsy) \<rightarrow> \<langle>Rx \<times>\<^sub>r Ry\<rangle>Rsp)"
  shows "(\<lambda>x y. sigma x (\<lambda>_. y), op_set_cart) \<in> \<langle>Rx\<rangle>Rsx \<rightarrow> \<langle>Ry\<rangle>Rsy \<rightarrow> \<langle>Rx \<times>\<^sub>r Ry\<rangle>Rsp"
  unfolding op_set_cart_def[abs_def]
  by parametricity
lemmas [autoref_rules] = gen_cart[OF _ GEN_OP_D]

(* Collections: Added Union-operation *)
(* TODO: Move to Set{intf,gen}*)
(* Union-operation *)
context begin interpretation autoref_syn .
  lemma [autoref_itype]: "Union ::\<^sub>i \<langle>\<langle>I\<rangle>\<^sub>ii_set\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set" by simp_all
end

lemma hom_set_Union[autoref_hom]:
  "CONSTRAINT Union (\<langle>\<langle>R\<rangle>Ri\<rangle>Ro \<rightarrow> \<langle>R\<rangle>Ri)"
  by simp_all

lemma foldli_Union: "det_fold_set X (\<lambda>_. True) (op \<union>) {} Union"
proof
  case (goal1 l)
  have "\<forall>a. foldli l (\<lambda>_. True) op \<union> a = a \<union> \<Union>set l"
    by (induct l) auto
  thus ?case by auto
qed

definition gen_Union
  :: "_ \<Rightarrow> 's3 \<Rightarrow> ('s2 \<Rightarrow> 's3 \<Rightarrow> 's3) 
      \<Rightarrow> 's1 \<Rightarrow> 's3"
  where 
  "gen_Union it emp un X \<equiv> it X (\<lambda>_. True) un emp"

lemma gen_Union[autoref_rules_raw]:
  assumes PRIO_TAG_GEN_ALGO
  assumes EMP: "GEN_OP emp {} (\<langle>Rk\<rangle>Rs3)"
  assumes UN: "GEN_OP un (op \<union>) (\<langle>Rk\<rangle>Rs2\<rightarrow>\<langle>Rk\<rangle>Rs3\<rightarrow>\<langle>Rk\<rangle>Rs3)"
  assumes IT: "SIDE_GEN_ALGO (is_set_to_list (\<langle>Rk\<rangle>Rs2) Rs1 tsl)"
  shows "(gen_Union (\<lambda>x. foldli (tsl x)) emp un,Union) \<in> \<langle>\<langle>Rk\<rangle>Rs2\<rangle>Rs1 \<rightarrow> \<langle>Rk\<rangle>Rs3"
  apply (intro fun_relI)
  unfolding gen_Union_def 
  apply (rule det_fold_set[OF 
    foldli_Union IT[unfolded autoref_tag_defs]])
  using EMP UN
  unfolding autoref_tag_defs
  apply (parametricity)+
  done

(* Collections: Added atLeastLessThan for nat. *)
(* TODO: Move to Set_{Intf,Gen} *)
(* atLeastLessThan - operation ({a..<b}) *)
(* TODO: Currently only for nat. Is there a typeclass that has all 
    requirements? *)

definition "atLeastLessThan_impl a b \<equiv> do {
  (_,r) \<leftarrow> WHILET (\<lambda>(i,r). i<b) (\<lambda>(i,r). RETURN (i+1, insert i r)) (a,{});
  RETURN r
}"

lemma atLeastLessThan_impl_correct: 
  "atLeastLessThan_impl a b \<le> SPEC (\<lambda>r. r = {a..<b::nat})"
  unfolding atLeastLessThan_impl_def
  apply (refine_rcg refine_vcg WHILET_rule[where 
    I = "\<lambda>(i,r). r = {a..<i} \<and> a\<le>i \<and> ((a<b \<longrightarrow> i\<le>b) \<and> (\<not>a<b \<longrightarrow> i=a))"
    and R = "measure (\<lambda>(i,_). b - i)"
    ])
  by auto

schematic_lemma atLeastLessThan_code_aux:
  notes [autoref_rules] = IdI[of a] IdI[of b]
  assumes [autoref_rules]: "(emp,{})\<in>Rs"
  assumes [autoref_rules]: "(ins,insert)\<in>nat_rel \<rightarrow> Rs \<rightarrow> Rs"
  assumes [relator_props]: "single_valued Rs"
  shows "(?c, atLeastLessThan_impl) 
  \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Rs\<rangle>nres_rel"
  unfolding atLeastLessThan_impl_def[abs_def]
  apply (autoref (keep_goal))
  done
concrete_definition atLeastLessThan_code uses atLeastLessThan_code_aux

schematic_lemma atLeastLessThan_tr_aux:
  "RETURN ?c \<le> atLeastLessThan_code emp ins a b"
  unfolding atLeastLessThan_code_def
  by (refine_transfer (post))
concrete_definition atLeastLessThan_tr 
  for emp ins a b uses atLeastLessThan_tr_aux

lemma atLeastLessThan_gen[autoref_rules]: 
  assumes "PRIO_TAG_GEN_ALGO"
  assumes "GEN_OP emp {} Rs"
  assumes "GEN_OP ins insert (nat_rel \<rightarrow> Rs \<rightarrow> Rs)"
  assumes "PREFER single_valued Rs"
  shows "(atLeastLessThan_tr emp ins, atLeastLessThan) 
    \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> Rs"
proof (intro fun_relI, simp)
  fix a b
  from assms have GEN: 
    "(emp,{})\<in>Rs" "(ins,insert)\<in>nat_rel \<rightarrow> Rs \<rightarrow> Rs" "single_valued Rs"
    by auto

  note atLeastLessThan_tr.refine[of emp ins a b]
  also note 
    atLeastLessThan_code.refine[OF GEN,param_fo, OF IdI IdI, THEN nres_relD]
  also note atLeastLessThan_impl_correct
  finally show "(atLeastLessThan_tr emp ins a b, {a..<b}) \<in> Rs"
    by (auto simp: pw_le_iff refine_pw_simps)
qed

(* Automatic_Refinement: Added elim-rule to obtain invar and abs-fun from 
    any single-valued relation *)
lemma single_valued_as_brE:
  assumes "single_valued R"
  obtains \<alpha> invar where "R=br \<alpha> invar"
  apply (rule that[of "\<lambda>x. THE y. (x,y)\<in>R" "\<lambda>x. x\<in>Domain R"])
  using assms unfolding br_def
  by (auto dest: single_valuedD 
    intro: the_equality[symmetric] theI)

end
