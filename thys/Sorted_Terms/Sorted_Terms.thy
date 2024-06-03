section \<open>Sorted Terms\<close>

theory Sorted_Terms
  imports Sorted_Sets "First_Order_Terms.Term"
begin

subsection \<open>Overloaded Notations\<close>

consts vars :: "'a \<Rightarrow> 'b set"

adhoc_overloading vars vars_term

consts map_vars :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd"

adhoc_overloading map_vars "map_term (\<lambda>x. x)"

lemma map_term_eq_Var: "map_term F V s = Var y \<longleftrightarrow> (\<exists>x. s = Var x \<and> y = V x)"
  by (cases s, auto)

lemma map_vars_id_iff: "map_vars f s = s \<longleftrightarrow> (\<forall>x \<in> vars_term s. f x = x)"
  by (induct s, auto simp: list_eq_iff_nth_eq all_set_conv_all_nth)

lemma map_var_term_id[simp]: "map_term (\<lambda>x. x) id = id" by (auto simp: id_def[symmetric] term.map_id)

lemma map_term_eq_Fun:
  "map_term F V s = Fun g ts \<longleftrightarrow> (\<exists>f ss. s = Fun f ss \<and> g = F f \<and> ts = map (map_term F V) ss)"
  by (cases s, auto)

declare domIff[iff del]

subsection \<open>Sorted Signatures and Sorted Sets of Terms\<close>

text \<open>We view a sorted signature as a partial map 
that assigns an output sort to the pair of a function symbol and a list of input sorts.\<close>

type_synonym ('f,'s) ssig = "'f \<times> 's list \<rightharpoonup> 's"

definition hastype_in_ssig :: "'f \<Rightarrow> 's list \<Rightarrow> 's \<Rightarrow> ('f,'s) ssig \<Rightarrow> bool"
  ("_ : _ \<rightarrow> _ in _" [50,61,61,50]50)
  where "f : \<sigma>s \<rightarrow> \<tau> in F \<equiv> F (f,\<sigma>s) = Some \<tau>"

lemmas hastype_in_ssigI = hastype_in_ssig_def[unfolded atomize_eq, THEN iffD2]
lemmas hastype_in_ssigD = hastype_in_ssig_def[unfolded atomize_eq, THEN iffD1]

lemma hastype_in_ssig_imp_dom:
  assumes "f : \<sigma>s \<rightarrow> \<tau> in F" shows "(f,\<sigma>s) \<in> dom F"
  using assms by (auto simp: hastype_in_ssig_def domIff)

lemma has_same_type_ssig:
  assumes "f : \<sigma>s \<rightarrow> \<tau> in F" and "f : \<sigma>s \<rightarrow> \<tau>' in F" shows "\<tau> = \<tau>'"
  using assms by (auto simp: hastype_in_ssig_def)

lemma hastype_restrict_ssig: "f : \<sigma>s \<rightarrow> \<tau> in F |` S \<longleftrightarrow> (f,\<sigma>s) \<in> S \<and> f : \<sigma>s \<rightarrow> \<tau> in F"
  by (auto simp: restrict_map_def hastype_in_ssig_def)

lemma subssigI: assumes "\<And>f \<sigma>s \<tau>. f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> f : \<sigma>s \<rightarrow> \<tau> in F'"
  shows "F \<subseteq>\<^sub>m F'"
  using assms by (auto simp: map_le_def hastype_in_ssig_def dom_def)

lemma subssigD: assumes FF: "F \<subseteq>\<^sub>m F'" and "f : \<sigma>s \<rightarrow> \<tau> in F" shows "f : \<sigma>s \<rightarrow> \<tau> in F'"
  using assms by (auto simp: map_le_def hastype_in_ssig_def dom_def)

text \<open>The sorted set of terms:\<close>

primrec Term ("\<T>'(_,_')") where
  "\<T>(F,V) (Var v) = V v"
| "\<T>(F,V) (Fun f ss) =
  (case those (map \<T>(F,V) ss) of None \<Rightarrow> None | Some \<sigma>s \<Rightarrow> F (f,\<sigma>s))"

lemma Var_hastype[simp]: "Var v : \<sigma> in \<T>(F,V) \<longleftrightarrow> v : \<sigma> in V"
  by (auto simp: hastype_def)

lemma Fun_hastype:
  "Fun f ss : \<tau> in \<T>(F,V) \<longleftrightarrow> (\<exists>\<sigma>s. f : \<sigma>s \<rightarrow> \<tau> in F \<and> ss :\<^sub>l \<sigma>s in \<T>(F,V))"
  apply (unfold hastype_list_iff_those)
  by (auto simp: hastype_in_ssig_def hastype_def split:option.split_asm)

lemma Fun_in_dom_imp_arg_in_dom: "Fun f ss \<in> dom \<T>(F,V) \<Longrightarrow> s \<in> set ss \<Longrightarrow> s \<in> dom \<T>(F,V)"
  by (auto simp: in_dom_iff_ex_type Fun_hastype list_all2_conv_all_nth in_set_conv_nth)

lemma Fun_hastypeI: "f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> ss :\<^sub>l \<sigma>s in \<T>(F,V) \<Longrightarrow> Fun f ss : \<tau> in \<T>(F,V)"
  by (auto simp: Fun_hastype)

lemma hastype_in_Term_induct[case_names Var Fun, induct pred]:
  assumes s: "s : \<sigma> in \<T>(F,V)"
    and V: "\<And>v \<sigma>. v : \<sigma> in V \<Longrightarrow> P (Var v) \<sigma>"
    and F: "\<And>f ss \<sigma>s \<tau>.
        f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> ss :\<^sub>l \<sigma>s in \<T>(F,V) \<Longrightarrow> list_all2 P ss \<sigma>s \<Longrightarrow> P (Fun f ss) \<tau>"
  shows "P s \<sigma>"
proof (insert s, induct s arbitrary: \<sigma> rule:term.induct)
  case (Var v \<sigma>)
  with V[of v \<sigma>] show ?case by auto
next
  case (Fun f ss \<tau>)
  then obtain \<sigma>s where f: "f : \<sigma>s \<rightarrow> \<tau> in F" and ss: "ss :\<^sub>l \<sigma>s in \<T>(F,V)" by (auto simp:Fun_hastype)
  show ?case
  proof (rule F[OF f ss], unfold list_all2_conv_all_nth, safe)
    from ss show len: "length ss = length \<sigma>s" by (auto dest: list_all2_lengthD)
    fix i assume i: "i < length ss"
    with ss have *: "ss ! i : \<sigma>s ! i in \<T>(F,V)" by (auto simp: list_all2_conv_all_nth)
    from i have ssi: "ss ! i \<in> set ss" by auto
    from Fun(1)[OF this *]
    show "P (ss ! i) (\<sigma>s ! i)".
  qed
qed

lemma in_dom_Term_induct[case_names Var Fun, induct pred]:
  assumes s: "s \<in> dom \<T>(F,V)"
  assumes V: "\<And>v \<sigma>. v : \<sigma> in V \<Longrightarrow> P (Var v)"
  assumes F: "\<And>f ss \<sigma>s \<tau>.
    f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> ss :\<^sub>l \<sigma>s in \<T>(F,V) \<Longrightarrow> \<forall>s \<in> set ss. P s \<Longrightarrow> P (Fun f ss)"
  shows "P s"
proof-
  from s obtain \<sigma> where "s : \<sigma> in \<T>(F,V)" by (auto elim!:in_dom_hastypeE)
  then show ?thesis
    by (induct rule: hastype_in_Term_induct, auto intro!: V F simp: list_all2_indep2)
qed

lemma Term_mono_left: assumes FF: "F \<subseteq>\<^sub>m F'" shows "\<T>(F,V) \<subseteq>\<^sub>m \<T>(F',V)"
proof (intro subssetI, elim hastype_in_Term_induct, goal_cases)
  case (1 a \<sigma> v \<sigma>')
  then show ?case by auto
next
  case (2 a \<sigma> f ss \<sigma>s \<tau>)
  then show ?case
    by (auto intro!:exI[of _ \<sigma>s] dest!: subssigD[OF FF] simp: Fun_hastype)
qed

lemmas hastype_in_Term_mono_left = Term_mono_left[THEN subssetD]

lemmas dom_Term_mono_left = Term_mono_left[THEN map_le_implies_dom_le]

lemma Term_mono_right: assumes VV: "V \<subseteq>\<^sub>m V'" shows "\<T>(F,V) \<subseteq>\<^sub>m \<T>(F,V')"
proof (intro subssetI, elim hastype_in_Term_induct, goal_cases)
  case (1 a \<sigma> v \<sigma>')
  with VV show ?case by (auto dest!:subssetD)
next
  case (2 a \<sigma> f ss \<sigma>s \<tau>)
  then show ?case
    by (auto intro!:exI[of _ \<sigma>s] simp: Fun_hastype)
qed

lemmas hastype_in_Term_mono_right = Term_mono_right[THEN subssetD]

lemmas dom_Term_mono_right = Term_mono_right[THEN map_le_implies_dom_le]

lemmas Term_mono = map_le_trans[OF Term_mono_left Term_mono_right]

lemmas hastype_in_Term_mono = Term_mono[THEN subssetD]

lemmas dom_Term_mono = Term_mono[THEN map_le_implies_dom_le]

lemma hastype_in_Term_restrict_vars: "s : \<sigma> in \<T>(F, V |` vars s) \<longleftrightarrow> s : \<sigma> in \<T>(F,V)"
  (is "?l s \<longleftrightarrow> ?r s")
proof (rule iffI)
  assume "?l s"
  from hastype_in_Term_mono_right[OF restrict_submap this]
  show "?r s".
next
  show "?r s \<Longrightarrow> ?l s"
  proof (induct rule: hastype_in_Term_induct)
    case (Var v \<sigma>)
    then show ?case by (auto simp:hastype_restrict)
  next
    case (Fun f ss \<sigma>s \<tau>)
    have "ss :\<^sub>l \<sigma>s in \<T>(F,V |` vars (Fun f ss))"
      apply (rule list.rel_mono_strong[OF Fun(3) hastype_in_Term_mono_right])
      by (auto intro: restrict_map_mono_right)
    with Fun show ?case
      by (auto simp:Fun_hastype)
  qed
qed

lemma hastype_in_Term_imp_vars: "s : \<sigma> in \<T>(F,V) \<Longrightarrow> v \<in> vars s \<Longrightarrow> v \<in> dom V"
proof (induct s \<sigma> rule: hastype_in_Term_induct)
  case (Var v \<sigma>)
  then show ?case by auto
next
  case (Fun f ss \<sigma>s \<tau>)
  then obtain i where i: "i < length ss" and v: "v \<in> vars (ss!i)" by (auto simp:in_set_conv_nth)
  from Fun(3) i v
  show ?case by (auto simp: list_all2_conv_all_nth)
qed

lemma in_dom_Term_imp_vars: "s \<in> dom \<T>(F,V) \<Longrightarrow> v \<in> vars s \<Longrightarrow> v \<in> dom V"
  by (auto elim!: in_dom_hastypeE simp: hastype_in_Term_imp_vars)

lemma hastype_in_Term_imp_vars_subset: "t : s in \<T>(F,V) \<Longrightarrow> vars t \<subseteq> dom V" 
  by (auto dest: hastype_in_Term_imp_vars)

interpretation Var: sorted_map Var V "\<T>(F,V)" for F V by (auto intro!: sorted_mapI)


subsection \<open>Sorted Algebras\<close>

locale sorted_algebra_syntax =
  fixes F :: "('f,'s) ssig" and A :: "'a \<rightharpoonup> 's" and I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"

locale sorted_algebra = sorted_algebra_syntax +
  assumes sort_matches: "f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> as :\<^sub>l \<sigma>s in A \<Longrightarrow> I f as : \<tau> in A"
begin

context
  fixes \<alpha> V
  assumes \<alpha>: "\<alpha> :\<^sub>s V \<rightarrow> A"
begin

lemma eval_hastype:
  assumes s: "s : \<sigma> in \<T>(F,V)" shows "I\<lbrakk>s\<rbrakk>\<alpha> : \<sigma> in A"
  by (insert s, induct s \<sigma> rule: hastype_in_Term_induct,
      auto simp: sorted_mapD[OF \<alpha>] intro!: sort_matches simp: list_all2_conv_all_nth)

interpretation eval: sorted_map "\<lambda>s. I\<lbrakk>s\<rbrakk>\<alpha>" "\<T>(F,V)" A
  by (auto intro!: sorted_mapI eval_hastype)

lemmas eval_sorted_map = eval.sorted_map_axioms
lemmas eval_dom = eval.in_dom
lemmas map_eval_hastype = eval.sorted_map_list
lemmas eval_has_same_type = eval.target_has_same_type
lemmas eval_dom_iff_hastype = eval.target_dom_iff_hastype
lemmas dom_iff_hastype = eval.source_dom_iff_hastype

end

lemmas eval_hastype_vars =
  eval_hastype[OF _ hastype_in_Term_restrict_vars[THEN iffD2]]

lemmas eval_has_same_type_vars =
  eval_has_same_type[OF _ hastype_in_Term_restrict_vars[THEN iffD2]]

end

lemma sorted_algebra_cong:
  assumes "F = F'" and "A = A'"
    and "\<And>f \<sigma>s \<tau> as. f : \<sigma>s \<rightarrow> \<tau> in F' \<Longrightarrow> as :\<^sub>l \<sigma>s in A' \<Longrightarrow> I f as = I' f as"
  shows "sorted_algebra F A I = sorted_algebra F' A' I'"
  using assms by (auto simp: sorted_algebra_def)

subsubsection \<open>Term Algebras\<close>

text \<open>The sorted set of terms constitutes a sorted algebra, in which
evaluation is substitution.\<close>

interpretation "term": sorted_algebra F "\<T>(F,V)" Fun for F V
  apply (unfold_locales)
  by (auto simp: Fun_hastype)

text \<open>Sorted substitution preserves type:\<close>

lemma subst_hastype: "\<theta> :\<^sub>s X \<rightarrow> \<T>(F,V) \<Longrightarrow> s : \<sigma> in \<T>(F,X) \<Longrightarrow> s\<cdot>\<theta> : \<sigma> in \<T>(F,V)"
  using term.eval_hastype.

lemmas subst_hastype_imp_dom_iff = term.dom_iff_hastype
lemmas subst_hastype_vars = term.eval_hastype_vars
lemmas subst_has_same_type = term.eval_has_same_type
lemmas subst_same_vars = eval_same_vars[of _ _ _ Fun]
lemmas subst_map_vars = eval_map_vars[of Fun]
lemmas subst_o = eval_o[of Fun]
lemmas subst_sorted_map = term.eval_sorted_map
lemmas map_subst_hastype = term.map_eval_hastype

lemma subst_compose_sorted_map:
  assumes "\<theta> :\<^sub>s X \<rightarrow> \<T>(F,Y)" and "\<rho> :\<^sub>s Y \<rightarrow> \<T>(F,Z)"
  shows "\<theta> \<circ>\<^sub>s \<rho> :\<^sub>s X \<rightarrow> \<T>(F,Z)"
  using assms by (simp add: sorted_map_def subst_compose subst_hastype)

lemma subst_hastype_iff_vars:
  assumes "\<forall>x\<in>vars s. \<forall>\<sigma>. \<theta> x : \<sigma> in \<T>(F,W) \<longleftrightarrow> x : \<sigma> in V"
  shows "s \<cdot> \<theta> : \<sigma> in \<T>(F,W) \<longleftrightarrow> s : \<sigma> in \<T>(F,V)"
proof (insert assms, induct s arbitrary: \<sigma>)
  case (Var x)
  then show ?case by (auto intro!: hastypeI)
next
  case (Fun f ss \<tau>)
  then show ?case by (simp add:Fun_hastype list_all2_conv_all_nth cong:map_cong)
qed

lemma subst_in_dom_imp_var_in_dom:
  assumes "s\<cdot>\<theta> \<in> dom \<T>(F,V)" and "x \<in> vars s" shows "\<theta> x \<in> dom \<T>(F,V)"
  using assms
proof (induction s)
  case (Var v)
  then show ?case by auto
next
  case (Fun f ss)
  then obtain s where s: "s \<in> set ss" and "s\<cdot>\<theta> : dom \<T>(F,V)" and xs: "x \<in> vars s"
    by (auto dest!: Fun_in_dom_imp_arg_in_dom)
  from Fun.IH[OF this]
  show ?case.
qed

lemma subst_sorted_map_restrict_vars:
  assumes \<theta>: "\<theta> :\<^sub>s X \<rightarrow> \<T>(F,V)" and WV: "W \<subseteq>\<^sub>m V" and s\<theta>: "s\<cdot>\<theta> \<in> dom \<T>(F,W)"
  shows "\<theta> :\<^sub>s X |` vars s \<rightarrow> \<T>(F,W)"
proof (safe intro!: sorted_mapI dest!: hastype_restrict[THEN iffD1])
  fix x \<sigma> assume xs: "x \<in> vars s" and x\<sigma>: "x : \<sigma> in X"
  from sorted_mapD[OF \<theta> x\<sigma>] have x\<theta>\<sigma>: "\<theta> x : \<sigma> in \<T>(F,V)" by auto
  from subst_in_dom_imp_var_in_dom[OF s\<theta> xs]
  obtain \<sigma>' where "\<theta> x : \<sigma>' in \<T>(F,W)" by (auto simp: in_dom_iff_ex_type)
  with hastype_in_Term_mono[OF map_le_refl WV this] x\<theta>\<sigma>
  show "\<theta> x : \<sigma> in \<T>(F,W)" by (auto simp: has_same_type)
qed

subsubsection \<open>Homomorphisms\<close>

locale sorted_distributive =
  sort_preserving \<phi> A + source: sorted_algebra F A I for F \<phi> A I J +
  assumes distrib: "f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> as :\<^sub>l \<sigma>s in A \<Longrightarrow> \<phi> (I f as) = J f (map \<phi> as)"
begin

lemma distrib_eval:
  assumes \<alpha>: "\<alpha> :\<^sub>s V \<rightarrow> A" and s: "s : \<sigma> in \<T>(F,V)"
  shows "\<phi> (I\<lbrakk>s\<rbrakk>\<alpha>) = J\<lbrakk>s\<rbrakk>(\<phi> \<circ> \<alpha>)"
proof (insert s, induct rule: hastype_in_Term_induct)
  case (Var v \<sigma>)
  then show ?case by auto
next
  case (Fun f ss \<sigma>s \<tau>)
  note ty = source.map_eval_hastype[OF \<alpha> Fun(2)]
  from Fun(3)[unfolded list_all2_indep2] distrib[OF Fun(1) ty]
  show ?case by (auto simp: o_def cong:map_cong)
qed

text \<open>The image of a distributive map forms a sorted algebra.\<close>

sublocale image: sorted_algebra F "\<phi> `\<^sup>s A" J
proof (unfold_locales)
  fix f \<sigma>s \<tau> bs
  assume f: "f : \<sigma>s \<rightarrow> \<tau> in F" and bs: "bs :\<^sub>l \<sigma>s in \<phi> `\<^sup>s A"
  from bs[unfolded hastype_list_in_image]
  obtain as where as: "as :\<^sub>l \<sigma>s in A" and asbs: "map \<phi> as = bs" by auto
  show "J f bs : \<tau> in \<phi> `\<^sup>s A"
    apply (rule hastype_in_imageI)
    apply (fact source.sort_matches[OF f as])
    by (auto simp: distrib[OF f as] asbs)
qed

end

lemma sorted_distributive_cong:
  fixes A A' :: "'a \<rightharpoonup> 's" and \<phi> :: "'a \<Rightarrow> 'b" and I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
  assumes \<phi>: "\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> \<phi> a = \<phi>' a"
    and A: "A = A'"
    and I: "\<And>f \<sigma>s \<tau> as. f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> as :\<^sub>l \<sigma>s in A \<Longrightarrow> I f as = I' f as"
    and J: "\<And>f \<sigma>s \<tau> as. f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> as :\<^sub>l \<sigma>s in A \<Longrightarrow> J f (map \<phi> as) = J' f (map \<phi> as)"
  shows "sorted_distributive F \<phi> A I J = sorted_distributive F \<phi>' A' I' J'"
proof-
  { fix A A' :: "'a \<rightharpoonup> 's" and \<phi> \<phi>' :: "'a \<Rightarrow> 'b" and I I' :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" and J J' :: "'f \<Rightarrow> 'b list \<Rightarrow> 'b"
    assume \<phi>: "\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> \<phi> a = \<phi>' a"
    have map_eq: "as :\<^sub>l \<sigma>s in A \<Longrightarrow> map \<phi> as = map \<phi>' as" for as \<sigma>s
      by (auto simp: list_eq_iff_nth_eq \<phi> dest:list_all2_nthD)
    { assume A: "A = A'"
        and I: "\<And>f \<sigma>s \<tau> as. f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> as :\<^sub>l \<sigma>s in A' \<Longrightarrow> I f as = I' f as"
        and J: "\<And>f \<sigma>s \<tau> as. f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> as :\<^sub>l \<sigma>s in A' \<Longrightarrow> J f (map \<phi> as) = J' f (map \<phi> as)"
      { assume hom: "sorted_distributive F \<phi>' A' I' J'"
        from hom interpret sorted_distributive F \<phi>' A' I' J'.
        interpret I: sorted_algebra F A I
          using source.sort_matches A I by (auto intro!: sorted_algebra.intro)
        have "sorted_distributive F \<phi> A I J"
        proof (intro sorted_distributive.intro sorted_distributive_axioms.intro
              I.sorted_algebra_axioms)
          show "sort_preserving \<phi> A" using sort_preserving_axioms[folded A] \<phi>
            by (simp cong: sort_preserving_cong)
          fix f \<sigma>s \<tau> as
          assume f: "f : \<sigma>s \<rightarrow> \<tau> in F" and as: "as :\<^sub>l \<sigma>s in A"
          from distrib[OF f as[unfolded A]] \<phi> as I.sort_matches[OF f as]
            I[OF f as[unfolded A]] 
          show "\<phi> (I f as) = J f (map \<phi> as)" by (auto simp: map_eq[symmetric] A intro!: J[OF f, symmetric])
        qed
      }
    }
    note this map_eq
  }
  note * = this(1) and map_eq = this(2)
  from map_eq[unfolded atomize_imp atomize_all, folded atomize_imp] \<phi>
  have map_eq: "as :\<^sub>l \<sigma>s in A \<Longrightarrow> map \<phi> as = map \<phi>' as" for as \<sigma>s by metis
  show ?thesis
  proof (rule iffI)
    assume pre: "sorted_distributive F \<phi> A I J"
    show "sorted_distributive F \<phi>' A' I' J'"
      apply (rule *[rotated -1, OF pre])
      using assms by (auto simp: map_eq)
  next
    assume pre: "sorted_distributive F \<phi>' A' I' J'"
    show "sorted_distributive F \<phi> A I J"
      apply (rule *[rotated -1, OF pre])
      using assms by auto
  qed
qed

lemma sorted_distributive_o:
  assumes "sorted_distributive F \<phi> A I J" and "sorted_distributive F \<psi> (\<phi> `\<^sup>s A) J K"
  shows "sorted_distributive F (\<psi> \<circ> \<phi>) A I K"
proof-
  interpret \<phi>: sorted_distributive F \<phi> A I J + \<psi>: sorted_distributive F \<psi> "\<phi>`\<^sup>sA" J K using assms.
  interpret sort_preserving "\<psi>\<circ>\<phi>" A by (rule sort_preserving_o; unfold_locales)
  show ?thesis
    apply (unfold_locales)
    by (simp add: \<phi>.distrib \<psi>.distrib[OF _ \<phi>.to_image.sorted_map_list])
qed

locale sorted_homomorphism = sorted_distributive F \<phi> A I J + sorted_map \<phi> A B +
  target: sorted_algebra F B J for F \<phi> A I B J
begin
end

lemma sorted_homomorphism_o:
  assumes "sorted_homomorphism F \<phi> A I B J" and "sorted_homomorphism F \<psi> B J C K"
  shows "sorted_homomorphism F (\<psi> \<circ> \<phi>) A I C K"
proof-
  interpret \<phi>: sorted_homomorphism F \<phi> A I B J + \<psi>: sorted_homomorphism F \<psi> B J C K using assms.
  interpret sorted_map "\<psi> \<circ> \<phi>" A C
    using sorted_map_o[OF \<phi>.sorted_map_axioms \<psi>.sorted_map_axioms].
  show ?thesis
    apply (unfold_locales)
    by (simp add: \<phi>.distrib \<psi>.distrib[OF _ \<phi>.sorted_map_list])
qed

context sorted_algebra begin

context fixes \<alpha> V assumes sorted: "\<alpha> :\<^sub>s V \<rightarrow> A"
begin

text \<open> The term algebra is free in all @{term F}-algebras;
that is, every assignment @{term \<open>\<alpha> :\<^sub>s V \<rightarrow> A\<close>} is extended to a homomorphism @{term \<open>\<lambda>s. I\<lbrakk>s\<rbrakk>\<alpha>\<close>}. \<close>

interpretation sorted_map \<alpha> V A using sorted.

interpretation eval: sorted_map \<open>\<lambda>s. I\<lbrakk>s\<rbrakk>\<alpha>\<close> \<open>\<T>(F,V)\<close> A using eval_sorted_map[OF sorted].

interpretation eval: sorted_homomorphism F \<open>\<lambda>s. I\<lbrakk>s\<rbrakk>\<alpha>\<close> \<open>\<T>(F,V)\<close> Fun A I
  apply (unfold_locales) by auto

lemmas eval_sorted_homomorphism = eval.sorted_homomorphism_axioms

end

end

lemma sorted_homomorphism_cong:
  fixes A A' :: "'a \<rightharpoonup> 's" and \<phi> :: "'a \<Rightarrow> 'b" and I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
  assumes \<phi>: "\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> \<phi> a = \<phi>' a"
    and A: "A = A'"
    and I: "\<And>f \<sigma>s \<tau> as. f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> as :\<^sub>l \<sigma>s in A \<Longrightarrow> I f as = I' f as"
    and B: "B = B'"
    and J: "\<And>f \<sigma>s \<tau> bs. f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> bs :\<^sub>l \<sigma>s in B \<Longrightarrow> J f bs = J' f bs"
  shows "sorted_homomorphism F \<phi> A I B J = sorted_homomorphism F \<phi>' A' I' B' J'" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then interpret sorted_homomorphism F \<phi> A I B J.
  have J': "as :\<^sub>l \<sigma>s in A' \<Longrightarrow> J f (map \<phi> as) = J' f (map \<phi> as)" if f: "f : \<sigma>s \<rightarrow> \<tau> in F" for f \<sigma>s \<tau> as
    apply (rule J[OF f]) using A B sorted_map_list by auto
  note * = sorted_distributive_cong[THEN iffD1, rotated -1, OF sorted_distributive_axioms]
  show ?r
    apply (intro sorted_homomorphism.intro *)
    using assms J' sorted_map_axioms target.sorted_algebra_axioms
    by (simp_all cong: sorted_map_cong sorted_algebra_cong)
next
  assume ?r
  then interpret sorted_homomorphism F \<phi>' A' I' B' J'.
  have J': "as :\<^sub>l \<sigma>s in A' \<Longrightarrow> J f (map \<phi>' as) = J' f (map \<phi>' as)" if f: "f : \<sigma>s \<rightarrow> \<tau> in F" for f \<sigma>s \<tau> as
    apply (rule J[OF f]) using A B sorted_map_list \<phi> by auto
  note * = sorted_distributive_cong[THEN iffD1, rotated -1, OF sorted_distributive_axioms]
  note 2 = sorted_map_cong[THEN iffD1, rotated -1, OF sorted_map_axioms]
  show ?l
    apply (intro sorted_homomorphism.intro * 2)
    using assms J' target.sorted_algebra_axioms
    by (simp_all cong: sorted_distributive_cong sorted_algebra_cong)
qed

context sort_preserving begin

lemma sort_preserving_map_vars: "sort_preserving (map_vars f) \<T>(F,A)"
proof
  fix a b \<sigma> \<tau>
  assume a: "a : \<sigma> in \<T>(F,A)" and b: "b : \<tau> in \<T>(F,A)" and eq: "map_vars f a = map_vars f b"
  from a b eq show "\<sigma> = \<tau>"
  proof (induct arbitrary: \<tau> b)
    case (Var x \<sigma>)
    then show ?case by (cases b, auto simp: same_value_imp_same_type)
  next
    case IH: (Fun ff ss \<sigma>s \<sigma>)
    show ?case
    proof (cases b)
      case (Var y)
      with IH show ?thesis by auto
    next
      case (Fun gg tt)
      with IH have eq: "map (map_vars f) ss = map (map_vars f) tt" by (auto simp: id_def)
      from arg_cong[OF this, of length] have lensstt: "length ss = length tt" by auto
      with IH obtain \<tau>s where ff2: "ff : \<tau>s \<rightarrow> \<tau> in F" and tt: "tt :\<^sub>l \<tau>s in \<T>(F,A)"
        by (auto simp: Fun Fun_hastype)
      from IH have lenss: "length ss = length \<sigma>s" by (auto simp: list_all2_lengthD)
      have "\<sigma>s = \<tau>s"
      proof (unfold list_eq_iff_nth_eq, safe)
        from lensstt tt IH show len2: "length \<sigma>s = length \<tau>s" by (auto simp: list_all2_lengthD)
        fix i assume "i < length \<sigma>s"
        with lenss have i: "i < length ss" by auto
        show "\<sigma>s ! i = \<tau>s ! i"
        proof(rule list_all2_nthD[OF IH(3) i, rule_format])
          from i lenss lensstt arg_cong[OF eq, of "\<lambda>xs. xs!i"]
          show "map_vars f (ss ! i) = map_vars f (tt ! i)" by auto
          from i lensstt list_all2_nthD[OF tt]
          show "tt ! i : \<tau>s ! i in \<T>(F,A)" by auto
        qed
      qed
      with ff2 Fun IH.hyps(1) show "\<sigma> = \<tau>" by (auto simp: hastype_in_ssig_def)
    qed
  qed
qed

lemma map_vars_image_Term: "map_vars f `\<^sup>s \<T>(F,A) = \<T>(F,f `\<^sup>s A)" (is "?L = ?R")
proof (intro sset_eqI)
  interpret map_vars: sort_preserving "map_term (\<lambda>x. x) f" "\<T>(F,A)" using sort_preserving_map_vars.
  fix a \<sigma>
  show "a : \<sigma> in ?L \<longleftrightarrow> a : \<sigma> in ?R"
  proof (induct a arbitrary: \<sigma>)
    case (Var x)
    then show ?case 
      by (auto simp: map_vars.hastype_in_image map_term_eq_Var hastype_in_image)
        (metis Var_hastype)
  next
    case IH: (Fun ff as)
    show ?case
    proof (unfold Fun_hastype map_vars.hastype_in_image map_term_eq_Fun, safe dest!: Fun_hastype[THEN iffD1])
      fix ss \<sigma>s
      assume as: "as = map (map_vars f) ss" and ff: "ff : \<sigma>s \<rightarrow> \<sigma> in F" and ss: "ss :\<^sub>l \<sigma>s in \<T>(F,A)"
      from ss have "map (map_vars f) ss :\<^sub>l \<sigma>s in map_vars f `\<^sup>s \<T>(F,A)"
        by (auto simp: map_vars.hastype_list_in_image)
      with IH[unfolded as]
      have "map (map_vars f) ss :\<^sub>l \<sigma>s in \<T>(F,f `\<^sup>s A)"
        by (auto simp: list_all2_conv_all_nth)
      with ff
      show "\<exists>\<sigma>s. ff : \<sigma>s \<rightarrow> \<sigma> in F \<and> map (map_vars f) ss :\<^sub>l \<sigma>s in \<T>(F,f `\<^sup>s A)" by auto
    next
      fix \<sigma>s assume ff: "ff : \<sigma>s \<rightarrow> \<sigma> in F" and as: "as :\<^sub>l \<sigma>s in \<T>(F,f `\<^sup>s A)"
      with IH have "as :\<^sub>l \<sigma>s in map_vars f `\<^sup>s \<T>(F,A)"
        by (auto simp: map_vars.hastype_in_image list_all2_conv_all_nth)
      then obtain ss where ss: "ss :\<^sub>l \<sigma>s in \<T>(F,A)" and as: "as = map (map_vars f) ss"
        by (auto simp: map_vars.hastype_list_in_image)
      from ss ff have a: "Fun ff ss : \<sigma> in \<T>(F,A)" by (auto simp: Fun_hastype)
      show "\<exists>a. a : \<sigma> in \<T>(F,A) \<and> (\<exists>fa ss. a = Fun fa ss \<and> ff = fa \<and> as = map (map_vars f) ss)"
        apply (rule exI[of _ "Fun ff ss"])
        using a as by auto
    qed
  qed
qed

end

context sorted_map begin

lemma sorted_map_map_vars: "map_vars f :\<^sub>s \<T>(F,A) \<rightarrow> \<T>(F,B)"
proof-
  interpret map_vars: sort_preserving \<open>map_vars f\<close> \<open>\<T>(F,A)\<close> using sort_preserving_map_vars.
  show ?thesis
    apply (unfold map_vars.sorted_map_iff_image_subset)
    apply (unfold map_vars_image_Term)
    apply (rule Term_mono_right)
    using image_subsset.
qed

end

subsection \<open>Lifting Sorts\<close>

text \<open>By `uni-sorted' we mean the situation where there is only one sort @{term "()"}.
This situation is isomorphic to sets.\<close>
definition "unisorted A a \<equiv> if a \<in> A then Some () else None"

lemma unisorted_eq_Some[simp]: "unisorted A a = Some \<sigma> \<longleftrightarrow> a \<in> A"
  and unisorted_eq_None[simp]: "unisorted A a = None \<longleftrightarrow> a \<notin> A"
  and hastype_in_unisorted[simp]: "a : \<sigma> in unisorted A \<longleftrightarrow> a \<in> A"
  by (auto simp: unisorted_def hastype_def)

lemma hastype_list_in_unisorted[simp]: "as :\<^sub>l \<sigma>s in unisorted A \<longleftrightarrow> length as = length \<sigma>s \<and> set as \<subseteq> A"
  by (auto simp: list_all2_conv_all_nth dest: all_nth_imp_all_set)

lemma dom_unisorted[simp]: "dom (unisorted A) = A"
  by (auto simp: unisorted_def domIff split:if_split_asm)

lemma unisorted_map[simp]:
  "f :\<^sub>s unisorted A \<rightarrow> \<tau> \<longleftrightarrow> f : A \<rightarrow> dom \<tau>"
  "f :\<^sub>s \<sigma> \<rightarrow> unisorted B \<longleftrightarrow> f : dom \<sigma> \<rightarrow> B"
  by (auto simp: sorted_map_def hastype_def domIff)

lemma image_unisorted[simp]: "f `\<^sup>s unisorted A = unisorted (f ` A)"
  by (auto intro!:sset_eqI simp: hastype_def sorted_image_def safe_The_eq_Some) 

definition unisorted_sig :: "('f\<times>nat) set \<Rightarrow> ('f,unit) ssig"
  where "unisorted_sig F \<equiv> \<lambda>(f,\<sigma>s). if (f, length \<sigma>s) \<in> F then Some () else None"

lemma in_unisorted_sig[simp]: "f : \<sigma>s \<rightarrow> \<tau> in unisorted_sig F \<longleftrightarrow> (f,length \<sigma>s) \<in> F"
  by (auto simp: unisorted_sig_def hastype_in_ssig_def)

inductive_set uTerm ("\<TT>'(_,_')" [1,1]1000) for F V where
  "Var v \<in> \<TT>(F,V)" if "v \<in> V"
| "\<forall>s \<in> set ss. s \<in> \<TT>(F,V) \<Longrightarrow> Fun f ss \<in> \<TT>(F,V)" if "(f,length ss) \<in> F"

lemma Var_in_Term[simp]: "Var x \<in> \<TT>(F,V) \<longleftrightarrow> x \<in> V"
    using uTerm.cases by (auto intro: uTerm.intros)

lemma Fun_in_Term[simp]: "Fun f ss \<in> \<TT>(F,V) \<longleftrightarrow> (f,length ss) \<in> F \<and> set ss \<subseteq> \<TT>(F,V)"
  apply (unfold subset_iff)
  apply (fold Ball_def)
  by (metis (no_types, lifting) term.distinct(1) term.inject(2) uTerm.simps)

lemma hastype_in_unisorted_Term[simp]:
  "s : \<sigma> in \<T>(unisorted_sig F, unisorted V) \<longleftrightarrow> s \<in> \<TT>(F,V)"
proof (induct s)
case (Var x)
  then show ?case by auto
next
  case (Fun f ss)
  then show ?case
    by (auto simp: in_dom_iff_ex_type Fun_hastype list_all2_indep2
        intro!: exI[of _ "replicate (length ss) ()"])
qed

lemma unisorted_Term: "\<T>(unisorted_sig F, unisorted V) = unisorted \<TT>(F,V)"
  by (auto intro!: sset_eqI)

locale algebra =
  fixes F :: "('f \<times> nat) set" and A :: "'a set" and I
  assumes closed: "(f, length as) \<in> F \<Longrightarrow> set as \<subseteq> A \<Longrightarrow> I f as \<in> A"
begin
end

lemma unisorted_algebra: "sorted_algebra (unisorted_sig F) (unisorted A) I \<longleftrightarrow> algebra F A I"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume "?r"
  then interpret algebra.
  show ?l
    apply unfold_locales by (auto simp: list_all2_indep2 intro!: closed)
next
  assume ?l
  then interpret sorted_algebra \<open>unisorted_sig F\<close> \<open>unisorted A\<close> I.
  show ?r
  proof unfold_locales
    fix f as assume f: "(f, length as) \<in> F" and asA: "set as \<subseteq> A"
    from f have "f : replicate (length as) () \<rightarrow> () in unisorted_sig F" by auto
    from sort_matches[OF this] asA
    show "I f as \<in> A" by auto
  qed
qed

context algebra begin

interpretation unisorted: sorted_algebra \<open>unisorted_sig F\<close> \<open>unisorted A\<close> I
  apply (unfold unisorted_algebra)..

lemma eval_closed: "\<alpha> : V \<rightarrow> A \<Longrightarrow> s \<in> \<TT>(F,V) \<Longrightarrow> I\<lbrakk>s\<rbrakk>\<alpha> \<in> A"
  using unisorted.eval_hastype[of \<alpha> "unisorted V"] by simp

end

locale distributive =
  source: algebra F A I for F \<phi> A I J +
  assumes distrib: "(f, length as) \<in> F \<Longrightarrow> set as \<subseteq> A \<Longrightarrow> \<phi> (I f as) = J f (map \<phi> as)"

lemma unisorted_distributive:
  "sorted_distributive (unisorted_sig F) \<phi> (unisorted A) I J \<longleftrightarrow>
   distributive F \<phi> A I J" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?r
  then interpret distributive.
  show ?l
    apply (intro sorted_distributive.intro unisorted_algebra[THEN iffD2])
    apply (unfold_locales)
    by (auto intro!: distrib simp: list_all2_same_right)
next
  assume ?l
  then interpret sorted_distributive \<open>unisorted_sig F\<close> \<phi> \<open>unisorted A\<close> I J.
  from source.sorted_algebra_axioms
  interpret source: algebra F A I by (unfold unisorted_algebra)
  show ?r
  proof unfold_locales
    fix f as
    show "(f, length as) \<in> F \<Longrightarrow> set as \<subseteq> A \<Longrightarrow> \<phi> (I f as) = J f (map \<phi> as)"
      using distrib[of f "replicate (length as) ()" _ as]
      by auto
  qed
qed

locale homomorphism =
  distributive F \<phi> A I J + target: algebra F B J for F \<phi> A I B J +
  assumes funcset: "\<phi> : A \<rightarrow> B"

lemma unisorted_homomorphism:
  "sorted_homomorphism (unisorted_sig F) \<phi> (unisorted A) I (unisorted B) J \<longleftrightarrow>
   homomorphism F \<phi> A I B J" (is "?l \<longleftrightarrow> ?r")
  by (auto simp: sorted_homomorphism_def unisorted_distributive unisorted_algebra
      homomorphism_def homomorphism_axioms_def)

lemma homomorphism_cong:
  assumes \<phi>: "\<And>a. a \<in> A \<Longrightarrow> \<phi> a = \<phi>' a"
    and A: "A = A'"
    and I: "\<And>f as. (f, length as) \<in> F \<Longrightarrow> I f as = I' f as"
    and B: "B = B'"
    and J: "\<And>f bs. (f, length bs) \<in> F \<Longrightarrow> J f bs = J' f bs"
  shows "homomorphism F \<phi> A I B J = homomorphism F \<phi>' A' I' B' J'"
proof-
  note sorted_homomorphism_cong
    [where F = "unisorted_sig F" and A = "unisorted A" and A' = "unisorted A'" and B = "unisorted B" and B' = "unisorted B'"]
  note * = this[unfolded unisorted_homomorphism]
  show ?thesis apply (rule *)
    by (auto simp: A B \<phi> I J list_all2_same_right)
qed

context algebra begin

interpretation unisorted: sorted_algebra \<open>unisorted_sig F\<close> \<open>unisorted A\<close> I
  apply (unfold unisorted_algebra)..

lemma eval_homomorphism: "\<alpha> : V \<rightarrow> A \<Longrightarrow> homomorphism F (\<lambda>s. I\<lbrakk>s\<rbrakk>\<alpha>) \<TT>(F,V) Fun A I"
  apply (fold unisorted_homomorphism)
  apply (fold unisorted_Term)
  apply (rule unisorted.eval_sorted_homomorphism)
  by auto

end

context homomorphism begin

interpretation unisorted: sorted_homomorphism \<open>unisorted_sig F\<close> \<phi> \<open>unisorted A\<close> I \<open>unisorted B\<close> J
  apply (unfold unisorted_homomorphism)..

lemma distrib_eval: "\<alpha> : V \<rightarrow> A \<Longrightarrow> s \<in> \<TT>(F,V) \<Longrightarrow> \<phi> (I\<lbrakk>s\<rbrakk>\<alpha>) = J\<lbrakk>s\<rbrakk>(\<phi> \<circ> \<alpha>)"
  using unisorted.distrib_eval[of _ "unisorted V"] by simp

end

text \<open>By `unsorted' we mean the situation where any element has the unique type @{term "()"}.\<close>

lemma Term_UNIV[simp]: "\<TT>(UNIV,UNIV) = UNIV"
proof-
  have "s \<in> \<TT>(UNIV,UNIV)" for s by (induct s, auto)
  then show ?thesis by auto
qed

text \<open>When the carrier is unsorted, any interpretation forms an algebra.\<close>

interpretation unsorted: algebra UNIV UNIV I
  rewrites "\<And>a. a \<in> UNIV \<longleftrightarrow> True"
    and "\<And>P0. (True \<Longrightarrow> P0) \<equiv> Trueprop P0"
    and "\<And>P0. (True \<Longrightarrow> PROP P0) \<equiv> PROP P0"
    and "\<And>P0 P1. (True \<Longrightarrow> PROP P1 \<Longrightarrow> P0) \<equiv> (PROP P1 \<Longrightarrow> P0)" 
  for F I
 apply unfold_locales by auto

interpretation unsorted.eval: homomorphism UNIV "\<lambda>s. I\<lbrakk>s\<rbrakk>\<alpha>" UNIV Fun UNIV I
  rewrites "\<And>a. a \<in> UNIV \<longleftrightarrow> True"
    and "\<And>X. X \<subseteq> UNIV \<longleftrightarrow> True"
    and "\<And>P0. (True \<Longrightarrow> P0) \<equiv> Trueprop P0"
    and "\<And>P0. (True \<Longrightarrow> PROP P0) \<equiv> PROP P0"
    and "\<And>P0 P1. (True \<Longrightarrow> PROP P1 \<Longrightarrow> P0) \<equiv> (PROP P1 \<Longrightarrow> P0)"
  for I
  using unsorted.eval_homomorphism[of _ UNIV] by auto

text \<open>Evaluation distributes over evaluations in the term algebra, i.e., substitutions.\<close>
lemma subst_eval: "I\<lbrakk>s\<cdot>\<theta>\<rbrakk>\<alpha> = I\<lbrakk>s\<rbrakk>(\<lambda>x. I\<lbrakk>\<theta> x\<rbrakk>\<alpha>)"
  using unsorted.eval.distrib_eval[of _ UNIV, unfolded o_def]
  by auto

lemmas subst_subst = subst_eval[of Fun]

subsubsection \<open>Collecting Variables via Evaluation\<close>

definition "var_list_term t \<equiv> (\<lambda>f. concat)\<lbrakk>t\<rbrakk>(\<lambda>v. [v])"

lemma var_list_Fun[simp]: "var_list_term (Fun f ss) = concat (map var_list_term ss)"
  and var_list_Var[simp]: "var_list_term (Var x) = [x]"
  by (simp_all add: var_list_term_def[abs_def])

lemma set_var_list[simp]: "set (var_list_term s) = vars s"
  by (induct s, auto simp: var_list_term_def)

lemma eval_subset_Un_vars:
  assumes "\<forall>f as. foo (I f as) \<subseteq> \<Union>(foo ` set as)"
  shows "foo (I\<lbrakk>s\<rbrakk>\<alpha>) \<subseteq> (\<Union>x\<in>vars_term s. foo (\<alpha> x))"
proof (induct s)
  case (Var x)
  show ?case by simp
next
  case (Fun f ss)
  have "foo (I\<lbrakk>Fun f ss\<rbrakk>\<alpha>) = foo (I f (map (\<lambda>s. I\<lbrakk>s\<rbrakk>\<alpha>) ss))" by simp
  also note assms[rule_format]
  also have "\<Union> (foo ` set (map (\<lambda>s. I\<lbrakk>s\<rbrakk>\<alpha>) ss)) = (\<Union>s\<in>set ss. foo (I\<lbrakk>s\<rbrakk>\<alpha>))" by simp
  also have "\<dots> \<subseteq> (\<Union>s \<in> set ss. (\<Union> x \<in> vars_term s. foo (\<alpha> x)))"
    apply (rule UN_mono)
    using Fun by auto
  finally show ?case by simp
qed

subsubsection \<open>Ground terms\<close>

lemma hastype_in_Term_empty_imp_vars: "s : \<sigma> in \<T>(F,\<emptyset>) \<Longrightarrow> vars s = {}" 
  by (auto dest: hastype_in_Term_imp_vars_subset)

lemma hastype_in_Term_empty_imp_vars_subst: "s : \<sigma> in \<T>(F,\<emptyset>) \<Longrightarrow> vars (s\<cdot>\<theta>) = {}"
  by (auto simp: vars_term_subst_apply_term hastype_in_Term_empty_imp_vars)

lemma ground_Term_iff: "s : \<sigma> in \<T>(F,V) \<and> ground s \<longleftrightarrow> s : \<sigma> in \<T>(F,\<emptyset>)"
  using hastype_in_Term_restrict_vars[of s \<sigma> F V]
  by (auto simp: hastype_in_Term_empty_imp_vars ground_vars_term_empty)

lemma hastype_in_Term_empty_imp_subst:
  "s : \<sigma> in \<T>(F,\<emptyset>) \<Longrightarrow> s\<cdot>\<theta> : \<sigma> in \<T>(F,V)"
  by (rule subst_hastype, auto)

locale subsignature = fixes F G :: "('f,'s) ssig" assumes subssig: "F \<subseteq>\<^sub>m G"
begin

lemmas Term_subsset = Term_mono_left[OF subssig]
lemmas hastype_in_Term_sub = Term_subsset[THEN subssetD]

lemma subsignature: "f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> f : \<sigma>s \<rightarrow> \<tau> in G"
  using subssig by (auto dest: subssigD)

end

locale subsignature_algebra = subsignature + super: sorted_algebra G
begin

sublocale sorted_algebra F A I
  apply unfold_locales
  using super.sort_matches[OF subssigD[OF subssig]] by auto

end

locale subalgebra = sorted_algebra F A I + super: sorted_algebra G B J +
  subsignature F G
  for F :: "('f,'s) ssig" and A :: "'a \<rightharpoonup> 's" and I
  and G :: "('f,'s) ssig" and B :: "'a \<rightharpoonup> 's" and J +
  assumes subcar: "A \<subseteq>\<^sub>m B"
  assumes subintp: "f : \<sigma>s \<rightarrow> \<tau> in F \<Longrightarrow> as :\<^sub>l \<sigma>s in A \<Longrightarrow> I f as = J f as"
begin

lemma subcarrier: "a : \<sigma> in A \<Longrightarrow> a : \<sigma> in B"
  using subcar by (auto dest: subssetD)

lemma subeval:
  assumes s: "s : \<sigma> in \<T>(F,V)" and \<alpha>: "\<alpha> :\<^sub>s V \<rightarrow> A" shows "J\<lbrakk>s\<rbrakk>\<alpha> = I\<lbrakk>s\<rbrakk>\<alpha>"
proof (insert s, induct rule: hastype_in_Term_induct)
  case (Var v \<sigma>)
  then show ?case by auto
next
  case (Fun f ss \<sigma>s \<tau>)
  then show ?case
    by (auto simp: list_all2_indep2 cong:map_cong intro!:subintp[symmetric] map_eval_hastype \<alpha>)
qed

end

lemma term_subalgebra:
  assumes FG: "F \<subseteq>\<^sub>m G" and VW: "V \<subseteq>\<^sub>m W"
  shows "subalgebra F \<T>(F,V) Fun G \<T>(G,W) Fun"
  apply unfold_locales
  using FG VW Term_mono[OF FG VW] by auto


text \<open> An algebra where every element has a representation: \<close>
locale sorted_algebra_constant = sorted_algebra_syntax +
  fixes const
  assumes vars_const[simp]: "\<And>d. vars (const d) = {}"
  assumes eval_const[simp]: "\<And>d \<alpha>. I\<lbrakk>const d\<rbrakk>\<alpha> = d"
begin

lemma eval_subst_const[simp]: "I\<lbrakk>e\<cdot>(const\<circ>\<alpha>)\<rbrakk>\<beta> = I\<lbrakk>e\<rbrakk>\<alpha>"
  by (induct e, auto simp:o_def intro!:arg_cong[of _ _ "I _"])

lemma eval_upd_as_subst: "I\<lbrakk>e\<rbrakk>\<alpha>(x:=a) = I\<lbrakk>e \<cdot> Var(x:=const a)\<rbrakk>\<alpha>"
  by (induct e, auto simp: o_def intro: arg_cong[of _ _ "I _"])

end

context sorted_algebra_syntax begin

definition "constant_at f \<sigma>s i \<equiv>
  \<forall>as b. as :\<^sub>l \<sigma>s in A \<longrightarrow> A b = A (as!i) \<longrightarrow> I f (as[i:=b]) = I f as"

lemma constant_atI[intro]:
  assumes "\<And>as b. as :\<^sub>l \<sigma>s in A \<Longrightarrow> A b = A (as!i) \<Longrightarrow> I f (as[i:=b]) = I f as"
  shows "constant_at f \<sigma>s i" using assms by (auto simp: constant_at_def)

lemma constant_atD:
  "constant_at f \<sigma>s i \<Longrightarrow> as :\<^sub>l \<sigma>s in A \<Longrightarrow> A b = A (as!i) \<Longrightarrow> I f (as[i:=b]) = I f as"
  by (auto simp: constant_at_def)

lemma constant_atE[elim]:
  assumes "constant_at f \<sigma>s i"
    and "(\<And>as b. as :\<^sub>l \<sigma>s in A \<Longrightarrow> A b = A (as!i) \<Longrightarrow> I f (as[i:=b]) = I f as) \<Longrightarrow> thesis"
  shows thesis using assms by (auto simp: constant_at_def)

definition "constant_term_on s x \<equiv> \<forall>\<alpha> a. I\<lbrakk>s\<rbrakk>\<alpha>(x:=a) = I\<lbrakk>s\<rbrakk>\<alpha>"

lemma constant_term_onI:
  assumes "\<And>\<alpha> a. I\<lbrakk>s\<rbrakk>\<alpha>(x:=a) = I\<lbrakk>s\<rbrakk>\<alpha>" shows "constant_term_on s x"
  using assms by (auto simp: constant_term_on_def)

lemma constant_term_onD:
  assumes "constant_term_on s x" shows "I\<lbrakk>s\<rbrakk>\<alpha>(x:=a) = I\<lbrakk>s\<rbrakk>\<alpha>"
  using assms by (auto simp: constant_term_on_def)

lemma constant_term_onE:
  assumes "constant_term_on s x" and "(\<And>\<alpha> a. I\<lbrakk>s\<rbrakk>\<alpha>(x:=a) = I\<lbrakk>s\<rbrakk>\<alpha>) \<Longrightarrow> thesis"
  shows thesis using assms by (auto simp: constant_term_on_def)

lemma constant_term_on_extra_var: "x \<notin> vars s \<Longrightarrow> constant_term_on s x"
  by (auto intro!: constant_term_onI simp: eval_with_fresh_var)

lemma constant_term_on_eq:
  assumes st: "I\<lbrakk>s\<rbrakk> = I\<lbrakk>t\<rbrakk>" and s: "constant_term_on s x" shows "constant_term_on t x"
  using s fun_cong[OF st] by (auto simp: constant_term_on_def)

definition "constant_term s \<equiv> \<forall>x. constant_term_on s x"

lemma constant_termI: assumes "\<And>x. constant_term_on s x" shows "constant_term s"
  using assms by (auto simp: constant_term_def)

lemma ground_imp_constant: "vars s = {} \<Longrightarrow> constant_term s"
  by (auto intro!: constant_termI constant_term_on_extra_var)

end

end

