(*  Title:      Morphisms
    File:       Combinatorics_Words.Morphisms
    Author:     Štěpán Holub, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Morphisms

imports CoWBasic Submonoids

begin

chapter "Morphisms"

section \<open>One morphism\<close>

subsection  \<open>Morphism, core map and extension\<close>

definition list_extension :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('a list \<Rightarrow> 'b list)" ("_\<^sup>\<L>" [1000] 1000)
  where "t\<^sup>\<L> \<equiv> (\<lambda> x. concat (map t x))"

definition morphism_core :: "('a list \<Rightarrow> 'b list) \<Rightarrow> ('a  \<Rightarrow> 'b list)" ("_\<^sup>\<C>" [1000] 1000)
  where core_def: "f\<^sup>\<C> \<equiv> (\<lambda> x. f [x])"

(*QUESTION simp? abbereviation?
  SH: attribute simp destroys proofs based on core*)
lemma core_sing: "f\<^sup>\<C> a = f [a]"
  unfolding core_def..

lemma range_map_core: "range (map f\<^sup>\<C>) = lists (range f\<^sup>\<C>)"
    using lists_image[of "\<lambda>x. f [x]" UNIV, folded core_def, symmetric]
    unfolding lists_UNIV.

lemma map_core_lists: "(map f\<^sup>\<C> w) \<in> lists (range f\<^sup>\<C>)"
  by auto

lemma comp_core: "(f \<circ> g)\<^sup>\<C> = f \<circ> g\<^sup>\<C>"
  unfolding core_def
  by auto

locale morphism_on =
  fixes f :: "'a list \<Rightarrow> 'b list" and A :: "'a list set"
  assumes morph_on: "u \<in> \<langle>A\<rangle> \<Longrightarrow> v \<in> \<langle>A\<rangle> \<Longrightarrow> f (u \<cdot> v) = f u \<cdot> f v"

begin

lemma emp_to_emp[simp]: "f \<epsilon> = \<epsilon>"
  using morph_on[of \<epsilon> \<epsilon>] self_append_conv2[of "f \<epsilon>" "f \<epsilon>"] by simp

lemma emp_to_emp': "w = \<epsilon> \<Longrightarrow> f w = \<epsilon>"
  using morph_on[of \<epsilon> \<epsilon>] self_append_conv2[of "f \<epsilon>" "f \<epsilon>"] by simp

lemma morph_concat_concat_map: "ws \<in> lists \<langle>A\<rangle> \<Longrightarrow> f (concat ws) = concat (map f ws)"
  by (induct ws, simp_all add: morph_on hull_closed_lists)

lemma hull_im_hull:
  shows "\<langle>f ` A\<rangle> = f ` \<langle>A\<rangle>"
proof
  show " \<langle>f ` A\<rangle> \<subseteq> f ` \<langle>A\<rangle>"
  proof (rule subsetI)
    fix x
    show "x \<in> \<langle>f ` A\<rangle> \<Longrightarrow> x \<in> f ` \<langle>A\<rangle>"
    proof (induction rule: hull.induct)
      show "\<epsilon> \<in> f ` \<langle>A\<rangle>"
        using  hull.emp_in emp_to_emp by force
      show "w1 \<cdot> w2 \<in> f ` \<langle>A\<rangle>" if "w1 \<in> f ` A" and  "w2 \<in> f ` \<langle>A\<rangle>" for w1 w2
      proof-
        from that
        obtain pre1 pre2 where "pre1 \<in> \<langle>A\<rangle>" and "pre2 \<in> \<langle>A\<rangle>" and "f pre1 = w1" and "f pre2 = w2"
          using imageE by blast+
        from hull_closed[OF this(1-2)] morph_on[OF \<open>pre1 \<in> \<langle>A\<rangle>\<close> \<open>pre2 \<in> \<langle>A\<rangle>\<close>, unfolded this(3-4)]
        show "w1 \<cdot> w2 \<in> f ` \<langle>A\<rangle>"
          by force
      qed
    qed
  qed
  show "f ` \<langle>A\<rangle> \<subseteq> \<langle>f ` A\<rangle>"
  proof
    fix x
    assume "x \<in> f ` \<langle>A\<rangle>"
    then obtain xs where "f (concat xs) = x" and "xs \<in> lists A"
      using hull_concat_lists0 by blast
    from this[unfolded morph_concat_concat_map]
        morph_concat_concat_map[OF genset_sub_lists[OF this(2)]]
    show "x \<in> \<langle>f ` A\<rangle>"
      by fastforce
  qed
qed

lemma inj_basis_to_basis: assumes "inj_on f \<langle>A\<rangle>"
            shows "f ` (\<BB> \<langle>A\<rangle>) = \<BB> (f`\<langle>A\<rangle>)"
proof
  interpret basis: morphism_on f "\<BB> \<langle>A\<rangle>"
    by (rule morph_on morphism_on.intro, unfold basis_gen_hull'[of A])
    (simp only: morph_on)
  show "\<BB> (f ` \<langle>A\<rangle>) \<subseteq> f ` \<BB> \<langle>A\<rangle>"
    using basis.hull_im_hull unfolding basis_gen_hull unfolding self_gen using basis_hull_sub[of "f ` \<BB> \<langle>A\<rangle>"] by argo
  show "f ` \<BB> \<langle>A\<rangle> \<subseteq> \<BB> (f ` \<langle>A\<rangle>)"
  proof
    fix x
    assume "x \<in> f ` \<BB> \<langle>A\<rangle>"
    then obtain y where "y \<in> \<BB> \<langle>A\<rangle>" and "x = f y" by blast
    hence "x \<in> f ` \<langle>A\<rangle>"
      using basis_sub by blast
    from basis_concat_listsE[OF this]
    obtain xs where "xs \<in> lists \<BB> (f `\<langle>A\<rangle>)" and "concat xs = x".
    hence "\<epsilon> \<notin>  set xs"
      using emp_not_basis  by blast
    have "xs \<in> lists (f `\<langle>A\<rangle>)"
      using \<open>xs \<in> lists \<BB> (f `\<langle>A\<rangle>)\<close> basis_sub by blast
    then obtain ys where "map f ys = xs" and "ys \<in> lists \<langle>A\<rangle>"
      unfolding lists_image by blast
    have "\<epsilon> \<notin> set ys"
      using emp_to_emp \<open>\<epsilon> \<notin>  set xs\<close>
       imageI[of \<epsilon> "set ys" f] unfolding list.set_map[of f ys, unfolded \<open>map f ys = xs\<close>] by presburger
    hence "ys \<in> lists (\<langle>A\<rangle> - {\<epsilon>}) "
      using \<open>ys \<in> lists \<langle>A\<rangle>\<close> by fast
    have "f (concat ys) = x"
      unfolding morph_concat_concat_map[OF \<open>ys \<in> lists \<langle>A\<rangle>\<close>] \<open>map f ys = xs\<close> by fact
    from \<open>inj_on f \<langle>A\<rangle>\<close> this[unfolded  \<open>x = f y\<close>]
    have "concat ys = y"
      unfolding inj_on_def using subsetD[OF basis_sub \<open>y \<in> \<BB> \<langle>A\<rangle>\<close>] hull_closed_lists[OF \<open>ys \<in> lists \<langle>A\<rangle>\<close>] by blast
    hence "\<^bold>|ys\<^bold>| = 1"
      using \<open>y \<in> \<BB> \<langle>A\<rangle>\<close>  \<open>ys \<in> lists (\<langle>A\<rangle> - {\<epsilon>})\<close> unfolding basis_def simple_element_def mem_Collect_eq by fast
    hence "\<^bold>|xs\<^bold>| = 1"
      using \<open>map f ys = xs\<close> by fastforce
    with \<open>concat xs = x\<close> \<open>xs \<in> lists \<BB> (f `\<langle>A\<rangle>)\<close>
    show "x \<in> \<BB> (f ` \<langle>A\<rangle>)"
      using len_one_concat_in by blast
  qed
qed

lemma inj_code_to_code: assumes "inj_on f \<langle>A\<rangle>" and "code A"
            shows "code (f ` A)"
proof
  fix xs ys
  assume "xs \<in> lists (f ` A)" and "ys \<in> lists (f ` A)"
  then obtain xs' ys' where "xs' \<in> lists A" and "map f xs' = xs" and "ys' \<in> lists A" and "map f ys' = ys"
    unfolding lists_image by blast
  assume "concat xs = concat ys"
  hence "f (concat xs') = f (concat ys')"
    by (simp add: \<open>map f xs' = xs\<close> \<open>map f ys' = ys\<close> \<open>xs' \<in> lists A\<close> \<open>ys' \<in> lists A\<close> genset_sub_lists morph_concat_concat_map)
  hence "concat xs' = concat ys'"
    using \<open>inj_on f \<langle>A\<rangle>\<close>[unfolded inj_on_def] \<open>xs' \<in> lists A\<close> \<open>ys' \<in> lists A\<close> by auto
  hence "xs' = ys'"
    using \<open>code A\<close>[unfolded code_def] \<open>xs' \<in> lists A\<close> \<open>ys' \<in> lists A\<close> by simp
  thus "xs = ys"
    using \<open>map f xs' = xs\<close> \<open>map f ys' = ys\<close> by blast
qed

end

locale  morphism =
  fixes f :: "'a list \<Rightarrow> 'b list"
  assumes morph: "f (u \<cdot> v) = f u \<cdot> f v"
begin

sublocale morphism_on f UNIV
  by (simp add: morph morphism_on.intro)

lemma map_core_lists[simp]: "map f\<^sup>\<C> xs \<in> lists (range f\<^sup>\<C>)"
  by auto

lemma pow_morph: "f (x\<^sup>@k) = (f x)\<^sup>@k"
  by (induction k) (simp add: morph)+

lemma rev_map_pow:  "(rev_map f) (w\<^sup>@n) = rev ((f (rev w))\<^sup>@n)"
  by (simp add: pow_morph rev_map_arg rev_pow)

lemma pop_hd: "f (a#u) = f [a] \<cdot> f u"
  unfolding hd_word[of a u] using morph.

lemma pop_hd_nemp: "u \<noteq> \<epsilon> \<Longrightarrow> f (u) = f [hd u] \<cdot> f (tl u)"
  using list.exhaust_sel pop_hd[of "hd u" "tl u"] by force

lemma pop_last_nemp: "u \<noteq> \<epsilon> \<Longrightarrow> f (u) = f (butlast u) \<cdot> f [last u]"
  unfolding morph[symmetric] append_butlast_last_id ..

lemma pref_mono: "u \<le>p v \<Longrightarrow> f u \<le>p f v"
  using morph by (auto simp add: prefix_def)

lemma suf_mono: "u \<le>s v \<Longrightarrow> f u \<le>s f v"
  using morph by (auto simp add: suffix_def)

lemma morph_concat_map: "concat (map f\<^sup>\<C> x) = f x"
  unfolding core_def
proof (induction x)
  case (Cons a x)
  then show ?case
    unfolding pop_hd[of a x] by auto
qed simp

lemma morph_concat_map': "(\<lambda> x. concat (map f\<^sup>\<C> x)) = f"
  using morph_concat_map by simp

lemma morph_to_concat:
  obtains xs where "xs \<in> lists (range f\<^sup>\<C>)" and "f x = concat xs"
proof-
  have "map f\<^sup>\<C> x \<in> lists (range f\<^sup>\<C>)"
    by fastforce
      from that[OF this morph_concat_map[symmetric]]
  show thesis.
qed

lemma range_hull: "range f = \<langle>(range f\<^sup>\<C>)\<rangle>"
  using arg_cong[OF range_map_core[of f], of "image concat", unfolded image_comp, folded hull_concat_lists] morph_concat_map by auto

lemma im_in_hull: "f w \<in> \<langle>(range f\<^sup>\<C>)\<rangle>"
  using range_hull by blast

lemma core_ext_id: "f\<^sup>\<C>\<^sup>\<L> = f"
using morph_concat_map unfolding list_extension_def core_def by simp

lemma  rev_map_morph: "morphism (rev_map f)"
  by (standard, auto simp add: rev_map_def morph)

lemma morph_rev_len:  "\<^bold>|f (rev u)\<^bold>| = \<^bold>|f u\<^bold>|"
proof (induction u)
  case (Cons a u)
  then show ?case
    unfolding rev.simps(2) pop_hd[of a u] morph lenmorph by force
qed simp

lemma  rev_map_len: "\<^bold>|rev_map f u\<^bold>| = \<^bold>|f u\<^bold>|"
  unfolding rev_map_def
  by (simp add: morph_rev_len)

lemma in_set_morph_len: assumes "a \<in> set w" shows "\<^bold>|f [a]\<^bold>| \<le> \<^bold>|f w\<^bold>|"
proof-
  from split_listE[OF assms]
  obtain p s where "w = p \<cdot> [a] \<cdot> s".
  from lenarg[OF arg_cong[of _ _ f, OF this], unfolded morph lenmorph]
  show ?thesis by linarith
qed

lemma morph_lq_comm: "u \<le>p v \<Longrightarrow> f (u\<inverse>\<^sup>>v) = (f u)\<inverse>\<^sup>>(f v)"
  using morph by (auto simp add: prefix_def)

lemma morph_rq_comm: assumes "v \<le>s u"
  shows "f (u\<^sup><\<inverse>v) = (f u)\<^sup><\<inverse>(f v)"
  using arg_cong[OF rq_suf[OF \<open>v \<le>s u\<close>], of f, unfolded morph, THEN rqI, symmetric].

lemma code_set_morph: assumes c: "code (f\<^sup>\<C> `(set (u \<cdot> v)))" and i: "inj_on f\<^sup>\<C> (set (u \<cdot> v))"
 and "f u = f v"
  shows "u = v"
proof-
  let ?C = "f\<^sup>\<C> `(set (u \<cdot> v))"
  interpret code ?C
    using c by blast
  have "(map f\<^sup>\<C> u) \<in> lists ?C" and "(map f\<^sup>\<C> v) \<in> lists ?C"
    by (simp_all add: in_listsI)
  from is_code[OF this \<open>f u = f v\<close>[folded morph_concat_map]]
  show "u = v"
    using  inj_on_map_lists[OF i] unfolding inj_on_def
    by (simp add: in_listsI)
qed

lemma morph_concat_concat_map: "f (concat ws) = concat (map f ws)"
  by (induct ws, simp_all add: morph)

lemma morph_on: "morphism_on f A"
  unfolding morphism_on_def using morph by blast

lemma noner_sings_conv: "(\<forall> w. w = \<epsilon> \<longleftrightarrow> f w = \<epsilon>) \<longleftrightarrow> (\<forall> a. f [a] \<noteq> \<epsilon>)"
  by (rule iffI, blast)
   (metis Nil_is_append_conv emp_to_emp' hd_tlE pop_hd)

lemma fac_mono: "u \<le>f w \<Longrightarrow> f u \<le>f f w"
  using morph by fastforce

lemma set_core_set: "set (f w) = \<Union> (set ` f\<^sup>\<C> ` (set w))"
  unfolding list.set_map[symmetric]
  unfolding image_set[of set "(map f\<^sup>\<C> w)", symmetric]
  unfolding morph_concat_map[symmetric, of w]
  using set_concat.

end

lemma morph_map: "morphism (map f)"
  by (simp add: morphism_def)

lemma list_ext_morph: "morphism t\<^sup>\<L>"
  unfolding list_extension_def by (simp add: morphism_def)

lemma ext_def_on_set: "(\<And> a. a \<in> set u \<Longrightarrow> g a = f a) \<Longrightarrow> g\<^sup>\<L> u = f\<^sup>\<L> u"
  unfolding list_extension_def using map_ext by metis

lemma morph_def_on_set: "morphism f \<Longrightarrow> morphism g \<Longrightarrow> (\<And> a. a \<in> set u \<Longrightarrow> g\<^sup>\<C> a = f\<^sup>\<C> a) \<Longrightarrow> g u = f u"
  using ext_def_on_set morphism.core_ext_id by metis

lemma morph_compose: "morphism f \<Longrightarrow> morphism g \<Longrightarrow> morphism (f \<circ> g)"
  by (simp add: morphism_def)

subsection \<open>Periodic morphism\<close>

locale periodic_morphism = morphism +
  assumes ims_comm: "\<And> u v. f u \<cdot> f v = f v \<cdot> f u" and
    not_triv_emp: "\<not> (\<forall> c. f [c] =  \<epsilon>)"
begin

lemma per_morph_root_ex:
  "\<exists> r. \<forall> u. \<exists> n. f u = r\<^sup>@n \<and> primitive r"
proof-
  obtain c root n where "f[c] = root\<^sup>@n" and "root = \<rho> (f [c])" and "f [c] \<noteq> \<epsilon>"
    using primroot_expE not_triv_emp by metis
  have "\<exists> n. f u = root\<^sup>@n" for u
    using comm_primroot_exp[OF \<open>f [c] \<noteq> \<epsilon>\<close>, OF ims_comm, folded \<open>root = \<rho> (f [c])\<close>] by metis
  thus ?thesis
    using \<open>root = \<rho> (f [c])\<close> \<open>f [c] \<noteq> \<epsilon>\<close> by auto
qed

definition mroot where "mroot \<equiv> (SOME r. (\<forall> u. \<exists> n. f u = r\<^sup>@n) \<and> primitive r)"
definition mexp :: "'a \<Rightarrow> nat" where "mexp c \<equiv> (SOME n. f [c] = mroot\<^sup>@n)"

lemma per_morph_rootI: "\<forall> u. \<exists> n. f u = mroot\<^sup>@n" and
  per_morph_root_prim: "primitive mroot"
  using per_morph_root_ex exE_some[of "\<lambda> r. \<forall>u. \<exists>n. f u = r \<^sup>@ n \<and> primitive r", of mroot]
  unfolding mroot_def by auto

lemma per_morph_expI': "f [c] = mroot\<^sup>@(mexp c)"
  using per_morph_rootI exE_some[of "\<lambda> n. f [c] = mroot \<^sup>@ n", of "mexp c"]
  unfolding mexp_def by blast

lemma per_morph_expE:
  obtains n where "f u = mroot\<^sup>@n"
  using per_morph_rootI by auto

interpretation mirror: periodic_morphism "rev_map f"
proof
  show "rev_map f (u \<cdot> v) = rev_map f u \<cdot> rev_map f v" for u v
    using  morphism.morph[OF rev_map_morph].
  show "rev_map f u \<cdot> rev_map f v = rev_map f v \<cdot> rev_map f u" for u v
    unfolding comm_rev_iff ims_comm rev_map_arg..
  show "\<not> (\<forall>c. rev_map f [c] = \<epsilon>)"
    using not_triv_emp unfolding rev_map_sing by blast
qed

lemma mroot_rev: "mirror.mroot = rev mroot"
proof-
  have "primitive (rev mroot)"
    using per_morph_root_prim prim_rev_iff by blast
  obtain u where "f u \<noteq> \<epsilon>"
    using not_triv_emp by auto
  obtain n where "f u = mroot\<^sup>@n"
    using per_morph_expE[of u].
  hence "0 < n"
    using \<open>f u \<noteq> \<epsilon>\<close> by blast
  obtain n' where "rev (f u) = mirror.mroot\<^sup>@n'" "0 < n'"
    using mirror.per_morph_expE rev_map_arg_rev
     \<open>f u \<noteq> \<epsilon>\<close>[folded Nil_is_rev_conv, symmetric]
    using bot_nat_0.not_eq_extremum zero_exp by metis
  from this(1)[unfolded \<open>f u = mroot\<^sup>@ n\<close>, unfolded rev_pow]
  have *: "rev mroot \<^sup>@  n = mirror.mroot \<^sup>@ n'".
  have "(rev mroot) \<cdot> mirror.mroot = mirror.mroot \<cdot> (rev mroot)"
    by (rule comm_drop_exps[OF _ \<open>0 < n\<close> \<open>0 < n'\<close>]) (use * in blast)
  thus ?thesis
    using comm_prim[OF \<open>primitive (rev mroot)\<close> mirror.per_morph_root_prim] by force
qed

end


subsection  \<open>Non-erasing morphism\<close>

locale nonerasing_morphism = morphism  +
  assumes nonerasing: "f w = \<epsilon> \<Longrightarrow> w = \<epsilon>"
begin

lemma core_nemp: "f\<^sup>\<C> a \<noteq> \<epsilon>"
  unfolding core_def using nonerasing not_Cons_self2 by blast

lemma nemp_to_nemp: "w \<noteq> \<epsilon> \<Longrightarrow> f w \<noteq> \<epsilon>"
  using nonerasing by blast

lemma sing_to_nemp: "f [a] \<noteq> \<epsilon>"
  by (simp add: nemp_to_nemp)

lemma pref_morph_pref_eq: "u \<le>p v \<Longrightarrow> f v \<le>p f u \<Longrightarrow> u = v"
  using nonerasing morph[of u "u\<inverse>\<^sup>>v"] unfolding prefix_def by fastforce

lemma comm_eq_im_eq:
  "u \<cdot> v = v \<cdot> u \<Longrightarrow> f u = f v \<Longrightarrow> u = v"
  by (elim ruler_eqE)
     (simp_all add: pref_morph_pref_eq pref_morph_pref_eq[symmetric])

lemma comm_eq_im_iff :
  assumes "u \<cdot> v = v \<cdot> u"
  shows "f u = f v \<longleftrightarrow> u = v"
  using comm_eq_im_eq[OF \<open>u \<cdot> v = v \<cdot> u\<close>] by blast

lemma rev_map_nonerasing: "nonerasing_morphism (rev_map f)"
proof
  show "rev_map f (u \<cdot> v) = rev_map f u \<cdot> rev_map f v" for u v
    by (simp add: morphism.morph rev_map_morph)
  show "rev_map f w = \<epsilon> \<Longrightarrow> w = \<epsilon>" for w
    unfolding rev_map_arg using rev_is_Nil_conv nonerasing by fast
qed

lemma first_of_first: "(f (a # ws))!0 = f [a]!0"
  unfolding pop_hd[of a ws] using  hd_prod[of "f[a]" "f ws", OF
      nonerasing[of "[a]", THEN contrapos_nn[OF not_Cons_self2[of a \<epsilon>], of \<open>f (a # \<epsilon>) = \<epsilon>\<close>]]].

lemma hd_im_hd_hd: assumes "u \<noteq> \<epsilon>" shows "hd (f u) = hd (f [hd u])"
  unfolding hd_append2[OF sing_to_nemp] pop_hd_nemp[OF \<open>u \<noteq> \<epsilon>\<close>]..

lemma ssuf_mono: "u <s v \<Longrightarrow> f u <s f v"
  by (elim strict_suffixE')
  (use morph sing_to_nemp ssufI1 suf_nemp in metis)

lemma im_len_le: "\<^bold>|u\<^bold>| \<le> \<^bold>|f u\<^bold>|"
proof (induct u)
  case (Cons a u)
  show ?case
    unfolding hd_word[of a u] morph lenmorph sing_len
    by (rule add_mono[OF _ \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|f u\<^bold>|\<close>], use nemp_le_len[OF sing_to_nemp] in force)
qed simp

lemma im_len_eq_iff: "\<^bold>|u\<^bold>| = \<^bold>|f u\<^bold>| \<longleftrightarrow> (\<forall> c. c \<in> set u \<longrightarrow> \<^bold>|f [c]\<^bold>| = 1)"
proof (induct u)
  case (Cons a u)
  show ?case
  proof
    assume "\<^bold>|a # u\<^bold>| = \<^bold>|f (a # u)\<^bold>|"
    from this[unfolded  hd_word[of a u] morph lenmorph sing_len]
    have "\<^bold>|f [a]\<^bold>| = 1" and "\<^bold>|u\<^bold>| = \<^bold>|f u\<^bold>|"
      unfolding sing_len[of a, symmetric] using  im_len_le[of "[a]"] im_len_le[of u] by auto
    from this(2)[unfolded Cons.hyps] this(1)
    show "\<forall>c. c \<in> set (a # u) \<longrightarrow> \<^bold>|f [c]\<^bold>| = 1" by auto
  next
    assume "\<forall>c. c \<in> set (a # u) \<longrightarrow> \<^bold>|f [c]\<^bold>| = 1"
    hence all: "\<forall>c. c \<in> set u \<longrightarrow> \<^bold>|f [c]\<^bold>| = 1" and "\<^bold>|f [a]\<^bold>| = 1"
      by simp_all
    show "\<^bold>|a # u\<^bold>| = \<^bold>|f (a # u)\<^bold>|"
      unfolding hd_word[of a u] morph lenmorph sing_len \<open>\<^bold>|f [a]\<^bold>| = 1\<close> all[folded Cons.hyps]..
  qed
qed simp

lemma im_len_less: "a \<in> set u \<Longrightarrow> \<^bold>|f [a]\<^bold>| \<noteq> 1 \<Longrightarrow> \<^bold>|u\<^bold>| < \<^bold>|f u\<^bold>|"
  using im_len_le im_len_eq_iff order_le_neq_trans by auto

end

lemma (in morphism) nonerI[intro]: assumes "(\<And> a. f\<^sup>\<C> a \<noteq> \<epsilon>)"
  shows "nonerasing_morphism f"
proof
  from assms[unfolded core_def] noner_sings_conv
  show "\<And>w. f w = \<epsilon> \<Longrightarrow> w = \<epsilon>" by presburger
qed

lemma (in morphism) prim_morph_noner:
  assumes prim_morph: "\<And>u. 2 \<le> \<^bold>|u\<^bold>| \<Longrightarrow> primitive u \<Longrightarrow> primitive (f u)"
  and non_single_dom: "\<exists>a b :: 'a. a \<noteq> b"
    shows "nonerasing_morphism f"
proof (intro nonerI notI)
  fix a
  assume "f\<^sup>\<C> a = \<epsilon>"
  obtain c d :: "'a" where "c \<noteq> d"
    using non_single_dom by blast
  then obtain b where "a \<noteq> b"
    by (cases "a = c") simp_all
  then have "\<not> primitive (f ([a] \<cdot> [b] \<cdot> [b]))"
    using \<open>f\<^sup>\<C> a = \<epsilon>\<close> unfolding morph
    by (simp add: core_def eq_append_not_prim)
  have "primitive ([a] \<cdot> [b] \<cdot> [b])"
    using prim_abk[OF \<open>a \<noteq> b\<close>, of 2] by simp
  from prim_morph[OF _ this] \<open>\<not> primitive (f ([a] \<cdot> [b] \<cdot> [b]))\<close>
  show False
    by simp
qed

subsection \<open>Code morphism\<close>

text \<open>The term ``Code morphism'' is equivalent to ``injective morphism''.\<close>

text \<open>Note that this is not equivalent to @{term "code (range f\<^sup>\<C>)"}, since the core can be not injective.\<close>

lemma (in morphism) code_core_range_inj: "inj f \<longleftrightarrow> code (range f\<^sup>\<C>) \<and> inj f\<^sup>\<C>"
proof
  assume "inj f"
  show "code (range f\<^sup>\<C>) \<and> inj f\<^sup>\<C>"
  proof
    show "inj f\<^sup>\<C>"
      using \<open>inj f\<close> unfolding inj_on_def core_def by blast
    show "code (range f\<^sup>\<C>)"
    proof
      show
        "xs \<in> lists (range f\<^sup>\<C>) \<Longrightarrow> ys \<in> lists (range f\<^sup>\<C>) \<Longrightarrow> concat xs = concat ys \<Longrightarrow> xs = ys" for xs ys
        unfolding range_map_core[symmetric] using \<open>inj f\<close>[unfolded inj_on_def core_def] morph_concat_map
        by force
    qed
  qed
next
  assume "code (range f\<^sup>\<C>) \<and> inj f\<^sup>\<C>" hence "code (range f\<^sup>\<C>)" and "inj f\<^sup>\<C>" by blast+
  show "inj f"
  proof
    fix x y assume "f x = f y"
    with code.is_code[OF \<open>code (range f\<^sup>\<C>)\<close>, folded range_map_core, OF rangeI rangeI, unfolded morph_concat_map]
    have "map f\<^sup>\<C> x = map f\<^sup>\<C> y" by blast
    with \<open>inj f\<^sup>\<C>\<close>
    show "x = y" by simp
  qed
qed


locale code_morphism = morphism f for f +
   assumes code_morph: "inj f"

begin

lemma inj_core: "inj f\<^sup>\<C>"
  using code_morph unfolding core_def inj_on_def by blast

lemma sing_im_core: "f [a] \<in> (range f\<^sup>\<C>)"
  unfolding core_def by simp

lemma code_im: "code (range f\<^sup>\<C>)"
  using code_morph morph_concat_map unfolding inj_on_def code_def core_def
  unfolding lists_image lists_UNIV by fastforce

sublocale code "range f\<^sup>\<C>"
  using code_im.

sublocale nonerasing_morphism
  by (rule nonerI, simp add: nemp)

lemma code_morph_code: assumes "f r = f s" shows "r = s"
proof-
  from code.is_code[OF code_im, of "map f\<^sup>\<C> r" "map f\<^sup>\<C> s"]
  have "map f\<^sup>\<C> r = map f\<^sup>\<C> s"
    unfolding morph_concat_map using range_map_core assms by blast
  thus "r = s"
    unfolding inj_map_eq_map[OF inj_core].
qed

lemma code_morph_bij: "bij_betw f UNIV \<langle>(range f\<^sup>\<C>)\<rangle>"
  unfolding bij_betw_def
  by (rule disjE, simp_all add: range_hull)
     (rule injI,  simp add: code_morph_code)

lemma code_morphism_rev_map: "code_morphism (rev_map f)"
  unfolding code_morphism_def code_morphism_axioms_def
proof (rule conjI)
  show "inj (rev_map f)"
    using code_morph
    unfolding inj_def rev_map_arg rev_is_rev_conv
    using  rev_is_rev_conv by blast
qed (simp add: rev_map_morph)

lemma morph_on_inj_on:
  "morphism_on f A" "inj_on f A"
  using morph code_morph_code unfolding morphism_on_def inj_on_def
  by blast+

end

lemma (in morphism) code_morphismI: "inj f \<Longrightarrow> code_morphism f"
  by unfold_locales

lemma (in nonerasing_morphism) code_morphismI' :
  assumes comm: "\<And>u v. f u = f v \<Longrightarrow> u \<cdot> v = v \<cdot> u"
  shows "code_morphism f"
proof (unfold_locales, intro injI)
  fix u v
  assume "f u = f v"
  then have "u \<cdot> v =  v \<cdot> u"
    by (fact comm)
  from comm_eq_im_eq[OF this \<open>f u = f v\<close>]
  show "u = v".
qed

subsection \<open>Prefix code morphism\<close>

locale pref_code_morphism = nonerasing_morphism  +
  assumes
          pref_free: "f\<^sup>\<C> a \<le>p f\<^sup>\<C> b \<Longrightarrow> a = b"

begin

interpretation prefrange: pref_code "(range f\<^sup>\<C>)"
  by (unfold_locales, unfold image_iff)
  (use core_nemp in metis, use pref_free in fast)

lemma inj_core: "inj f\<^sup>\<C>"
  unfolding inj_on_def using pref_free by force

sublocale code_morphism
proof
  show "inj f"
 proof (rule injI)
    fix x y
    assume "f x =  f y"
    hence "map f\<^sup>\<C> x = map f\<^sup>\<C> y"
      using prefrange.is_code[folded range_map_core, of "map f\<^sup>\<C> x" "map f\<^sup>\<C> y"]
      unfolding morph_concat_map by fast
    with inj_core[folded inj_map[of "f\<^sup>\<C>"], unfolded inj_on_def]
    show "x = y"
      by fast
  qed
qed

thm nonerasing

lemma pref_free_morph: assumes "f r \<le>p f s" shows "r \<le>p s"
  using assms
proof (induction r s rule: list_induct2')
  case (2 x xs)
  then show ?case
    using emp_to_emp nonerasing prefix_bot.extremum_unique by auto
next
  case (3 y ys)
  then show ?case
    using emp_to_emp nonerasing prefix_bot.extremum_unique by blast
next
  case (4 x xs y ys)
  then show ?case
  proof-
    have "f\<^sup>\<C> x \<le>p f\<^sup>\<C> y \<cdot> f ys"
      unfolding core_def using "4.prems"[unfolded pop_hd[of x xs] pop_hd[of y ys], THEN  append_prefixD].
    from ruler_pref'[OF this] prefrange.pref_free[OF rangeI rangeI] inj_core
    have "x = y"
      unfolding inj_on_def by fastforce
    show ?case
      using "4.IH" "4.prems" unfolding  pop_hd[of x xs] pop_hd[of y ys]
      unfolding \<open>x = y\<close> by fastforce
  qed
qed simp

end

subsection \<open>Marked morphism\<close>

locale marked_morphism = nonerasing_morphism  +
  assumes
          marked_core: "hd (f\<^sup>\<C> a) = hd (f\<^sup>\<C> b) \<Longrightarrow> a = b"

begin

lemma marked_im: "marked_code (range f\<^sup>\<C>)"
  by (unfold_locales, unfold image_iff)
  (use marked_core core_nemp in metis)+

interpretation marked_code "(range f\<^sup>\<C>)"
  using marked_im.

lemmas marked_morph = marked_core[unfolded core_sing]

sublocale pref_code_morphism
  by (unfold_locales, simp_all add: core_nemp marked_core pref_hd_eq)

lemma hd_im_eq_hd_eq: assumes "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>"  and "hd (f u) = hd (f v)"
 shows "hd u = hd v"
  using   marked_morph[OF \<open>hd (f u) = hd (f v)\<close>[unfolded hd_im_hd_hd[OF \<open>u \<noteq> \<epsilon>\<close>] hd_im_hd_hd[OF \<open>v \<noteq> \<epsilon>\<close>]]].

lemma marked_morph_lcp: "f (r \<and>\<^sub>p s) = f r \<and>\<^sub>p f s"
  by (rule marked_concat_lcp[of "map f\<^sup>\<C> r" "map f\<^sup>\<C> s", unfolded map_lcp_conv[OF inj_core] morph_concat_map]) simp_all

lemma marked_inj_map: "inj e \<Longrightarrow> marked_morphism ((map e) \<circ> f)"
  unfolding inj_on_def
  by unfold_locales
  (simp add: morph, simp add: code_morph_code, simp add: core_def core_nemp nemp_to_nemp marked_core  list.map_sel(1) sing_to_nemp)

end

thm morphism.nonerI

lemma (in morphism) marked_morphismI:
  "(\<And> a. f[a] \<noteq> \<epsilon>) \<Longrightarrow> (\<And> a b. a \<noteq> b) \<Longrightarrow> hd (f[a]) \<noteq> hd (f[b]) \<Longrightarrow> marked_morphism f"
  by unfold_locales  presburger+

subsection "Image length"

definition max_image_length:: "('a list \<Rightarrow> 'b list) \<Rightarrow> nat" ("\<lceil>_\<rceil>")
  where "max_image_length f = Max (length`(range f\<^sup>\<C>))"

definition min_image_length::"('a list \<Rightarrow> 'b list) \<Rightarrow> nat" ("\<lfloor>_\<rfloor>" )
  where "min_image_length f = Min (length`(range f\<^sup>\<C>))"

lemma max_im_len_id: "\<lceil>id::('a list \<Rightarrow> 'a list)\<rceil> = 1" and min_im_len_id: "\<lfloor>id::('a list \<Rightarrow> 'a list)\<rfloor> = 1"
proof-
  have a1: "length ` range (\<lambda>x. [x]) = {1}"
    by force
  show "\<lceil>id::('a list \<Rightarrow> 'a list)\<rceil> = 1" and "\<lfloor>id::('a list \<Rightarrow> 'a list)\<rfloor> = 1"
    unfolding max_image_length_def min_image_length_def core_def id_apply a1
    by force+
qed

context morphism
begin

lemma max_im_len_le: "finite (length`range f\<^sup>\<C>) \<Longrightarrow> \<^bold>|f z\<^bold>| \<le> \<^bold>|z\<^bold>|*\<lceil>f\<rceil>"
proof(induction z)
  case (Cons a z)
  have "\<^bold>|f [a]\<^bold>| \<in> length`(range f\<^sup>\<C>)"
    by (simp add: core_def)
  hence "\<^bold>|f [a]\<^bold>| \<le> \<lceil>f\<rceil>"
    unfolding max_image_length_def
    using Cons.prems Max.coboundedI by metis
  thus ?case
    unfolding hd_word[of a z] morph[of "[a]" z]
    unfolding lenmorph
    using Cons.IH[OF Cons.prems] by auto
qed simp

lemma max_im_len_le_sing: assumes "finite (length`range f\<^sup>\<C>)"
  shows "\<^bold>|f [a]\<^bold>| \<le> \<lceil>f\<rceil>"
  using max_im_len_le[OF assms, of "[a]"]
  unfolding mult_1 sing_len.

lemma min_im_len_ge: "finite (length`range f\<^sup>\<C>) \<Longrightarrow>  \<^bold>|z\<^bold>| * \<lfloor>f\<rfloor> \<le> \<^bold>|f z\<^bold>|"
proof(induction z)
  case (Cons a z)
  have "\<^bold>|f [a]\<^bold>| \<in> length`(range f\<^sup>\<C>)"
    by (simp add: core_def)
  hence "\<lfloor>f\<rfloor> \<le> \<^bold>|f [a]\<^bold>|"
    unfolding min_image_length_def
    by (meson Cons.prems Min_le)
  thus ?case
    unfolding hd_word[of a z] morph[of "[a]" z]
    unfolding lenmorph
    using Cons.IH[OF Cons.prems] by auto
qed simp

lemma max_im_len_comp_le: assumes finite_f: "finite (length`range f\<^sup>\<C>)" and
  finite_g: "finite (length`range g\<^sup>\<C>)" and "morphism g"
  shows "finite (length ` range (g \<circ> f)\<^sup>\<C>)" "\<lceil>g \<circ> f\<rceil> \<le> \<lceil>f\<rceil>*\<lceil>g\<rceil>"
proof-
  interpret mg: morphism g
    by (simp add: \<open>morphism g\<close>)

  have "\<^bold>|g (f [x])\<^bold>| \<le> \<lceil>f\<rceil>*\<lceil>g\<rceil>" for x
  proof-
    have "\<^bold>|f [x]\<^bold>| \<le> \<lceil>f\<rceil>"
      using finite_f max_im_len_le_sing by presburger
    thus "\<^bold>|g (f [x])\<^bold>| \<le> \<lceil>f\<rceil>*\<lceil>g\<rceil>"
      by (meson finite_g le_trans mg.max_im_len_le mult_le_cancel2)
  qed
  hence "\<^bold>|(g o f)\<^sup>\<C> x\<^bold>| \<le> \<lceil>f\<rceil>*\<lceil>g\<rceil>" for x
    by (simp add: core_sing)
  hence "l \<in> length ` range (g \<circ> f)\<^sup>\<C> \<Longrightarrow> l \<le> \<lceil>f\<rceil>*\<lceil>g\<rceil>" for l
    by blast
  thus "finite (length ` range (g \<circ> f)\<^sup>\<C>)"
    using finite_nat_set_iff_bounded_le by metis
  from Max.boundedI[OF this]
  show "\<lceil>g o f\<rceil> \<le> \<lceil>f\<rceil>*\<lceil>g\<rceil>"
    using \<open>\<And>l. l \<in> length ` range (g \<circ> f)\<^sup>\<C> \<Longrightarrow> l \<le> \<lceil>f\<rceil> * \<lceil>g\<rceil>\<close>
    unfolding max_image_length_def
    by blast
qed

lemma max_im_len_emp: assumes "finite (length ` range f\<^sup>\<C>)"
  shows "\<lceil>f\<rceil> = 0 \<longleftrightarrow> (f = (\<lambda>w. \<epsilon>))"
  by (rule iffI, use max_im_len_le[OF assms] npos_len in force, simp add: core_def max_image_length_def)

lemmas max_im_len_le_dom = max_im_len_le[OF finite_imageI, OF finite_imageI] and
  max_im_len_le_sing_dom = max_im_len_le_sing[OF finite_imageI, OF finite_imageI] and
  min_im_len_ge_dom = min_im_len_ge[OF finite_imageI, OF finite_imageI] and
  max_im_len_comp_le_dom = max_im_len_comp_le[OF finite_imageI, OF finite_imageI] and
  max_im_len_emp_dom = max_im_len_emp[OF finite_imageI, OF finite_imageI]

end
subsection "Endomorphism"

locale endomorphism = morphism f for f:: "'a list \<Rightarrow> 'a list"
begin

lemma pow_endomorphism: "endomorphism (f^^k)"
  by (unfold_locales, induction k) (simp_all add: power.power.power_0 morph)

interpretation pow_endm: endomorphism "(f^^k)"
  using pow_endomorphism by blast


lemmas pow_morphism = pow_endm.morphism_axioms and
       pow_morph = pow_endm.morph and
       pow_emp_to_emp = pow_endm.emp_to_emp




lemma pow_sets_im: "set w = set v \<Longrightarrow> set ((f^^k) w) = set ((f^^k) v)"
  by(induct k, auto simp add: power.power.power_0 set_core_set)

lemma fin_len_ran_pow: "finite (length ` range f\<^sup>\<C>) \<Longrightarrow> finite (length ` range (f^^k)\<^sup>\<C>)"
proof(induction k)
  case 0
  have "(w::'a list) \<in> range (\<lambda>a. [a]) \<Longrightarrow> \<^bold>|w\<^bold>| = 1" for w
    by force
  thus ?case
    unfolding funpow_0 core_def
    using finite_nat_set_iff_bounded_le by auto
next
  case (Suc k)
  show ?case
    using pow_endm.max_im_len_comp_le(1)[of _ f, folded funpow.simps(2), OF Suc.IH, OF Suc.prems Suc.prems morphism_axioms].
qed

lemma max_im_len_pow_le: assumes "finite (length ` range f\<^sup>\<C>)" shows "\<lceil>f^^k\<rceil> \<le> \<lceil>f\<rceil>^k"
proof(induction k)
  have funpow_1: "f^^1 = f" by simp
  case (Suc k)
  show ?case
    using  mult_le_mono2[OF Suc.IH[OF Suc.prems], of "\<lceil>f ^^ 1\<rceil>"] pow_endm.max_im_len_comp_le(2)[OF fin_len_ran_pow, OF \<open>finite (length ` range f\<^sup>\<C>)\<close> \<open>finite (length ` range f\<^sup>\<C>)\<close> morphism_axioms]
    unfolding compow_Suc funpow_1 comp_apply
    unfolding power_class.power.power_Suc
    unfolding mult.commute[of "\<lceil>f\<rceil>"]
    using dual_order.trans by blast
qed (simp add: max_im_len_id[unfolded id_def])

lemma max_im_len_pow_le': "finite (length ` range f\<^sup>\<C>) \<Longrightarrow> \<^bold>|(f^^k) w\<^bold>| \<le> \<^bold>|w\<^bold>| * \<lceil>f\<rceil>^k"
  using fin_len_ran_pow le_trans max_im_len_pow_le mult_le_mono2 pow_endm.max_im_len_le by meson

lemmas max_im_len_pow_le_dom = max_im_len_pow_le[OF finite_imageI, OF finite_imageI] and
       max_im_len_pow_le'_dom = max_im_len_pow_le'[OF finite_imageI, OF finite_imageI]

lemma funpow_nonerasing_morphism: assumes "nonerasing_morphism f"
  shows "nonerasing_morphism (f^^k)"
proof(unfold_locales, induction k)
  case (Suc k)
  then show ?case
    using nonerasing_morphism.nonerasing[OF assms]
    unfolding compow_Suc' by blast
qed simp

lemma im_len_pow_mono: assumes "nonerasing_morphism f" "i \<le> j"
  shows "(\<^bold>|(f^^i) w\<^bold>| \<le> \<^bold>|(f^^j) w\<^bold>|)"
  using nonerasing_morphism.im_len_le[OF funpow_nonerasing_morphism[of "j-i"], OF \<open>nonerasing_morphism f\<close>, of "(f^^i) w"]
  using funpow_add[unfolded comp_apply, of "j-i" i f]
  unfolding diff_add[OF \<open>i \<le> j\<close>]
  by simp

lemma fac_mono_pow: "u \<le>f (f^^k) w \<Longrightarrow> (f^^l) u \<le>f (f^^(l+k)) w"
  by (simp add: funpow_add pow_endm.fac_mono)

lemma rev_map_endomorph: "endomorphism (rev_map f)"
  by (simp add: endomorphism.intro rev_map_morph)

end
section \<open>Primitivity preserving morphisms\<close>

locale primitivity_preserving_morphism = nonerasing_morphism +
  assumes prim_morph : "2 \<le> \<^bold>|u\<^bold>| \<Longrightarrow> primitive u \<Longrightarrow> primitive (f u)"
begin

sublocale code_morphism
proof (rule code_morphismI', rule nemp_comm)
  fix u v
  assume "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" and "f u = f v"
  then have "2 \<le> \<^bold>|u \<cdot> v\<^bold>|" and "2 \<le> \<^bold>|u \<cdot> v \<cdot> v\<^bold>|"
    by (simp_all flip: len_nemp_conv)
  moreover have "\<not> primitive (f (u \<cdot> v))" and "\<not> primitive (f (u \<cdot> v \<cdot> v))"
    using pow_nemp_imprim[of 2] pow_nemp_imprim[of 3] unfolding numeral_nat
    by (simp_all add: morph \<open>f u = f v\<close>) assumption+
  ultimately have "\<not> primitive (u \<cdot> v)" and "\<not> primitive (u \<cdot> v \<cdot> v)"
    by (intro notI; elim prim_morph[rotated, elim_format], blast+)+
  then show "u \<cdot> v = v \<cdot> u"
    by (fact imprim_ext_suf_comm)
qed

lemmas code_morph = code_morph

end

section \<open>Two morphisms\<close>

text \<open>Solutions and the coincidence pairs are defined for any two mappings\<close>

subsection \<open>Solutions\<close>

definition minimal_solution :: "'a list \<Rightarrow> ('a list \<Rightarrow> 'b list) \<Rightarrow> ('a list \<Rightarrow> 'b list) \<Rightarrow> bool"
  ("_ \<in> _ =\<^sub>M _" [80,80,80] 51 )
  where min_sol_def:  "minimal_solution s g h \<equiv> s \<noteq> \<epsilon> \<and> g s = h s
      \<and> (\<forall> s'. s' \<noteq> \<epsilon> \<and> s' \<le>p s \<and> g s' = h s' \<longrightarrow> s' = s)"

lemma min_solD: "s \<in> g =\<^sub>M h \<Longrightarrow> g s = h s"
  using min_sol_def by blast

lemma min_solD': "s \<in> g =\<^sub>M h \<Longrightarrow> s \<noteq> \<epsilon>"
  using min_sol_def by blast

lemma min_solD_min: "s \<in> g =\<^sub>M h \<Longrightarrow> p \<noteq> \<epsilon> \<Longrightarrow> p \<le>p s \<Longrightarrow> g p = h p \<Longrightarrow> p = s"
  by (simp add: min_sol_def)

lemma min_solI[intro]: "s \<noteq> \<epsilon> \<Longrightarrow> g s = h s \<Longrightarrow> (\<And> s'. s'\<le>p s \<Longrightarrow> s' \<noteq> \<epsilon>  \<Longrightarrow>  g s' = h s' \<Longrightarrow> s' = s) \<Longrightarrow> s \<in> g =\<^sub>M h"
  using min_sol_def by metis

lemma min_sol_sym_iff: "s \<in> g =\<^sub>M h  \<longleftrightarrow> s \<in> h =\<^sub>M g"
  unfolding min_sol_def  eq_commute[of "g _" "h _"] by blast

lemma min_sol_sym[sym]: "s \<in> g =\<^sub>M h  \<Longrightarrow> s \<in> h =\<^sub>M g"
  unfolding min_sol_def eq_commute[of "g _"].

lemma min_sol_prefE:
  assumes "g r = h r" and "r \<noteq> \<epsilon>"
  obtains e where  "e \<in> g =\<^sub>M h" and "e \<le>p r"
proof-
  let ?min = "\<lambda> n. take n r \<noteq> \<epsilon> \<and> g (take n r) = h (take n r)"
  have "?min \<^bold>|r\<^bold>|"
    using assms by force
  define n where "n = (LEAST n. ?min n)"
  define e where "e = take n r"
  from Least_le[of ?min, folded n_def, OF \<open>?min \<^bold>|r\<^bold>|\<close>]
  have "n = \<^bold>|e\<^bold>|"
    unfolding e_def by simp
  show thesis
  proof (rule that)
    show "e \<le>p r"
      unfolding e_def using take_is_prefix by blast
    show "e \<in> g =\<^sub>M h"
    proof (rule min_solI)
      from LeastI[of ?min, OF \<open>?min \<^bold>|r\<^bold>|\<close>, folded n_def e_def]
      show "e \<noteq> \<epsilon>" and "g e = h e"
        by blast+
      show min: "s = e" if "s \<le>p e" "s \<noteq> \<epsilon>" "g s = h s" for s
      proof-
        have "\<^bold>|s\<^bold>| \<le> \<^bold>|e\<^bold>|"
          using pref_len[OF \<open>s \<le>p e\<close>].
        hence "take \<^bold>|s\<^bold>| r = s"
          using \<open>s \<le>p e\<close> pref_take unfolding e_def by fastforce
        from not_less_Least[of "\<^bold>|s\<^bold>|" ?min, folded e_def n_def, unfolded this]
        show "s = e"
          using that leI long_pref unfolding \<open>n = \<^bold>|e\<^bold>|\<close> by fast
      qed
    qed
  qed
qed

subsection \<open>Coincidence pairs\<close>

definition coincidence_set :: "('a list \<Rightarrow> 'b list) \<Rightarrow> ('a list \<Rightarrow> 'b list) \<Rightarrow> ('a list \<times> 'a list) set" ("\<CC>")
  where "coincidence_set g h \<equiv> {(r,s). g r = h s}"

lemma coin_set_eq: "(g \<circ> fst)`(\<CC> g h) = (h \<circ> snd)`(\<CC> g h)"
  unfolding coincidence_set_def comp_apply using Product_Type.Collect_case_prodD[of _ "\<lambda> x y. g x = h y"] image_cong by auto

lemma coin_setD: "pair \<in> \<CC> g h \<Longrightarrow> g (fst pair) = h (snd pair)"
  unfolding coincidence_set_def by force

lemma coin_setD_iff: "pair \<in> \<CC> g h \<longleftrightarrow> g (fst pair) = h (snd pair)"
  unfolding coincidence_set_def by force

lemma coin_set_sym: "fst`(\<CC> g h) = snd `(\<CC> h g)"
  unfolding coincidence_set_def
  by (rule set_eqI) (auto simp add: image_iff, metis)

lemma coin_set_inter_fst: "(g \<circ> fst)`(\<CC> g h) = range g \<inter> range h"
proof
  show "(g \<circ> fst) ` \<CC> g h \<subseteq> range g \<inter> range h"
  proof
    fix x assume "x \<in> (g \<circ> fst) ` \<CC> g h"
    then obtain pair where "x = g (fst pair)" and "pair \<in> \<CC> g h"
      by force
    from this(1)[unfolded coin_setD[OF this(2)]] this(1)
    show "x \<in> range g \<inter> range h" by blast
  qed
next
  show "range g \<inter> range h \<subseteq> (g \<circ> fst) ` \<CC> g h"
  proof
    fix x assume "x \<in> range g \<inter> range h"
    then obtain r s where "g r = h s" and "x = g r" by blast
    hence "(r,s) \<in> \<CC> g h"
      unfolding coincidence_set_def by blast
    thus "x \<in> (g \<circ> fst) ` \<CC> g h"
      unfolding \<open>x = g r\<close> by force
  qed
qed

lemmas coin_set_inter_snd = coin_set_inter_fst[unfolded coin_set_eq]

definition minimal_coincidence :: "('a list \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> ('a list \<Rightarrow> 'b list) \<Rightarrow>  'a list \<Rightarrow> bool" ("(_ _) =\<^sub>m (_ _)" [80,81,80,81] 51 )
  where min_coin_def:  "minimal_coincidence g r h s \<equiv> r \<noteq> \<epsilon> \<and> s \<noteq> \<epsilon> \<and> g r = h s \<and> (\<forall> r' s'. r' \<le>np r \<and> s' \<le>np s \<and> g r' = h s' \<longrightarrow> r' = r \<and> s' = s)"

definition min_coincidence_set :: "('a list \<Rightarrow> 'b list) \<Rightarrow> ('a list \<Rightarrow> 'b list) \<Rightarrow> ('a list \<times> 'a list) set" ("\<CC>\<^sub>m")
  where "min_coincidence_set g h \<equiv> ({(r,s) . g r =\<^sub>m h s})"

lemma min_coin_minD: "g r =\<^sub>m h s \<Longrightarrow> r' \<le>np r \<Longrightarrow> s' \<le>np s \<Longrightarrow>  g r' = h s' \<Longrightarrow> r' = r \<and> s' = s"
  using min_coin_def by blast

lemma min_coin_setD: "p \<in> \<CC>\<^sub>m g h \<Longrightarrow> g (fst p) =\<^sub>m h (snd p)"
  unfolding min_coincidence_set_def by force

lemma min_coinD: "g r =\<^sub>m h s \<Longrightarrow> g r = h s"
  using min_coin_def by blast

lemma min_coinD': "g r =\<^sub>m h s \<Longrightarrow> r \<noteq> \<epsilon> \<and> s \<noteq> \<epsilon>"
  using min_coin_def by blast

lemma min_coin_sub: "\<CC>\<^sub>m g h \<subseteq> \<CC> g h"
  unfolding coincidence_set_def min_coincidence_set_def
  using  min_coinD by blast

lemma min_coin_defI: assumes "r \<noteq> \<epsilon>" and "s \<noteq> \<epsilon>" and  "g r = h s" and
      "(\<And> r' s'. r' \<le>np r \<Longrightarrow> s' \<le>np s \<Longrightarrow> g r' = h s' \<Longrightarrow> r' = r \<and> s' = s)"
   shows "g r =\<^sub>m h s"
  unfolding min_coin_def[rule_format] using assms by blast

lemma min_coin_sym[sym]: "g r =\<^sub>m h s \<Longrightarrow> h s =\<^sub>m g r"
  unfolding min_coin_def eq_commute[of "g _" "h _"] by blast

lemma min_coin_sym_iff: "g r =\<^sub>m h s \<longleftrightarrow> h s =\<^sub>m g r"
  using min_coin_sym by auto

lemma min_coin_set_sym: "fst`(\<CC>\<^sub>m g h) = snd `(\<CC>\<^sub>m h g)"
  unfolding min_coincidence_set_def image_iff
  by (rule set_eqI, rule iffI) (simp_all add: image_iff min_coin_sym_iff)

subsection \<open>Basics\<close>

locale two_morphisms = g: morphism g + h: morphism h for g h :: "'a list \<Rightarrow> 'b list"

begin

lemma def_on_sings:
  assumes "\<And>a. a \<in> set u \<Longrightarrow> g [a] = h [a]"
  shows "g u = h u"
using assms
proof (induct u)
next
  case (Cons a u)
  then show ?case
    unfolding g.pop_hd[of a u] h.pop_hd[of a u] using assms by simp
qed simp

lemma def_on_sings_eq:
  assumes "\<And>a. g [a] = h [a]"
  shows "g = h"
  using def_on_sings[OF assms]
  by (simp add: ext)

lemma ims_prefs_comp:
  assumes "u \<le>p u'" and "v \<le>p v'" and "g u' \<bowtie> h v'" shows  "g u \<bowtie> h v"
  using ruler_comp[OF g.pref_mono h.pref_mono, OF assms].

lemma ims_sufs_comp:
  assumes "u \<le>s u'" and "v \<le>s v'" and "g u' \<bowtie>\<^sub>s h v'" shows  "g u \<bowtie>\<^sub>s h v"
  using suf_ruler_comp[OF g.suf_mono h.suf_mono, OF assms].

lemma ims_hd_eq_comp:
  assumes "u \<noteq> \<epsilon>" and "g u = h u" shows "g [hd u] \<bowtie> h [hd u]"
  using ims_prefs_comp[OF hd_pref[OF \<open>u \<noteq> \<epsilon>\<close>] hd_pref[OF \<open>u \<noteq> \<epsilon>\<close>]]
  unfolding \<open>g u = h u\<close> by blast

lemma ims_last_eq_suf_comp:
  assumes "u \<noteq> \<epsilon>" and "g u = h u" shows "g [last u] \<bowtie>\<^sub>s h [last u]"
  using ims_sufs_comp[OF hd_pref[reversed, OF \<open>u \<noteq> \<epsilon>\<close>] hd_pref[reversed, OF \<open>u \<noteq> \<epsilon>\<close>]]
  unfolding \<open>g u = h u\<close> using comp_refl[reversed] by blast

lemma len_im_le:
  assumes "(\<And>a. a \<in> set s \<Longrightarrow> \<^bold>|g [a]\<^bold>| \<le> \<^bold>|h [a]\<^bold>|)"
  shows "\<^bold>|g s\<^bold>| \<le> \<^bold>|h s\<^bold>|"
using assms proof (induction s)
  case (Cons a s)
    have IH_prem: "\<And>a. a \<in> set s \<Longrightarrow> \<^bold>|g [a]\<^bold>| \<le> \<^bold>|h [a]\<^bold>|" using Cons.prems by simp
    show "\<^bold>|g (a # s)\<^bold>| \<le> \<^bold>|h (a # s)\<^bold>|"
      unfolding g.pop_hd[of _ s] h.pop_hd[of _ s] lenmorph
      using Cons.prems[of a, simplified] Cons.IH[OF IH_prem]
      by (rule add_le_mono)
qed simp

lemma len_im_less:
  assumes "\<And>a. a \<in> set s \<Longrightarrow> \<^bold>|g [a]\<^bold>| \<le> \<^bold>|h [a]\<^bold>|" and
          "b \<in> set s" and "\<^bold>|g [b]\<^bold>| < \<^bold>|h [b]\<^bold>|"
  shows "\<^bold>|g s\<^bold>| < \<^bold>|h s\<^bold>|"
using assms proof (induction s arbitrary: b)
  case (Cons a s)
    have IH_prem: "\<And>a. a \<in> set s \<Longrightarrow> \<^bold>|g [a]\<^bold>| \<le> \<^bold>|h [a]\<^bold>|" using Cons.prems(1)[OF list.set_intros(2)].
    note split = g.pop_hd[of _ s] h.pop_hd[of _ s] lenmorph
    show "\<^bold>|g (a # s)\<^bold>| < \<^bold>|h (a # s)\<^bold>|"
    proof (cases)
      assume "a = b" show "\<^bold>|g (a # s)\<^bold>| < \<^bold>|h (a # s)\<^bold>|"
        unfolding split \<open>a = b\<close> using \<open>\<^bold>|g [b]\<^bold>| < \<^bold>|h [b]\<^bold>|\<close> len_im_le[OF IH_prem]
        by (rule add_less_le_mono)
    next
      assume "a \<noteq> b"
      then have "b \<in> set s" using \<open>b \<in> set (a # s)\<close> by simp
      show "\<^bold>|g (a # s)\<^bold>| < \<^bold>|h (a # s)\<^bold>|"
        unfolding split using Cons.prems(1)[OF list.set_intros(1)]
          Cons.IH[OF IH_prem \<open>b \<in> set s\<close> \<open>\<^bold>|g [b]\<^bold>| < \<^bold>|h [b]\<^bold>|\<close>]
        by (rule add_le_less_mono)
    qed
qed simp

lemma solution_eq_len_eq:
  assumes "g s = h s" and "\<And>a. a \<in> set s \<Longrightarrow> \<^bold>|g [a]\<^bold>| = \<^bold>|h [a]\<^bold>|"
  shows "\<And>a. a \<in> set s \<Longrightarrow> g [a] = h [a]"
using assms proof (induction s)
  case (Cons b s)
  have nemp: "b # s \<noteq> \<epsilon>" using list.distinct(2).
  from ims_hd_eq_comp[OF nemp \<open>g (b # s) = h (b # s)\<close>] Cons.prems(3)[OF list.set_intros(1)]
  have *: "g [b] = h [b]" unfolding list.sel(1) by (fact pref_comp_eq)
  moreover have "g s = h s"
    using \<open>g (b # s) = h (b # s)\<close>
    unfolding g.pop_hd_nemp[OF nemp] h.pop_hd_nemp[OF nemp] list.sel * ..
  from Cons.IH[OF _ this Cons.prems(3)[OF list.set_intros(2)]]
  have "a \<in> set s \<Longrightarrow> g [a] = h [a]" for a.
  ultimately show "\<And>a. a \<in> set (b # s) \<Longrightarrow> g [a] = h [a]" by auto
qed auto

lemma rev_maps: "two_morphisms (rev_map g) (rev_map h)"
  using g.rev_map_morph h.rev_map_morph by (intro two_morphisms.intro)

lemma min_solD_min_suf: assumes "sol \<in> g =\<^sub>M h" and "s \<noteq> \<epsilon>" "s \<le>s sol" and "g s = h s"
  shows "s = sol"
proof (rule ccontr)
  assume "s \<noteq> sol"
  from sufE[OF \<open>s \<le>s sol\<close>]
  obtain y where "sol = y \<cdot> s".
  hence "y \<noteq> \<epsilon>"
    using \<open>s \<noteq> sol\<close> by force
  have "g y = h y"
    using min_solD[OF \<open>sol \<in> g =\<^sub>M h\<close>, unfolded \<open>sol = y \<cdot> s\<close>]
    unfolding g.morph h.morph \<open>g s = h s\<close> by blast
  from min_solD_min[OF \<open>sol \<in> g =\<^sub>M h\<close> \<open>y \<noteq> \<epsilon>\<close> _ this]
  have "y = sol"
    using \<open>sol = y \<cdot> s\<close> by blast
  thus False
    using \<open>sol = y \<cdot> s\<close> \<open>s \<noteq> \<epsilon>\<close> by fast
qed

lemma min_sol_rev[reversal_rule]:
  assumes "s \<in> g =\<^sub>M h"
  shows "(rev s) \<in> (rev_map g) =\<^sub>M (rev_map h)"
  unfolding min_sol_def[of _ "rev_map g" "rev_map h", reversed]
  using min_solD[OF assms] min_solD'[OF assms] min_solD_min_suf[OF assms] by blast

lemma coin_set_lists_concat: "ps \<in> lists (\<CC> g h) \<Longrightarrow> g (concat (map fst ps)) = h (concat (map snd ps))"
  unfolding coincidence_set_def
  by (induct ps, simp, auto simp add: g.morph h.morph)

lemma coin_set_hull: "\<langle>snd `(\<CC> g h)\<rangle> = snd `(\<CC> g h)"
proof (rule equalityI, rule subsetI)
  fix x assume "x \<in> \<langle>snd ` \<CC> g h\<rangle>"
  then obtain xs where "xs \<in> lists (snd ` \<CC> g h)" and "concat xs = x"
    using hull_concat_lists0 by blast
  then obtain ps where "ps \<in> lists (\<CC> g h)" and "map snd ps = xs"
    unfolding image_iff lists_image by blast
  from coin_set_lists_concat[OF this(1), unfolded this(2) \<open>concat xs = x\<close>]
  show "x \<in> snd ` \<CC> g h"
    unfolding coincidence_set_def by force
qed simp

lemma min_sol_sufE:
  assumes "g r = h r" and "r \<noteq> \<epsilon>"
  obtains e where  "e \<in> g =\<^sub>M h" and "e \<le>s r"
  using assms
proof (induction "\<^bold>|r\<^bold>|" arbitrary: r thesis rule: less_induct)
    case less
    then show thesis
    proof-
     from min_sol_prefE[of g r h, OF \<open>g r = h r\<close> \<open>r \<noteq> \<epsilon>\<close>]
  obtain p where "p \<in> g =\<^sub>M h" and "p \<le>p r".
  show thesis
    proof (cases "p = r", (use less.prems(1)[OF \<open>p \<in> g =\<^sub>M h\<close>] in fast))
      assume "p \<noteq> r"
      from prefE[OF \<open>p \<le>p r\<close>]
      obtain r' where "r = p \<cdot> r'".
      have "g r' = h r'"
        using \<open>g r = h r\<close>[unfolded \<open>r = p \<cdot> r'\<close> g.morph h.morph min_solD[OF \<open>p \<in> g =\<^sub>M h\<close>] cancel].
      from \<open>p \<noteq> r\<close> \<open>r = p \<cdot> r'\<close>
      have "r' \<noteq> \<epsilon>" by fast
      from min_solD'[OF \<open>p \<in> g =\<^sub>M h\<close>] \<open>r = p \<cdot> r'\<close>
      have "\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|" by fastforce
      from less.hyps[OF this _ \<open>g r' = h r'\<close> \<open>r' \<noteq> \<epsilon>\<close>]
      obtain e where "e \<in> g =\<^sub>M h" "e \<le>s r'".
      from less.prems(1)[OF this(1), unfolded \<open>r = p \<cdot> r'\<close>, OF suf_ext, OF this(2)]
      show thesis.
    qed
  qed
qed

lemma min_sol_primitive: assumes "sol \<in> g =\<^sub>M h" shows "primitive sol"
proof (rule ccontr)
  have "sol \<noteq> \<epsilon>"
    using assms min_sol_def by auto
  assume "\<not> primitive sol"
  from not_prim_primroot_expE[OF this]
  obtain k where "(\<rho> sol)\<^sup>@k = sol" "2 \<le> k".
  hence "0 < k" by linarith
  note  min_solD[OF assms]
  have "g (\<rho> sol) = h (\<rho> sol)"
    by (rule pow_eq_eq[OF _ \<open>0 < k\<close>])
    (unfold g.pow_morph[of "\<rho> sol" k, symmetric] h.pow_morph[of "\<rho> sol" k, symmetric] \<open>(\<rho> sol)\<^sup>@k = sol\<close>, fact)
  thus False
    using \<open>\<not> primitive sol\<close>  min_solD_min[OF \<open>sol \<in> g =\<^sub>M h\<close> primroot_nemp primroot_pref] \<open>sol \<noteq> \<epsilon>\<close>
    unfolding prim_primroot_conv[OF \<open>sol \<noteq> \<epsilon>\<close>, symmetric] by blast
qed

lemma prim_sol_two_sols:
  assumes "g u = h u" and "\<not> u \<in> g =\<^sub>M h" and "primitive u"
  obtains s1 s2 where "s1 \<in> g =\<^sub>M h" and "s2 \<in> g =\<^sub>M h" and "s1 \<noteq> s2"
proof-
  show thesis
    using assms
  proof (induction "\<^bold>|u\<^bold>|" arbitrary: u rule: less_induct)
    case less
    then show ?case
    proof-
      obtain s1 where "s1 \<in> g =\<^sub>M h" and "s1 \<le>p u"
        using min_sol_prefE[of g u h, OF \<open>g u = h u\<close> prim_nemp[OF \<open>primitive u\<close>]].
      obtain u' where "s1 \<cdot> u' = u"
        using \<open>s1 \<le>p u\<close> unfolding prefix_def by blast
      have "g u' = h u'"
        using \<open>g u = h u\<close>[folded \<open>s1 \<cdot> u' = u\<close>]
        unfolding g.morph h.morph  min_solD[OF \<open>s1 \<in> g =\<^sub>M h\<close>] cancel.
      have "u' \<noteq> \<epsilon>"
        using \<open>s1 \<in> g =\<^sub>M h\<close> \<open>\<not> u \<in> g =\<^sub>M h\<close>[folded \<open>s1 \<cdot> u' = u\<close>] by force
      obtain exp where "(\<rho> u')\<^sup>@exp = u'" "0 < exp"
        using primroot_expE.
      from pow_eq_eq[of "g (\<rho> u')" exp "h (\<rho> u')", folded g.pow_morph h.pow_morph, unfolded this(1), OF \<open>g u' = h u'\<close> \<open>0 < exp\<close>]
      have "g (\<rho> u') = h (\<rho> u')".
      have "\<^bold>|\<rho> u'\<^bold>| < \<^bold>|u\<^bold>|"
        using add_strict_increasing[OF nemp_pos_len [OF min_solD'[OF \<open>s1 \<in> g =\<^sub>M h\<close>]] primroot_len_le[OF \<open>u' \<noteq> \<epsilon>\<close>]]
        unfolding lenarg[OF \<open>s1 \<cdot> u' = u\<close>, unfolded lenmorph].
      show thesis
      proof (cases)
        assume "\<rho> u' \<in> g =\<^sub>M h"
        have "\<rho> u' \<noteq> s1"
          using \<open>primitive u\<close>[folded \<open>s1 \<cdot> u' = u\<close>]  comm_not_prim[OF primroot_nemp[OF \<open>u' \<noteq> \<epsilon>\<close>] \<open>u' \<noteq> \<epsilon>\<close>  comm_primroot[symmetric]] by fast
        from that[OF \<open>\<rho> u' \<in> g =\<^sub>M h\<close> \<open>s1 \<in> g =\<^sub>M h\<close> this]
        show thesis.
      next
        assume "\<not> \<rho> u' \<in> g =\<^sub>M h"
        from less.hyps[OF \<open>\<^bold>|\<rho> u'\<^bold>| < \<^bold>|u\<^bold>|\<close> \<open>g (\<rho> u') = h (\<rho> u')\<close> this]
        show thesis
          using \<open>u' \<noteq> \<epsilon>\<close> by blast
      qed
    qed
  qed
qed

lemma prim_sols_two_sols:
  assumes "g r = h r" and "g s = h s" and "primitive s" and "primitive r" and "r \<noteq> s"
  obtains s1 s2 where "s1 \<in> g =\<^sub>M h" and "s2 \<in> g =\<^sub>M h" and "s1 \<noteq> s2"
  using prim_sol_two_sols assms by blast

end

subsection \<open>Two nonerasing morphisms\<close>

text \<open>Minimal coincidence pairs and minimal solutions make good sense for nonerasing morphisms only.\<close>

locale two_nonerasing_morphisms = two_morphisms +
  g: nonerasing_morphism g  +
  h: nonerasing_morphism h

begin

thm g.morph
thm g.emp_to_emp

lemma two_nonerasing_morphisms_swap: "two_nonerasing_morphisms h g"
  by unfold_locales

lemma noner_eq_emp_iff: "g u = h v \<Longrightarrow> u = \<epsilon> \<longleftrightarrow> v = \<epsilon>"
  by (metis g.emp_to_emp g.nonerasing h.emp_to_emp h.nonerasing)

lemma min_coin_rev:
  assumes "g r =\<^sub>m h s"
  shows "(rev_map g) (rev r) =\<^sub>m (rev_map h) (rev s)"
proof (rule min_coin_defI)
  show "rev r \<noteq> \<epsilon>" and "rev s \<noteq> \<epsilon>"
    using min_coinD'[OF \<open>g r =\<^sub>m h s\<close>] by simp_all
  show "rev_map g (rev r) = rev_map h (rev s)"
    unfolding rev_map_def using min_coinD[OF \<open>g r =\<^sub>m h s\<close>] by auto
next
  fix r' s' assume "r' \<le>np rev r" "s' \<le>np rev s" "rev_map g r' = rev_map h s'"
  then obtain r'' s'' where "r''\<cdot> rev r' = r" and "s''\<cdot> rev s' = s"
    using npD[OF \<open>s' \<le>np rev s\<close>] npD[OF \<open>r' \<le>np rev r\<close>]
    unfolding pref_rev_suf_iff rev_rev_ident using sufD by (auto simp add: suffix_def)
  have "g (rev r') = h (rev s')"
    using \<open>rev_map g r' = rev_map h s'\<close>[unfolded rev_map_def rev_is_rev_conv] by simp
  hence "g r'' = h s''"
    using min_coinD[OF \<open>g r =\<^sub>m h s\<close>, folded \<open>r''\<cdot> rev r' = r\<close> \<open>s''\<cdot> rev s' = s\<close>,
        unfolded  g.morph h.morph] by simp
  have "r'' \<noteq> r"
    using \<open>r' \<le>np rev r\<close> \<open>r'' \<cdot> rev r' = r\<close> by auto
  hence "r'' = \<epsilon> \<or> s'' = \<epsilon>"
    using \<open>g r =\<^sub>m h s\<close>[unfolded min_coin_def nonempty_prefix_def]
      \<open>r''\<cdot> rev r' = r\<close> \<open>s''\<cdot> rev s' = s\<close> \<open>g r'' = h s''\<close>
    by blast
  hence "r'' = \<epsilon>" and  "s'' = \<epsilon>"
    using noner_eq_emp_iff[OF \<open>g r'' = h s''\<close>] by force+
  thus "r' = rev r \<and> s' = rev s"
    using  \<open>r''\<cdot> rev r' = r\<close> \<open>s''\<cdot> rev s' = s\<close> by auto
qed

lemma min_coin_pref_eq:
  assumes "g e =\<^sub>m h f" and "g e' = h f'" and "e' \<le>np e" and "f' \<bowtie> f"
  shows "e' = e" and "f' = f"
proof-
  note npD'[OF \<open>e' \<le>np e\<close>] npD[OF \<open>e' \<le>np e\<close>]
  have "f \<noteq> \<epsilon>" and "g e  = h f"
    using \<open>g e =\<^sub>m h f\<close>[unfolded min_coin_def] by blast+
  have "f' \<noteq> \<epsilon>"
    using \<open>g e' = h f'\<close> \<open>e' \<noteq> \<epsilon>\<close> by (simp add: noner_eq_emp_iff)
  from g.pref_mono[OF \<open>e' \<le>p e\<close>, unfolded \<open>g e = h f\<close> \<open>g e' = h f'\<close>]
  have "f' \<le>p f"
    using pref_compE[OF \<open>f' \<bowtie> f\<close>] \<open>f' \<noteq> \<epsilon>\<close> h.pref_mono h.pref_morph_pref_eq  by metis
  hence "f' \<le>np f"
    using \<open>f' \<noteq> \<epsilon>\<close> by blast
  with \<open>g e =\<^sub>m h f\<close>[unfolded min_coin_def]
  show "e' = e" and "f' = f"
    using \<open>g e' = h f'\<close> \<open>e' \<le>np e\<close> by blast+
qed

lemma min_coin_prefE:
  assumes "g r = h s" and "r \<noteq> \<epsilon>"
  obtains e f where  "g e =\<^sub>m h f" and "e \<le>p r" and  "f \<le>p s" and "hd e = hd r"
proof-
  define P where "P = (\<lambda> k. \<exists> e f. g e = h f \<and> e \<noteq> \<epsilon> \<and>  e \<le>p r \<and> f \<le>p s \<and> \<^bold>|e\<^bold>| = k)"
  define d where "d = (LEAST k. P k)"
  obtain e f where "g e = h f" and "e \<noteq> \<epsilon>" and  "e \<le>p r" and  "f \<le>p s" and "\<^bold>|e\<^bold>| = d"
    using \<open>g r = h s\<close> LeastI[of P "\<^bold>|r\<^bold>|"]  P_def assms(2) d_def by blast
  hence "f \<noteq> \<epsilon>"
    using noner_eq_emp_iff by blast
  have "r' \<le>np e \<Longrightarrow> s' \<le>np f \<Longrightarrow> g r' = h s' \<Longrightarrow> r' = e \<and> s' = f" for r' s'
  proof-
    assume "r' \<le>np e" and "s' \<le>np f" and "g r' = h s'"
    hence "P \<^bold>|r'\<^bold>|"
      unfolding P_def using \<open>e \<le>p r\<close> \<open>f \<le>p s\<close> npD'[OF \<open>r' \<le>np e\<close>]
          pref_trans[OF npD[OF \<open>r' \<le>np e\<close>] \<open>e \<le>p r\<close>]
          pref_trans[OF npD[OF \<open>s' \<le>np f\<close>] \<open>f \<le>p s\<close>] by blast
    from Least_le[of P, OF this, folded \<open>\<^bold>|e\<^bold>| = d\<close> d_def]
    have "r' = e"
      using  long_pref[OF npD[OF \<open>r' \<le>np e\<close>]] by blast
    from \<open>g e = h f\<close>[folded this, unfolded \<open>g r' = h s'\<close>] this
    show  ?thesis
      using conjunct2[OF \<open>s' \<le>np f\<close>[unfolded nonempty_prefix_def]] h.pref_morph_pref_eq
      by simp
  qed
  hence "g e =\<^sub>m h f"
    unfolding min_coin_def using \<open>e \<noteq> \<epsilon>\<close> \<open>f \<noteq> \<epsilon>\<close> \<open>g e = h f\<close> by blast
  from that[OF this \<open>e \<le>p r\<close> \<open>f \<le>p s\<close> pref_hd_eq[OF \<open>e \<le>p r\<close> \<open>e \<noteq> \<epsilon>\<close>]]
  show thesis.
qed

lemma min_coin_dec: assumes "g e = h f"
  obtains ps where "concat (map fst ps) = e" and "concat (map snd ps) = f" and
    "\<And> p. p \<in> set ps \<Longrightarrow> g (fst p) =\<^sub>m h (snd p)"
  using assms
proof (induct "\<^bold>|e\<^bold>|" arbitrary: e f thesis rule: less_induct)
  case less
  then show ?case
  proof-
    show thesis
    proof (cases "e = \<epsilon>")
      assume "e = \<epsilon>"
      hence "f = \<epsilon>" using \<open>g e = h f\<close>
        using noner_eq_emp_iff by auto
      from less.prems(1)[of \<epsilon>] \<open>e = \<epsilon>\<close> \<open>f = \<epsilon>\<close>
      show thesis by simp
    next
      assume "e \<noteq> \<epsilon>"
      from min_coin_prefE[OF \<open>g e  = h f\<close> this]
      obtain e\<^sub>1 e\<^sub>2 f\<^sub>1 f\<^sub>2 where "g e\<^sub>1 =\<^sub>m h f\<^sub>1" and "e\<^sub>1 \<cdot> e\<^sub>2 = e" and "f\<^sub>1 \<cdot> f\<^sub>2 = f" and "e\<^sub>1 \<noteq> \<epsilon>" and "f\<^sub>1 \<noteq> \<epsilon>"
        using min_coinD' prefD by metis
      have "g e\<^sub>2 = h f\<^sub>2"
        using \<open>g e  = h f\<close>[folded \<open>e\<^sub>1 \<cdot> e\<^sub>2 = e\<close> \<open>f\<^sub>1 \<cdot> f\<^sub>2 = f\<close>, unfolded g.morph h.morph min_coinD[OF \<open>g e\<^sub>1 =\<^sub>m h f\<^sub>1\<close>] cancel].
      have "\<^bold>|e\<^sub>2\<^bold>| < \<^bold>|e\<^bold>|"
        using lenarg[OF \<open>e\<^sub>1 \<cdot> e\<^sub>2 = e\<close>] nemp_pos_len[OF \<open>e\<^sub>1 \<noteq> \<epsilon>\<close>] unfolding lenmorph by linarith
      from less.hyps[OF \<open>\<^bold>|e\<^sub>2\<^bold>| < \<^bold>|e\<^bold>|\<close> _ \<open>g e\<^sub>2 = h f\<^sub>2\<close>]
      obtain ps' where "concat (map fst ps') = e\<^sub>2" and "concat (map snd ps') = f\<^sub>2" and "\<And>p. p \<in> set ps' \<Longrightarrow> g (fst p) =\<^sub>m h (snd p)"
        by blast
      show thesis
      proof(rule less.prems(1)[of "(e\<^sub>1,f\<^sub>1)#ps'"])
        show "concat (map fst ((e\<^sub>1, f\<^sub>1) # ps')) = e"
          using \<open>concat (map fst ps') = e\<^sub>2\<close> \<open>e\<^sub>1 \<cdot> e\<^sub>2 = e\<close> by simp
        show "concat (map snd ((e\<^sub>1, f\<^sub>1) # ps')) = f"
          using \<open>concat (map snd ps') = f\<^sub>2\<close> \<open>f\<^sub>1 \<cdot> f\<^sub>2 = f\<close> by simp
        show "\<And>p. p \<in> set ((e\<^sub>1, f\<^sub>1) # ps') \<Longrightarrow> g (fst p) =\<^sub>m h (snd p)"
          using \<open>\<And>p. p \<in> set ps' \<Longrightarrow> g (fst p) =\<^sub>m h (snd p)\<close> \<open>g e\<^sub>1 =\<^sub>m h f\<^sub>1\<close> by auto
      qed
    qed
  qed
qed

lemma min_coin_code:
  assumes "xs \<in> lists (\<CC>\<^sub>m g h)" and "ys \<in> lists (\<CC>\<^sub>m g h)" and
           "concat (map fst xs) = concat (map fst ys)" and
           "concat (map snd xs) = concat (map snd ys)"
         shows "xs = ys"
  using assms
proof (induction xs ys rule: list_induct2')
  case (2 x xs)
  then show ?case
    using min_coin_setD[THEN min_coinD', of x g h] listsE[OF \<open>x # xs \<in> lists (\<CC>\<^sub>m g h)\<close>] by force
next
  case (3 y ys)
  then show ?case
    using min_coin_setD[of y g h, THEN min_coinD'] listsE[OF \<open>y # ys \<in> lists (\<CC>\<^sub>m g h)\<close>]  by auto
next
  case (4 x xs y ys)
  then show ?case
  proof-
    have "concat (map fst (x#xs)) = fst x \<cdot> concat (map fst xs)"
         "concat (map fst (y#ys)) = fst y \<cdot> concat (map fst ys)"
         "concat (map snd (x#xs)) = snd x \<cdot> concat (map snd xs)"
         "concat (map snd (y#ys)) = snd y \<cdot> concat (map snd ys)"
      by auto
    from eqd_comp[OF \<open>concat (map fst (x#xs)) = concat (map fst (y#ys))\<close>[unfolded this]] eqd_comp[OF \<open>concat (map snd (x#xs)) = concat (map snd (y#ys))\<close>[unfolded this]]
    have "fst x \<bowtie> fst y" and "snd x \<bowtie> snd y".
    have "g (fst y) =\<^sub>m h (snd y)" and "g (fst x) =\<^sub>m h (snd x)"
      by  (use min_coin_setD  listsE[OF \<open>y # ys \<in> lists (\<CC>\<^sub>m g h)\<close>] in blast)
          (use  min_coin_setD listsE[OF \<open>x # xs \<in> lists (\<CC>\<^sub>m g h)\<close>] in blast)
    from min_coin_pref_eq[OF this(1) min_coinD[OF this(2)] _ \<open>snd x \<bowtie> snd y\<close>]
         min_coin_pref_eq[OF this(2) min_coinD[OF this(1)] _ pref_comp_sym[OF \<open>snd x \<bowtie> snd y\<close>]] min_coinD'[OF this(1)] min_coinD'[OF this(2)]
    have "fst x = fst y" and "snd x = snd y"
      using  npI pref_compE[OF \<open>fst x \<bowtie> fst y\<close>] by metis+
    hence eq: "concat (map fst xs) = concat (map fst ys)"
                  "concat (map snd xs) = concat (map snd ys)"
      using "4.prems"(3-4) by fastforce+
    have "xs \<in> lists (\<CC>\<^sub>m g h)" "ys \<in> lists (\<CC>\<^sub>m g h)"
      using "4.prems"(1-2) by fastforce+
    from "4.IH"(1)[OF this eq] prod_eqI[OF \<open>fst x = fst y\<close> \<open>snd x = snd y\<close>]
    show "x # xs = y # ys"
      by blast
  qed
qed simp

lemma  coin_closed: "ps \<in> lists (\<CC> g h) \<Longrightarrow> (concat (map fst ps), concat (map snd ps)) \<in> \<CC> g h"
  unfolding coincidence_set_def
  by (induct ps, simp, auto simp add: g.morph h.morph)

lemma min_coin_gen_snd: "\<langle>snd ` (\<CC>\<^sub>m g h)\<rangle> = snd `(\<CC> g h)"
proof
  show "\<langle>snd ` \<CC>\<^sub>m g h\<rangle> \<subseteq> snd ` \<CC> g h"
  proof
    fix x assume "x \<in> \<langle>snd ` \<CC>\<^sub>m g h\<rangle>"
    then obtain xs where "xs \<in> lists (snd ` \<CC>\<^sub>m g h)" and "x = concat xs"
      using hull_concat_lists0 by blast
    then obtain ps where "ps \<in> lists (\<CC>\<^sub>m g h)" and "xs = map snd ps"
      unfolding lists_image image_iff by blast
    from min_coin_sub coin_closed this(1)
    have "(concat (map fst ps), x) \<in> \<CC> g h"
       unfolding \<open>x = concat xs\<close> \<open>xs = map snd ps\<close> by fast
    thus "x \<in> snd ` \<CC> g h" by force
  qed
  show "snd ` \<CC> g h \<subseteq> \<langle>snd ` \<CC>\<^sub>m g h\<rangle>"
  proof
    fix x assume "x \<in> snd ` \<CC> g h"
    then obtain r where "g r = h x"
      unfolding image_iff coincidence_set_def by force
    from min_coin_dec[OF this]
    obtain ps where "concat (map snd ps) = x" and "\<And>p. p \<in> set ps \<Longrightarrow> g (fst p) =\<^sub>m h (snd p)" by metis
    thus "x \<in> \<langle>snd ` \<CC>\<^sub>m g h\<rangle>"
      unfolding min_coincidence_set_def image_def by fastforce
  qed
qed

lemma min_coin_gen_fst: "\<langle>fst ` (\<CC>\<^sub>m g h)\<rangle> = fst `(\<CC> g h)"
  using two_nonerasing_morphisms.min_coin_gen_snd[folded coin_set_sym min_coin_set_sym, OF two_nonerasing_morphisms_swap].

lemma min_coin_code_snd:
  assumes "code_morphism g" shows "code (snd ` (\<CC>\<^sub>m g h))"
proof
  fix xs ys assume "xs \<in> lists (snd ` \<CC>\<^sub>m g h)" and "ys \<in> lists (snd ` \<CC>\<^sub>m g h)"
  then obtain psx psy where "psx \<in> lists (\<CC>\<^sub>m g h)" and "xs = map snd psx" and
                            "psy \<in> lists (\<CC>\<^sub>m g h)" and "ys = map snd psy"
    unfolding image_iff lists_image by blast+
  have eq1: "g (concat (map fst psx)) = h (concat xs)"
    using \<open>psx \<in> lists (\<CC>\<^sub>m g h)\<close> \<open>xs = map snd psx\<close> min_coin_sub[of g h]
    coin_set_lists_concat by fastforce
  have eq2: "g (concat (map fst psy)) = h (concat ys)"
    using \<open>psy \<in> lists (\<CC>\<^sub>m g h)\<close> \<open>ys = map snd psy\<close> min_coin_sub[of g h]
    coin_set_lists_concat by fastforce
  assume "concat xs = concat ys"
  from arg_cong[OF this, of h, folded eq1 eq2]
  have "concat (map fst psx) = concat (map fst psy)"
    using code_morphism.code_morph_code[OF \<open>code_morphism g\<close>] by auto
  have "concat (map snd psx) = concat (map snd psy)"
    using \<open>concat xs = concat ys\<close> \<open>xs = map snd psx\<close> \<open>ys = map snd psy\<close> by auto
  from min_coin_code[OF \<open>psx \<in> lists (\<CC>\<^sub>m g h)\<close> \<open>psy \<in> lists (\<CC>\<^sub>m g h)\<close> \<open>concat (map fst psx) = concat (map fst psy)\<close> this]
  show  "xs = ys"
    unfolding \<open>xs = map snd psx\<close> \<open>ys = map snd psy\<close> by blast
 qed

lemma min_coin_code_fst:
  "code_morphism h \<Longrightarrow> code (fst ` (\<CC>\<^sub>m g h))"
    using two_nonerasing_morphisms.min_coin_code_snd[OF two_nonerasing_morphisms_swap, folded min_coin_set_sym].

lemma min_coin_basis_snd:
  assumes "code_morphism g"
  shows "\<BB> (snd `(\<CC> g h)) = snd ` (\<CC>\<^sub>m g h)"
  unfolding min_coin_gen_snd[symmetric] basis_of_hull
  using min_coin_code_snd[OF assms] code.code_is_basis by blast

lemma min_coin_basis_fst:
  "code_morphism h \<Longrightarrow> \<BB> (fst `(\<CC> g h)) = fst ` (\<CC>\<^sub>m g h)"
  using two_nonerasing_morphisms.min_coin_basis_snd[folded coin_set_sym min_coin_set_sym, OF two_nonerasing_morphisms_swap].

lemma sol_im_len_less: assumes "g u = h u" and "g \<noteq> h" and "set u = UNIV"
  shows "\<^bold>|u\<^bold>| < \<^bold>|g u\<^bold>|"
proof (rule ccontr)
  assume "\<not> \<^bold>|u\<^bold>| < \<^bold>|g u\<^bold>|"
  hence "\<^bold>|u\<^bold>| = \<^bold>|g u\<^bold>|" and "\<^bold>|u\<^bold>| = \<^bold>|h u\<^bold>|"
    unfolding \<open>g u = h u\<close> using h.im_len_le le_neq_implies_less by blast+
  from this(1)[unfolded g.im_len_eq_iff] this(2)[unfolded h.im_len_eq_iff] \<open>set u = UNIV\<close>
  have "\<^bold>|g [c]\<^bold>| = 1" and "\<^bold>|h [c]\<^bold>| = 1" for c by blast+
  hence "g  = h"
    using solution_eq_len_eq[OF \<open>g u = h u\<close>, THEN  def_on_sings_eq, unfolded \<open>set u = UNIV\<close>, OF _ UNIV_I]
    by force
  thus False using \<open>g \<noteq> h\<close> by contradiction
qed

end

locale two_code_morphisms = g: code_morphism g + h: code_morphism h
  for g h :: "'a list \<Rightarrow> 'b list"

begin

sublocale two_nonerasing_morphisms g h
  by unfold_locales

lemmas code_morphs = g.code_morphism_axioms h.code_morphism_axioms

lemma revs_two_code_morphisms: "two_code_morphisms (rev_map g) (rev_map h)"
  by (simp add: g.code_morphism_rev_map h.code_morphism_rev_map two_code_morphisms.intro)

lemma min_coin_im_basis:
  "\<BB> (h` (snd `(\<CC> g h))) = h ` snd ` (\<CC>\<^sub>m g h)"
        "\<BB> (g` (fst `(\<CC> g h))) = g ` fst ` (\<CC>\<^sub>m g h)"
proof-
  thm   morphism_on.inj_basis_to_basis
        code_morphism.morph_on_inj_on
        min_coin_basis_snd

  note basis_morph_swap = morphism_on.inj_basis_to_basis[OF code_morphism.morph_on_inj_on, symmetric]
  thm basis_morph_swap
      coin_set_hull
      basis_morph_swap[OF code_morphs(2) code_morphs(2), of "snd ` \<CC> g h",   unfolded coin_set_hull]
  show "\<BB> (h ` snd ` \<CC> g h) = h ` snd ` \<CC>\<^sub>m g h"
    unfolding basis_morph_swap[OF code_morphs(2) code_morphs(2), of "snd ` \<CC> g h",   unfolded coin_set_hull]
    unfolding min_coin_basis_snd[OF code_morphs(1)]..

  interpret swap: two_code_morphisms h g
    using two_code_morphisms_def code_morphs by blast

  thm basis_morph_swap[OF code_morphs(1) code_morphs(1), of "fst ` \<CC> g h"]
      swap.coin_set_hull
      coin_set_hull
      coin_set_sym
      swap.coin_set_hull[folded coin_set_sym]
      basis_morph_swap[OF code_morphs(1) code_morphs(1), of "fst ` \<CC> g h", unfolded swap.coin_set_hull[folded coin_set_sym]]
      min_coin_basis_fst

  show "\<BB> (g ` fst ` \<CC> g h) = g ` fst ` \<CC>\<^sub>m g h"
    unfolding basis_morph_swap[OF code_morphs(1) code_morphs(1), of "fst ` \<CC> g h", unfolded swap.coin_set_hull[folded coin_set_sym]]
    unfolding min_coin_basis_fst[OF code_morphs(2)]
    unfolding min_coin_gen_fst..
qed

lemma range_inter_basis_snd:
  shows "\<BB> (range g \<inter> range h) = h ` (snd ` \<CC>\<^sub>m g h)"
        "\<BB> (range g \<inter> range h) = g ` (fst ` \<CC>\<^sub>m g h)"
proof-
  show "\<BB> (range g \<inter> range h) = h ` (snd ` \<CC>\<^sub>m g h)"
  unfolding coin_set_inter_snd[folded image_comp, symmetric]
  using  min_coin_im_basis(1).
  show "\<BB> (range g \<inter> range h) = g ` (fst ` \<CC>\<^sub>m g h)"
  unfolding coin_set_inter_fst[folded image_comp, symmetric]
  using min_coin_im_basis(2).
qed

lemma range_inter_code:
  shows  "code \<BB> (range g \<inter> range h)"
  unfolding range_inter_basis_snd
  thm morphism_on.inj_code_to_code
  by (rule morphism_on.inj_code_to_code)
   (simp_all add:  h.morph_on  h.morph_on_inj_on(2) code_morphs(1) min_coin_code_snd)

end

subsection \<open>Two marked morphisms\<close>

locale two_marked_morphisms = two_nonerasing_morphisms +
       g: marked_morphism g +  h: marked_morphism h

begin

sublocale revs: two_code_morphisms g h
  by (simp add: g.code_morphism_axioms h.code_morphism_axioms two_code_morphisms.intro)

lemmas ne_g = g.nonerasing and
       ne_h = h.nonerasing

lemma unique_continuation:
  "z \<cdot> g r = z' \<cdot> h s \<Longrightarrow>  z \<cdot> g r' = z' \<cdot> h s' \<Longrightarrow> z \<cdot> g (r \<and>\<^sub>p r') = z' \<cdot> h (s \<and>\<^sub>p s')"
  using lcp_ext_left g.marked_morph_lcp h.marked_morph_lcp by metis

lemmas empty_sol = noner_eq_emp_iff

lemma comparable_min_sol_eq: assumes "r \<le>p r'" and "g r =\<^sub>m h s" and "g r' =\<^sub>m h s'"
  shows  "r = r'" and "s = s'"
proof-
  have "s \<le>p s'"
    using  g.pref_mono[OF \<open>r \<le>p r'\<close>]
           h.pref_free_morph
    unfolding min_coinD[OF \<open>g r =\<^sub>m h s\<close>] min_coinD[OF \<open>g r' =\<^sub>m h s'\<close>] by simp
  thus "r = r'"and "s = s'"
    using \<open>g r' =\<^sub>m h s'\<close>[unfolded  min_coin_def] min_coinD[OF \<open>g r =\<^sub>m h s\<close>] min_coinD'[OF \<open>g r =\<^sub>m h s\<close>] \<open>r \<le>p r'\<close>
     by blast+
qed

lemma first_letter_determines:
  assumes "g e =\<^sub>m h f" and "g e' = h f'" and "hd e = hd e'" and "e' \<noteq> \<epsilon>"
  shows "e \<le>p e'" and  "f \<le>p f'"
proof-
  have "g (e \<and>\<^sub>p e') = h (f \<and>\<^sub>p f')"
    using unique_continuation[of \<epsilon> e \<epsilon> f e' f', unfolded emp_simps, OF min_coinD[OF\<open>g e =\<^sub>m h f\<close>] \<open>g e' = h f'\<close>].
  have "e \<noteq> \<epsilon>"
    using \<open>g e =\<^sub>m h f\<close> min_coinD' by auto
  hence eq1: "e = [hd e] \<cdot> tl e" and eq2: "e' = [hd e'] \<cdot> tl e'" using \<open>e' \<noteq> \<epsilon>\<close> by simp+
  from lcp_ext_left[of "[hd e]" "tl e" "tl e'", folded  eq1 eq2[folded \<open>hd e = hd e'\<close>]]
  have "e \<and>\<^sub>p e' \<noteq> \<epsilon>" by force
  from this
  have "f \<and>\<^sub>p f' \<noteq> \<epsilon>"
    using \<open>g (e \<and>\<^sub>p e') = h (f \<and>\<^sub>p f')\<close> g.nonerasing h.emp_to_emp by force
  from npI[OF \<open>e \<and>\<^sub>p e' \<noteq> \<epsilon>\<close> lcp_pref] npI[OF \<open>f \<and>\<^sub>p f' \<noteq> \<epsilon>\<close> lcp_pref]
  show  "e \<le>p e'" and  "f \<le>p f'"
    using min_coin_minD[OF assms(1) \<open>e \<and>\<^sub>p e' \<le>np e\<close> \<open>f \<and>\<^sub>p f' \<le>np f\<close> \<open>g (e \<and>\<^sub>p e') = h (f \<and>\<^sub>p f')\<close>,
          unfolded lcp_sym[of e] lcp_sym[of f]] lcp_pref by metis+
qed

corollary first_letter_determines':
  assumes "g e =\<^sub>m h f" and "g e' =\<^sub>m h f'" and "hd e = hd e'"
  shows "e = e'" and "f = f'"
proof-
  have "e \<noteq> \<epsilon>" and "e' \<noteq> \<epsilon>"
     using \<open>g e =\<^sub>m h f\<close> \<open>g e' =\<^sub>m h f'\<close> min_coinD' by blast+
   have "g e' = h f'" and "g e = h f"
     using \<open>g e =\<^sub>m h f\<close> \<open>g e' =\<^sub>m h f'\<close> min_coinD by blast+
   show "e = e'" and "f = f'"
    using first_letter_determines[OF \<open>g e =\<^sub>m h f\<close> \<open>g e' = h f'\<close> \<open>hd e = hd e'\<close> \<open>e' \<noteq> \<epsilon>\<close>]
          first_letter_determines[OF \<open>g e' =\<^sub>m h f'\<close> \<open>g e = h f\<close> \<open>hd e = hd e'\<close>[symmetric] \<open>e \<noteq> \<epsilon>\<close>]
    by force+
qed

lemma first_letter_determines_sol: assumes "r \<in> g =\<^sub>M h" and "s \<in> g =\<^sub>M h" and "hd r = hd s"
  shows "r = s"
proof-
  have "r \<and>\<^sub>p s \<noteq> \<epsilon>"
    using nemp_lcp_distinct_hd[OF min_solD'[OF \<open>r \<in> g =\<^sub>M h\<close>] min_solD'[OF \<open>s \<in> g =\<^sub>M h\<close>]] \<open>hd r = hd s\<close>
    by blast
  have "g r = h r" and "g s = h s"
    using min_solD[OF \<open>r \<in> g =\<^sub>M h\<close>] min_solD[OF \<open>s \<in> g =\<^sub>M h\<close>].
  have "g (r \<and>\<^sub>p s) = h (r \<and>\<^sub>p s)"
    unfolding \<open>g r = h r\<close> \<open>g s = h s\<close> g.marked_morph_lcp h.marked_morph_lcp..
  from min_solD_min[OF \<open>r \<in> g =\<^sub>M h\<close> \<open>r \<and>\<^sub>p s \<noteq> \<epsilon>\<close> lcp_pref this] min_solD_min[OF \<open>s \<in> g =\<^sub>M h\<close> \<open>r \<and>\<^sub>p s \<noteq> \<epsilon>\<close>  lcp_pref'  this]
  show "r = s" by force
qed

definition pre_block :: "'a \<Rightarrow> 'a list \<times> 'a list"
  where  "pre_block a = (THE p. (g (fst p) =\<^sub>m h (snd p)) \<and> hd (fst p) = a)"
\<comment> \<open>@{term "pre_block a"} may not be a block, if no such exists\<close>

definition blockP :: "'a \<Rightarrow> bool"
  where  "blockP a \<equiv> g (fst (pre_block a)) =\<^sub>m h (snd (pre_block a)) \<and> hd (fst (pre_block a)) = a"
\<comment> \<open>Predicate: the @{term pre_block} of the letter @{term a} is indeed a block\<close>

lemma pre_blockI: "g u =\<^sub>m h v \<Longrightarrow> pre_block (hd u) = (u,v)"
  unfolding pre_block_def
proof (rule the_equality)
  show "\<And>p. g u =\<^sub>m h v \<Longrightarrow> g (fst p) =\<^sub>m h (snd p) \<and> hd (fst p) = hd u \<Longrightarrow> p = (u, v)"
    using first_letter_determines' by force
qed simp

lemma blockI: assumes "g u =\<^sub>m h v" and "hd u = a"
  shows "blockP a"
proof-
  from pre_blockI[OF \<open>g u =\<^sub>m h v\<close>, unfolded \<open>hd u = a\<close>]
  show "blockP a"
    unfolding blockP_def using assms by simp
qed

lemma hd_im_comm_eq_aux:
  assumes "g w = h w" and "w \<noteq> \<epsilon>" and comm: "g\<^sup>\<C> (hd w) \<cdot> h\<^sup>\<C>(hd w) = h\<^sup>\<C> (hd w) \<cdot> g\<^sup>\<C>(hd w)" and len: "\<^bold>|g\<^sup>\<C> (hd w)\<^bold>| \<le> \<^bold>|h\<^sup>\<C>(hd w)\<^bold>|"
  shows "g\<^sup>\<C> (hd w) = h\<^sup>\<C> (hd w)"
proof(cases "w \<in> [hd w]*")
  assume  "w \<in> [hd w]*"
  then obtain l where "w = [hd w]\<^sup>@l"
    unfolding root_def by metis
  from nemp_exp_pos[OF \<open>w \<noteq> \<epsilon>\<close>, of "[hd w]" l, folded this]
  have "l \<noteq> 0"
    by fast
  from \<open>g w = h w\<close>
  have "(g [hd w])\<^sup>@l = (h [hd w])\<^sup>@l"
    unfolding g.pow_morph[symmetric] h.pow_morph[symmetric] \<open>w = [hd w]\<^sup>@l\<close>[symmetric].
  with \<open>l \<noteq> 0\<close>
  have "g [hd w] = h [hd w]"
    using pow_eq_eq by blast
  thus "g\<^sup>\<C> (hd w) = h\<^sup>\<C> (hd w)"
    unfolding core_def.
next
  assume  "w \<notin> [hd w]*"
  from distinct_letter_in_hd[OF this]
  obtain b l w' where "[hd w]\<^sup>@l \<cdot> [b] \<cdot> w' = w" and "b \<noteq> hd w" and "l \<noteq> 0".
  from commE[OF comm]
  obtain t m k where "g\<^sup>\<C> (hd w) = t\<^sup>@m" and "h\<^sup>\<C> (hd w) = t\<^sup>@k".
  have "\<^bold>|t\<^bold>| \<noteq> 0" and "t \<noteq> \<epsilon>" and "m \<noteq> 0"
    using \<open>g\<^sup>\<C> (hd w) = t\<^sup>@m\<close> g.core_nemp pow_zero[of t] by (fastforce, fastforce, metis)
  with lenarg[OF \<open>g\<^sup>\<C> (hd w) = t\<^sup>@m\<close>] lenarg[OF \<open>h\<^sup>\<C> (hd w) = t\<^sup>@k\<close>]
  have "m \<le> k"
    unfolding pow_len lenmorph using len by auto
  have "m = k"
  proof(rule ccontr)
    assume "m \<noteq> k" hence "m < k" using \<open>m \<le> k\<close> by simp
    have "0 < k*l-m*l"
      using \<open>m < k\<close> \<open>l \<noteq> 0\<close> by force
    have "g w = t\<^sup>@(m*l) \<cdot> g [b] \<cdot> g w'"
      unfolding arg_cong[OF \<open>[hd w]\<^sup>@l \<cdot> [b] \<cdot> w' = w\<close>, of g, symmetric] g.morph
        g.pow_morph  \<open>g\<^sup>\<C> (hd w) = t\<^sup>@m\<close>[unfolded core_def] pow_mult[symmetric]..
    moreover have "h w = t\<^sup>@(k*l) \<cdot> h [b] \<cdot> h w'"
      unfolding arg_cong[OF \<open>[hd w]\<^sup>@l \<cdot> [b] \<cdot> w' = w\<close>, of h, symmetric] h.morph
        h.pow_morph  \<open>h\<^sup>\<C> (hd w) = t\<^sup>@k\<close>[unfolded core_def] pow_mult[symmetric]..
    ultimately have *: "g [b] \<cdot>  g w' = t\<^sup>@(k*l-m*l) \<cdot> h [b] \<cdot> h w'"
      using \<open>g w = h w\<close> pop_pow_cancel[OF _ mult_le_mono1[OF \<open>m \<le> k\<close>]]
      unfolding  g.morph[symmetric] h.morph[symmetric] by metis
    have "t\<^sup>@(k*l-m*l) \<noteq> \<epsilon>"
      using gr_implies_not0[OF \<open>0 < k * l - m * l\<close>] unfolding nemp_emp_pow[OF \<open>t \<noteq> \<epsilon>\<close>].
    have "hd (t\<^sup>@(k*l-m*l)) = hd t"
      using hd_append2[OF \<open>t \<noteq> \<epsilon>\<close>] unfolding pow_pos[OF \<open>0 < k * l - m * l\<close>].
    have "hd t = hd (g [b])"
      using hd_append2[OF g.sing_to_nemp[of b], of "g w'"]
      unfolding   hd_append2[of _ "h [b] \<cdot> h w'", OF \<open>t\<^sup>@(k*l-m*l) \<noteq> \<epsilon>\<close>, folded *] \<open>hd (t\<^sup>@(k*l-m*l)) = hd t\<close>.
    have "hd t = hd (g [hd w])"
      using g.hd_im_hd_hd[OF \<open>w \<noteq> \<epsilon>\<close>, unfolded  \<open>g\<^sup>\<C> (hd w) = t \<^sup>@ m\<close>[unfolded core_def]]
            hd_append2[OF \<open>t \<noteq> \<epsilon>\<close>, of "t\<^sup>@(m-1)", unfolded pow_Suc, folded pow_Suc[of t "m-1", unfolded Suc_minus[OF \<open>m \<noteq> 0\<close>]]]
            g.hd_im_hd_hd[OF \<open>w \<noteq> \<epsilon>\<close>] by force
    thus False
      unfolding \<open>hd t = hd (g [b])\<close> using \<open>b \<noteq> hd w\<close> g.marked_morph by blast
  qed
  show "g\<^sup>\<C> (hd w) = h\<^sup>\<C> (hd w)"
    unfolding \<open>g\<^sup>\<C> (hd w) = t\<^sup>@m\<close> \<open>h\<^sup>\<C> (hd w) = t\<^sup>@k\<close> \<open>m = k\<close>..
qed

lemma hd_im_comm_eq:
  assumes "g w = h w" and "w \<noteq> \<epsilon>" and comm: "g\<^sup>\<C> (hd w) \<cdot> h\<^sup>\<C>(hd w) = h\<^sup>\<C> (hd w) \<cdot> g\<^sup>\<C>(hd w)"
  shows "g\<^sup>\<C> (hd w) = h\<^sup>\<C> (hd w)"
proof-
  interpret swap: two_marked_morphisms h g by unfold_locales
  show "g\<^sup>\<C> (hd w) = h\<^sup>\<C> (hd w)"
  using hd_im_comm_eq_aux[OF assms] swap.hd_im_comm_eq_aux[OF assms(1)[symmetric] assms(2) assms(3)[symmetric], symmetric]
  by force
qed

lemma block_ex: assumes "g u =\<^sub>m h v"  shows "blockP (hd u)"
  unfolding blockP_def using pre_blockI[OF assms] assms by simp

lemma sol_block_ex: assumes "g u = h v" and "u \<noteq> \<epsilon>"  shows "blockP (hd u)"
  using min_coin_prefE[OF assms]  block_ex by metis

\<comment> \<open>Successor morphisms\<close>

definition suc_fst where  "suc_fst  \<equiv> \<lambda> x. concat(map (\<lambda> y. fst (pre_block y)) x)"
definition suc_snd where  "suc_snd  \<equiv> \<lambda> x. concat(map (\<lambda> y. snd (pre_block y)) x)"

lemma blockP_D: "blockP a \<Longrightarrow> g (suc_fst [a]) =\<^sub>m h (suc_snd [a])"
  unfolding blockP_def suc_fst_def suc_snd_def by simp

lemma blockP_D_hd: "blockP a \<Longrightarrow> hd (suc_fst [a]) = a"
  unfolding blockP_def suc_fst_def by simp

abbreviation "blocks \<tau> \<equiv> (\<forall> a. a \<in> set \<tau> \<longrightarrow> blockP a)"

sublocale sucs: two_morphisms suc_fst suc_snd
  by (standard)  (simp_all add: suc_fst_def suc_snd_def)



lemma blockP_D_hd_hd: assumes "blockP a"
  shows "hd (h\<^sup>\<C> (hd (suc_snd [a]))) = hd (g\<^sup>\<C> a)"
proof-
  from hd_tlE[OF conjunct2[OF min_coinD'[OF blockP_D[OF \<open>blockP a\<close>]]]]
  obtain b where "hd (suc_snd [a]) = b" by blast
  have "suc_fst [a] \<noteq> \<epsilon>" and "suc_snd [a] \<noteq> \<epsilon>"
   using min_coinD'[OF  blockP_D[OF \<open>blockP a\<close>]] by blast+
  from  g.hd_im_hd_hd[OF this(1)] h.hd_im_hd_hd[OF this(2)]
  have "hd (h\<^sup>\<C> (hd (suc_snd [a]))) = hd (g\<^sup>\<C> (hd (suc_fst [a])))"
    unfolding core_def min_coinD[OF  blockP_D[OF \<open>blockP a\<close>]] by argo
  thus ?thesis
    unfolding blockP_D_hd[OF assms].
qed

lemma suc_morph_sings: assumes "g e =\<^sub>m h f"
  shows "suc_fst [hd e] = e" and "suc_snd [hd e] = f"
  unfolding suc_fst_def suc_snd_def using pre_blockI[OF assms] by simp_all

lemma blocks_eq: "blocks \<tau> \<Longrightarrow> g (suc_fst \<tau>)  = h (suc_snd \<tau>)"
proof (induct \<tau>)
  case (Cons a \<tau>)
  have "blocks \<tau>" and "blockP a"
    using \<open>blocks (a # \<tau>)\<close> by simp_all
  from Cons.hyps[OF this(1)]
  show ?case
    unfolding sucs.g.pop_hd[of a \<tau>] sucs.h.pop_hd[of a \<tau>] g.morph h.morph
    using min_coinD[OF blockP_D, OF \<open>blockP a\<close>] by simp
qed simp

lemma suc_eq': assumes "\<And> a. blockP a" shows "g(suc_fst w) = h(suc_snd w)"
  by (simp add: assms blocks_eq)

lemma suc_eq: assumes all_blocks: "\<And> a. blockP a" shows "g \<circ> suc_fst = h \<circ> suc_snd"
  using suc_eq'[OF assms] by fastforce

lemma block_eq: "blockP a \<Longrightarrow> g (suc_fst [a]) = h (suc_snd [a])"
  using blockP_D min_coinD by blast

lemma blocks_inj_suc: assumes "blocks \<tau>" shows "inj_on suc_fst\<^sup>\<C> (set \<tau>)"
  unfolding inj_on_def core_def using blockP_D_hd[OF \<open>blocks \<tau>\<close>[rule_format]]
  by metis

lemma blocks_inj_suc': assumes "blocks \<tau>" shows "inj_on suc_snd\<^sup>\<C> (set \<tau>)"
   using  g.marked_core blockP_D_hd_hd[OF \<open>blocks \<tau>\<close>[rule_format]]
   unfolding inj_on_def core_def by metis

lemma blocks_marked_code: assumes "blocks \<tau>"
  shows "marked_code (suc_fst\<^sup>\<C> `(set \<tau>))"
proof
  show "\<epsilon> \<notin> suc_fst\<^sup>\<C> ` set \<tau>"
    unfolding core_def image_iff using min_coinD'[OF blockP_D[OF \<open>blocks \<tau>\<close>[rule_format]]] by fastforce
  show "\<And>u v. u \<in> suc_fst\<^sup>\<C> ` set \<tau> \<Longrightarrow>
           v \<in> suc_fst\<^sup>\<C> ` set \<tau> \<Longrightarrow> hd u = hd v \<Longrightarrow> u = v"
    using blockP_D_hd[OF \<open>blocks \<tau>\<close>[rule_format]] unfolding core_def by fastforce
qed

lemma blocks_marked_code': assumes all_blocks: "\<And> a. a \<in> set \<tau> \<Longrightarrow> blockP a"
  shows "marked_code (suc_snd\<^sup>\<C> `(set \<tau>))"
proof
  show "\<epsilon> \<notin> suc_snd\<^sup>\<C> ` set \<tau>"
    unfolding core_def image_iff using min_coinD'[OF all_blocks[THEN blockP_D]] by fastforce
  show "u = v" if "u \<in> suc_snd\<^sup>\<C> ` set \<tau>" and "v \<in> suc_snd\<^sup>\<C> ` set \<tau>" and "hd u = hd v"  for u v
  proof-
    obtain a b where "u = suc_snd [a]" and "v = suc_snd [b]" and "a \<in> set \<tau>" and "b \<in> set \<tau>"
      using \<open>v \<in> suc_snd\<^sup>\<C> ` set \<tau>\<close> \<open>u \<in> suc_snd\<^sup>\<C> ` set \<tau>\<close> unfolding core_def by fast+
    from g.marked_core[of a b,
         folded blockP_D_hd_hd[OF all_blocks, OF \<open>a \<in> set \<tau>\<close>] blockP_D_hd_hd[OF all_blocks, OF \<open>b \<in> set \<tau>\<close>]
         this(1-2) \<open>hd u = hd v\<close>,OF refl]
    show "u = v"
      unfolding \<open>u = suc_snd [a]\<close> \<open>v = suc_snd [b]\<close> by blast
  qed
qed

lemma sucs_marked_morphs: assumes all_blocks: "\<And> a. blockP a"
  shows "two_marked_morphisms suc_fst suc_snd"
proof
  show "hd (suc_fst\<^sup>\<C> a) = hd (suc_fst\<^sup>\<C> b) \<Longrightarrow> a = b" for a b
   using blockP_D_hd[OF all_blocks] unfolding core_def by force
  show "hd (suc_snd\<^sup>\<C> a) = hd (suc_snd\<^sup>\<C> b) \<Longrightarrow> a = b" for a b
    using blockP_D_hd_hd[OF all_blocks, folded core_sing] g.marked_core by metis
  show "suc_fst w = \<epsilon> \<Longrightarrow> w = \<epsilon>" for w
    using assms blockP_D min_coinD' sucs.g.noner_sings_conv by blast
  show  "suc_snd w = \<epsilon> \<Longrightarrow> w = \<epsilon>" for w
    using blockP_D[OF assms(1), THEN min_coinD'] sucs.h.noner_sings_conv by blast
qed

lemma pre_blocks_range: "{(e,f). g e =\<^sub>m h f } \<subseteq> range pre_block"
  using pre_blockI case_prodE by blast

corollary card_blocks: assumes "finite (UNIV :: 'a set)" shows "card {(e,f). g e =\<^sub>m h f } \<le> card (UNIV :: 'a set)"
    using le_trans[OF card_mono[OF finite_imageI pre_blocks_range, OF assms] card_image_le[of _ pre_block, OF assms]].

lemma block_decomposition: assumes "g e = h f"
  obtains \<tau> where  "suc_fst \<tau> = e" and  "suc_snd \<tau> = f" and "blocks \<tau>"
using assms
proof (induct "\<^bold>|e\<^bold>|" arbitrary: e f thesis rule: less_induct)
  case less
    show ?case
  proof (cases "e = \<epsilon>")
    assume "e = \<epsilon>"
    hence  "f = \<epsilon>"
      using less.hyps empty_sol[OF \<open>g e = h f\<close>] by blast
    hence "suc_fst \<epsilon> = e" and "suc_snd \<epsilon> = f"
      unfolding suc_fst_def suc_snd_def by (simp add: \<open>e = \<epsilon>\<close>)+
    from less.prems(1)[OF this]
    show thesis
      by simp
  next
    assume "e \<noteq> \<epsilon>"
    from min_coin_prefE[OF \<open>g e = h f\<close> this]
    obtain  e\<^sub>1 e\<^sub>2 f\<^sub>1 f\<^sub>2
      where "g e\<^sub>1 =\<^sub>m h f\<^sub>1" and "e\<^sub>1\<cdot>e\<^sub>2 = e" and "f\<^sub>1\<cdot>f\<^sub>2 = f" and "e\<^sub>1 \<noteq> \<epsilon>" and "f\<^sub>1 \<noteq> \<epsilon>"
      by (metis min_coinD' prefD)
    from \<open>g e = h f\<close>[folded \<open>e\<^sub>1\<cdot>e\<^sub>2 = e\<close> \<open>f\<^sub>1\<cdot>f\<^sub>2 = f\<close>, unfolded g.morph h.morph]
    have "g e\<^sub>2 = h f\<^sub>2"
      using min_coinD[OF \<open>g e\<^sub>1 =\<^sub>m h f\<^sub>1\<close>] by simp
    have "\<^bold>|e\<^sub>2\<^bold>| < \<^bold>|e\<^bold>|"
      using \<open>e\<^sub>1\<cdot>e\<^sub>2 = e\<close> \<open>e\<^sub>1 \<noteq> \<epsilon>\<close> by auto
    from less.hyps[OF this _ \<open>g e\<^sub>2 = h f\<^sub>2\<close>]
    obtain \<tau>' where "suc_fst \<tau>' = e\<^sub>2" and "suc_snd \<tau>' = f\<^sub>2" and "blocks \<tau>'".
    have "suc_fst [hd e] = e\<^sub>1" and "suc_snd [hd e] = f\<^sub>1"
      using suc_morph_sings \<open>e\<^sub>1 \<cdot> e\<^sub>2 = e\<close> \<open>g e\<^sub>1 =\<^sub>m h f\<^sub>1\<close> \<open>e\<^sub>1 \<noteq> \<epsilon>\<close>  by auto
    hence "suc_fst (hd e # \<tau>') = e" and "suc_snd (hd e # \<tau>') = f"
      using   \<open>e\<^sub>1 \<cdot> e\<^sub>2 = e\<close> \<open>f\<^sub>1 \<cdot> f\<^sub>2 = f\<close>
      unfolding hd_word[of "hd e" \<tau>'] sucs.g.morph sucs.h.morph \<open>suc_fst \<tau>' = e\<^sub>2\<close> \<open>suc_snd \<tau>' = f\<^sub>2\<close> \<open>suc_fst [hd e] = e\<^sub>1\<close> \<open>suc_snd [hd e] = f\<^sub>1\<close> by force+
    have "blocks (hd e # \<tau>')"
      using \<open>blocks \<tau>'\<close> \<open>e\<^sub>1 \<cdot> e\<^sub>2 = e\<close> \<open>e\<^sub>1 \<noteq> \<epsilon>\<close> \<open>g e\<^sub>1 =\<^sub>m h f\<^sub>1\<close> block_ex by force
    from less.prems(1)[OF _ _ this]
    show thesis
      by (simp add: \<open>suc_fst (hd e # \<tau>') = e\<close> \<open>suc_snd (hd e # \<tau>') = f\<close>)
  qed
qed

lemma block_decomposition_unique: assumes "g e = h f" and
   "suc_fst \<tau> = e" and "suc_fst \<tau>' = e" and "blocks \<tau>" and "blocks \<tau>'" shows "\<tau> = \<tau>'"
proof-
  let ?C = "suc_fst\<^sup>\<C>`(set (\<tau>  \<cdot> \<tau>'))"
  have "blocks (\<tau> \<cdot> \<tau>')"
    using \<open>blocks \<tau>\<close> \<open>blocks \<tau>'\<close> by auto
  interpret marked_code ?C
    by (rule blocks_marked_code) (simp add: \<open>blocks (\<tau> \<cdot> \<tau>')\<close>)
  have "inj_on suc_fst\<^sup>\<C> (set (\<tau>   \<cdot> \<tau>'))"
    using \<open>blocks (\<tau> \<cdot> \<tau>')\<close> blocks_inj_suc by blast
  from sucs.g.code_set_morph[OF code_axioms this \<open>suc_fst \<tau> = e\<close>[folded \<open>suc_fst \<tau>' = e\<close>]]
  show "\<tau> = \<tau>'".
qed

lemma block_decomposition_unique': assumes "g e = h f" and
   "suc_snd \<tau> = f" and "suc_snd \<tau>' = f" and "blocks \<tau>" and "blocks \<tau>'"
 shows "\<tau> = \<tau>'"
proof-
  have "suc_fst \<tau> = e" and "suc_fst \<tau>' = e"
    using assms blocks_eq g.code_morph_code by presburger+
 from block_decomposition_unique[OF assms(1) this assms(4-5)]
  show "\<tau> = \<tau>'".
qed

lemma comm_sings_block: assumes "g[a] \<cdot> h[b] = h[b] \<cdot> g[a]"
  obtains m n where "suc_fst [a] = [a]\<^sup>@Suc m" and "suc_snd [a] = [b]\<^sup>@Suc n"
proof-
  have "[a] \<^sup>@ \<^bold>|h [b]\<^bold>| \<noteq> \<epsilon>"
    using nemp_len[OF h.sing_to_nemp, of b, folded sing_pow_empty[of a "\<^bold>|h [b]\<^bold>|"]].
  obtain e f where "g e =\<^sub>m h f" and "e \<le>p [a] \<^sup>@ \<^bold>|h [b]\<^bold>|" and "f \<le>p [b] \<^sup>@ \<^bold>|g [a]\<^bold>|"
    using   min_coin_prefE[OF comm_common_power[OF assms,folded g.pow_morph h.pow_morph] \<open>[a] \<^sup>@ \<^bold>|h [b]\<^bold>| \<noteq> \<epsilon>\<close>, of thesis] by blast
  note e =  pref_sing_pow[OF \<open>e \<le>p [a] \<^sup>@ \<^bold>|h [b]\<^bold>|\<close>]
  note f = pref_sing_pow[OF \<open>f \<le>p [b] \<^sup>@ \<^bold>|g [a]\<^bold>|\<close>]
  from min_coinD'[OF \<open>g e =\<^sub>m h f\<close>]
  have exps: "\<^bold>|e\<^bold>| = Suc (\<^bold>|e\<^bold>| - 1)" "\<^bold>|f\<^bold>| = Suc (\<^bold>|f\<^bold>| - 1)"
    by auto
  have "hd e = a"
    using \<open>e = [a] \<^sup>@ \<^bold>|e\<^bold>|\<close>[unfolded pow_Suc[of "[a]" "\<^bold>|e\<^bold>| - 1", folded \<open>\<^bold>|e\<^bold>| = Suc (\<^bold>|e\<^bold>| - 1)\<close>], folded hd_word[of a "[a] \<^sup>@ (\<^bold>|e\<^bold>| - 1)"]]
    list.sel(1)[of a "[a] \<^sup>@ (\<^bold>|e\<^bold>| - 1)"] by argo
  from that suc_morph_sings[OF \<open>g e =\<^sub>m h f\<close>, unfolded this] e f exps
  show thesis
    by metis
qed

\<comment> \<open>a variant of successor morphisms: target alphabet encoded to be the same as for original morphisms\<close>

definition sucs_encoding where "sucs_encoding = (\<lambda> a. hd (g [a]))"
definition sucs_decoding where "sucs_decoding = (\<lambda> a. SOME c. hd (g[c]) = a)"


lemma sucs_encoding_inv: "sucs_decoding \<circ> sucs_encoding = id"
  by (rule ext)
  (unfold sucs_encoding_def sucs_decoding_def comp_apply id_apply, use g.marked_core[unfolded core_def] in blast)


lemma encoding_inj: "inj sucs_encoding"
  unfolding sucs_encoding_def inj_on_def using g.marked_core[unfolded core_def] by blast

lemma map_encoding_inj: "inj (map sucs_encoding)"
  using encoding_inj by simp

definition suc_fst' where "suc_fst' = (map sucs_encoding) \<circ> suc_fst"
definition suc_snd' where "suc_snd' = (map sucs_encoding) \<circ> suc_snd"

lemma encoded_sucs_eq_conv: "suc_fst w = suc_snd w' \<longleftrightarrow> suc_fst' w = suc_snd' w'"
  unfolding suc_fst'_def suc_snd'_def  using encoding_inj by force

lemma encoded_sucs_eq_conv': "suc_fst = suc_snd \<longleftrightarrow> suc_fst' = suc_snd'"
  unfolding suc_fst'_def suc_snd'_def  using inj_comp_eq[OF map_encoding_inj] by blast

lemma encoded_sucs: assumes "\<And> c. blockP c" shows "two_marked_morphisms suc_fst' suc_snd'"
unfolding suc_fst'_def suc_snd'_def
proof-
  from sucs_marked_morphs[OF assms]
  interpret sucs: two_marked_morphisms suc_fst suc_snd
    by force
  interpret nonerasing_morphism "(map sucs_encoding) \<circ> suc_fst"
    unfolding comp_apply  by (standard, simp add: sucs.g.morph, use  sucs.g.nemp_to_nemp in fast)
  interpret nonerasing_morphism "(map sucs_encoding) \<circ> suc_snd"
    unfolding comp_apply  by (standard, simp add: sucs.h.morph, use  sucs.h.nemp_to_nemp in fast)
  interpret marked_morphism "(map sucs_encoding) \<circ> suc_fst"
  proof
    show "hd ((map sucs_encoding \<circ> suc_fst)\<^sup>\<C> a) = hd ((map sucs_encoding \<circ> suc_fst)\<^sup>\<C> b) \<Longrightarrow> a = b" for a b
      unfolding comp_apply core_def sucs_encoding_def hd_map[OF sucs.g.sing_to_nemp]
      unfolding  blockP_D_hd[OF assms] using  g.marked_morph.
  qed
  interpret marked_morphism "(map sucs_encoding) \<circ> suc_snd"
  proof
    show "hd ((map sucs_encoding \<circ> suc_snd)\<^sup>\<C> a) = hd ((map sucs_encoding \<circ> suc_snd)\<^sup>\<C> b) \<Longrightarrow> a = b" for a b
      unfolding comp_apply core_def sucs_encoding_def hd_map[OF sucs.h.sing_to_nemp]
      using g.marked_morph[THEN sucs.h.marked_morph].
  qed
  show "two_marked_morphisms ((map sucs_encoding) \<circ> suc_fst) ((map sucs_encoding) \<circ> suc_snd)"..
qed

lemma encoded_sucs_len: "\<^bold>|suc_fst w\<^bold>| = \<^bold>|suc_fst' w\<^bold>|" and "\<^bold>|suc_snd w\<^bold>| = \<^bold>|suc_snd' w\<^bold>|"
  unfolding suc_fst'_def suc_snd'_def sucs_encoding_def comp_apply by force+

end

end
