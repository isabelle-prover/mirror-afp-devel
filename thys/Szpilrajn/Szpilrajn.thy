(*<*)
theory Szpilrajn 
  imports Main
begin
  (*>*)

text \<open>
  We formalize a more general version of Szpilrajn's extension theorem~\<^cite>\<open>"Szpilrajn:1930"\<close>,
  employing the terminology of Bossert and Suzumura~\<^cite>\<open>"Bossert:2010"\<close>. We also formalize 
  Theorem 2.7 of their book. Our extension theorem states that any preorder can be extended to a
  total preorder while maintaining its structure. The proof of the extension theorem follows the
  proof presented in the Wikipedia article~\<^cite>\<open>Wiki\<close>.
\<close>

section \<open>Definitions\<close>

subsection \<open>Symmetric and asymmetric factor of a relation\<close>

text \<open>
  According to Bossert and Suzumura, every relation can be partitioned into its symmetric
  and asymmetric factor. The symmetric factor of a relation \<^term>\<open>r\<close> contains all pairs
  \<^term>\<open>(x, y) \<in> r\<close> where \<^term>\<open>(y, x) \<in> r\<close>. Conversely, the asymmetric factor contains all pairs
   where this is not the case. In terms of an order \<^term>\<open>(\<le>)\<close>, the asymmetric factor contains all
  \<^term>\<open>(x, y) \<in> {(x, y) |x y. x \<le> y}\<close> where \<^term>\<open>x < y\<close>.
\<close>
definition sym_factor :: "'a rel \<Rightarrow> 'a rel"
  where "sym_factor r \<equiv> {(x, y) \<in> r. (y, x) \<in> r}"

lemma sym_factor_def': "sym_factor r = r \<inter> r\<inverse>"
  unfolding sym_factor_def by fast

definition asym_factor :: "'a rel \<Rightarrow> 'a rel"
  where "asym_factor r = {(x, y) \<in> r. (y, x) \<notin> r}"


subsubsection \<open>Properties of the symmetric factor\<close>

lemma sym_factorI[intro]: "(x, y) \<in> r \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> (x, y) \<in> sym_factor r"
  unfolding sym_factor_def by blast

lemma sym_factorE[elim?]:
  assumes "(x, y) \<in> sym_factor r" obtains "(x, y) \<in> r" "(y, x) \<in> r"
  using assms[unfolded sym_factor_def] by blast

lemma sym_sym_factor[simp]: "sym (sym_factor r)"
  unfolding sym_factor_def
  by (auto intro!: symI) 

lemma trans_sym_factor[simp]: "trans r \<Longrightarrow> trans (sym_factor r)"
  unfolding sym_factor_def' using trans_Int by force

lemma refl_on_sym_factor[simp]: "refl_on A r \<Longrightarrow> refl_on A (sym_factor r)"
  unfolding sym_factor_def
  by (auto intro!: refl_onI dest: refl_onD refl_onD1)

lemma sym_factor_absorb_if_sym[simp]: "sym r \<Longrightarrow> sym_factor r = r"
  unfolding sym_factor_def'
  by (simp add: sym_conv_converse_eq)

lemma sym_factor_idem[simp]: "sym_factor (sym_factor r) = sym_factor r"
  using sym_factor_absorb_if_sym[OF sym_sym_factor] .

lemma sym_factor_reflc[simp]: "sym_factor (r\<^sup>=) = (sym_factor r)\<^sup>="
  unfolding sym_factor_def by auto

lemma sym_factor_Restr[simp]: "sym_factor (Restr r A) = Restr (sym_factor r) A"
  unfolding sym_factor_def by blast

text \<open>
  In contrast to \<^term>\<open>asym_factor\<close>, the \<^term>\<open>sym_factor\<close> is monotone.
\<close>
lemma sym_factor_mono: "r \<subseteq> s \<Longrightarrow> sym_factor r \<subseteq> sym_factor s"
  unfolding sym_factor_def by auto


subsubsection \<open>Properties of the asymmetric factor\<close>

lemma asym_factorI[intro]: "(x, y) \<in> r \<Longrightarrow> (y, x) \<notin> r \<Longrightarrow> (x, y) \<in> asym_factor r"
  unfolding asym_factor_def by blast

lemma asym_factorE[elim?]:
  assumes "(x, y) \<in> asym_factor r" obtains "(x, y) \<in> r"
  using assms unfolding asym_factor_def by blast

lemma refl_not_in_asym_factor[simp]: "(x, x) \<notin> asym_factor r"
  unfolding asym_factor_def by blast

lemma irrefl_asym_factor[simp]: "irrefl (asym_factor r)"
  unfolding asym_factor_def irrefl_def by fast

lemma asym_asym_factor[simp]: "asym (asym_factor r)"
  using irrefl_asym_factor
  by (auto intro!: asymI simp: asym_factor_def)

lemma trans_asym_factor[simp]: "trans r \<Longrightarrow> trans (asym_factor r)"
  unfolding asym_factor_def trans_def by fast

lemma asym_if_irrefl_trans: "irrefl r \<Longrightarrow> trans r \<Longrightarrow> asym r"
  by (intro asymI) (auto simp: irrefl_def trans_def)

lemma antisym_if_irrefl_trans: "irrefl r \<Longrightarrow> trans r \<Longrightarrow> antisym r"
  using antisym_def asym_if_irrefl_trans by (auto dest: asymD)
    
lemma asym_factor_asym_rel[simp]: "asym r \<Longrightarrow> asym_factor r = r"
  unfolding asym_factor_def
  by (auto dest: asymD)

lemma irrefl_trans_asym_factor_id[simp]: "irrefl r \<Longrightarrow> trans r \<Longrightarrow> asym_factor r = r"
  using asym_factor_asym_rel[OF asym_if_irrefl_trans] .

lemma asym_factor_id[simp]: "asym_factor (asym_factor r) = asym_factor r"
  using asym_factor_asym_rel[OF asym_asym_factor] .

lemma asym_factor_rtrancl: "asym_factor (r\<^sup>*) = asym_factor (r\<^sup>+)"
  unfolding asym_factor_def
  by (auto simp add: rtrancl_eq_or_trancl)

lemma asym_factor_Restr[simp]: "asym_factor (Restr r A) = Restr (asym_factor r) A"
  unfolding asym_factor_def by blast

lemma acyclic_asym_factor[simp]: "acyclic r \<Longrightarrow> acyclic (asym_factor r)"
  unfolding asym_factor_def by (auto intro: acyclic_subset)


subsubsection \<open>Relations between symmetric and asymmetric factor\<close>

text \<open>
  We prove that \<^term>\<open>sym_factor\<close> and \<^term>\<open>asym_factor\<close> partition the input relation.
\<close>
lemma sym_asym_factor_Un: "sym_factor r \<union> asym_factor r = r"
  unfolding sym_factor_def asym_factor_def by blast

lemma disjnt_sym_asym_factor[simp]: "disjnt (sym_factor r) (asym_factor r)"
  unfolding disjnt_def
  unfolding sym_factor_def asym_factor_def by blast

lemma Field_sym_asym_factor_Un:
  "Field (sym_factor r) \<union> Field (asym_factor r) = Field r"
  using sym_asym_factor_Un Field_Un by metis

lemma asym_factor_tranclE:
  assumes "(a, b) \<in> (asym_factor r)\<^sup>+" shows "(a, b) \<in> r\<^sup>+"
  using assms sym_asym_factor_Un
  by (metis UnCI subsetI trancl_mono)


subsection \<open>Extension of Orders\<close>

text \<open>
  We use the definition of Bossert and Suzumura for \<open>extends\<close>. The requirement \<^term>\<open>r \<subseteq> R\<close> is
  obvious. The second requirement \<^term>\<open>asym_factor r \<subseteq> asym_factor R\<close> enforces that the 
  extension \<^term>\<open>R\<close> maintains all strict preferences of \<^term>\<open>r\<close> (viewing \<^term>\<open>r\<close> as a 
  preference relation).
\<close>
                    
definition extends :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "extends R r \<equiv> r \<subseteq> R \<and> asym_factor r \<subseteq> asym_factor R"

text \<open>
  We define a stronger notion of \<^term>\<open>extends\<close> where we also demand that
  \<^term>\<open>sym_factor R \<subseteq> (sym_factor r)\<^sup>=\<close>. This enforces that the extension does not introduce
  preference cycles between previously unrelated pairs \<^term>\<open>(x, y) \<in> R - r\<close>.
\<close>

definition strict_extends :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "strict_extends R r \<equiv> extends R r \<and> sym_factor R \<subseteq> (sym_factor r)\<^sup>="

lemma extendsI[intro]: "r \<subseteq> R \<Longrightarrow> asym_factor r \<subseteq> asym_factor R \<Longrightarrow> extends R r"
  unfolding extends_def by (intro conjI)

lemma extendsE:
  assumes "extends R r"
  obtains "r \<subseteq> R" "asym_factor r \<subseteq> asym_factor R"
  using assms unfolding extends_def by blast

lemma trancl_subs_extends_if_trans: "extends r_ext r \<Longrightarrow> trans r_ext \<Longrightarrow> r\<^sup>+ \<subseteq> r_ext"
  unfolding extends_def asym_factor_def
  by (metis subrelI trancl_id trancl_mono)

lemma extends_if_strict_extends: "strict_extends r_ext ext \<Longrightarrow> extends r_ext ext"
  unfolding strict_extends_def by blast

lemma strict_extendsI[intro]:
  assumes "r \<subseteq> R" "asym_factor r \<subseteq> asym_factor R" "sym_factor R \<subseteq> (sym_factor r)\<^sup>="
  shows "strict_extends R r"
  unfolding strict_extends_def using assms by (intro conjI extendsI)

lemma strict_extendsE:
  assumes "strict_extends R r"
  obtains "r \<subseteq> R" "asym_factor r \<subseteq> asym_factor R" "sym_factor R \<subseteq> (sym_factor r)\<^sup>="
  using assms extendsE unfolding strict_extends_def by blast

lemma strict_extends_antisym_Restr:
  assumes "strict_extends R r"
  assumes "antisym (Restr r A)"
  shows "antisym ((R - r) \<union> Restr r A)"
proof(rule antisymI, rule ccontr)
  fix x y assume "(x, y) \<in> (R - r) \<union> Restr r A" "(y, x) \<in> (R - r) \<union> Restr r A" "x \<noteq> y"
  with \<open>strict_extends R r\<close> have "(x, y) \<in> sym_factor R"
    unfolding sym_factor_def by (auto elim!: strict_extendsE)
  with assms \<open>x \<noteq> y\<close> have "(x, y) \<in> sym_factor r"
    by (auto elim!: strict_extendsE)
  then have "(x, y) \<in> r" "(y, x) \<in> r"
    unfolding sym_factor_def by simp_all
  with \<open>antisym (Restr r A)\<close> \<open>x \<noteq> y\<close> \<open>(y, x) \<in> R - r \<union> Restr r A\<close> show False
    using antisymD by fastforce
qed

text \<open>Here we prove that we have no preference cycles between previously unrelated pairs.\<close>
lemma antisym_Diff_if_strict_extends:
  assumes "strict_extends R r"
  shows "antisym (R - r)"
  using strict_extends_antisym_Restr[OF assms, where ?A="{}"] by simp

lemma strict_extends_antisym:
  assumes "strict_extends R r"
  assumes "antisym r"
  shows "antisym R"
  using assms strict_extends_antisym_Restr[OF assms(1), where ?A=UNIV]
  by (auto elim!: strict_extendsE simp: antisym_def) 

lemma strict_extends_if_strict_extends_reflc:
  assumes "strict_extends r_ext (r\<^sup>=)"
  shows "strict_extends r_ext r"
proof(intro strict_extendsI)
  from assms show "r \<subseteq> r_ext"
    by (auto elim: strict_extendsE)

  from assms \<open>r \<subseteq> r_ext\<close> show "asym_factor r \<subseteq> asym_factor r_ext"
    unfolding strict_extends_def
    by (auto simp: asym_factor_def sym_factor_def)

  from assms show "sym_factor r_ext \<subseteq> (sym_factor r)\<^sup>="
    by (auto simp: sym_factor_def strict_extends_def)
qed

lemma strict_extends_diff_Id:
  assumes "irrefl r" "trans r"
  assumes "strict_extends r_ext (r\<^sup>=)"
  shows "strict_extends (r_ext - Id) r"
proof(intro strict_extendsI)
  from assms show "r \<subseteq> r_ext - Id"
    by (auto elim: strict_extendsE simp: irrefl_def)

  note antisym_r = antisym_if_irrefl_trans[OF assms(1,2)]
  with assms strict_extends_if_strict_extends_reflc show "asym_factor r \<subseteq> asym_factor (r_ext - Id)"
    unfolding asym_factor_def
    by (auto intro: strict_extends_antisym[THEN antisymD] elim: strict_extendsE transE)

  from assms antisym_r show "sym_factor (r_ext - Id) \<subseteq> (sym_factor r)\<^sup>="
    unfolding sym_factor_def
    by (auto intro: strict_extends_antisym[THEN antisymD])
qed

text \<open>
  Both \<^term>\<open>extends\<close> and \<^term>\<open>strict_extends\<close> form a partial order since they
  are reflexive, transitive, and antisymmetric.
\<close>
lemma shows
    reflp_extends: "reflp extends" and
    transp_extends: "transp extends" and
    antisymp_extends: "antisymp extends"
  unfolding extends_def reflp_def transp_def antisymp_def
  by auto

lemma shows
    reflp_strict_extends: "reflp strict_extends" and
    transp_strict_extends: "transp strict_extends" and
    antisymp_strict_extends: "antisymp strict_extends"
  using reflp_extends transp_extends antisymp_extends
  unfolding strict_extends_def reflp_def transp_def antisymp_def
  by auto

subsection \<open>Missing order definitions\<close>

lemma preorder_onD[dest?]:
  assumes "preorder_on A r"
  shows "refl_on A r" "trans r"
  using assms unfolding preorder_on_def by blast+

lemma preorder_onI[intro]: "refl_on A r \<Longrightarrow> trans r \<Longrightarrow> preorder_on A r"
  unfolding preorder_on_def by (intro conjI)

abbreviation "preorder \<equiv> preorder_on UNIV"

lemma preorder_rtrancl: "preorder (r\<^sup>*)"
  by (intro preorder_onI refl_rtrancl trans_rtrancl)

definition "total_preorder_on A r \<equiv> preorder_on A r \<and> total_on A r"

abbreviation "total_preorder r \<equiv> total_preorder_on UNIV r"

lemma total_preorder_onI[intro]:
  "refl_on A r \<Longrightarrow> trans r \<Longrightarrow> total_on A r \<Longrightarrow> total_preorder_on A r"
  unfolding total_preorder_on_def by (intro conjI preorder_onI)

lemma total_preorder_onD[dest?]:
  assumes "total_preorder_on A r"
  shows "refl_on A r" "trans r" "total_on A r"
  using assms unfolding total_preorder_on_def preorder_on_def by blast+

definition "strict_partial_order r \<equiv> trans r \<and> irrefl r"

lemma strict_partial_orderI[intro]:
  "trans r \<Longrightarrow> irrefl r \<Longrightarrow> strict_partial_order r"
  unfolding strict_partial_order_def by blast

lemma strict_partial_orderD[dest?]:
  assumes "strict_partial_order r"
  shows "trans r" "irrefl r"
  using assms unfolding strict_partial_order_def by blast+

lemma strict_partial_order_acyclic:
  assumes "strict_partial_order r"
  shows "acyclic r"
  by (metis acyclic_irrefl assms strict_partial_order_def trancl_id)


abbreviation "partial_order \<equiv> partial_order_on UNIV"

lemma partial_order_onI[intro]:
  "refl_on A r \<Longrightarrow> trans r \<Longrightarrow> antisym r \<Longrightarrow> partial_order_on A r"
  using partial_order_on_def by blast

lemma linear_order_onI[intro]:
  "refl_on A r \<Longrightarrow> trans r \<Longrightarrow> antisym r \<Longrightarrow> total_on A r \<Longrightarrow> linear_order_on A r"
  using linear_order_on_def by blast

lemma linear_order_onD[dest?]:
  assumes "linear_order_on A r"
  shows "refl_on A r" "trans r" "antisym r" "total_on A r"
  using assms[unfolded linear_order_on_def] partial_order_onD by blast+

text \<open>A typical example is \<^term>\<open>(\<subset>)\<close> on sets:\<close>

lemma strict_partial_order_subset:
  "strict_partial_order {(x,y). x \<subset> y}"
proof
  show "trans {(x,y). x \<subset> y}"
    by (auto simp add: trans_def)
  show "irrefl {(x, y). x \<subset> y}"
    by (simp add: irrefl_def)
qed

text \<open>We already have a definition of a strict linear order in \<^term>\<open>strict_linear_order\<close>.\<close>

section \<open>Extending preorders to total preorders\<close>

text \<open>
  We start by proving that a preorder with two incomparable elements \<^term>\<open>x\<close> and \<^term>\<open>y\<close> can be
  strictly extended to a preorder where \<^term>\<open>x < y\<close>.
\<close>

lemma can_extend_preorder: 
  assumes "preorder_on A r"
    and "y \<in> A" "x \<in> A" "(y, x) \<notin> r"
  shows
    "preorder_on A ((insert (x, y) r)\<^sup>+)" "strict_extends ((insert (x, y) r)\<^sup>+) r"
proof -
  note preorder_onD[OF \<open>preorder_on A r\<close>]
  then have "insert (x, y) r \<subseteq> A \<times> A"
    using \<open>y \<in> A\<close> \<open>x \<in> A\<close> refl_on_domain by fast
  with \<open>refl_on A r\<close> show "preorder_on A ((insert (x, y) r)\<^sup>+)"
    by (intro preorder_onI refl_onI trans_trancl)
       (auto simp: trancl_subset_Sigma intro!: r_into_trancl' dest: refl_onD)

  show "strict_extends ((insert (x, y) r)\<^sup>+) r"
  proof(intro strict_extendsI)
    from preorder_onD(2)[OF \<open>preorder_on A r\<close>] \<open>(y, x) \<notin> r\<close>
    show "asym_factor r \<subseteq> asym_factor ((insert (x, y) r)\<^sup>+)"
       unfolding asym_factor_def trancl_insert
       using rtranclD rtrancl_into_trancl1 r_r_into_trancl
       by fastforce

     from assms have "(y, x) \<notin> (insert (x, y) r)\<^sup>+"
       unfolding preorder_on_def trancl_insert
       using refl_onD rtranclD by fastforce
     with \<open>trans r\<close> show "sym_factor ((insert (x, y) r)\<^sup>+) \<subseteq> (sym_factor r)\<^sup>="
       unfolding trancl_insert sym_factor_def by (fastforce intro: rtrancl_trans)
  qed auto
qed


text \<open>
  With this, we can start the proof of our main extension theorem.
  For this we will use a variant of Zorns Lemma, which only considers nonempty chains:
\<close>
lemma Zorns_po_lemma_nonempty:
  assumes po: "Partial_order r"
    and u: "\<And>C. \<lbrakk>C \<in> Chains r; C\<noteq>{}\<rbrakk> \<Longrightarrow> \<exists>u\<in>Field r. \<forall>a\<in>C. (a, u) \<in> r"
    and "r \<noteq> {}"
  shows "\<exists>m\<in>Field r. \<forall>a\<in>Field r. (m, a) \<in> r \<longrightarrow> a = m"
proof -
  from \<open>r \<noteq> {}\<close> obtain x where "x \<in> Field r"
    using FieldI2 by fastforce
  with assms show ?thesis
    using Zorns_po_lemma by (metis empty_iff)  
qed


theorem strict_extends_preorder_on:
  assumes "preorder_on A base_r"
  shows "\<exists>r. total_preorder_on A r \<and> strict_extends r base_r" 
proof -

  text \<open>
    We define an order on the set of strict extensions of the base relation \<^term>\<open>base_r\<close>, 
    where \<^term>\<open>r \<le> s\<close> iff \<^term>\<open>strict_extends r base_r\<close> and \<^term>\<open>strict_extends s r\<close>:
  \<close>

  define order_of_orders :: "('a rel) rel" where "order_of_orders =
    Restr {(r, s). strict_extends r base_r \<and> strict_extends s r} {r. preorder_on A r}"

  text \<open>
    We show that this order consists of those relations that are preorders and that strictly extend
    the base relation \<^term>\<open>base_r\<close>
  \<close>

  have Field_order_of_orders: "Field order_of_orders =
    {r. preorder_on A r \<and> strict_extends r base_r}"
    using transp_strict_extends
  proof(safe)
    fix r assume "preorder_on A r" "strict_extends r base_r"
    with reflp_strict_extends have
      "(r, r) \<in> {(r, s). strict_extends r base_r \<and> strict_extends s r}"
      by (auto elim!: reflpE)
    with \<open>preorder_on A r\<close> show "r \<in> Field order_of_orders"
      unfolding order_of_orders_def by (auto simp: Field_def)
  qed (auto simp: order_of_orders_def Field_def elim: transpE)

  text \<open>
    We now show that this set has a maximum and that any maximum of this set is a total preorder
    and as thus is one of the extensions we are looking for.
    We begin by showing the existence of a maximal element using Zorn's lemma.
  \<close>

  have "\<exists>m \<in> Field order_of_orders.
      \<forall>a \<in> Field order_of_orders. (m, a) \<in> order_of_orders \<longrightarrow> a = m"
  proof (rule Zorns_po_lemma_nonempty)

    text \<open>
      Zorn's Lemma requires us to prove that our \<^term>\<open>order_of_orders\<close> is a nonempty partial order
      and that every nonempty chain has an upper bound. 
      The partial order property is trivial, since we used \<^term>\<open>strict_extends\<close> for the relation, 
      which is a partial order as shown above.
    \<close>

    from reflp_strict_extends transp_strict_extends
    have "Refl {(r, s). strict_extends r base_r \<and> strict_extends s r}"
      unfolding refl_on_def Field_def by (auto elim: transpE reflpE)
    moreover have "trans {(r, s). strict_extends r base_r \<and> strict_extends s r}"
      using transp_strict_extends  by (auto elim: transpE intro: transI)
    moreover have "antisym {(r, s). strict_extends r base_r \<and> strict_extends s r}"
      using antisymp_strict_extends by (fastforce dest: antisympD intro: antisymI)

    ultimately show "Partial_order order_of_orders"
      unfolding order_of_orders_def order_on_defs
      using Field_order_of_orders Refl_Restr trans_Restr antisym_Restr
      by blast

    text \<open>Also, our order is obviously not empty since it contains \<^term>\<open>(base_r, base_r)\<close>:\<close>

    have "(base_r, base_r) \<in> order_of_orders"
      unfolding order_of_orders_def
      using assms reflp_strict_extends by (auto dest: reflpD)
    thus "order_of_orders \<noteq> {}" by force


    text \<open>
      Next we show that each chain has an upper bound.
      For the upper bound we take the union of all relations in the chain.
    \<close>

    show "\<exists>u \<in> Field order_of_orders. \<forall>a \<in> C. (a, u) \<in> order_of_orders" 
      if C_def: "C \<in> Chains order_of_orders" and C_nonempty: "C \<noteq> {}"
      for C
    proof (rule bexI[where x="\<Union>C"])

      text \<open>
        Obviously each element in the chain is a strict extension of \<^term>\<open>base_r\<close> by definition
        and as such it is also a preorder.
      \<close>

      have preorder_r: "preorder_on A r" and extends_r: "strict_extends r base_r" if "r \<in> C" for r
        using that C_def[unfolded order_of_orders_def Chains_def] by blast+

      text \<open>
        Because a chain is partially ordered, the union of the chain is reflexive and transitive.
      \<close>

      have total_subs_C: "r \<subseteq> s \<or> s \<subseteq> r" if "r \<in> C" and "s \<in> C" for r s
        using C_def that
        unfolding Chains_def order_of_orders_def strict_extends_def extends_def
        by blast

      have preorder_UnC: "preorder_on A (\<Union>C)"
      proof(intro preorder_onI)
        show "refl_on A (\<Union>C)"
          using preorder_onD(1)[OF preorder_r] C_nonempty
          unfolding refl_on_def by auto

        from total_subs_C show "trans (\<Union>C)"
          using chain_subset_trans_Union[unfolded chain_subset_def]
          by (metis preorder_onD(2)[OF preorder_r])
      qed

      text \<open>We show that \<^term>\<open>\<Union>C\<close> strictly extends the base relation.\<close>
    
      have strict_extends_UnC: "strict_extends (\<Union>C) base_r"
      proof(intro strict_extendsI)
        note extends_r_unfolded = extends_r[unfolded extends_def strict_extends_def]

        show "base_r \<subseteq> (\<Union>C)"
          using C_nonempty extends_r_unfolded
          by blast

        then show "asym_factor base_r \<subseteq> asym_factor (\<Union>C)"
          using extends_r_unfolded
          unfolding asym_factor_def by auto

        show "sym_factor (\<Union>C) \<subseteq> (sym_factor base_r)\<^sup>="
        proof(safe)
          fix x y assume "(x, y) \<in> sym_factor (\<Union>C)" "(x, y) \<notin> sym_factor base_r"
          then have "(x, y) \<in> \<Union>C" "(y, x) \<in> \<Union>C"
            unfolding sym_factor_def by blast+

          with extends_r obtain c where "c \<in> C" "(x, y) \<in> c" "(y, x) \<in> c"
            "strict_extends c base_r"
            using total_subs_C by blast
          then have "(x, y) \<in> sym_factor c"
            unfolding sym_factor_def by blast
          with \<open>strict_extends c base_r\<close> \<open>(x, y) \<notin> sym_factor base_r\<close>
          show "x = y"
            unfolding strict_extends_def by blast
        qed
      qed

      from preorder_UnC strict_extends_UnC show "(\<Union>C) \<in> Field order_of_orders"
        unfolding Field_order_of_orders by simp

      text \<open>
        Lastly, we prove by contradiction that \<^term>\<open>\<Union>C\<close> is an upper bound for the chain.
      \<close>

      show "\<forall>a \<in> C. (a, \<Union>C) \<in> order_of_orders"
      proof(rule ccontr)
        presume "\<exists>a \<in> C. (a, \<Union>C) \<notin> order_of_orders"
        then obtain m where m: "m \<in> C" "(m, \<Union>C) \<notin> order_of_orders"
          by blast

        hence strict_extends_m: "strict_extends m base_r" "preorder_on A m"
          using extends_r preorder_r by blast+
        with m have "\<not> strict_extends (\<Union>C) m"
          using preorder_UnC unfolding order_of_orders_def by blast

        from m have "m \<subseteq> \<Union>C"
          by blast
        moreover
        have "sym_factor (\<Union>C) \<subseteq> (sym_factor m)\<^sup>="
        proof(safe)
          fix a b
          assume "(a, b) \<in> sym_factor (\<Union> C)" "(a, b) \<notin> sym_factor m"
          then have "(a, b) \<in> sym_factor base_r \<or> (a, b) \<in> Id"
            using strict_extends_UnC[unfolded strict_extends_def] by blast
          with \<open>(a, b) \<notin> sym_factor m\<close> strict_extends_m(1) show "a = b"
            by (auto elim: strict_extendsE simp: sym_factor_mono[THEN in_mono])
        qed
        ultimately
        have "\<not> asym_factor m \<subseteq> asym_factor (\<Union>C)"
          using \<open>\<not> strict_extends (\<Union>C) m\<close> unfolding strict_extends_def extends_def by blast

        then obtain x y where
          "(x, y) \<in> m" "(y, x) \<notin> m" "(x, y) \<in> asym_factor m" "(x, y) \<notin> asym_factor (\<Union>C)"
          unfolding asym_factor_def by blast
    
        then obtain w where "w \<in> C" "(y, x) \<in> w"
          unfolding asym_factor_def using \<open>m \<in> C\<close> by auto

        with \<open>(y, x) \<notin> m\<close> have "\<not> extends m w"
          unfolding extends_def by auto
        moreover
        from \<open>(x, y) \<in> m\<close> have "\<not> extends w m"
        proof(cases "(x, y) \<in> w")
          case True
          with \<open>(y, x) \<in> w\<close> have "(x, y) \<notin> asym_factor w"
            unfolding asym_factor_def by simp
          with \<open>(x, y) \<in> asym_factor m\<close> show "\<not> extends w m"
            unfolding extends_def by auto
        qed (auto simp: extends_def)

        ultimately show False
          using \<open>m \<in> C\<close> \<open>w \<in> C\<close>
          using C_def[unfolded Chains_def order_of_orders_def strict_extends_def]
          by auto
      qed blast
    qed
  qed

  text \<open>Let our maximal element be named \<^term>\<open>max\<close>:\<close>

  from this obtain max 
    where max_field: "max \<in> Field order_of_orders"
      and is_max: 
        "\<forall>a\<in>Field order_of_orders. (max, a) \<in> order_of_orders \<longrightarrow> a = max"
    by auto

  from max_field have max_extends_base: "preorder_on A max" "strict_extends max base_r"
    using Field_order_of_orders by blast+

  text \<open>
    We still have to show, that \<^term>\<open>max\<close> is a strict linear order,
    meaning that it is also a total order:
  \<close>

  have "total_on A max"
  proof
    fix x y :: 'a
    assume "x \<noteq> y" "x \<in> A" "y \<in> A"

    show "(x, y) \<in> max \<or> (y, x) \<in> max"
    proof (rule ccontr)

      text \<open>
        Assume that \<^term>\<open>max\<close> is not total, and \<^term>\<open>x\<close> and \<^term>\<open>y\<close> are incomparable.
        Then we can extend \<^term>\<open>max\<close> by setting $x < y$:
      \<close>

      presume "(x, y) \<notin> max" and "(y, x) \<notin> max"
      let ?max' = "(insert (x, y) max)\<^sup>+"

      note max'_extends_max = can_extend_preorder[OF
          \<open>preorder_on A max\<close> \<open>y \<in> A\<close> \<open>x \<in> A\<close> \<open>(y, x) \<notin> max\<close>]

      hence max'_extends_base: "strict_extends ?max' base_r"
        using \<open>strict_extends max base_r\<close> transp_strict_extends by (auto elim: transpE)


      text \<open>The extended relation is greater than \<^term>\<open>max\<close>, which is a contradiction.\<close>

      have "(max, ?max') \<in> order_of_orders"
        using max'_extends_base max'_extends_max max_extends_base
        unfolding order_of_orders_def by simp
      thus False
        using FieldI2 \<open>(x, y) \<notin> max\<close> is_max by fastforce
    qed simp_all
  qed

  with \<open>preorder_on A max\<close> have "total_preorder_on A max"
    unfolding total_preorder_on_def by simp

  with \<open>strict_extends max base_r\<close> show "?thesis" by blast
qed

text \<open>
  With this extension theorem, we can easily prove Szpilrajn's theorem and its equivalent for
  partial orders.
\<close>

corollary partial_order_extension:
  assumes "partial_order_on A r"
  shows "\<exists>r_ext. linear_order_on A r_ext \<and> r \<subseteq> r_ext"
proof -
  from assms strict_extends_preorder_on obtain r_ext where r_ext:
    "total_preorder_on A r_ext" "strict_extends r_ext r"
    unfolding partial_order_on_def by blast

  with assms have "antisym r_ext"
    unfolding partial_order_on_def using strict_extends_antisym by blast

  with assms r_ext have "linear_order_on A r_ext \<and> r \<subseteq> r_ext"
    unfolding total_preorder_on_def order_on_defs strict_extends_def extends_def
    by blast
  then show ?thesis ..
qed

corollary Szpilrajn:
  assumes "strict_partial_order r"
  shows "\<exists>r_ext. strict_linear_order r_ext \<and> r \<subseteq> r_ext"
proof -
  from assms have "partial_order (r\<^sup>=)"
    by (auto simp: antisym_if_irrefl_trans strict_partial_order_def)
  from partial_order_extension[OF this] obtain r_ext where "linear_order r_ext" "(r\<^sup>=) \<subseteq> r_ext"
    by blast
  with assms have "r \<subseteq> r_ext - Id" "strict_linear_order (r_ext - Id)"
    by (auto simp: irrefl_def strict_linear_order_on_diff_Id dest: strict_partial_orderD(2))
  then show ?thesis by blast
qed

corollary acyclic_order_extension:
  assumes "acyclic r"
  shows "\<exists>r_ext. strict_linear_order r_ext \<and> r \<subseteq> r_ext"
proof -
  from assms have "strict_partial_order (r\<^sup>+)"
    unfolding strict_partial_order_def using acyclic_irrefl trans_trancl by blast
  thus ?thesis
    by (meson Szpilrajn r_into_trancl' subset_iff)
qed

section \<open>Consistency\<close>

text \<open>
  As a weakening of transitivity, Suzumura introduces the notion of consistency which rules out
  all preference cycles that contain at least one strict preference.
  Consistency characterises those order relations which can be extended (in terms of \<^term>\<open>extends\<close>)
  to a total order relation. 
\<close>

definition consistent :: "'a rel \<Rightarrow> bool"
  where "consistent r = (\<forall>(x, y) \<in> r\<^sup>+. (y, x) \<notin> asym_factor r)"

lemma consistentI: "(\<And>x y. (x, y) \<in> r\<^sup>+ \<Longrightarrow> (y, x) \<notin> asym_factor r) \<Longrightarrow> consistent r"
  unfolding consistent_def by blast

lemma consistent_if_preorder_on[simp]:
  "preorder_on A r \<Longrightarrow> consistent r"
  unfolding preorder_on_def consistent_def asym_factor_def by auto

lemma consistent_asym_factor[simp]: "consistent r \<Longrightarrow> consistent (asym_factor r)"
  unfolding consistent_def
  using asym_factor_tranclE by fastforce

lemma acyclic_asym_factor_if_consistent[simp]: "consistent r \<Longrightarrow> acyclic (asym_factor r)"
  unfolding consistent_def acyclic_def
  using asym_factor_tranclE by (metis case_prodD trancl.simps)

lemma consistent_Restr[simp]: "consistent r \<Longrightarrow> consistent (Restr r A)"
  unfolding consistent_def asym_factor_def
  using trancl_mono by fastforce

text \<open>
  This corresponds to Theorem 2.2~\<^cite>\<open>"Bossert:2010"\<close>.
\<close>
theorem trans_if_refl_total_consistent:
  assumes "refl r" "total r" and "consistent r"
  shows "trans r"
proof
  fix x y z assume "(x, y) \<in> r" "(y, z) \<in> r"
  
  from \<open>(x, y) \<in> r\<close> \<open>(y, z) \<in> r\<close> have "(x, z) \<in> r\<^sup>+"
    by simp
  hence "(z, x) \<notin> asym_factor r"
    using \<open>consistent r\<close> unfolding consistent_def by blast
  hence "x \<noteq> z \<Longrightarrow> (x, z) \<in> r"
    unfolding asym_factor_def using \<open>total r\<close>
    by (auto simp: total_on_def)
  then show "(x, z) \<in> r"
    apply(cases "x = z")
    using refl_onD[OF \<open>refl r\<close>] by blast+ 
qed


lemma order_extension_if_consistent:
  assumes "consistent r"
  obtains r_ext where "extends r_ext r" "total_preorder r_ext"  
proof -
  from assms have extends: "extends (r\<^sup>*) r"
    unfolding extends_def consistent_def asym_factor_def
    using rtranclD by (fastforce simp: Field_def)
  have preorder: "preorder (r\<^sup>*)"
    unfolding preorder_on_def using refl_on_def trans_def by fastforce

  from strict_extends_preorder_on[OF preorder] extends obtain r_ext where
    "total_preorder r_ext" "extends r_ext r"
    using transpE[OF transp_extends] unfolding strict_extends_def by blast
  then show thesis using that by blast
qed

lemma consistent_if_extends_trans:
  assumes "extends r_ext r" "trans r_ext"
  shows "consistent r"
proof(rule consistentI, standard)
  fix x y assume *: "(x, y) \<in> r\<^sup>+" "(y, x) \<in> asym_factor r"
  with assms have "(x, y) \<in> r_ext"
    using trancl_subs_extends_if_trans[OF assms] by blast
  moreover from * assms have "(x, y) \<notin> r_ext"
    unfolding extends_def asym_factor_def by auto
  ultimately show False by blast
qed

text \<open>
  With Theorem 2.6~\<^cite>\<open>"Bossert:2010"\<close>, we show that \<^term>\<open>consistent\<close> characterises the existence
  of order extensions.
\<close>
corollary order_extension_iff_consistent:
  "(\<exists>r_ext. extends r_ext r \<and> total_preorder r_ext) \<longleftrightarrow> consistent r"
  using order_extension_if_consistent consistent_if_extends_trans
  by (metis total_preorder_onD(2))


text \<open>
  The following theorem corresponds to Theorem 2.7~\<^cite>\<open>"Bossert:2010"\<close>.
  Bossert and Suzumura claim that this theorem generalises Szpilrajn's theorem; however, we cannot
  use the theorem to strictly extend a given order \<^term>\<open>Q\<close>. Therefore, it is not strong enough to
  extend a strict partial order to a strict linear order. It works for total preorders (called 
  orderings by Bossert and Suzumura). Unfortunately, we were not able to generalise the theorem
  to allow for strict extensions.
\<close>

theorem general_order_extension_iff_consistent:
  assumes "\<And>x y. \<lbrakk> x \<in> S; y \<in> S; x \<noteq> y \<rbrakk> \<Longrightarrow> (x, y) \<notin> Q\<^sup>+"
  assumes "total_preorder_on S Ord"
  shows "(\<exists>Ext. extends Ext Q \<and> total_preorder Ext \<and> Restr Ext S = Ord)
     \<longleftrightarrow> consistent Q" (is "?ExExt \<longleftrightarrow> _")
proof
  assume "?ExExt"
  then obtain Ext where
    "extends Ext Q"
    "refl Ext" "trans Ext" "total Ext"
    "Restr Ext S = Restr Ord S"
    using total_preorder_onD by fast
  show "consistent Q"
  proof(rule consistentI)
    fix x y assume "(x, y) \<in> Q\<^sup>+"
    with \<open>extends Ext Q\<close> \<open>trans Ext\<close> have "(x, y) \<in> Ext"
      unfolding extends_def by (metis trancl_id trancl_mono)
    then have "(y, x) \<notin> asym_factor Ext"
      unfolding asym_factor_def by blast
    with \<open>extends Ext Q\<close> show "(y, x) \<notin> asym_factor Q"
      unfolding extends_def asym_factor_def by blast
  qed
next
  assume "consistent Q"

  define Q' where "Q' \<equiv> Q\<^sup>* \<union> Ord \<union> Ord O Q\<^sup>* \<union> Q\<^sup>* O Ord \<union> (Q\<^sup>* O Ord) O Q\<^sup>*"

  have "refl (Q\<^sup>*)" "trans (Q\<^sup>*)" "refl_on S Ord" "trans Ord" "total_on S Ord"
    using refl_rtrancl trans_rtrancl total_preorder_onD[OF \<open>total_preorder_on S Ord\<close>]
    by - assumption

  have preorder_Q': "preorder Q'"
  proof
    show "refl Q'"
      unfolding Q'_def refl_on_def by auto

    from \<open>trans (Q\<^sup>*)\<close> \<open>refl_on S Ord\<close> \<open>trans Ord\<close> show "trans Q'"
      unfolding Q'_def[simplified]
      apply(safe intro!: transI)
      unfolding relcomp.simps
      by (metis assms(1) refl_on_domain rtranclD transD)+
  qed

  have "consistent Q'"
    using consistent_if_preorder_on preorder_Q' by blast

  have "extends Q' Q"
  proof(rule extendsI)
    have "Q \<subseteq> Restr (Q\<^sup>*) (Field Q)"
      by (auto intro: FieldI1 FieldI2)
    then show "Q \<subseteq> Q'"
      unfolding Q'_def by blast

    from \<open>consistent Q\<close> have consistentD: "(x, y) \<in> Q\<^sup>+ \<Longrightarrow> (y, x) \<in> Q \<Longrightarrow> (x, y) \<in> Q" for x y
      unfolding consistent_def asym_factor_def using rtranclD by fastforce
    have refl_on_domainE: "\<lbrakk> (x, y) \<in> Ord; x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" for x y P
      using refl_on_domain[OF \<open>refl_on S Ord\<close>] by blast

    show "asym_factor Q \<subseteq> asym_factor Q'"
      unfolding Q'_def asym_factor_def Field_def
      apply(safe)
      using assms(1) consistentD refl_on_domainE
      by (metis r_into_rtrancl rtranclD rtrancl_trancl_trancl)+
  qed

  with strict_extends_preorder_on[OF \<open>preorder Q'\<close>]
  obtain Ext where Ext: "extends Ext Q'" "extends Ext Q" "total_preorder Ext"
    unfolding strict_extends_def
    by (metis transpE transp_extends)

  have not_in_Q': "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> (x, y) \<notin> Ord \<Longrightarrow> (x, y) \<notin> Q'" for x y
    using assms(1) unfolding Q'_def
    apply(safe)
    by (metis \<open>refl_on S Ord\<close> refl_on_def refl_on_domain rtranclD)+

  have "Restr Ext S = Ord"
  proof
    from \<open>extends Ext Q'\<close> have "Ord \<subseteq> Ext"
      unfolding Q'_def extends_def by auto
    with \<open>refl_on S Ord\<close> show "Ord \<subseteq> Restr Ext S"
      using refl_on_domain by fast
  next
    have "(x, y) \<in> Ord" if "x \<in> S" and "y \<in> S" and "(x, y) \<in> Ext" for x y
    proof(rule ccontr)
      assume "(x, y) \<notin> Ord"
      with that not_in_Q' have "(x, y) \<notin> Q'"
        by blast
      with \<open>refl_on S Ord\<close> \<open>total_on S Ord\<close> \<open>x \<in> S\<close> \<open>y \<in> S\<close> \<open>(x, y) \<notin> Ord\<close>
      have "(y, x) \<in> Ord"
        unfolding refl_on_def total_on_def by fast
      hence "(y, x) \<in> Q'"
        unfolding Q'_def by blast
      with \<open>(x, y) \<notin> Q'\<close> \<open>(y, x) \<in> Q'\<close> \<open>extends Ext Q'\<close>
      have "(x, y) \<notin> Ext"
        unfolding extends_def asym_factor_def by auto
      with \<open>(x, y) \<in> Ext\<close> show False by blast
    qed
    then show "Restr Ext S \<subseteq> Ord"
      by blast
  qed

  with Ext show "?ExExt" by blast
qed

section \<open>Strong consistency\<close>

text \<open>
  We define a stronger version of \<^term>\<open>consistent\<close> which requires that the relation does not
  contain hidden preference cycles, i.e. if there is a preference cycle then all the elements
  in the cycle should already be related (in both directions).
  In contrast to consistency which characterises relations that can be extended, strong consistency
  characterises relations that can be extended strictly (cf. \<^term>\<open>strict_extends\<close>).
\<close>

definition "strongly_consistent r \<equiv> sym_factor (r\<^sup>+) \<subseteq> sym_factor (r\<^sup>=)"

lemma consistent_if_strongly_consistent: "strongly_consistent r \<Longrightarrow> consistent r"
  unfolding strongly_consistent_def consistent_def
  by (auto simp: sym_factor_def asym_factor_def) 

lemma strongly_consistentI: "sym_factor (r\<^sup>+) \<subseteq> sym_factor (r\<^sup>=) \<Longrightarrow> strongly_consistent r"
  unfolding strongly_consistent_def by blast

lemma strongly_consistent_if_trans_strict_extension:
  assumes "strict_extends r_ext r"
  assumes "trans r_ext"
  shows   "strongly_consistent r"
proof(unfold strongly_consistent_def, standard)
  fix x assume "x \<in> sym_factor (r\<^sup>+)"
  then show "x \<in> sym_factor (r\<^sup>=)"
    using assms trancl_subs_extends_if_trans[OF extends_if_strict_extends]
    by (metis sym_factor_mono strict_extendsE subsetD sym_factor_reflc)
qed

lemma strict_order_extension_if_consistent:
  assumes "strongly_consistent r"
  obtains r_ext where "strict_extends r_ext r" "total_preorder r_ext" 
proof -
  from assms have "strict_extends (r\<^sup>+) r"
    unfolding strongly_consistent_def strict_extends_def extends_def asym_factor_def sym_factor_def
    by (auto simp: Field_def dest: tranclD)
  moreover have "strict_extends (r\<^sup>*) (r\<^sup>+)"
    unfolding strict_extends_def extends_def
    by (auto simp: asym_factor_rtrancl sym_factor_def dest: rtranclD)
  ultimately have extends: "strict_extends (r\<^sup>*) r"
    using transpE[OF transp_strict_extends] by blast

  have "preorder (r\<^sup>*)"
    unfolding preorder_on_def using refl_on_def trans_def by fastforce
  from strict_extends_preorder_on[OF this] extends obtain r_ext where
    "total_preorder r_ext" "strict_extends r_ext r"
    using transpE[OF transp_strict_extends] by blast
  then show thesis using that by blast
qed


experiment begin

text \<open>We can instantiate the above theorem to get Szpilrajn's theorem.\<close>
lemma
  assumes "strict_partial_order r"
  shows "\<exists>r_ext. strict_linear_order r_ext \<and> r \<subseteq> r_ext"
proof -                  
  from assms[unfolded strict_partial_order_def] have "strongly_consistent r" "antisym r"
    unfolding strongly_consistent_def by (simp_all add: antisym_if_irrefl_trans)
  from strict_order_extension_if_consistent[OF this(1)] obtain r_ext
    where "strict_extends r_ext r" "total_preorder r_ext" 
    by blast
  with assms[unfolded strict_partial_order_def] 
  have "trans (r_ext - Id)" "irrefl (r_ext - Id)" "total (r_ext - Id)" "r \<subseteq> (r_ext - Id)"
    using strict_extends_antisym[OF _ \<open>antisym r\<close>]
    by (auto simp: irrefl_def elim: strict_extendsE intro: trans_diff_Id dest: total_preorder_onD)
  then show ?thesis
    unfolding strict_linear_order_on_def by blast
qed

end

 
(*<*)
end
(*>*)

