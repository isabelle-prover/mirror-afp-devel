(*  Title:      Two Generated Word Monoids_Intersection
    File:       Two_Generated_Word_Monoids_Intersection.Two_Generated_Word_Monoids_Intersection
    Author:     Štěpán Holub, Charles University
    Author:     Štěpán Starosta, CTU in Prague

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Two_Generated_Word_Monoids_Intersection
  imports Combinatorics_Words.Equations_Basic Combinatorics_Words.Binary_Code_Morphisms Combinatorics_Words_Graph_Lemma.Glued_Codes
begin

text
  \<open>The characterization of intersection of binary languages formalized here is due to @{cite Ka_intersections}.\<close>

chapter "Binary Intersection Formalized"

locale  binary_codes_coincidence_two_generators = binary_codes_coincidence +
  assumes  two_coins: "\<exists> r s r' s'. g r =\<^sub>m h s \<and> g r' =\<^sub>m h s' \<and> (r,s) \<noteq> (r',s')"

begin

lemma  criticalE':
  obtains p q r1 s1 r2 s2 where
    "g p \<cdot> \<alpha>\<^sub>g = h q \<cdot> \<alpha>\<^sub>h" and
    "g (p \<cdot> r1) = h (q \<cdot> s1)" and
    "g (p \<cdot> r2) = h (q \<cdot> s2)" and
    "r1 \<noteq> \<epsilon>" and "r2 \<noteq> \<epsilon>" and
    "hd r1 \<noteq> hd r2"
proof-
  obtain r s r' s' where "g r =\<^sub>m h s" and  "g r' =\<^sub>m h s'" and "(r,s) \<noteq> (r',s')"
    using two_coins by blast
  note eqs =  min_coinD[OF \<open>g r =\<^sub>m h s\<close>] min_coinD[OF \<open>g r' =\<^sub>m h s'\<close>]
  have "s \<cdot> s' \<noteq> s' \<cdot> s"
  proof
    assume "s \<cdot> s' = s' \<cdot> s"
    from arg_cong[OF this, of h]
    have "g (r \<cdot> r') = g (r' \<cdot> r)"
      unfolding g.morph h.morph using \<open>g r = h s\<close> \<open>g r' = h s'\<close> by argo
    from g.code_morph_code[OF this]
    have "r \<cdot> r' = r' \<cdot> r".
    from ruler_eq[OF \<open>r \<cdot> r' = r' \<cdot> r\<close>] ruler_eq[OF \<open>s \<cdot> s' = s' \<cdot> s\<close>]
    have "s \<le>p s' \<Longrightarrow> r \<le>p r'" and "s' \<le>p s \<Longrightarrow> r' \<le>p r"
      using \<open>g r = h s\<close> \<open>g r' = h s'\<close> g.pref_morph_pref_eq h.pref_mono by metis+
    hence "(r, s) = (r', s')"
      using \<open>s \<le>p s' \<or> s' \<le>p s\<close> \<open>g r =\<^sub>m h s\<close> \<open>g r' =\<^sub>m h s'\<close> npI
      unfolding min_coin_def by metis
    thus False
      using \<open>(r, s) \<noteq> (r', s')\<close> by blast
  qed
  hence "h (s \<cdot> s') \<cdot> \<alpha>\<^sub>h \<noteq> h (s' \<cdot> s) \<cdot> \<alpha>\<^sub>h"
    unfolding cancel_right using h.code_morph_code by blast
  hence "\<not> h (s \<cdot> s') \<cdot> \<alpha>\<^sub>h \<bowtie> h (s' \<cdot> s) \<cdot> \<alpha>\<^sub>h"
    unfolding h.morph using comm_comp_eq_conv comp_prefs_comp by metis
  hence h\<^sub>m: "h (s \<cdot> s') \<cdot> \<alpha>\<^sub>h \<cdot> \<alpha> \<and>\<^sub>p h(s' \<cdot> s) \<cdot> \<alpha>\<^sub>h \<cdot> \<alpha> = h (s \<cdot> s' \<and>\<^sub>p s' \<cdot> s) \<cdot> \<alpha>\<^sub>h"
    using lcp_ext_right_conv[of "h (s \<cdot> s') \<cdot> \<alpha>\<^sub>h" "h (s' \<cdot> s) \<cdot> \<alpha>\<^sub>h" "\<alpha>" "\<alpha>"]
      h.bin_code_lcp[symmetric] unfolding h.bin_code_lcp[symmetric] rassoc by blast

  let ?p = "r \<cdot> r' \<and>\<^sub>p r' \<cdot> r"
  let ?q = "s \<cdot> s' \<and>\<^sub>p s' \<cdot> s"
  let ?r1 = "?p\<inverse>\<^sup>>(r \<cdot> r')"
  let ?r2 = "?p\<inverse>\<^sup>>(r' \<cdot> r)"
  let ?s1 = "?q\<inverse>\<^sup>>(s \<cdot> s')"
  let ?s2 = "?q\<inverse>\<^sup>>(s' \<cdot> s)"

  from eqs
  have "g (r \<cdot> r') \<cdot> \<alpha>\<^sub>g = h (s \<cdot> s') \<cdot> \<alpha>\<^sub>h \<cdot> \<alpha>" and
    "g (r' \<cdot> r) \<cdot> \<alpha>\<^sub>g = h (s' \<cdot> s) \<cdot> \<alpha>\<^sub>h \<cdot> \<alpha>"
    unfolding g.morph h.morph  lcp_diff cancel_right by auto

  hence "g ?p \<cdot> \<alpha>\<^sub>g = h ?q \<cdot> \<alpha>\<^sub>h"
    unfolding g.bin_code_lcp[symmetric] h\<^sub>m[symmetric] by argo

  have "g (?p \<cdot> ?r1) = h (?q \<cdot> ?s1)"
    unfolding lq_pref[OF lcp_pref] g.morph h.morph \<open>g r = h s\<close> \<open>g r' = h s'\<close>..
  have "g (?p \<cdot> ?r2) = h (?q \<cdot> ?s2)"
    unfolding lq_pref[OF lcp_pref'] g.morph h.morph \<open>g r = h s\<close> \<open>g r' = h s'\<close>..

  have "r \<cdot> r' \<noteq> r' \<cdot> r"
  proof
    assume "r \<cdot> r' = r' \<cdot> r"
    from arg_cong[OF this, of g]
    have "h (s \<cdot> s') = h (s' \<cdot> s)"
      unfolding g.morph h.morph using \<open>g r = h s\<close> \<open>g r' = h s'\<close> by argo
    from h.code_morph_code[OF this] \<open>s \<cdot> s' \<noteq> s' \<cdot> s\<close>
    show False by blast
  qed
  from \<open>r \<cdot> r' \<noteq> r' \<cdot> r\<close>
  have "\<not> r \<cdot> r' \<bowtie> r' \<cdot> r"
    using comm_comp_eq by blast

  from that[OF \<open>g ?p \<cdot> \<alpha>\<^sub>g = h ?q \<cdot> \<alpha>\<^sub>h\<close> \<open>g (?p \<cdot> ?r1) = h (?q \<cdot> ?s1)\<close>
      \<open>g (?p \<cdot> ?r2) = h (?q \<cdot> ?s2)\<close>] lcp_mismatch_lq[OF \<open>\<not> r \<cdot> r' \<bowtie> r' \<cdot> r\<close>]
  show thesis
    by blast
qed

lemma alphas_suf: "\<alpha>\<^sub>h \<le>s \<alpha>\<^sub>g"
proof-
  from criticalE'
  obtain p q where "g p \<cdot> \<alpha>\<^sub>g = h q \<cdot> \<alpha>\<^sub>h" by meson
  from eqd[reversed, OF this[symmetric] alphas_len]
  show "\<alpha>\<^sub>h \<le>s \<alpha>\<^sub>g" by blast
qed

lemma c_def: "\<c> \<cdot> \<alpha>\<^sub>h = \<alpha>\<^sub>g"
  unfolding critical_overflow_def using rq_suf[OF alphas_suf].

lemma marked_version_solution_conv: "g\<^sub>m r = h\<^sub>m s \<longleftrightarrow> g r \<cdot> \<c>  = \<c> \<cdot>  h s"
  unfolding cancel_right[of "g r \<cdot> \<c>" \<alpha>\<^sub>h  "\<c> \<cdot> h s", symmetric] c_def rassoc
    g.marked_version_conjugates[symmetric] h.marked_version_conjugates[symmetric]
  unfolding lassoc c_def cancel..

lemma  criticalE:
  obtains p q r1 s1 r2 s2 where
    "\<alpha>\<^sub>g \<cdot> g\<^sub>m p = \<alpha>\<^sub>h \<cdot> h\<^sub>m q" and
    "\<And> p' q'. \<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q' \<Longrightarrow> p \<le>p p' \<and> q \<le>p q'" and
    "g\<^sub>m (r1 \<cdot> p) = h\<^sub>m (s1 \<cdot> q)" and
    "g\<^sub>m (r2 \<cdot> p) = h\<^sub>m (s2 \<cdot> q)" and
    "r1 \<cdot> p \<noteq> \<epsilon>" and "r2 \<cdot> p \<noteq> \<epsilon>" and
    "hd (r1 \<cdot> p) \<noteq> hd (r2 \<cdot> p)"
proof-
  from criticalE'
  obtain p' q' r1 s1 r2 s2 where
    "g p' \<cdot> \<alpha>\<^sub>g = h q' \<cdot> \<alpha>\<^sub>h" and
    "g (p' \<cdot> r1) = h (q' \<cdot> s1)" and
    "g (p' \<cdot> r2) = h (q' \<cdot> s2)" and
    "r1 \<noteq> \<epsilon>" and "r2 \<noteq> \<epsilon>" and
    "hd r1 \<noteq> hd r2".
  from this(1)[folded g.marked_version_conjugates h.marked_version_conjugates]
  have "\<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q'".
  from min_completionE[OF this]
  obtain p q where "\<alpha>\<^sub>g \<cdot> g\<^sub>m p = \<alpha>\<^sub>h \<cdot> h\<^sub>m q" and "\<And>p' q'. \<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q' \<Longrightarrow> p \<le>p p' \<and> q \<le>p q'"
    by blast
  show thesis
  proof(rule)
    show "\<alpha>\<^sub>g \<cdot> g\<^sub>m p = \<alpha>\<^sub>h \<cdot> h\<^sub>m q" by fact
    hence "g p \<cdot> \<c> = h q"
      unfolding g.marked_version_conjugates h.marked_version_conjugates unfolding c_def[symmetric] lassoc cancel_right.
    from  \<open>g (p' \<cdot> r1) = h (q' \<cdot> s1)\<close>[unfolded g.morph h.morph]
    have "g r1 = \<c> \<cdot> h s1"
      unfolding \<open>g p' \<cdot> \<alpha>\<^sub>g = h q' \<cdot> \<alpha>\<^sub>h\<close>[unfolded c_def[symmetric] lassoc cancel_right, symmetric] rassoc cancel.
    show "g\<^sub>m (r1 \<cdot> p) = h\<^sub>m (s1 \<cdot> q)"
      unfolding marked_version_solution_conv g.morph h.morph rassoc \<open>g p \<cdot> \<c> = h q\<close> \<open>g r1 = \<c> \<cdot> h s1\<close>..
    from  \<open>g (p' \<cdot> r2) = h (q' \<cdot> s2)\<close>[unfolded g.morph h.morph]
    have "g r2 = \<c> \<cdot> h s2"
      unfolding \<open>g p' \<cdot> \<alpha>\<^sub>g = h q' \<cdot> \<alpha>\<^sub>h\<close>[unfolded c_def[symmetric] lassoc cancel_right, symmetric] rassoc cancel.
    show "g\<^sub>m (r2 \<cdot> p) = h\<^sub>m (s2 \<cdot> q)"
      unfolding marked_version_solution_conv g.morph h.morph rassoc \<open>g p \<cdot> \<c> = h q\<close> \<open>g r2 = \<c> \<cdot> h s2\<close>..
    show "r1 \<cdot> p \<noteq> \<epsilon>"
      using \<open>r1 \<noteq> \<epsilon>\<close> by blast
    show "r2 \<cdot> p \<noteq> \<epsilon>"
      using \<open>r2 \<noteq> \<epsilon>\<close> by blast
    show "hd (r1 \<cdot> p) \<noteq> hd (r2 \<cdot> p)"
      using \<open>hd r1 \<noteq> hd r2\<close> \<open>r1 \<noteq> \<epsilon>\<close> \<open>r2 \<noteq> \<epsilon>\<close> by simp
    show " \<And>p' q'. \<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q' \<Longrightarrow> p \<le>p p' \<and> q \<le>p q'" by fact
  qed
qed

text \<open>Defining the beginning block\<close>

definition beginning_block :: "binA list * binA list"  where
  "beginning_block = (SOME pair. \<alpha>\<^sub>g \<cdot> g\<^sub>m (fst pair) = \<alpha>\<^sub>h \<cdot> h\<^sub>m (snd pair) \<and>
   (\<forall> p' q'. \<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q' \<longrightarrow> (fst pair) \<le>p p' \<and> (snd pair) \<le>p q'))"

definition fst_beginning_block ("p") where
  "fst_beginning_block \<equiv> fst beginning_block"
definition snd_beginning_block ("q") where
  "snd_beginning_block \<equiv> snd beginning_block"

lemma begin_block: "\<alpha> \<cdot> g\<^sub>m p = h\<^sub>m q" and
  begin_block_min: "\<alpha> \<cdot> g\<^sub>m p' = h\<^sub>m q' \<Longrightarrow> p \<le>p p' \<and> q \<le>p q'"
proof-
  from criticalE
  obtain pa qa r1 s1 r2 s2 where
   "\<alpha>\<^sub>g \<cdot> g\<^sub>m pa = \<alpha>\<^sub>h \<cdot> h\<^sub>m qa" and
  "(\<And>p' q'. \<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q' \<Longrightarrow> pa \<le>p p' \<and> qa \<le>p q')" and
   "g\<^sub>m (r1 \<cdot> pa) = h\<^sub>m (s1 \<cdot> qa)" and "g\<^sub>m (r2 \<cdot> pa) = h\<^sub>m (s2 \<cdot> qa)" and
   "r1 \<cdot> pa \<noteq> \<epsilon>" and "r2 \<cdot> pa \<noteq> \<epsilon>" and "hd (r1 \<cdot> pa) \<noteq> hd (r2 \<cdot> pa)" by blast
  hence *: "\<alpha>\<^sub>g \<cdot> g\<^sub>m (fst (pa, qa)) = \<alpha>\<^sub>h \<cdot> h\<^sub>m (snd (pa, qa)) \<and>
    (\<forall>p' q'. \<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q' \<longrightarrow> fst (pa, qa) \<le>p p' \<and> snd (pa, qa) \<le>p q')"
    unfolding fst_conv snd_conv by fast
  let ?P =  "\<lambda> pair. (\<alpha>\<^sub>g \<cdot> g\<^sub>m (fst pair) = \<alpha>\<^sub>h \<cdot> h\<^sub>m (snd pair) \<and>
   (\<forall> p' q'. \<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q' \<longrightarrow> (fst pair) \<le>p p' \<and> (snd pair) \<le>p q'))"
  from someI[of ?P, OF *]
  have pq: "\<alpha>\<^sub>g \<cdot> g\<^sub>m p = \<alpha>\<^sub>h \<cdot> h\<^sub>m q" "\<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q' \<Longrightarrow> p \<le>p p' \<and> q \<le>p q'"
    unfolding fst_beginning_block_def snd_beginning_block_def beginning_block_def
    by blast+
  show "\<alpha> \<cdot> g\<^sub>m p =  h\<^sub>m q" and "\<alpha> \<cdot> g\<^sub>m p' = h\<^sub>m q' \<Longrightarrow> p \<le>p p' \<and> q \<le>p q'"
    using pq unfolding lcp_diff[symmetric] rassoc cancel.
qed

lemma begin_block_conjug_conv:
  assumes "r \<cdot> p = p \<cdot> r'" and "s \<cdot> q = q \<cdot> s'"
  shows "g r = h s \<longleftrightarrow> g\<^sub>m r' = h\<^sub>m s'"
  unfolding solution_marked_version_conv
proof-
  have "\<alpha> \<cdot> g\<^sub>m r = h\<^sub>m s \<cdot> \<alpha> \<longleftrightarrow> \<alpha> \<cdot> g\<^sub>m r \<cdot> g\<^sub>m p = h\<^sub>m s \<cdot> \<alpha> \<cdot> g\<^sub>m p"
    unfolding lassoc cancel_right..
  also have "... \<longleftrightarrow> \<alpha> \<cdot> g\<^sub>m p \<cdot> g\<^sub>m r' = h\<^sub>m q \<cdot> h\<^sub>m s'"
    unfolding begin_block gm.morph[symmetric] hm.morph[symmetric] assms..
  also have "... \<longleftrightarrow> g\<^sub>m r' = h\<^sub>m s'"
    unfolding lassoc begin_block cancel..
  finally show "(\<alpha> \<cdot> g\<^sub>m r = h\<^sub>m s \<cdot> \<alpha>) = (g\<^sub>m r' = h\<^sub>m s')".
qed

lemma solution_ext_conv: "g r = h s \<longleftrightarrow> \<alpha> \<cdot> g\<^sub>m (r \<cdot> p) = h\<^sub>m (s \<cdot> q)"
  unfolding gm.morph hm.morph lassoc begin_block[symmetric]  cancel_right solution_marked_version_conv..

text \<open>Both block exist\<close>

lemma both_blocks: "marked.blockP c"
proof-
  from criticalE
  obtain p' q' r1 s1 r2 s2
    where "\<alpha>\<^sub>g \<cdot> g\<^sub>m p' = \<alpha>\<^sub>h \<cdot> h\<^sub>m q'"
          "g\<^sub>m (r1 \<cdot> p') = h\<^sub>m (s1 \<cdot> q')" "g\<^sub>m (r2 \<cdot> p') = h\<^sub>m (s2 \<cdot> q')" "r1 \<cdot> p' \<noteq> \<epsilon>" "r2 \<cdot> p' \<noteq> \<epsilon>" "hd (r1 \<cdot> p') \<noteq> hd (r2 \<cdot> p')".
  let ?ua = "r1 \<cdot> p'" let ?va = "s1 \<cdot> q'" let ?ub = "r2 \<cdot> p'" let ?vb = "s2 \<cdot> q'"
  obtain ea fa where "g\<^sub>m (ea) =\<^sub>m h\<^sub>m (fa)" and "hd ea = hd ?ua"
    using marked.min_coin_prefE[OF \<open>g\<^sub>m (?ua) = h\<^sub>m (?va)\<close> \<open>?ua \<noteq> \<epsilon>\<close>].
  obtain eb fb where "g\<^sub>m (eb) =\<^sub>m h\<^sub>m (fb)" and "hd eb = hd ?ub"
    using  marked.min_coin_prefE[OF \<open>g\<^sub>m ?ub = h\<^sub>m ?vb\<close> \<open>?ub \<noteq> \<epsilon>\<close>].
  from bin_neq_induct[OF \<open>hd ?ua \<noteq> hd ?ub\<close>[folded \<open>hd ea = hd ?ua\<close> \<open>hd eb = hd ?ub\<close>] marked.block_ex[OF \<open>g\<^sub>m ea =\<^sub>m h\<^sub>m fa\<close>] marked.block_ex[OF \<open>g\<^sub>m eb =\<^sub>m h\<^sub>m fb\<close>]]
  show "marked.blockP c".
qed

notation marked.suc_fst ("\<ee>") and
         marked.suc_snd ("\<ff>")

lemma sucs_eq: "g\<^sub>m (\<ee> \<tau>) = h\<^sub>m (\<ff> \<tau>)"
  using marked.blocks_eq both_blocks by blast

sublocale marked: two_binary_marked_blocks g\<^sub>m h\<^sub>m
  by unfold_locales (use both_blocks in fast)


section \<open>Blocks and intersection\<close>

text\<open>Every solution has a block decomposition. However, not all block combinations yield a solution. This motivates the following definition.\<close>

definition coin_block where "coin_block \<tau>  \<equiv> p \<le>s p \<cdot> (\<ee> \<tau>) \<and> q \<le>s q \<cdot> (\<ff> \<tau>)"

theorem  char_coincidence:
  "g r = h s \<longleftrightarrow> (\<exists> \<tau>. coin_block \<tau> \<and> r = (p \<cdot> \<ee> \<tau>)\<^sup><\<inverse>p \<and> s = (q \<cdot> \<ff> \<tau>)\<^sup><\<inverse>q)" (is "g r = h s \<longleftrightarrow> ?Q")
proof
  assume "g r = h s"
  hence "p \<le>p r \<cdot> p" and "q \<le>p s \<cdot> q"
    unfolding solution_ext_conv using begin_block_min  by blast+
  from lq_pref[OF this(1), symmetric] lq_pref[OF this(2), symmetric]
  have "r \<cdot> p = p \<cdot> p\<inverse>\<^sup>>(r \<cdot> p)" and "s \<cdot> q = q \<cdot> q\<inverse>\<^sup>>(s \<cdot> q)".
  hence "g\<^sub>m (p\<inverse>\<^sup>>(r \<cdot> p)) = h\<^sub>m (q\<inverse>\<^sup>>(s \<cdot> q))"
    using \<open>g r = h s\<close> begin_block_conjug_conv[of r "p\<inverse>\<^sup>> (r \<cdot> p)" s "q\<inverse>\<^sup>> (s \<cdot> q)"]
     by fast
  from marked.block_decomposition[OF this]
  obtain \<tau> where gsuc: "\<ee> \<tau> = p\<inverse>\<^sup>>(r \<cdot> p)" and hsuc: "\<ff> \<tau> = q\<inverse>\<^sup>>(s \<cdot> q)".
  note lq = lq_pref[OF \<open>p \<le>p r \<cdot> p\<close>] lq_pref[OF \<open>q \<le>p s \<cdot> q\<close>]
  have r: "r = (p \<cdot> \<ee> \<tau>)\<^sup><\<inverse>p" and s: "s = (q \<cdot> \<ff> \<tau>)\<^sup><\<inverse>q"
    unfolding \<open>\<ee> \<tau> = p\<inverse>\<^sup>>(r \<cdot> p)\<close> \<open>\<ff> \<tau> = q\<inverse>\<^sup>>(s \<cdot> q)\<close>lq rq_triv by simp_all
  have "coin_block \<tau>"
    unfolding coin_block_def gsuc hsuc lq using triv_suf by blast+
  thus ?Q
    using s r by blast
next
  assume ?Q
  then obtain \<tau> where "p \<le>s p \<cdot> (\<ee> \<tau>)" and "q \<le>s q \<cdot> (\<ff> \<tau>)"
    and r: "r = (p\<cdot> (\<ee> \<tau>))\<^sup><\<inverse>p" and s: "s = (q\<cdot>(\<ff> \<tau>))\<^sup><\<inverse>q" unfolding coin_block_def by blast
  hence gp: "g\<^sub>m p \<cdot> g\<^sub>m (\<ee> \<tau>) = g\<^sub>m ((p\<cdot>(\<ee> \<tau>))\<^sup><\<inverse>p) \<cdot> g\<^sub>m p"
    unfolding gm.morph[symmetric] rq_suf[OF \<open>p \<le>s p \<cdot> (\<ee> \<tau>)\<close>] by blast
  have hq: "h\<^sub>m q \<cdot> h\<^sub>m (\<ff> \<tau>) = h\<^sub>m ((q\<cdot>(\<ff> \<tau>))\<^sup><\<inverse>q) \<cdot> h\<^sub>m q"
    unfolding  hm.morph[symmetric] rq_suf[OF \<open>q \<le>s q \<cdot> (\<ff> \<tau>)\<close>] by blast
  from this
  show "g r = h s"
    unfolding begin_block[symmetric] sucs_eq[symmetric] rassoc gp
    unfolding lassoc cancel_right
    unfolding solution_marked_version_conv
    unfolding r s.
qed

theorem  char_coincidence':
  "g r = h s \<longleftrightarrow> (g\<^sub>m (p\<inverse>\<^sup>>(r \<cdot> p)) = h\<^sub>m (q\<inverse>\<^sup>>(s \<cdot> q)) \<and> p \<le>p r \<cdot> p \<and> q \<le>p s \<cdot> q)" (is "g r = h s \<longleftrightarrow> ?Q")
proof
  assume "g r = h s"
  from this[unfolded char_coincidence coin_block_def]
  obtain e f where  "g\<^sub>m e = h\<^sub>m f" "p \<le>s p \<cdot> e" "q \<le>s q \<cdot> f" "r = (p \<cdot> e)\<^sup><\<inverse>p" "s = (q \<cdot> f)\<^sup><\<inverse>q"
    using sucs_eq by blast
  have "r \<cdot> p = p \<cdot> e" and "s \<cdot> q = q \<cdot> f"
    unfolding \<open>r = (p \<cdot> e)\<^sup><\<inverse>p\<close> rq_suf[OF \<open>p \<le>s p \<cdot> e\<close>] \<open>s = (q \<cdot> f)\<^sup><\<inverse>q\<close> rq_suf[OF \<open>q \<le>s q \<cdot> f\<close>] by blast+
  hence "e = p\<inverse>\<^sup>>(r \<cdot> p)" and "f = q\<inverse>\<^sup>>(s \<cdot> q)"
    using lq_triv by fastforce+
  from \<open>g\<^sub>m e = h\<^sub>m f\<close>[unfolded this]
  show ?Q
    using triv_pref \<open>r \<cdot> p = p \<cdot> e\<close> \<open>s \<cdot> q = q \<cdot> f\<close> by blast
next
  assume ?Q
  hence "g\<^sub>m (p\<inverse>\<^sup>>(r \<cdot> p)) = h\<^sub>m (q\<inverse>\<^sup>>(s \<cdot> q))" and "p \<le>p r \<cdot> p" and "q \<le>p s \<cdot> q"
    by blast+
  from this(1)
  show "g r = h s"
    unfolding begin_block_conjug_conv[of r "p\<inverse>\<^sup>>(r \<cdot> p)" s "q\<inverse>\<^sup>>(s \<cdot> q)", OF lq_pref[symmetric] lq_pref[symmetric], OF \<open>p \<le>p r \<cdot> p\<close> \<open>q \<le>p s \<cdot> q\<close>].
qed

theorem coincidence_eq_blocks: "\<CC> g h = {((p \<cdot> \<ee> \<tau>)\<^sup><\<inverse>p,(q \<cdot> \<ff> \<tau>)\<^sup><\<inverse>q) | \<tau>. coin_block \<tau>}"
  unfolding coincidence_set_def
  using pairs_extensional'[OF char_coincidence].

lemma
  minblock0:  "g\<^sub>m (\<ee> \<aa>) =\<^sub>m h\<^sub>m (\<ff> \<aa>)" and
  minblock1:  "g\<^sub>m (\<ee> \<bb>) =\<^sub>m h\<^sub>m (\<ff> \<bb>)" and
  hdblock0:   "hd (\<ee> \<aa>)  = bina" and
  hdblock1:   "hd (\<ee> \<bb>) = binb"
  using marked.blockP_D both_blocks marked.blockP_D_hd  by blast+

definition \<T> where "\<T> \<equiv> {\<tau> . coin_block \<tau>}"

lemma \<T>_def': "\<tau> \<in> \<T> \<longleftrightarrow> coin_block \<tau>"
  unfolding \<T>_def mem_Collect_eq..

text\<open>Properties of the set of coincidence blocks\<close>

lemma \<T>_closed: assumes "coin_block \<tau>\<^sub>1" and "coin_block \<tau>\<^sub>2"
  shows "coin_block (\<tau>\<^sub>1\<cdot>\<tau>\<^sub>2)"
proof-
  from assms
  have "p \<le>s p \<cdot> \<ee> \<tau>\<^sub>2" and "p \<le>s p \<cdot> \<ee> \<tau>\<^sub>1" and
    "q \<le>s q \<cdot> \<ff> \<tau>\<^sub>2" and "q \<le>s q \<cdot> \<ff> \<tau>\<^sub>1"
    unfolding coin_block_def by blast+
  from suf_prolong[OF this(1-2), unfolded rassoc] suf_prolong[OF this(3-4), unfolded rassoc]
  show "coin_block (\<tau>\<^sub>1\<cdot>\<tau>\<^sub>2)"
    unfolding coin_block_def marked.sucs.h.morph marked.sucs.g.morph by blast
qed

lemma emp_block: "coin_block \<epsilon>"
  unfolding coin_block_def marked.sucs.g.emp_to_emp marked.sucs.h.emp_to_emp by force

lemma \<T>_hull:  "\<langle>\<T>\<rangle> = \<T>"
proof (intro hull_I)
  show "\<epsilon> \<in> \<T>"
    unfolding \<T>_def' coin_block_def marked.sucs.g.emp_to_emp marked.sucs.h.emp_to_emp by force
  show "\<And>x y. x \<in> \<T> \<Longrightarrow> y \<in> \<T> \<Longrightarrow> x \<cdot> y \<in> \<T>"
    unfolding \<T>_def' using \<T>_closed.
qed

lemma  \<T>_pref: "coin_block \<tau>\<^sub>1 \<Longrightarrow> coin_block (\<tau>\<^sub>1 \<cdot> \<tau>\<^sub>2) \<Longrightarrow> coin_block \<tau>\<^sub>2"
  using suf_prod_suf[of p "p \<cdot> \<ee> \<tau>\<^sub>1" "\<ee> \<tau>\<^sub>2"]
    suf_prod_suf[of q "q \<cdot> \<ff> \<tau>\<^sub>1" "\<ff> \<tau>\<^sub>2"]
  unfolding coin_block_def marked.sucs.g.morph marked.sucs.h.morph rassoc
  by blast

text \<open>Translation from blocks to the intersection\<close>

lemma translate_coin_blocks_to_intersection:
  "(h \<circ> (\<lambda> x. (q \<cdot> x)\<^sup><\<inverse>q) \<circ> \<ff>) ` \<T> = range g \<inter> range h"
  unfolding coin_set_inter_snd[of h g, unfolded coincidence_eq_blocks, symmetric] \<T>_def
proof-
  have   "(h \<circ> snd) ` {(F x, G x) | x. coin_block x} = {h (G x) | x. coin_block x}" for F G :: "binA list \<Rightarrow> binA list"
    by (standard, standard, auto, force)
  note rule1 = this[of "\<lambda>\<tau>. (p \<cdot> \<ee> \<tau>)\<^sup><\<inverse>p" "\<lambda>\<tau>. (q \<cdot> \<ff> \<tau>)\<^sup><\<inverse>q"]
  have "(h \<circ> I \<circ> \<ff>) ` {x . coin_block x} = {h (I (\<ff> x))| x. coin_block x}" for I
    by rule auto
  from this[of "(\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q)", folded rule1]
  show "(h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) ` Collect coin_block =
    (h \<circ> snd) ` {((p \<cdot> \<ee> \<tau>)\<^sup><\<inverse>p , (q \<cdot> \<ff> \<tau>)\<^sup><\<inverse>q ) |\<tau>. coin_block \<tau>}".
qed

lemma translation_blocks_inj:
  "inj_on (h \<circ> (\<lambda> x. (q \<cdot> x)\<^sup><\<inverse>q) \<circ> \<ff>) \<langle>\<T>\<rangle>"
proof
  fix x y assume "x \<in> \<langle>\<T>\<rangle>" and "y \<in> \<langle>\<T>\<rangle>"
  hence "q \<le>s q \<cdot> \<ff> x" and "q \<le>s q \<cdot> \<ff> y" unfolding \<T>_def' \<T>_hull coin_block_def by blast+
  assume "(h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) x = (h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) y"
  hence "h ((q \<cdot> \<ff> x)\<^sup><\<inverse>q) = h ((q \<cdot> \<ff> y)\<^sup><\<inverse>q)"
    by simp
  from h.code_morph_code[OF this] rq_suf[OF \<open>q \<le>s q \<cdot> \<ff> x\<close>] rq_suf[OF \<open>q \<le>s q \<cdot> \<ff> y\<close>]
  have "\<ff> x = \<ff> y"
    unfolding cancel[of q "\<ff> x" "\<ff> y", symmetric] by argo
  thus "x = y"
    using marked.sucs.h.code_morph_code by blast
qed

lemma translation_blocks_morph_on:  "morphism_on (h \<circ> (\<lambda> x. (q \<cdot> x)\<^sup><\<inverse>q) \<circ> \<ff>) \<T>"
proof
  fix x y assume "x \<in> \<langle>\<T>\<rangle>" and "y \<in> \<langle>\<T>\<rangle>"
  hence "q \<le>s q \<cdot> \<ff> x" and "q \<le>s q \<cdot> \<ff> y"
    unfolding \<T>_hull \<T>_def' coin_block_def by blast+
  show "(h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) (x \<cdot> y) =
           (h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) x\<cdot> (h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) y"
    unfolding comp_apply h.morph[symmetric] rq_reassoc[OF \<open>q \<le>s q \<cdot> \<ff> y\<close>] lassoc rq_suf[OF \<open>q \<le>s q \<cdot> \<ff> x\<close>]
    unfolding rassoc marked.sucs.h.morph..
qed

interpretation  morphism_on "(h \<circ> (\<lambda> x. (q \<cdot> x)\<^sup><\<inverse>q) \<circ> \<ff>)" \<T>
  using translation_blocks_morph_on.

theorem inter_basis: "\<BB> (range g \<inter> range h) = (h \<circ> (\<lambda> x. (q \<cdot> x)\<^sup><\<inverse>q) \<circ> \<ff>) ` (\<BB> \<T>)"
  using inj_basis_to_basis[OF translation_blocks_inj, unfolded \<T>_hull]
    translate_coin_blocks_to_intersection by presburger


section \<open>Simple blocks\<close>

text \<open>If both letters are blocks, the situation is easy\<close>

theorem simple_blocks:  assumes "\<And> a. coin_block [a]" shows
  "coin_block \<tau>"
  by (induct "\<tau>", simp add: emp_block)
    (use assms \<T>_closed[OF assms] hd_word in force)

theorem simple_blocks_UNIV: "(\<And> a. coin_block [a]) \<Longrightarrow> \<T> = UNIV"
  using simple_blocks \<T>_def' by auto

theorem simple_blocks_basis: assumes "\<And>a. coin_block [a]"
  shows "\<BB> \<T> = {\<aa>, \<bb>}"
  using  basis_of_hull[of "{\<aa>,\<bb>}"] code.code_is_basis[OF bin_basis_code]
  unfolding bin_basis_generates simple_blocks_UNIV[OF assms, symmetric]
  by argo

section \<open>At least one block\<close>

text \<open>At least one letter -- the last one -- is a block\<close>

lemma last_letter_fst_suf: assumes "coin_block (z \<cdot> [c])"
  shows  "p <s \<ee> [c]"
proof-
  from assms
  have "p \<le>s p \<cdot> \<ee> (z \<cdot> [c])" and "q \<le>s q \<cdot> \<ff> (z \<cdot> [c])"
    unfolding coin_block_def by blast+
  hence "p \<bowtie>\<^sub>s \<ee> [c]" and "q \<bowtie>\<^sub>s \<ff> [c]"
    unfolding marked.sucs.g.morph marked.sucs.h.morph lassoc using ruler_suf'' by blast+
  have "\<not> \<ee> [c] \<le>s p"
  proof
    assume "\<ee> [c] \<le>s p"
    hence "g\<^sub>m (\<ee> [c]) \<le>s \<alpha> \<cdot> g\<^sub>m p"
      using gm.suf_mono suf_ext by blast
    hence "h\<^sub>m (\<ff> [c]) \<le>s h\<^sub>m q"
      unfolding begin_block sucs_eq.
    hence "\<ff> [c] \<le>s q"
      using hm.suf_mono
        \<open>q \<bowtie>\<^sub>s \<ff> [c]\<close>[unfolded suf_comp_or] hm.code_morph_code  suffix_order.antisym by metis
    have "\<alpha> \<cdot> g\<^sub>m (p\<^sup><\<inverse>\<ee> [c] \<cdot> \<ee> [c]) = h\<^sub>m (q\<^sup><\<inverse>\<ff>[c] \<cdot> \<ff>[c])"
      unfolding rq_suf[OF \<open>\<ee> [c] \<le>s p\<close>] rq_suf[OF \<open>\<ff> [c] \<le>s q\<close>] begin_block[symmetric]..
    hence "\<alpha> \<cdot> g\<^sub>m (p\<^sup><\<inverse>\<ee> [c]) = h\<^sub>m (q\<^sup><\<inverse>\<ff>[c])"
      unfolding gm.morph hm.morph marked.block_eq[OF both_blocks] lassoc cancel_right.
    from conjunct1[OF begin_block_min[OF this]]
    have "\<ee> [c] = \<epsilon>"
      using rq_suf[OF \<open>\<ee> [c] \<le>s p\<close>] same_prefix_nil by metis
    thus False
      using marked.sucs.g.sing_to_nemp by blast
  qed
  thus "p <s \<ee> [c]"
    unfolding strict_suffix_def using \<open>p \<bowtie>\<^sub>s \<ee> [c]\<close>[unfolded suf_comp_or]
    by metis
qed

lemma rich_block_suf_fst':
  assumes "coin_block (z \<cdot> [1-c] \<cdot> [c]\<^sup>@Suc i)"
  shows "gm.bin_code_lcs \<cdot> g\<^sub>m p \<le>s g\<^sub>m (\<ee> ([1-c]\<cdot>[c]\<^sup>@Suc i))"
proof-
  from last_letter_fst_suf assms[unfolded pow_Suc' lassoc]
  have "p <s \<ee> [c]"
    by blast
  hence "\<ee> [c] = [c] \<cdot> tl (\<ee> [c])"
    using marked.blockP_D_hd[OF both_blocks[of c]] hd_tl[OF marked.sucs.g.sing_to_nemp] by metis
  then obtain p' where "\<ee> [c] = [c] \<cdot> p' \<cdot> p"
    using ssufE[OF \<open>p <s \<ee> [c]\<close>] ssuf_tl_suf suffix_def by metis
  hence *: "\<ee>([1-c] \<cdot> [c]\<^sup>@Suc i) = \<ee> ([1-c] \<cdot> [c]\<^sup>@i) \<cdot> [c] \<cdot> p' \<cdot> p"
    unfolding pow_Suc' marked.sucs.g.morph by force
  have f1: "[c] \<le>f \<ee> ([1 - c] \<cdot> [c] \<^sup>@ i) \<cdot> [c] \<cdot> p'"
    by fast
  have "[1 - c] \<le>f ([1 - c] \<cdot> tl (\<ee> [1 - c])) \<cdot> \<ee> ([c] \<^sup>@ i) \<cdot> [c] \<cdot> p'"
    unfolding rassoc by blast
  from this[unfolded hd_tl[OF marked.sucs.g.sing_to_nemp, of "1-c", unfolded marked.blockP_D_hd[OF both_blocks[of "1-c"]]]]
  have f2: "[1-c] \<le>f \<ee> ([1 - c] \<cdot> [c] \<^sup>@ i) \<cdot> [c] \<cdot> p'"
    unfolding marked.sucs.g.morph rassoc.
  from marked.revs.g.bin_lcp_pref''[reversed, OF f1 f2, unfolded g.marked_lcs] g.marked_lcs
  show "gm.bin_code_lcs \<cdot> g\<^sub>m p \<le>s g\<^sub>m (\<ee> ([1-c]\<cdot>[c]\<^sup>@Suc i))"
    unfolding * gm.morph lassoc suf_cancel_conv lcp_diff[symmetric] by simp
qed

lemma rich_block_suf_fst:
  assumes "coin_block (z \<cdot> [1-c] \<cdot> [c]\<^sup>@Suc i)"
  shows "\<alpha> \<cdot> g\<^sub>m (p) \<le>s g\<^sub>m (\<ee> ([1-c]\<cdot>[c]\<^sup>@Suc i))"
  using rich_block_suf_fst'[OF assms]
  using g.marked_lcs lcp_diff[symmetric] rassoc
  using suf_extD by metis

lemma rich_block_suf_snd':
  assumes "coin_block (z \<cdot> [1-c] \<cdot> [c]\<^sup>@Suc i)"
  shows "\<alpha>\<^sub>h \<cdot> h\<^sub>m q \<le>s h\<^sub>m (\<ff> ([1-c]\<cdot>[c]\<^sup>@Suc i))"
  using rich_block_suf_fst'[OF assms, unfolded marked.suc_eq'[OF both_blocks] g.marked_lcs rassoc]
  unfolding lcp_diff[symmetric] rassoc begin_block
  using  suf_extD by blast

lemma rich_block_suf_snd:
  assumes "coin_block (z \<cdot> [1-c] \<cdot> [c]\<^sup>@Suc i)"
  shows "q \<le>s \<ff> ([1-c]\<cdot>[c]\<^sup>@Suc i)"
proof(rule ccontr)
  assume notsuf: "\<not> q \<le>s \<ff> ([1 - c] \<cdot> [c] \<^sup>@ Suc i)"
  from conjunct2[OF assms[unfolded coin_block_def]]
  have "q \<le>s (q \<cdot> \<ff> z) \<cdot> \<ff> ([1 - c] \<cdot> [c] \<^sup>@ Suc i)"
    unfolding marked.sucs.h.morph rassoc.
  note ruler = suf_ruler[OF this triv_suf]
  from this
  have "\<ff> ([1 - c] \<cdot> [c] \<^sup>@ Suc i) <s q"
    using notsuf suffix_order.less_le_not_le by blast
   from hm.ssuf_mono[OF this]  rich_block_suf_fst[OF assms, unfolded marked.suc_eq'[OF both_blocks] begin_block]
  show False by force
qed

lemma  last_letter_block: assumes "coin_block (z \<cdot> [c])"
  shows "coin_block [c]"
proof (cases)
  assume "z \<in> [c]*"
  from sing_pow_exp[OF this]
  obtain i where "z = [c]\<^sup>@i"
    by blast
  have "z \<cdot> [c] = [c]\<^sup>@Suc i"
    unfolding \<open>z = [c]\<^sup>@i\<close> pow_Suc'..
  have "\<ee> (z \<cdot> [c]) = (\<ee> [c])\<^sup>@Suc i" and "\<ff> (z \<cdot> [c]) = (\<ff> [c])\<^sup>@Suc i"
    unfolding \<open>z \<cdot> [c] = [c]\<^sup>@Suc i\<close> marked.sucs.g.pow_morph marked.sucs.h.pow_morph by simp_all
  from \<open>coin_block (z \<cdot> [c])\<close>[unfolded coin_block_def this]
  show "coin_block [c]"
    unfolding coin_block_def using per_drop_exp_rev[OF zero_less_Suc] by metis
next
  assume "z \<notin> [c]*"
  from distinct_letter_in_suf[OF this]
  obtain t z' b where z: "z = z' \<cdot> [b] \<cdot> [c]\<^sup>@t" and "b \<noteq> c"
    unfolding suffix_def by metis
  have "p <s \<ee> [c]"
    using last_letter_fst_suf[OF \<open>coin_block (z \<cdot> [c])\<close>].
  from ssufD[OF this, unfolded suffix_def]
  obtain p' where "p'\<cdot> p = \<ee>[c]" and "p' \<noteq> \<epsilon>" by force
  hence "hd p' = c"
    using marked.blockP_D_hd[OF both_blocks[of c]] hd_append2[OF \<open>p' \<noteq> \<epsilon>\<close>, of p] by argo
  hence "\<ee>[c] = [c] \<cdot> tl p' \<cdot> p"
    unfolding \<open>p'\<cdot> p = \<ee>[c]\<close>[symmetric] using hd_tl[OF \<open>p' \<noteq> \<epsilon>\<close>] by simp
  show "coin_block [c]"
  proof(cases)
    assume "q \<le>s q \<cdot> \<ff> [c]"
    thus "coin_block [c]"
      unfolding coin_block_def using ssufD1[OF ssuf_ext[OF \<open>p <s \<ee> [c]\<close>]] by blast
  next \<comment> \<open>the other option leads to a contradiction\<close>
    write
      marked.sucs.h.bin_morph_mismatch_suf ("\<dd>") and
      marked.sucs.h.bin_code_lcs ("\<beta>\<^sub>\<hh>") and
      hm.bin_code_lcs ("\<beta>\<^sub>H") and
      gm.bin_code_lcs ("\<beta>\<^sub>G") and
      g.bin_code_lcs ("\<beta>\<^sub>g")
    assume "\<not> q \<le>s q \<cdot> \<ff> [c]"
      \<comment> \<open>suffix of @{term q}\<close>
    hence "\<not> q \<le>s q \<cdot> \<ff> ([c]\<^sup>@ Suc t)"
      unfolding marked.sucs.h.pow_morph using per_drop_exp'[reversed] by blast
    hence "\<not> q \<le>s \<beta>\<^sub>\<hh> \<cdot> \<ff> ([c]\<^sup>@Suc t)"
      using suf_prolong_per_root[OF _ marked.sucs.revs.h.bin_lcp_pref_all[reversed], of q "[c]\<^sup>@Suc t"] by blast

\<comment> \<open>analysis of q\<close>
    have "q \<le>s q \<cdot> \<ff>(z' \<cdot> [b] \<cdot> [c]\<^sup>@Suc t)"
      using \<open>coin_block (z \<cdot> [c])\<close>
      unfolding z coin_block_def rassoc pow_Suc' by blast
    note per_exp_pref[reversed, OF this, of 2, unfolded pow_two]
    hence suf1:  "q \<le>s q \<cdot> \<ff> (z' \<cdot> [b]) \<cdot> \<ff> ([c] \<^sup>@ Suc t \<cdot> z' \<cdot> [b]) \<cdot> \<ff> ([c] \<^sup>@ Suc t)"
      unfolding marked.sucs.h.morph rassoc.
    have "[\<dd> b] \<cdot> \<beta>\<^sub>\<hh> \<le>s \<ff> ([c]\<^sup>@Suc t \<cdot> z') \<cdot> \<ff> [b]"
      by (rule marked.sucs.revs.h.bin_lcp_mismatch_pref_all_set[reversed])
        (unfold bin_neq_swap[OF \<open>b \<noteq> c\<close>], simp)
    from this[folded marked.sucs.h.morph lassoc, unfolded suffix_def]
    obtain zs where "\<ff> ([c] \<^sup>@ Suc t \<cdot> z' \<cdot> [b]) = zs \<cdot> [\<dd> b] \<cdot> \<beta>\<^sub>\<hh>"
      by blast
    have suf2: "[\<dd> b] \<cdot> \<beta>\<^sub>\<hh> \<cdot> \<ff> ([c]\<^sup>@Suc t) \<le>s q \<cdot> \<ff> (z' \<cdot> [b]) \<cdot> \<ff> ([c] \<^sup>@ Suc t \<cdot> z' \<cdot> [b]) \<cdot> \<ff> ([c] \<^sup>@ Suc t)"
      unfolding \<open>\<ff> ([c] \<^sup>@ Suc t \<cdot> z' \<cdot> [b]) = zs \<cdot> [\<dd> b] \<cdot> \<beta>\<^sub>\<hh>\<close>
      using triv_suf[of "[\<dd> b] \<cdot> \<beta>\<^sub>\<hh> \<cdot> \<ff> ([c] \<^sup>@ Suc t)" "q \<cdot> \<ff> (z' \<cdot> [b]) \<cdot> zs"] unfolding rassoc.
    have "q \<bowtie>\<^sub>s [\<dd> b] \<cdot> \<beta>\<^sub>\<hh> \<cdot> \<ff> ([c]\<^sup>@Suc t)"
      using ruler[reversed, OF suf1 suf2] unfolding suf_comp_or.
    with \<open>\<not> q \<le>s \<beta>\<^sub>\<hh> \<cdot> \<ff> ([c]\<^sup>@Suc t)\<close>
    have "[\<dd> b] \<cdot> \<beta>\<^sub>\<hh> \<cdot> \<ff> ([c]\<^sup>@Suc t) \<le>s q"
      unfolding suf_comp_or hd_word[symmetric] suffix_Cons using suffix_order.eq_refl[OF sym, of q] by blast
    from suffixE[OF this]
    obtain q' where q_factors: "q = q' \<cdot> [\<dd> b] \<cdot> \<beta>\<^sub>\<hh> \<cdot> \<ff> ([c] \<^sup>@ Suc t)".

\<comment> \<open>length of @{term "\<beta>\<^sub>H \<and>\<^sub>p \<alpha>"}\<close>
\<comment> \<open>1. inequality\<close>
    from marked.lcs_fst_suf_snd
    have "\<beta>\<^sub>G \<le>s \<beta>\<^sub>H \<cdot> h\<^sub>m \<beta>\<^sub>\<hh>".
    from suf_len[OF this, unfolded lenmorph]
    have ineq1: "\<^bold>|\<beta>\<^sub>G\<^bold>| \<le> \<^bold>|\<beta>\<^sub>H\<^bold>| + \<^bold>|h\<^sub>m \<beta>\<^sub>\<hh>\<^bold>|"
      using lenarg[OF lcp_diff, unfolded lenmorph] by linarith
        \<comment> \<open>2. inequality\<close>
    from begin_block[unfolded q_factors, unfolded pow_Suc' marked.sucs.h.morph hm.morph, folded sucs_eq[of "[c]"], unfolded \<open>\<ee>[c] = [c] \<cdot> tl p' \<cdot> p\<close> gm.morph lassoc cancel_right, unfolded rassoc]
    have "\<alpha> = h\<^sub>m q' \<cdot> h\<^sub>m [\<dd> b] \<cdot> h\<^sub>m \<beta>\<^sub>\<hh> \<cdot> h\<^sub>m (\<ff> ([c] \<^sup>@ t)) \<cdot> g\<^sub>m [c] \<cdot> g\<^sub>m (tl p')".
    from lenarg[OF this] lenarg[OF lcp_diff]
    have ineq2: "\<^bold>|h\<^sub>m [\<dd> b]\<^bold>| + \<^bold>|g\<^sub>m [c]\<^bold>| + \<^bold>|h\<^sub>m \<beta>\<^sub>\<hh>\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>g\<^bold>|"
      unfolding lenmorph by linarith
        \<comment> \<open>conclusions\<close>
    have concl1: "\<^bold>|h\<^sub>m [\<dd> b]\<^bold>| + \<^bold>|g\<^sub>m [c]\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>g\<^bold>|"
      using ineq2 by linarith
    have concl2: "\<^bold>|h\<^sub>m [\<dd> b]\<^bold>| + \<^bold>|g\<^sub>m [c]\<^bold>| \<le> \<^bold>|\<beta>\<^sub>H\<^bold>|"
      using ineq1 ineq2 lenarg[OF g.marked_lcs, unfolded lenmorph]
      by linarith
    from suf_comp_monotone[OF marked.suf_comp_lcs] sufI[OF g.marked_lcs[symmetric]]
    have "\<alpha>\<^sub>g \<bowtie>\<^sub>s \<beta>\<^sub>H"
      by blast
    have concl: "\<^bold>|h\<^sub>m [\<dd> b]\<^bold>| + \<^bold>|g\<^sub>m [c]\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>g \<and>\<^sub>s \<beta>\<^sub>H\<^bold>|"
      by (rule disjE[OF \<open>\<alpha>\<^sub>g \<bowtie>\<^sub>s \<beta>\<^sub>H\<close>[unfolded suf_comp_or], unfolded lcs_suf_conv[symmetric] lcs_sym[of \<beta>\<^sub>H]])
        (use concl1 concl2 in argo)+

\<comment> \<open>two periods of @{term "\<alpha>\<^sub>g \<and>\<^sub>s \<beta>\<^sub>H"}\<close>
    have "\<alpha>\<^sub>g \<le>s \<alpha>\<^sub>g \<cdot> g\<^sub>m [c]"
      unfolding g.marked_version_conjugates by blast
    hence per1: "\<alpha>\<^sub>g \<and>\<^sub>s \<beta>\<^sub>H \<le>s (\<alpha>\<^sub>g \<and>\<^sub>s \<beta>\<^sub>H) \<cdot> g\<^sub>m [c]"
      using lcs_suf suf_keeps_root by blast
    have "\<beta>\<^sub>H \<le>s \<beta>\<^sub>H \<cdot> h\<^sub>m [\<dd> b]"
      using marked.revs.h.bin_lcp_pref_all[reversed].
    hence per2: "\<alpha>\<^sub>g \<and>\<^sub>s \<beta>\<^sub>H \<le>s (\<alpha>\<^sub>g \<and>\<^sub>s \<beta>\<^sub>H) \<cdot> h\<^sub>m [\<dd> b]"
      using lcs_suf' suf_keeps_root by blast
    from two_pers[reversed, OF per2 per1 concl]
    have "g\<^sub>m [c] \<cdot> h\<^sub>m [\<dd> b] = h\<^sub>m [\<dd> b] \<cdot> g\<^sub>m [c]".

    from marked.comm_sings_block[OF this]
    obtain n where "\<ff> [c] = [\<dd> b] \<^sup>@ Suc n" by blast
    from marked.sucs.h.sing_pow_mismatch_suf[OF \<open>\<ff> [c] = [\<dd> b] \<^sup>@ Suc n\<close>]
         \<open>b \<noteq> c\<close> marked.sucs.h.bin_mismatch_suf_inj
    have False
      unfolding inj_on_def by blast
    thus "coin_block [c]"
      by blast
  qed
qed

end

section "Infinite case"

locale  binary_codes_coincidence_infinite = binary_codes_coincidence_two_generators for a1 +
  assumes non_block: "\<not> coin_block [a1]"

begin

subsection \<open>Description of coincidence blocks\<close>

lemma swap_coin_block: "coin_block [1-a1]"
proof-
  obtain u v where "g u =\<^sub>m h v"
    using coin_ex by blast
  from min_coinD[OF this, unfolded char_coincidence]
  obtain \<tau> where "coin_block \<tau>" and "u = (p \<cdot> \<ee> \<tau>)\<^sup><\<inverse>p"
    by blast
  from conjunct1[OF min_coinD'[OF \<open>g u =\<^sub>m h v\<close>], unfolded this(2)]
  have "\<tau> \<noteq> \<epsilon>"
    using rq_self[of p] marked.sucs.g.emp_to_emp emp_simps(1) by metis
  from append_butlast_last_id[OF this]
  have "coin_block [last \<tau>]"
    using \<open>coin_block \<tau>\<close> last_letter_block by metis
  with non_block
  show "coin_block [1-a1]"
    by (cases rule: bin_swap_exhaust[of "last \<tau>" a1]) simp_all
qed

definition coincidence_exponent ("t") where
  "coincidence_exponent = (LEAST x. (q \<le>s q \<cdot> \<ff>([a1] \<cdot> [1-a1]\<^sup>@Suc x)))"

lemma q_nemp: "q \<noteq> \<epsilon>"
proof (rule notI)
  assume "q = \<epsilon>"
  with coin_block_def
    marked.ne_g[OF suf_of_emp[OF begin_block[unfolded hm.emp_to_emp'[OF this]]]]  non_block
  show False by blast
qed

lemma p_suf: "p <s \<ee> [1-a1]"
  using last_letter_fst_suf[of \<epsilon>, unfolded emp_simps, OF swap_coin_block].

lemma coin_exp: "coin_block ([a1] \<cdot> [1-a1]\<^sup>@Suc t)" and
  coin_exp_min: "j \<le> t \<Longrightarrow> \<not> coin_block ([a1] \<cdot> [1-a1]\<^sup>@j)"
proof-
  have "\<^bold>|q\<^bold>| \<le> \<^bold>|\<ff> ([1-a1]\<^sup>@\<^bold>|q\<^bold>|)\<^bold>|"
    using long_pow marked.sucs.h.pow_morph marked.sucs.h.sing_to_nemp by metis
  moreover have "q \<le>s q \<cdot> \<ff> ([1-a1]\<^sup>@\<^bold>|q\<^bold>|)"
    unfolding marked.sucs.h.pow_morph using conjunct2[OF swap_coin_block[unfolded coin_block_def]] using per_exp_suf by blast
  ultimately have "q \<le>s \<ff> ([a1] \<cdot> [1-a1]\<^sup>@\<^bold>|q\<^bold>|)"
    unfolding marked.sucs.h.morph using suf_prod_le suf_ext by blast
  from LeastI[of "\<lambda> x. (q \<le>s q \<cdot> \<ff>([a1] \<cdot> [1-a1]\<^sup>@Suc x))",
      folded coincidence_exponent_def, of "\<^bold>|q\<^bold>| - 1"] suf_ext[OF this, of q]
  have "q \<le>s q \<cdot> \<ff> ([a1] \<cdot> [1 - a1] \<^sup>@ Suc t)"
    unfolding Suc_minus[OF nemp_len[OF q_nemp]] by blast
  thus "coin_block ([a1] \<cdot> [1-a1]\<^sup>@Suc t)"
    unfolding pow_Suc' marked.sucs.g.morph coin_block_def
    using suf_ext[OF ssufD1[OF p_suf], of "p \<cdot> \<ee> [a1] \<cdot> \<ee> ([1 - a1] \<^sup>@ t)", unfolded rassoc] by blast
next
  fix j assume "j \<le> t"
  show "\<not> coin_block ([a1] \<cdot> [1-a1]\<^sup>@j)"
  proof (cases "j = 0", simp add: non_block)
    assume "j \<noteq> 0"
    hence "j - 1 < t" and "t \<noteq> 0"
      using \<open>j \<le> t\<close> \<open>j \<noteq> 0\<close> by simp_all
    thus "\<not> coin_block ([a1] \<cdot> [1-a1]\<^sup>@j)"
      using not_less_Least[of "j - 1" "\<lambda> x. q \<le>s q \<cdot> \<ff> ([a1] \<cdot> [1 - a1] \<^sup>@ Suc x)", folded coincidence_exponent_def]
      unfolding coin_block_def Suc_minus[OF \<open>j \<noteq> 0\<close>] by linarith
  qed
qed

lemma exp_min: "\<not> q \<le>s \<ff> [1-a1]\<^sup>@t"
proof (cases "t = 0", simp add: q_nemp)
  assume "t \<noteq> 0"
  hence "t -1 < t" by simp
  show ?thesis
    using not_less_Least[of "t -1" "\<lambda> m. q \<le>s  q \<cdot> \<ff> ([a1] \<cdot> [1 - a1] \<^sup>@ Suc m)", folded coincidence_exponent_def, OF \<open>t - 1 < t\<close>, unfolded marked.sucs.h.morph Suc_minus[OF \<open>t \<noteq> 0\<close>]]
    unfolding marked.sucs.h.pow_morph using suf_ext by metis
qed

lemma q_suf_conv: "q \<le>s \<ff> ([a1]\<cdot>[1-a1]\<^sup>@Suc k) \<longleftrightarrow> t \<le> k"
proof
  have psuf': "p \<le>s p \<cdot> \<ee> ([a1] \<cdot> [1 - a1] \<^sup>@ Suc k)" for k
    unfolding pow_Suc' using  marked.sucs.g.morph ssufD1[OF p_suf] suffix_appendI by metis
  assume "q \<le>s \<ff> ([a1] \<cdot> [1 - a1] \<^sup>@ Suc k)"
  hence  "\<not> Suc k  \<le> t"
    using coin_exp_min[of "Suc k"] psuf'[of k] suf_ext[of q _ q] unfolding coin_block_def by blast
  thus "t \<le> k"
    by linarith
next
  assume "t \<le> k"
  have "q \<le>s q \<cdot> \<ff>[1-a1]"
    using coin_block_def swap_coin_block by blast
  have "q \<le>s \<ff> [a1] \<cdot> \<ff> ([1-a1]\<^sup>@Suc t)"
    using coin_exp rich_block_suf_snd[of \<epsilon> "1 - a1" t, unfolded emp_simps binA_simps] unfolding marked.sucs.h.morph  by blast
  from suf_prolong[OF per_exp_suf[OF \<open>q \<le>s q \<cdot> \<ff>[1-a1]\<close>, folded marked.sucs.h.pow_morph] this, of "k-t", folded marked.sucs.h.morph lassoc, folded add_exps[of "[1-a1]" "Suc t"]]
  show "q \<le>s \<ff> ([a1] \<cdot> [1-a1]\<^sup>@Suc k)"
    using \<open>t \<le>k\<close> by fastforce
qed

lemma coin_block_with_bad_letter: assumes "a1 \<in> set w"
  shows "coin_block w \<longleftrightarrow> [1-a1]\<^sup>@Suc t \<le>s w"
proof-
  obtain i b where "[b] \<cdot> [1-a1]\<^sup>@i \<le>s w" and "b \<noteq> 1-a1"
    using  distinct_letter_in_suf[of w "1-a1", OF neq_set_not_root[OF bin_swap_neq, OF assms]].
  have "b = a1"
    using bin_neq_swap'''[OF \<open>b \<noteq> 1-a1\<close>, unfolded binA_simps].
  from \<open>[b] \<cdot> [1-a1]\<^sup>@i \<le>s w\<close>[unfolded this, unfolded suffix_def]
  obtain w' where w: "w = w' \<cdot> [a1] \<cdot> [1-a1]\<^sup>@i" by blast
  show ?thesis
  proof(cases)
    assume "i = 0"
    have "\<not> [1 - a1] \<^sup>@ Suc t \<le>s w' \<cdot> [a1]"
      unfolding pow_Suc' using bin_swap_neq[of a1]
      by simp
    then show "coin_block w \<longleftrightarrow> [1-a1]\<^sup>@Suc t \<le>s w"
      unfolding w \<open>i = 0\<close> cow_simps using last_letter_block non_block by meson
  next
    assume "i \<noteq> 0"
    have psuf: "p \<le>s p \<cdot> \<ee> (w' \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc k)" for k
      unfolding pow_Suc' using  marked.sucs.g.morph ssufD1[OF p_suf] suffix_appendI by metis
    have psuf': "p \<le>s p \<cdot> \<ee> ([a1] \<cdot> [1 - a1] \<^sup>@ Suc k)" for k
      unfolding pow_Suc' using  marked.sucs.g.morph ssufD1[OF p_suf] suffix_appendI by metis
    have equiv1: "coin_block (w'\<cdot>[a1]\<cdot>[1-a1]\<^sup>@Suc k) \<longleftrightarrow> q \<le>s \<ff> ([a1]\<cdot>[1-a1]\<^sup>@Suc k)" for k
    proof
      show "coin_block (w' \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc k) \<Longrightarrow> q \<le>s \<ff> ([a1] \<cdot> [1 - a1] \<^sup>@ Suc k)"
        using rich_block_suf_snd[of w' "1 - a1" k] suffix_append unfolding binA_simps marked.sucs.h.morph by blast
      show "q \<le>s \<ff> ([a1] \<cdot> [1 - a1] \<^sup>@ Suc k) \<Longrightarrow> coin_block (w' \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc k)"
        unfolding coin_block_def marked.sucs.h.morph using psuf suffix_appendI by metis
    qed
    have "t \<le> k \<longleftrightarrow> [1-a1]\<^sup>@Suc t \<le>s w'\<cdot>[a1]\<cdot>[1-a1]\<^sup>@Suc k" for k
      using sing_exp_pref_iff[reversed, OF bin_swap_neq', symmetric, of "Suc t" "Suc k" "1-a1", unfolded Suc_le_mono binA_simps rassoc].
    from equiv1[unfolded q_suf_conv this, of "i-1", unfolded Suc_minus[OF \<open>i \<noteq> 0\<close>], folded w]
    show ?thesis.
  qed
qed

section \<open>Description of the basis\<close>

text\<open>The infinite part of the basis\<close>

inductive_set \<W> :: "binA list set" where
  "[a1] \<cdot> [1-a1]\<^sup>@Suc t  \<in> \<W>"
| "\<tau> \<in> \<W> \<Longrightarrow>  i \<le> t \<Longrightarrow> [a1] \<cdot> [1-a1]\<^sup>@i \<cdot> \<tau> \<in> \<W>"

lemma \<W>_nemp: "x \<in> \<W> \<Longrightarrow> x \<noteq> \<epsilon>"
  by (rule \<W>.cases[of x "x \<noteq> \<epsilon>"], simp_all)

lemma \<W>_nemp': "x \<in> ({[1 - a1]} \<union> \<W>) \<Longrightarrow> x \<noteq> \<epsilon>"
  using \<W>_nemp by blast

lemma \<W>_hd: "x \<in>  \<W> \<Longrightarrow>  hd x = a1"
  by (induction x rule: \<W>.induct, simp_all)

lemma \<W>_set: "x \<in> \<W> \<Longrightarrow>  a1 \<in> set x"
  using \<W>_hd \<W>_nemp hd_in_set by blast

lemma \<W>_butlast_hd_tl: "x \<in> \<W> \<Longrightarrow>  butlast x = [a1] \<cdot> butlast (tl x)"
  by (induction x rule: \<W>.induct, auto)

lemma \<W>_suf: "x \<in> \<W> \<Longrightarrow>  [a1] \<cdot>[1-a1]\<^sup>@Suc t \<le>s x"
  by (induction x rule: \<W>.induct, simp_all add: suffix_Cons suffix_append)

lemma \<W>_fac: "x \<in> \<W> \<Longrightarrow>  \<not> [1-a1]\<^sup>@Suc t \<le>f butlast x"
proof (induction x rule: \<W>.induct)
  show "\<not> [1 - a1] \<^sup>@ Suc t \<le>f butlast ([a1] \<cdot> [1 - a1] \<^sup>@ Suc t)"
    using fac_len_eq[of "[1 - a1] \<^sup>@ Suc t" "butlast ([a1] \<cdot> [1 - a1] \<^sup>@ Suc t)"]
    unfolding pow_Suc' lassoc butlast_snoc  sing_pow_len lenmorph sing_len
    unfolding pow_comm[of "[1-a1]"] add.commute[of t] cancel_right
    using bin_swap_neq by fast
  fix x' i
  assume "x' \<in> \<W>" and notf: "\<not> [1 - a1] \<^sup>@ Suc t \<le>f butlast x'" and "i \<le> t"
  show "\<not> [1 - a1] \<^sup>@ Suc t \<le>f butlast ([a1] \<cdot> [1 - a1] \<^sup>@ i \<cdot> x')"
  proof
    assume "[1 - a1] \<^sup>@ Suc t \<le>f butlast ([a1] \<cdot> [1 - a1] \<^sup>@ i \<cdot> x')"
    hence "[1 - a1] \<^sup>@ Suc t \<le>f [a1] \<cdot> [1 - a1] \<^sup>@ i \<cdot> butlast x'"
      unfolding lassoc butlast_append using \<W>_nemp[OF  \<open>x' \<in> \<W>\<close>] by force
    then obtain pp ss where fac: "pp \<cdot> [1 - a1] \<^sup>@ Suc t \<cdot> ss = ([a1] \<cdot> [1 - a1] \<^sup>@ i) \<cdot> butlast x'" unfolding rassoc by fast
    from notf eqd[OF this[symmetric]]
    have "\<not> \<^bold>|[a1] \<cdot> [1 - a1] \<^sup>@ i\<^bold>| \<le> \<^bold>|pp\<^bold>|"
      unfolding fac_def by metis
    hence "\<^bold>|pp\<^bold>| \<le> i"
      unfolding lenmorph by simp
    have "pp \<noteq> \<epsilon>"
      using fac emp_simps(2) bin_swap_neq[of a1] unfolding pow_Suc rassoc by force
    have "Suc i < \<^bold>|pp\<^bold>| + Suc t" and "Suc i -\<^bold>|pp\<^bold>| < Suc t"
      using nemp_len[OF \<open>pp \<noteq> \<epsilon>\<close>] \<open>i \<le> t\<close> by linarith+
    have "(pp \<cdot> [1 - a1] \<^sup>@ Suc t \<cdot> ss)!(Suc i) = a1"
      unfolding fac \<W>_butlast_hd_tl[OF \<open>x' \<in> \<W>\<close>]
      using nth_append_length[of "[a1] \<cdot> [1 - a1] \<^sup>@ i" a1] unfolding lenmorph sing_pow_len sing_len swap_len by force
    from this[unfolded lassoc nth_append[of _ ss]]
    have "(pp \<cdot> [1 - a1] \<^sup>@ Suc t)!(Suc i) = a1"
      unfolding lenmorph sing_pow_len using \<open>Suc i < \<^bold>|pp\<^bold>| + Suc t\<close> by presburger
    from this[unfolded nth_append]
    have "([1 - a1] \<^sup>@ Suc t)!(Suc i - \<^bold>|pp\<^bold>|) = a1"
      using \<open>\<^bold>|pp\<^bold>| \<le> i\<close> by force
    thus False
      unfolding sing_pow_nth[OF \<open>Suc i -\<^bold>|pp\<^bold>| < Suc t\<close>]
      using bin_swap_neq by blast
  qed
qed

lemma pref_code_\<W>: "pref_code ({[1-a1]} \<union> \<W>)"
proof
  show nemp: "\<epsilon> \<notin> {[1 - a1]} \<union> \<W>"
    using \<W>_nemp by auto
  show "u = v" if u_in: "u \<in> {[1 - a1]} \<union> \<W>" and v_in: "v \<in> {[1 - a1]} \<union> \<W>" and  "u \<le>p v" for u v
  proof (rule bin_swap_exhaust[of "hd u" a1])
    assume "hd u = 1 - a1"
    hence "u = [1-a1]"
      using u_in[unfolded Un_def mem_Collect_eq]
        \<W>_hd[of u] bin_swap_neq' by blast
    from sing_pref_hd[OF \<open>u \<le>p v\<close>[unfolded this]]
    have "hd v = 1 - a1".
    hence "v = [1-a1]"
      using v_in[unfolded Un_def mem_Collect_eq]
        \<W>_hd[of v] bin_swap_neq' by blast
    with \<open>u = [1-a1]\<close>
    show "u = v"
      by simp
  next
    assume "hd u = a1"
    have "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>"
      using  nemp u_in v_in by blast+
    from pref_hd_eq[OF \<open>u \<le>p v\<close> \<open>u \<noteq> \<epsilon>\<close>]
    have "hd v = a1"
      using \<open>hd u = a1\<close> by simp
    from  u_in \<open>hd u = a1\<close> bin_swap_neq[of a1]
    have "u \<in> \<W>"
      unfolding Un_def mem_Collect_eq using singletonD[of u "[1-a1]"] list.sel(1)[of "1-a1" \<epsilon>] by metis
    from \<open>hd v = a1\<close> v_in \<open>hd u = a1\<close> bin_swap_neq[of a1]
    have "v \<in> \<W>"
      unfolding Un_def mem_Collect_eq using singletonD[of v "[1-a1]"] list.sel(1)[of "1-a1" \<epsilon>] by metis
    from \<W>_suf[OF \<open>u \<in> \<W>\<close>]
    have "[1 - a1] \<^sup>@ Suc t \<le>s u"
      using suf_extD by blast
    hence "\<not> u \<le>p butlast v"
      using \<W>_fac[OF \<open>v \<in> \<W>\<close>] unfolding fac_def suffix_def prefix_def by fastforce
    with \<open>u \<le>p v\<close>
    show "u = v"
      using spref_butlast_pref by blast
  qed
qed

lemma \<W>_coin_blocks:
  assumes  "x \<in> {[1 - a1]} \<union> \<W>"  shows "x \<in> \<T>"
proof-
  consider "x = [1-a1]" | "x \<in> \<W>"
    using \<open>x \<in> {[1 - a1]} \<union> \<W>\<close>  by blast
  thus "x \<in> \<T>"
  proof (cases)
    assume "x = [1-a1]"
    show "x \<in> \<T>"
      unfolding \<T>_def' \<open>x = [1-a1]\<close> using swap_coin_block.
  next
    assume "x \<in> \<W>"
    show "x \<in> \<T>"
      unfolding \<T>_def' coin_block_with_bad_letter[OF \<W>_set[OF \<open>x \<in> \<W>\<close>]] using suf_extD[OF \<W>_suf[OF \<open>x \<in> \<W>\<close>]].
  qed
qed

lemma \<W>_gen_T: "\<langle>{[1-a1]} \<union> \<W>\<rangle> = \<T>"
proof
  from subsetI[OF \<W>_coin_blocks, THEN hull_mono]
  show "\<langle>{[1 - a1]} \<union> \<W>\<rangle> \<subseteq> \<T>"
    unfolding \<T>_hull.
next
  show "\<T> \<subseteq> \<langle>{[1 - a1]} \<union> \<W>\<rangle>"
  proof
    fix x assume "x \<in> \<T>"
    from this[unfolded \<T>_def'] have "coin_block x".
    thus "x \<in> \<langle>{[1 - a1]} \<union> \<W>\<rangle>"
    proof (induction "\<^bold>|x\<^bold>|" arbitrary: x rule: less_induct)
      case less
      show ?case
      proof (cases "\<exists> px. px \<noteq> \<epsilon> \<and> px <p x \<and> coin_block px")
        assume "\<exists> px. px \<noteq> \<epsilon> \<and> px <p x \<and> coin_block px"
        from exE[OF this]
        obtain px where "px \<noteq> \<epsilon>" and "px <p x" and "coin_block px" by metis
        from spref_exE[OF \<open>px <p x\<close>]
        obtain sx where "px\<cdot>sx = x" and "sx \<noteq> \<epsilon>".
        from \<T>_pref[OF \<open>coin_block px\<close> \<open>coin_block x\<close>[folded \<open>px\<cdot>sx = x\<close>]]
        have "coin_block sx".
        have "\<^bold>|px\<^bold>| < \<^bold>|x\<^bold>|" and "\<^bold>|sx\<^bold>| < \<^bold>|x\<^bold>|"
          using \<open>px\<cdot>sx = x\<close> \<open>px \<noteq> \<epsilon>\<close> \<open>sx \<noteq> \<epsilon>\<close> by auto
        from less.hyps[OF this(1) \<open>coin_block px\<close>]
          less.hyps[OF this(2) \<open>coin_block sx\<close>]
        show "x \<in> \<langle>{[1 - a1]} \<union> \<W>\<rangle>"
          using \<open>px\<cdot>sx = x\<close> by auto
      next
        assume non_ex: "\<nexists> px. px \<noteq> \<epsilon> \<and> px <p x \<and> coin_block px"
        show "x \<in> \<langle>{[1 - a1]} \<union> \<W>\<rangle>"
        proof (cases "a1 \<in> set x")
          assume "a1 \<notin> set x"
          then obtain k where "x = [1 - a1]\<^sup>@k"
            using bin_without_letter by blast
          thus "x \<in> \<langle>{[1 - a1]} \<union> \<W>\<rangle>"
            using gen_in[THEN power_in] by fast
        next
          assume "a1 \<in> set x"
          hence "x \<noteq> \<epsilon>" by force
          have "hd x = a1"
          proof (rule ccontr)
            assume "hd x \<noteq> a1"
            hence "hd x = 1-a1"
              using bin_neq_iff by auto
            from non_ex swap_coin_block hd_tl[OF \<open>x \<noteq> \<epsilon>\<close>, unfolded this]
            have "tl x = \<epsilon>" by blast
            from \<open>[1 - a1] \<cdot> tl x = x\<close>[unfolded this emp_simps]
            show False
              using neq_in_set_not_pow[OF bin_swap_neq[of a1] \<open>a1 \<in> set x\<close>, of 1, unfolded exp_simps] by simp
          qed
          define j where "j = (LEAST k. \<not> [a1]\<cdot>[1-a1]\<^sup>@Suc k \<le>p x)"
          hence "\<not> [a1]\<cdot>[1-a1]\<^sup>@(Suc t) <p x"
            using coin_exp non_ex by blast
          hence "\<not> [a1]\<cdot>[1-a1]\<^sup>@Suc(Suc t) \<le>p x"
            unfolding pow_Suc'[of _ "Suc t"] lassoc
            using prefix_snocD by metis
          from Least_le[of "\<lambda> i. \<not> ([a1]\<cdot>[1-a1]\<^sup>@Suc i) \<le>p x", OF this, folded j_def]
          have "j \<le> Suc t".
          have "\<not> [a1]\<cdot>[1-a1]\<^sup>@ Suc j \<le>p x"
            using LeastI[of "\<lambda> i. \<not> ([a1]\<cdot>[1-a1]\<^sup>@Suc i) \<le>p x", OF \<open>\<not> ([a1]\<cdot>[1-a1]\<^sup>@Suc(Suc t)) \<le>p x\<close>, folded j_def].
          have "[a1]\<cdot>[1-a1]\<^sup>@j \<le>p x"
            using not_less_Least[of "j-1" "\<lambda> i. \<not> ([a1]\<cdot>[1-a1]\<^sup>@Suc i) \<le>p x"]
            unfolding j_def[symmetric] not_not
            by (cases "j = 0", simp_all add: hd_pref[OF \<open>x \<noteq> \<epsilon>\<close>, unfolded \<open>hd x = a1\<close>])
          show "x \<in> \<langle>{[1 - a1]} \<union> \<W>\<rangle>"
          proof(cases "j = Suc t")
            assume "j = Suc t"
            have "x = [a1]\<cdot>[1-a1]\<^sup>@j"
              using \<open>[a1]\<cdot>[1-a1]\<^sup>@j \<le>p x\<close> \<open>\<not> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t <p x\<close>
              unfolding \<open>j = Suc t\<close> by force
            from \<W>.intros(1)[folded \<open>j = Suc t\<close>, folded this]
            show "x \<in> \<langle>{[1 - a1]} \<union> \<W>\<rangle>" by auto
          next
            assume "j \<noteq> Suc t"
            hence "j \<le> t" using \<open>j \<le> Suc t\<close> by force
            from prefE[OF \<open>[a1]\<cdot>[1-a1]\<^sup>@j \<le>p x\<close>, unfolded rassoc]
            obtain x' where "x = [a1] \<cdot> [1-a1]\<^sup>@j \<cdot> x'".
            with coin_exp_min[OF \<open>j \<le> t\<close>] \<open>coin_block x\<close>
            have "x' \<noteq> \<epsilon>"
              by auto
            from \<open>\<not> [a1] \<cdot> [1-a1]\<^sup>@Suc j \<le>p x\<close> hd_tl[OF this]
            have "hd x' = a1"
              unfolding \<open>x = [a1] \<cdot> [1-a1]\<^sup>@j \<cdot> x'\<close> pow_Suc' pref_cancel_conv
              using bin_neq_iff'[of "hd x'" "1-a1", unfolded binA_simps] by fastforce
            from \<open>[hd x'] \<cdot> tl x' = x'\<close>[unfolded this]
              \<open>coin_block x\<close>[unfolded coin_block_with_bad_letter[OF \<open>a1 \<in> set x\<close>]]
            have "[1-a1]\<^sup>@Suc t \<le>s [a1] \<cdot> [1 - a1] \<^sup>@ j \<cdot> [a1] \<cdot> tl x'"
              unfolding \<open>x = [a1] \<cdot> [1-a1]\<^sup>@j \<cdot> x'\<close> by presburger
            have "a1 \<notin> set ([1-a1]\<^sup>@Suc t)"
              using neq_in_set_not_pow[OF bin_swap_neq, of a1] by blast
            hence "\<not> [a1] \<cdot> tl x' \<le>s [1-a1]\<^sup>@Suc t"
              unfolding suffix_def using Cons_eq_appendI in_set_conv_decomp by metis
            with ruler[reversed, of x', OF _ \<open>[1-a1]\<^sup>@Suc t \<le>s x\<close>]
            have "[1-a1]\<^sup>@Suc t \<le>s x'"
              unfolding \<open>x = [a1] \<cdot> [1-a1]\<^sup>@j \<cdot> x'\<close> \<open>[a1] \<cdot> tl x' = x'\<close> suffix_def by fastforce
            have "a1 \<in> set x'"
              using \<open>hd x' = a1\<close> \<open>x' \<noteq> \<epsilon>\<close> hd_in_set by blast
            from coin_block_with_bad_letter[OF this]
            have "coin_block x'"
              using \<open>[1-a1]\<^sup>@Suc t \<le>s x'\<close> by blast
            have "\<^bold>|x'\<^bold>| < \<^bold>|x\<^bold>|"
              using lenarg[OF \<open>x = [a1] \<cdot> [1-a1]\<^sup>@j \<cdot> x'\<close>] unfolding lenmorph by simp
            from less.hyps[OF this \<open>coin_block x'\<close>]
            obtain xs' where "xs' \<in> lists ({[1 - a1]} \<union> \<W>)" and "concat xs' = x'" using hull_concat_listsE by blast
            have "xs' \<noteq> \<epsilon>"
              using \<open>concat xs' = x'\<close> \<open>x' \<noteq> \<epsilon>\<close> concat.simps(1) by blast
            from lists_hd_in_set[OF this \<open>xs' \<in> lists ({[1 - a1]} \<union> \<W>)\<close>]
            have "hd xs' \<in> ({[1 - a1]} \<union> \<W>)".
            from \<W>_coin_blocks[OF this] \<W>_nemp'[OF this]
            have "coin_block (hd xs')" and "hd xs' \<noteq> \<epsilon>"
              unfolding \<T>_def'.
            have "hd (hd xs') = a1"
              using  hd_concat[OF \<open>xs' \<noteq> \<epsilon>\<close> \<open>hd xs' \<noteq> \<epsilon>\<close>, symmetric]
              unfolding \<open>concat xs' = x'\<close> \<open>hd x' = a1\<close>.
            hence "hd xs' \<in> \<W>"
              using \<open>hd xs' \<in> ({[1 - a1]} \<union> \<W>)\<close>  bin_swap_neq[of a1] list.sel(1)[of "1-a1" \<epsilon>]
              unfolding Un_def mem_Collect_eq singleton_iff by metis
            hence "[a1] \<cdot> [1-a1]\<^sup>@j \<cdot> hd xs' \<in> \<W>"
              using \<open>j \<le> t\<close> \<W>.intros(2) by blast
            with \<W>_coin_blocks
            have "coin_block ([a1] \<cdot> [1-a1]\<^sup>@j \<cdot> hd xs')"
              unfolding \<T>_def' Un_def by blast
            have "[a1] \<cdot> [1-a1]\<^sup>@j \<cdot> hd xs' \<le>p x"
              using hd_concat_tl[OF \<open>xs' \<noteq> \<epsilon>\<close>]
              unfolding \<open>concat xs' = x'\<close> \<open>x = [a1] \<cdot> [1-a1]\<^sup>@j \<cdot> x'\<close>
              by fastforce
            with non_ex \<open>coin_block (hd xs')\<close> \<open>hd xs' \<noteq> \<epsilon>\<close>
            have "x = [a1] \<cdot> [1-a1]\<^sup>@j \<cdot> hd xs'"
              using \<open>coin_block ([a1] \<cdot> [1 - a1] \<^sup>@ j \<cdot> hd xs')\<close> strict_prefixI suf_nemp by metis
            from \<open>[a1] \<cdot> [1-a1]\<^sup>@j \<cdot> hd xs' \<in> \<W>\<close>[folded this]
            show "x \<in> \<langle>{[1 - a1]} \<union> \<W>\<rangle>"
              by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma \<W>_explicit: "\<W> = {w \<cdot> [a1] \<cdot> [1-a1]\<^sup>@Suc t | w. w \<in> \<langle>{[a1] \<cdot> [1-a1]\<^sup>@i | i. i \<le> t}\<rangle>}"
proof
  show "\<W> \<subseteq> {w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t |w. w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>}"
  proof
    fix x assume "x \<in> \<W>"
    thus "x \<in> {w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t |w. w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>}"
      unfolding mem_Collect_eq
    proof (induction x rule: \<W>.induct, simp)
      case (2 \<tau> i)
      then obtain w where "\<tau> = w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t" and "w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>"
        by blast
      from hull.prod_cl[OF _ this(2), of "[a1] \<cdot> [1 - a1] \<^sup>@ i"] \<open>i \<le> t\<close>
      have "[a1] \<cdot> [1 - a1] \<^sup>@ i \<cdot> w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>"
        unfolding mem_Collect_eq by simp
      thus ?case
        using \<open>\<tau> = w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t\<close> by auto
    qed
  qed
next
  show "{w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t |w. w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>} \<subseteq> \<W>"
  proof
    fix x assume "x \<in> {w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t |w. w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>}"
    then obtain w where "x = w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t" and "w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>"
      unfolding mem_Collect_eq by blast
    show "x \<in> \<W>"
      unfolding \<open>x = w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t\<close>
      by (rule hull.induct[OF \<open>w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>\<close>], use \<W>.intros(1) in force)
        (use \<W>.intros(2) in force)
  qed
qed

theorem infinite_basis: "\<BB> \<T> = ({[1-a1]} \<union> \<W>)"
  using basis_of_hull[of "{[1-a1]} \<union> \<W>"]
  unfolding \<W>_gen_T  code.code_is_basis[OF pref_code.code, OF pref_code_\<W>].

end

section Intersection

lemma bin_inter_coin_set_fst: "\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle> = ((bin_morph_of x y) \<circ> fst) ` \<CC> (bin_morph_of x y) (bin_morph_of u v)"
  using bin_morph_of_range coin_set_inter_fst by metis

lemma bin_inter_coin_set_snd: "\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle> = ((bin_morph_of u v) \<circ> snd) ` \<CC> (bin_morph_of x y) (bin_morph_of u v)"
  using  bin_inter_coin_set_fst unfolding coin_set_eq.

theorem bin_inter_basis: assumes "binary_code x y" and "binary_code u v"
  shows  "\<BB> (\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle>) = ((bin_morph_of u v) \<circ> snd) ` \<CC>\<^sub>m (bin_morph_of x y) (bin_morph_of u v)"
  unfolding bin_inter_coin_set_snd
  using  two_code_morphisms.range_inter_basis_snd(1)[OF two_code_morphisms.intro, OF binary_code.code_morph_of binary_code.code_morph_of, OF assms, folded coin_set_inter_snd] unfolding image_comp.

theorem binary_intersection_code:
  assumes "binary_code x y" and "binary_code u v"
  shows "code \<BB> (\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle>)"
  using two_code_morphisms.range_inter_code[OF two_code_morphisms.intro[OF binary_code.code_morph_of[OF assms(1)] binary_code.code_morph_of[OF assms(2)]]]
  unfolding bin_morph_of_range.

theorem binary_intersection:
  assumes "binary_code x y" and "binary_code u v"
  obtains
    "\<BB> (\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle>) = {}"
  |
    \<beta> where  "\<BB> (\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle>) = {\<beta>}"
  |
    \<beta> \<gamma> where  "\<BB> (\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle>) = {\<beta>,\<gamma>}"
  |
    \<beta> \<gamma> \<delta> \<tt> where "\<delta> \<noteq> \<epsilon>" and  "\<gamma> \<cdot> \<beta> \<noteq> \<epsilon>" and "hd \<delta> \<noteq> hd (\<gamma> \<cdot> \<beta>)"
    "\<BB> (\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle>) = {\<beta> \<cdot> \<gamma>} \<union> {\<beta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@\<tt> \<cdot> w \<cdot> \<delta> \<cdot> \<gamma> | w. w \<in> \<langle>{\<delta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@i | i. i \<le> \<tt>}\<rangle>}"
  |
    \<beta> \<gamma> \<delta> \<tt> \<qq> where "\<delta> \<noteq> \<epsilon>"and  "\<gamma> \<cdot> \<beta> \<noteq> \<epsilon>" and "hd \<delta> \<noteq> hd (\<gamma> \<cdot> \<beta>)" and
    "1 \<le> \<qq> \<and> \<qq> \<le> \<tt>" and
    "\<BB> (\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle>) = {\<beta> \<cdot> \<gamma>} \<union> {\<beta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@\<tt> \<cdot> w \<cdot> \<delta>\<^sup><\<inverse>(\<beta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@(\<tt>-\<qq>)) |
                w. w \<in> \<langle>{\<delta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@i | i. i \<le> \<qq> - 1}\<rangle>}"
proof-
  define x' where "x' = (if \<^bold>|bin_lcp u v\<^bold>| \<le> \<^bold>|bin_lcp x y\<^bold>| then x else u)"
  define y' where "y' = (if \<^bold>|bin_lcp u v\<^bold>| \<le> \<^bold>|bin_lcp x y\<^bold>| then y else v)"
  define u' where "u' = (if \<^bold>|bin_lcp u v\<^bold>| \<le> \<^bold>|bin_lcp x y\<^bold>| then u else x)"
  define v' where "v' = (if \<^bold>|bin_lcp u v\<^bold>| \<le> \<^bold>|bin_lcp x y\<^bold>| then v else y)"
  have lcp_le: "\<^bold>|bin_lcp u' v'\<^bold>| \<le> \<^bold>|bin_lcp x' y'\<^bold>|"
    unfolding x'_def y'_def u'_def v'_def by simp
  have int': "\<langle>{x,y}\<rangle> \<inter> \<langle>{u,v}\<rangle> = \<langle>{x',y'}\<rangle> \<inter> \<langle>{u',v'}\<rangle>"
    unfolding x'_def y'_def u'_def v'_def using Int_commute by force
  have assms': "binary_code x' y'" "binary_code u' v'"
    using assms unfolding x'_def y'_def u'_def v'_def by simp_all

  define first_morphism ("g ")
    where "first_morphism \<equiv> bin_morph_of x' y'"
  define second_morphism ("h")
    where "second_morphism \<equiv> bin_morph_of u' v'"
  note mdefs = first_morphism_def second_morphism_def
  have ranges: "range g = \<langle>{x',y'}\<rangle>" "range h = \<langle>{u',v'}\<rangle>"
    unfolding mdefs bin_morph_of_range by blast+

  have nemp: "x' \<noteq> \<epsilon>" "y' \<noteq> \<epsilon>" "u' \<noteq> \<epsilon>" "v' \<noteq> \<epsilon>"
    using assms' binary_code.non_comm by blast+

  interpret two_binary_code_morphisms g h
    using two_binary_code_morphisms.intro
    unfolding binary_code_morphism_def first_morphism_def second_morphism_def
    using binary_code.code_morph_of assms' by blast

  interpret two_nonerasing_morphisms g h
    using code.two_nonerasing_morphisms_axioms.

  show thesis
  proof (cases)
    assume "\<CC>\<^sub>m g h = {}" \<comment> \<open>simple case: coincidence set is empty\<close>
    have "\<langle>{x',y'}\<rangle> \<inter> \<langle>{u',v'}\<rangle> = {\<epsilon>}"
      unfolding bin_inter_coin_set_snd image_comp[symmetric] mdefs[symmetric]
        code.min_coin_gen_snd[symmetric, unfolded \<open>\<CC>\<^sub>m g h = {}\<close>]
      by (simp add: emp_gen_set)
    from that(1)[unfolded int' this]
    show ?thesis
      unfolding emp_basis_iff by simp
  next
    assume "\<CC>\<^sub>m g h \<noteq> {}"
    then obtain r1 s1 where "g r1 =\<^sub>m h s1"
      unfolding min_coincidence_set_def by blast
    interpret binary_codes_coincidence g h
    proof
      show "\<exists>r s. g r =\<^sub>m h s"
        using \<open>g r1 =\<^sub>m h s1\<close> by blast
      show "\<^bold>|h.bin_code_lcp\<^bold>| \<le> \<^bold>|g.bin_code_lcp\<^bold>|"
        unfolding bin_morph_ofD mdefs using lcp_le.
    qed
    show thesis
    proof (cases)
      assume "\<CC>\<^sub>m g h = {(r1,s1)}" \<comment> \<open>min. coincidence set contains 1 element\<close>
      from that(2)[unfolded int']
      show thesis
        unfolding bin_inter_basis [OF assms', unfolded \<open>\<CC>\<^sub>m g h = {(r1,s1)}\<close>[unfolded mdefs] image_comp[symmetric]] by simp
    next
      assume "\<CC>\<^sub>m g h \<noteq> {(r1,s1)}" \<comment> \<open>min. coincidence set contains more than 1 element\<close>
      then obtain r2 s2 where "(r2,s2) \<in> \<CC>\<^sub>m g h" and "(r2,s2) \<noteq> (r1,s1)"
        using \<open>\<CC>\<^sub>m g h \<noteq> {}\<close> by auto
      from min_coin_setD[OF this(1)] \<open>g r1 =\<^sub>m h s1\<close> this(2)
      interpret binary_codes_coincidence_two_generators g h
        by unfold_locales auto
      write g.marked_version ("g\<^sub>m") and
        h.marked_version ("h\<^sub>m") and
        fst_beginning_block ("p")  and
        snd_beginning_block ("q")  and
        h.bin_code_lcp ("\<alpha>\<^sub>h") and
        marked.suc_snd ("\<ff>")
      show thesis
      proof(cases)
        assume "\<forall> a. coin_block [a]"
        hence "\<And> a. coin_block [a]" by force
        define \<beta> where "\<beta> = (h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) \<aa>"
        define \<gamma> where "\<gamma> = (h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) \<bb>"
        have "range (bin_morph_of x' y') = \<langle>{x',y'}\<rangle>"
          using bin_morph_of_range by auto
        from that(3)[ of \<beta> \<gamma>, unfolded int' \<beta>_def \<gamma>_def mdefs[symmetric]]
        show thesis
          using inter_basis[unfolded simple_blocks_basis[OF \<open>\<And> a. coin_block [a]\<close>] bin_morph_of_range]
          unfolding ranges by blast
      next
        assume "\<not> (\<forall> a. coin_block [a])"
        then obtain a1 where "\<not> coin_block [a1]" by blast
        then interpret binary_codes_coincidence_infinite g h a1
          by unfold_locales
        write coincidence_exponent ("t")

        from inter_basis[unfolded ranges infinite_basis bin_morph_of_range, folded Setcompr_eq_image, unfolded mem_Collect_eq]
        have inter:"\<BB> (\<langle>{x', y'}\<rangle> \<inter> \<langle>{u', v'}\<rangle>) = {(h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) x |x. x \<in> {[1 - a1]} \<union> \<W>}".

        have "q \<le>s q \<cdot> \<ff> [1 - a1]"
          using swap_coin_block[unfolded coin_block_def] by blast
        from conjug_eqE[OF rq_suf[OF this]] conjug_emp_emp'[OF this] marked.sucs.h.sing_to_nemp
        obtain q1 q2 k where q21: "\<ff> [1 - a1] = q2 \<cdot> q1" and
          q_def: "q = (q1 \<cdot> q2)\<^sup>@k \<cdot> q1" and "q2 \<noteq> \<epsilon>"
          by metis
        have "(h q1 \<cdot> h q2) \<cdot> (h q1 \<cdot> \<alpha>\<^sub>h) = (h q1 \<cdot> \<alpha>\<^sub>h) \<cdot> (h\<^sub>m q2 \<cdot> h\<^sub>m q1)"
          unfolding rassoc h.marked_version_conjugates[of "q2 \<cdot> q1", unfolded hm.morph h.morph]..
        from conjug_eqE[OF this] h.nemp_to_nemp[OF \<open>q2 \<noteq> \<epsilon>\<close>]
        obtain \<beta> \<gamma> k' where bg: "\<beta> \<cdot> \<gamma> = h (q1 \<cdot> q2)" and "\<gamma> \<cdot> \<beta> = h\<^sub>m (q2 \<cdot> q1)" and
          k': "\<beta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@k'  = h q1 \<cdot> \<alpha>\<^sub>h" and "\<gamma> \<noteq> \<epsilon>"
          unfolding hm.morph h.morph shift_pow by blast
        have bgb_q: "\<beta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@(k' + k) = \<alpha>\<^sub>h \<cdot> h\<^sub>m q"
          unfolding add_exps lassoc \<open>\<beta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@k'  = h q1 \<cdot> \<alpha>\<^sub>h\<close>
          unfolding \<open>\<gamma> \<cdot> \<beta> = h\<^sub>m (q2 \<cdot> q1)\<close> h.marked_version_conjugates[symmetric]
            rassoc cancel q_def shift_pow unfolding hm.morph hm.pow_morph..
        define \<delta> where "\<delta> = h\<^sub>m (\<ff> [a1])"
        have bg_def: "\<beta> \<cdot> \<gamma> = h ((q \<cdot> \<ff> [1 - a1])\<^sup><\<inverse>q )"
          unfolding bg q_def q21 rassoc shift_pow pow_comm
          unfolding lassoc[of "q1"]
          unfolding rq_triv..
        have bg_def': "(h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) [1-a1] = \<beta> \<cdot> \<gamma>"
          using bg_def by simp
        have gb_def: "\<gamma> \<cdot> \<beta> = h\<^sub>m (\<ff> [1 - a1])"
          unfolding  \<open>\<gamma> \<cdot> \<beta> = h\<^sub>m (q2 \<cdot> q1)\<close> q21..

        have "\<gamma> \<cdot> \<beta> \<noteq> \<epsilon>"
          using \<open>\<gamma> \<noteq> \<epsilon>\<close> by blast
        have "\<delta> \<noteq> \<epsilon>"
          unfolding \<delta>_def using hm.nonerasing  marked.sucs.h.sing_to_nemp by blast
        have "hd \<delta> \<noteq> hd (\<gamma> \<cdot> \<beta>)"
          unfolding \<delta>_def gb_def
          using hm.hd_im_eq_hd_eq marked.sucs.h.bin_marked_sing marked.sucs.h.sing_to_nemp by blast

        have w_decode: "w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle> \<Longrightarrow>  h\<^sub>m (\<ff> w) \<in> \<langle>{\<delta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ i |i. i \<le> t}\<rangle>"
          for w
        proof (induct w rule: hull.induct, unfold marked.sucs.h.emp_to_emp hm.emp_to_emp, fast)
          case (prod_cl w1 w2)
          then obtain i where "w1 = [a1] \<cdot> [1-a1]\<^sup>@i" and "i \<le> t" by blast
          with prod_cl.hyps
          show ?case
            unfolding marked.sucs.h.morph marked.sucs.h.pow_morph hm.morph
                      hm.pow_morph \<open>w1 = [a1] \<cdot> [1-a1]\<^sup>@i\<close> \<delta>_def[symmetric] gb_def[symmetric]
            by blast
        qed

        have w_decode': "w \<in> \<langle>{\<delta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ i |i. i \<le> t}\<rangle> \<Longrightarrow> \<exists> w'. w' \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle> \<and> h\<^sub>m (\<ff> w') = w" for w
        proof (induct w rule: hull.induct, use marked.sucs.h.emp_to_emp hm.emp_to_emp in force)
          case (prod_cl w1 w2)
          then obtain w' j where  "w' \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>" and "h\<^sub>m (\<ff> w') = w2" and "w1 = \<delta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ j" and "j \<le> t" by blast
          have "([a1] \<cdot> [1 - a1] \<^sup>@ j) \<cdot> w' \<in>  \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>"
            using \<open>w' \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>\<close> \<open>j \<le> t\<close> by blast
          moreover have "h\<^sub>m (\<ff> (([a1] \<cdot> [1 - a1] \<^sup>@ j) \<cdot> w')) = w1 \<cdot> w2"
            unfolding marked.sucs.h.morph marked.sucs.h.pow_morph hm.morph hm.pow_morph \<open>h\<^sub>m (\<ff> w') = w2\<close>
              \<delta>_def[symmetric] gb_def[symmetric] \<open>w1 = \<delta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ j\<close>..
          ultimately show " \<exists>w'. w' \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle> \<and> h\<^sub>m (\<ff> w') = w1 \<cdot> w2" by blast
        qed

        show thesis
        proof (cases)
          assume "\<alpha>\<^sub>h \<cdot> h\<^sub>m q <s h\<^sub>m (\<ff> ([1-a1]\<^sup>@Suc t))"
          from ssuf_extD[OF this[unfolded bgb_q[symmetric] marked.sucs.h.pow_morph q21 gb_def hm.pow_morph]]
          have "k' + k < Suc t"
            unfolding marked.sucs.h.pow_morph[symmetric] using comp_pows_ssuf by blast
          have "\<not> q \<le>s \<ff> ([1-a1]\<^sup>@t)"
            unfolding marked.sucs.h.pow_morph using exp_min.
          hence "t \<le> k"
            unfolding marked.sucs.h.pow_morph q21 q_def shift_pow
            using comp_pows_not_suf by blast
          hence "t = k" and "k' = 0"
            using \<open>k' + k < Suc t\<close> by force+

          from bgb_q[folded \<open>t = k\<close>, unfolded \<open>k' = 0\<close>]
          have "\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ t = \<alpha>\<^sub>h \<cdot> h\<^sub>m q" by simp
          have "q \<le>s \<ff> [1 - a1] \<^sup>@ Suc t"
            unfolding q_def \<open>t = k\<close> q21 pow_Suc shift_pow by force

          have "\<beta> = h q1 \<cdot> \<alpha>\<^sub>h"
            using \<open>\<beta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@k'  = h q1 \<cdot> \<alpha>\<^sub>h\<close>[unfolded \<open>k' = 0\<close> cow_simps].
          from gb_def[unfolded q21 hm.morph this h.marked_version_conjugates[symmetric]]
          have "\<gamma> \<cdot> \<alpha>\<^sub>h = h\<^sub>m q2"
            by force
          from h.marked_version_conjugates[of q2, folded this]
          have "h ((\<ff> [1 - a1] \<^sup>@ Suc t)\<^sup><\<inverse>q) = \<alpha>\<^sub>h \<cdot> \<gamma>"
            unfolding q_def \<open>t = k\<close> q21 pow_Suc shift_pow rassoc rq_triv by force

          have apply_h0:  "h ((q \<cdot> \<ff> (w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t))\<^sup><\<inverse>q) = \<beta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@t \<cdot> h\<^sub>m (\<ff> w) \<cdot> \<delta> \<cdot> \<gamma>" for w
          proof-
            have "\<beta> \<cdot> (\<gamma> \<cdot> \<beta>)\<^sup>@t \<cdot> h\<^sub>m (\<ff> w) \<cdot> \<delta> \<cdot> \<gamma> = \<alpha>\<^sub>h \<cdot> h\<^sub>m (q \<cdot> \<ff> (w \<cdot> [a1])) \<cdot> \<gamma>"
              unfolding hm.morph marked.sucs.h.morph \<delta>_def lassoc cancel_right \<open>\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ t = \<alpha>\<^sub>h \<cdot> h\<^sub>m q\<close>..
            also have "... = h (q \<cdot> \<ff> (w \<cdot> [a1])) \<cdot> h ((\<ff> [1 - a1] \<^sup>@ Suc t)\<^sup><\<inverse>q)"
              unfolding lassoc h.marked_version_conjugates
              unfolding \<open>h ((\<ff> [1 - a1] \<^sup>@ Suc t)\<^sup><\<inverse>q) = \<alpha>\<^sub>h \<cdot> \<gamma>\<close> rassoc..
            finally show ?thesis
              unfolding h.morph[symmetric] marked.sucs.h.morph marked.sucs.h.pow_morph
                rq_reassoc[OF \<open>q \<le>s \<ff> [1 - a1] \<^sup>@ Suc t\<close>, of "q \<cdot> \<ff> w \<cdot> \<ff> [a1]"]
              unfolding rassoc by argo
          qed

          have inf_part_equal:
            "{(h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) (w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t)
            |w. w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>}
          = {\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ t \<cdot> w \<cdot> \<delta> \<cdot> \<gamma> |w. w \<in> \<langle>{\<delta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ i |i. i \<le> t}\<rangle>}" (is "?I = ?E")
          proof
            show "?I \<subseteq> ?E"
            proof
              fix x assume "x \<in> ?I"
              then obtain w where "x = h ((q \<cdot> \<ff> (w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t))\<^sup><\<inverse>q )" and
                "w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>"
                unfolding mem_Collect_eq o_apply by blast
              from this(1)[unfolded apply_h0] w_decode[OF this(2)]
              show "x \<in> ?E" by blast
            qed
          next
            show "?E \<subseteq> ?I"
            proof
              fix x assume "x \<in> ?E"
              then obtain w where x: "x = \<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ t \<cdot> w \<cdot> \<delta> \<cdot> \<gamma>" and
                " w \<in> \<langle>{\<delta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ i |i. i \<le> t}\<rangle>" by blast
              from w_decode'[OF this(2)]
              obtain w'  where "w' \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>" and "h\<^sub>m (\<ff> w') = w" by blast
              from x[folded this(2), folded apply_h0[of w']] this(1)
              show "x \<in> ?I"
                unfolding o_apply by blast
            qed
          qed
          from that(4)[OF \<open>\<delta> \<noteq> \<epsilon>\<close> \<open>\<gamma> \<cdot> \<beta> \<noteq> \<epsilon>\<close> \<open>hd \<delta> \<noteq> hd (\<gamma> \<cdot> \<beta>)\<close>, unfolded int', of t,
              unfolded inter, folded inf_part_equal bg_def', unfolded \<W>_explicit]
          show thesis
            by blast
        next
          assume "\<not> \<alpha>\<^sub>h \<cdot> h\<^sub>m q <s h\<^sub>m (\<ff> ([1-a1]\<^sup>@Suc t))"
          note not_suf = this[unfolded marked.sucs.h.pow_morph q21]
          have "\<alpha>\<^sub>h \<cdot> h\<^sub>m q \<le>s (\<alpha>\<^sub>h \<cdot> h\<^sub>m q) \<cdot> h\<^sub>m ((q2 \<cdot> q1) \<^sup>@ Suc t)"
            unfolding q_def shift_pow rassoc hm.morph[symmetric] pows_comm[of _ k]
            unfolding hm.morph lassoc suf_cancel_conv
            unfolding rassoc hm.morph[symmetric] shift_pow[symmetric]
            unfolding hm.morph lassoc suf_cancel_conv
            unfolding h.marked_version_conjugates by blast
          from ruler[reversed, of "\<alpha>\<^sub>h \<cdot> h\<^sub>m q" _ "h\<^sub>m ((q2 \<cdot> q1) \<^sup>@ Suc t)", OF _ triv_suf,
              of "\<alpha>\<^sub>h \<cdot> h\<^sub>m q", OF this]
          have "h\<^sub>m ((q2\<cdot>q1)\<^sup>@Suc t) \<le>s \<alpha>\<^sub>h \<cdot> h\<^sub>m q"
            unfolding marked.sucs.h.pow_morph q21 using not_suf by force
          from this[unfolded q_def shift_pow hm.morph, unfolded hm.pow_morph, folded gb_def[unfolded q21], unfolded lassoc,
              folded k'[folded h.marked_version_conjugates], unfolded rassoc add_exps[symmetric]]
          have "Suc t \<le> k' + k"
            using comp_pows_suf'[OF \<open>\<gamma> \<noteq> \<epsilon>\<close>] by blast
          from le_add_diff_inverse2[OF this]
          have split: "\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k) = \<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k - Suc t) \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ Suc t"
            unfolding add_exps[symmetric] by argo

          have "\<alpha>\<^sub>h \<cdot> h\<^sub>m q = \<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k)"
            unfolding q_def shift_pow hm.morph
            unfolding hm.pow_morph gb_def[symmetric, unfolded q21] lassoc k'[folded h.marked_version_conjugates, symmetric]
            unfolding rassoc add_exps..

          have q_suf: "q \<le>s \<ff> ([a1] \<cdot> [1 - a1] \<^sup>@ Suc t)"
            unfolding q_suf_conv by blast
          have q_suf': "q \<le>s q \<cdot> \<ff> ((w \<cdot> [a1]) \<cdot> [1 - a1] \<^sup>@ Suc t)" for w
            using suf_ext[OF q_suf, of "q \<cdot> \<ff> w"] unfolding marked.sucs.h.morph rassoc.

          note long = rich_block_suf_snd'[of \<epsilon> "1-a1", unfolded emp_simps binA_simps, OF coin_exp]

          have delta_suf: "(\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k - Suc t)) \<le>s \<delta>"
            using long unfolding bgb_q[symmetric] \<delta>_def marked.sucs.h.morph marked.sucs.h.pow_morph q21 hm.morph
            unfolding hm.pow_morph gb_def[unfolded q21,symmetric] split
            unfolding lassoc suf_cancel_conv.

          have apply_h0:  "h ((q \<cdot> \<ff> (w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t))\<^sup><\<inverse>q)
              = \<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k) \<cdot>  h\<^sub>m (\<ff> w) \<cdot> \<delta>\<^sup><\<inverse>(\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k - Suc t))" for w
            unfolding cancel_right[symmetric, of "h ((q \<cdot> \<ff> (w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t))\<^sup><\<inverse>q)" _ "(\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k - Suc t))"]
            unfolding rassoc rq_suf[OF delta_suf]
            unfolding cancel_right[symmetric, of _ "\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k) \<cdot> h\<^sub>m (\<ff> w) \<cdot> \<delta>" "(\<gamma> \<cdot> \<beta>) \<^sup>@ Suc t"]
            unfolding rassoc add_exps[symmetric] \<open>k' + k - Suc t + Suc t = k' + k\<close>  bgb_q[unfolded h.marked_version_conjugates]
            unfolding lassoc h.morph[symmetric]
            unfolding rassoc rq_suf[OF q_suf', unfolded rassoc, of w]
            unfolding h.marked_version_conjugates[symmetric] hm.morph marked.sucs.h.morph
            unfolding lassoc bgb_q unfolding rassoc \<delta>_def gb_def hm.pow_morph marked.sucs.h.pow_morph..

          have inf_part_equal: "{(h \<circ> (\<lambda>x. (q \<cdot> x)\<^sup><\<inverse>q ) \<circ> \<ff>) (w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t) |w. w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>}
                = {\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k) \<cdot> w \<cdot> \<delta>\<^sup><\<inverse>(\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k - Suc t))  |w. w \<in> \<langle>{\<delta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ i |i. i \<le> t}\<rangle>}" (is "?I = ?E")
          proof
            show "?I \<subseteq> ?E"
            proof
              fix x assume "x \<in> ?I"
              then obtain w where "x = h ((q \<cdot> \<ff> (w \<cdot> [a1] \<cdot> [1 - a1] \<^sup>@ Suc t))\<^sup><\<inverse>q )" and
                "w \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>"
                unfolding mem_Collect_eq o_apply apply_h0 by blast

              from this(1)[unfolded apply_h0] w_decode[OF this(2)]
              show "x \<in> ?E" by blast
            qed
          next
            show "?E \<subseteq> ?I"
            proof
              fix x assume "x \<in> ?E"
              then obtain w where x: "x = \<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k) \<cdot> w \<cdot> \<delta>\<^sup><\<inverse>(\<beta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ (k' + k - Suc t))" and
                " w \<in> \<langle>{\<delta> \<cdot> (\<gamma> \<cdot> \<beta>) \<^sup>@ i |i. i \<le> t}\<rangle>" by blast
              from w_decode'[OF this(2)]
              obtain w'  where "w' \<in> \<langle>{[a1] \<cdot> [1 - a1] \<^sup>@ i |i. i \<le> t}\<rangle>" and "h\<^sub>m (\<ff> w') = w" by blast
              from x[folded this(2), folded apply_h0[of w']] this(1)
              show "x\<in> ?I"
                unfolding o_apply by blast
            qed
          qed
          have "1 \<le> Suc t \<and> Suc t \<le> k' + k" using \<open>Suc t \<le> k' + k\<close> by simp
          from that(5)[OF \<open>\<delta> \<noteq> \<epsilon>\<close> \<open>\<gamma> \<cdot> \<beta> \<noteq> \<epsilon>\<close> \<open>hd \<delta> \<noteq> hd (\<gamma> \<cdot> \<beta>)\<close> this]
          show thesis
            unfolding diff_Suc_1 unfolding int' unfolding inter \<W>_explicit bg_def'[symmetric]
            unfolding inf_part_equal[symmetric] by blast
        qed
      qed
    qed
  qed
qed

end
