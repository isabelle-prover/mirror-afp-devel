theory RRn_Automata
  imports Tree_Automata_Complement Ground_Ctxt
begin
section \<open>Regular relations\<close>

subsection \<open>Encoding pairs of terms\<close>

text \<open>The encoding of two terms $s$ and $t$ is given by its tree domain, which is the union of the
domains of $s$ and $t$, and the labels, which arise from looking up each position in $s$ and $t$,
respectively.\<close>

definition gpair :: "'f gterm \<Rightarrow> 'g gterm \<Rightarrow> ('f option \<times> 'g option) gterm" where
  "gpair s t = glabel (\<lambda>p. (gfun_at s p, gfun_at t p)) (gunion (gdomain s) (gdomain t))"

text \<open>We provide an efficient implementation of gpair.\<close>

definition zip_fill :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a option \<times> 'b option) list" where
  "zip_fill xs ys = zip (map Some xs @ replicate (length ys - length xs) None)
    (map Some ys @ replicate (length xs - length ys) None)"

lemma zip_fill_code [code]:
  "zip_fill xs [] = map (\<lambda>x. (Some x, None)) xs"
  "zip_fill [] ys = map (\<lambda>y. (None, Some y)) ys"
  "zip_fill (x # xs) (y # ys) = (Some x, Some y) # zip_fill xs ys"
  subgoal by (induct xs) (auto simp: zip_fill_def)
  subgoal by (induct ys) (auto simp: zip_fill_def)
  subgoal by (auto simp: zip_fill_def)
  done

lemma length_zip_fill [simp]:
  "length (zip_fill xs ys) = max (length xs) (length ys)"
  by (auto simp: zip_fill_def)

lemma nth_zip_fill:
  assumes "i < max (length xs) (length ys)"
  shows "zip_fill xs ys ! i = (if i < length xs then Some (xs ! i) else None, if i < length ys then Some (ys ! i) else None)"
  using assms by (auto simp: zip_fill_def nth_append)

fun gpair_impl :: "'f gterm option \<Rightarrow> 'g gterm option \<Rightarrow> ('f option \<times> 'g option) gterm" where
  "gpair_impl (Some s) (Some t) = gpair s t"
| "gpair_impl (Some s) None     = map_gterm (\<lambda>f. (Some f, None)) s"
| "gpair_impl None     (Some t) = map_gterm (\<lambda>f. (None, Some f)) t"
| "gpair_impl None     None     = GFun (None, None) []"

declare gpair_impl.simps(2-4)[code]

lemma gpair_impl_code [simp, code]:
  "gpair_impl (Some s) (Some t) =
    (case s of GFun f ss \<Rightarrow> case t of GFun g ts \<Rightarrow>
    GFun (Some f, Some g) (map (\<lambda>(s, t). gpair_impl s t) (zip_fill ss ts)))"
proof (induct "gdomain s" "gdomain t" arbitrary: s t rule: gunion.induct)
  case (1 f ss g ts)
  obtain f' ss' where [simp]: "s = GFun f' ss'" by (cases s)
  obtain g' ts' where [simp]: "t = GFun g' ts'" by (cases t)
  show ?case using 1(2,3) 1(1)[of i "ss' ! i" "ts' ! i" for i]
    by (auto simp: gpair_def comp_def nth_zip_fill intro: glabel_map_gterm_conv[unfolded comp_def]
      intro!: nth_equalityI)
qed

lemma gpair_code [code]:
  "gpair s t = gpair_impl (Some s) (Some t)"
  by simp

(* export_code gpair in Haskell *)

declare gpair_impl.simps(1)[simp del]

text \<open>We can easily prove some basic properties. I believe that proving them by induction with a
definition along the lines of @{const gpair_impl} would be very cumbersome.\<close>

lemma gpair_swap:
  "map_gterm prod.swap (gpair s t) = gpair t s"
  by (intro eq_gterm_by_gposs_gfun_at) (auto simp: gpair_def)

lemma gpair_assoc:
  defines "f \<equiv> \<lambda>(f, gh). (f, gh \<bind> fst, gh \<bind> snd)"
  defines "g \<equiv> \<lambda>(fg, h). (fg \<bind> fst, fg \<bind> snd, h)"
  shows "map_gterm f (gpair s (gpair t u)) = map_gterm g (gpair (gpair s t) u)"
  by (intro eq_gterm_by_gposs_gfun_at) (auto simp: gpair_def f_def g_def)


subsection \<open>Decoding of pairs\<close>

fun gcollapse :: "'f option gterm \<Rightarrow> 'f gterm option" where
  "gcollapse (GFun None _) = None"
| "gcollapse (GFun (Some f) ts) = Some (GFun f (map the (filter (\<lambda>t. \<not> Option.is_none t) (map gcollapse ts))))"

lemma gcollapse_groot_None [simp]:
  "groot_sym t = None \<Longrightarrow> gcollapse t = None"
  "fst (groot t) = None \<Longrightarrow> gcollapse t = None"
  by (cases t, simp)+

definition gfst :: "('f option \<times> 'g option) gterm \<Rightarrow> 'f gterm" where
  "gfst = the \<circ> gcollapse \<circ> map_gterm fst"

definition gsnd :: "('f option \<times> 'g option) gterm \<Rightarrow> 'g gterm" where
  "gsnd = the \<circ> gcollapse \<circ> map_gterm snd"

lemma filter_less_upt:
  "[i\<leftarrow>[i..<m] . i < n] = [i..<min n m]"
proof (cases "i \<le> m")
  case True then show ?thesis
  proof (induct rule: inc_induct)
    case (step n) then show ?case by (auto simp: upt_rec[of n])
  qed simp
qed simp

lemma gcollapse_aux:
  assumes "gposs s = {p. p \<in> gposs t \<and> gfun_at t p \<noteq> Some None}"
  shows "gposs (the (gcollapse t)) = gposs s"
    "\<And>p. p \<in> gposs s \<Longrightarrow> gfun_at (the (gcollapse t)) p = (gfun_at t p \<bind> id)"
proof (goal_cases)
  define s' t' where "s' \<equiv> gdomain s" and "t' \<equiv> gdomain t"
  have *: "gposs (the (gcollapse t)) = gposs s \<and>
    (\<forall>p. p \<in> gposs s \<longrightarrow> gfun_at (the (gcollapse t)) p = (gfun_at t p \<bind> id))"
  using assms s'_def t'_def
  proof (induct s' t' arbitrary: s t rule: gunion.induct)
    case (1 f' ss' g' ts')
    obtain f ss where s [simp]: "s = GFun f ss" by (cases s)
    obtain g ts where t [simp]: "t = GFun (Some g) ts"
      using arg_cong[OF 1(2), of "\<lambda>P. [] \<in> P"] by (cases t) auto
    have *: "i < length ts \<Longrightarrow> \<not> Option.is_none (gcollapse (ts ! i)) \<longleftrightarrow> i < length ss" for i
      using arg_cong[OF 1(2), of "\<lambda>P. [i] \<in> P"] by (cases "ts ! i") auto
    have l: "length ss \<le> length ts"
      using arg_cong[OF 1(2), of "\<lambda>P. [length ss-1] \<in> P"] by auto
    have [simp]: "[t\<leftarrow>map gcollapse ts . \<not> Option.is_none t] = take (length ss) (map gcollapse ts)"
      by (subst (2) map_nth[symmetric]) (auto simp add: * filter_map comp_def filter_less_upt
        cong: filter_cong[OF refl, of "[0..<length ts]", unfolded set_upt atLeastLessThan_iff]
        intro!: nth_equalityI)
    have [simp]: "i < length ss \<Longrightarrow> gposs (ss ! i) = gposs (the (gcollapse (ts ! i)))" for i
      using conjunct1[OF 1(1), of i "ss ! i" "ts ! i"] l arg_cong[OF 1(2), of "\<lambda>P. {p. i # p \<in> P}"]
        1(3,4) by simp
    show ?case
    proof (intro conjI allI, goal_cases A B)
      case A show ?case using l by (auto simp: comp_def split: if_splits)
    next
      case (B p) show ?case
      proof (cases p)
        case (Cons i q) then show ?thesis using arg_cong[OF 1(2), of "\<lambda>P. {p. i # p \<in> P}"]
          spec[OF conjunct2[OF 1(1)], of i "ss ! i" "ts ! i" q] 1(3,4) by auto
      qed auto
    qed
  qed
  { case 1 then show ?case using * by blast
  next
    case 2 then show ?case using * by blast }
qed

lemma gfst_gpair:
  "gfst (gpair s t) = s"
proof -
  have *: "gposs s = {p \<in> gposs (map_gterm fst (gpair s t)). gfun_at (map_gterm fst (gpair s t)) p \<noteq> Some None}"
    using gfun_at_nongposs
    by (fastforce simp: gpair_def elim: gfun_at_possE)
  show ?thesis unfolding gfst_def comp_def using gcollapse_aux[OF *]
    by (auto intro!: eq_gterm_by_gposs_gfun_at simp: gpair_def)
qed

lemma gsnd_gpair:
  "gsnd (gpair s t) = t"
  using gfst_gpair[of t s] gpair_swap[of t s, symmetric]
  by (simp add: gfst_def gsnd_def gpair_def gterm.map_comp comp_def)

lemma gpair_impl_None_Inv:
  "map_gterm (the \<circ> snd) (gpair_impl None (Some t)) = t"
  by (simp add: gterm.map_ident gterm.map_comp comp_def)

subsection \<open>Contexts to gpair\<close>

lemma gpair_context1:
  assumes "length ts = length us"
  shows "gpair (GFun f ts) (GFun f us) = GFun (Some f, Some f) (map (case_prod gpair) (zip ts us))"
  using assms unfolding gpair_code by (auto intro!: nth_equalityI simp: zip_fill_def)

lemma gpair_context2:
  assumes "\<And> i. i < length ts \<Longrightarrow> ts ! i = gpair (ss ! i) (us ! i)"
  and "length ss = length ts" and "length us = length ts"
  shows "GFun (Some f, Some h) ts = gpair (GFun f ss) (GFun h us)"
  using assms unfolding gpair_code gpair_impl_code
  by (auto simp: zip_fill_def intro!: nth_equalityI)

lemma map_funs_term_some_gpair:
  shows "gpair t t = map_gterm (\<lambda>f. (Some f, Some f)) t"
proof (induct t)
  case (GFun f ts)
  then show ?case by (auto intro!: gpair_context2[symmetric])
qed


lemma gpair_inject [simp]:
  "gpair s t = gpair s' t' \<longleftrightarrow> s = s' \<and> t = t'"
  by (metis gfst_gpair gsnd_gpair)

abbreviation gterm_to_None_Some :: "'f gterm \<Rightarrow> ('f option \<times> 'f option) gterm" where
  "gterm_to_None_Some t \<equiv> map_gterm (\<lambda>f. (None, Some f)) t"
abbreviation "gterm_to_Some_None t \<equiv> map_gterm (\<lambda>f. (Some f, None)) t"

lemma inj_gterm_to_None_Some: "inj gterm_to_None_Some"
    by (meson Pair_inject gterm.inj_map inj_onI option.inject)

lemma zip_fill1:
  assumes "length ss < length ts"
  shows "zip_fill ss ts = zip (map Some ss) (map Some (take (length ss) ts)) @
    map (\<lambda> x. (None, Some x)) (drop (length ss) ts)"
  using assms by (auto simp: zip_fill_def list_eq_iff_nth_eq nth_append simp add: min.absorb2)

lemma zip_fill2:
  assumes "length ts < length ss"
  shows "zip_fill ss ts = zip (map Some (take (length ts) ss)) (map Some ts) @
    map (\<lambda> x. (Some x, None)) (drop (length ts) ss)"
  using assms by (auto simp: zip_fill_def list_eq_iff_nth_eq nth_append simp add: min.absorb2)

(* GPair position lemmas *)

(* MOVE me*)
lemma not_gposs_append [simp]:
  assumes "p \<notin> gposs t"
  shows "p @ q \<in> gposs t = False" using assms poss_gposs_conv
  using poss_append_poss by blast

(*end Move *)

lemma gfun_at_gpair:
  "gfun_at (gpair s t) p = (if p \<in> gposs s then (if p \<in> gposs t
                                                 then Some (gfun_at s p, gfun_at t p)
                                                 else Some (gfun_at s p, None)) else
                           (if p \<in> gposs t then Some (None, gfun_at t p) else None))"
  using gfun_at_glabel by (auto simp: gpair_def)

lemma gposs_of_gpair [simp]:
  shows "gposs (gpair s t) = gposs s \<union> gposs t"
  by (auto simp: gpair_def)

lemma poss_to_gpair_poss:
  "p \<in> gposs s \<Longrightarrow> p \<in> gposs (gpair s t)"
  "p \<in> gposs t \<Longrightarrow> p \<in> gposs (gpair s t)"
  by auto

lemma gsubt_at_gpair_poss:
  assumes "p \<in> gposs s" and "p \<in> gposs t"
  shows "gsubt_at (gpair s t) p = gpair (gsubt_at s p) (gsubt_at t p)" using assms
  by (auto simp: gunion_gsubt_at_poss gfun_at_gpair intro!: eq_gterm_by_gposs_gfun_at)

lemma subst_at_gpair_nt_poss_Some_None:
  assumes "p \<in> gposs s" and "p \<notin> gposs t"
  shows "gsubt_at (gpair s t) p = gterm_to_Some_None (gsubt_at s p)" using assms gfun_at_poss
  by (force simp: gunion_gsubt_at_poss gfun_at_gpair intro!: eq_gterm_by_gposs_gfun_at)

lemma subst_at_gpair_nt_poss_None_Some:
  assumes "p \<in> gposs t" and "p \<notin> gposs s"
  shows "gsubt_at (gpair s t) p = gterm_to_None_Some (gsubt_at t p)" using assms gfun_at_poss
  by (force simp: gunion_gsubt_at_poss gfun_at_gpair intro!: eq_gterm_by_gposs_gfun_at)


lemma gpair_ctxt_decomposition:
  fixes C defines "p \<equiv> ghole_pos C"
  assumes "p \<notin> gposs s" and "gpair s t = C\<langle>gterm_to_None_Some u\<rangle>\<^sub>G"
  shows "gpair s (gctxt_at_pos t p)\<langle>v\<rangle>\<^sub>G = C\<langle>gterm_to_None_Some v\<rangle>\<^sub>G"
  using assms(2-)
proof -
  note p[simp] = assms(1)
  have pt: "p \<in> gposs t" and pc: "p \<in> gposs C\<langle>gterm_to_None_Some v\<rangle>\<^sub>G"
    and pu: "p \<in> gposs C\<langle>gterm_to_None_Some u\<rangle>\<^sub>G"
    using arg_cong[OF assms(3), of gposs] assms(2) ghole_pos_in_apply
    by auto
  have *: "gctxt_at_pos (gpair s (gctxt_at_pos t (ghole_pos C))\<langle>v\<rangle>\<^sub>G) (ghole_pos C) = gctxt_at_pos (gpair s t) (ghole_pos C)"
    using assms(2) pt
    by (intro eq_gctxt_at_pos)
      (auto simp: gposs_gctxt_at_pos gunion_gsubt_at_poss gfun_at_gpair gfun_at_gctxt_at_pos_not_after)
  have "gsubt_at (gpair s (gctxt_at_pos t p)\<langle>v\<rangle>\<^sub>G) p = gsubt_at C\<langle>gterm_to_None_Some v\<rangle>\<^sub>G p"
    using pt assms(2) subst_at_gpair_nt_poss_None_Some[OF _ assms(2), of "(gctxt_at_pos t p)\<langle>v\<rangle>\<^sub>G"]
    using ghole_pos_gctxt_at_pos
    by (simp add: ghole_pos_in_apply)
  then show ?thesis using assms(2) ghole_pos_gctxt_at_pos
    using gsubst_at_gctxt_at_eq_gtermD[OF assms(3) pu]
    by (intro gsubst_at_gctxt_at_eq_gtermI[OF _ pc])
       (auto simp: ghole_pos_in_apply * gposs_gctxt_at_pos[OF pt, unfolded p])
qed

lemma groot_gpair [simp]:
  "fst (groot (gpair s t)) = (Some (fst (groot s)), Some (fst (groot t)))"
  by (cases s; cases t) (auto simp add: gpair_code)

lemma ground_ctxt_adapt_ground [intro]:
  assumes "ground_ctxt C"
  shows "ground_ctxt (adapt_vars_ctxt C)"
  using assms by (induct C) auto

lemma adapt_vars_ctxt2 :
  assumes "ground_ctxt C"
  shows "adapt_vars_ctxt (adapt_vars_ctxt C) = adapt_vars_ctxt C" using assms
  by (induct C) (auto simp: adapt_vars2)

subsection \<open>Encoding of lists of terms\<close>

definition gencode :: "'f gterm list \<Rightarrow> 'f option list gterm" where
  "gencode ts = glabel (\<lambda>p. map (\<lambda>t. gfun_at t p) ts) (gunions (map gdomain ts))"

definition gdecode_nth :: "'f option list gterm \<Rightarrow> nat \<Rightarrow> 'f gterm" where
  "gdecode_nth t i = the (gcollapse (map_gterm (\<lambda>f. f ! i) t))"

lemma gdecode_nth_gencode:
  assumes "i < length ts"
  shows "gdecode_nth (gencode ts) i = ts ! i"
proof -
  have *: "gposs (ts ! i) = {p \<in> gposs (map_gterm (\<lambda>f. f ! i) (gencode ts)).
           gfun_at (map_gterm (\<lambda>f. f ! i) (gencode ts)) p \<noteq> Some None}"
    using assms
    by (auto simp: gencode_def elim: gfun_at_possE dest: gfun_at_poss_gpossD) (force simp: fun_at_def' split: if_splits)
  show ?thesis unfolding gdecode_nth_def comp_def using assms gcollapse_aux[OF *]
    by (auto intro!: eq_gterm_by_gposs_gfun_at simp: gencode_def)
     (metis (no_types) gposs_map_gterm length_map list.set_map map_nth_eq_conv nth_mem) 
qed

definition gdecode :: "'f option list gterm \<Rightarrow> 'f gterm list" where
  "gdecode t = (case t of GFun f ts \<Rightarrow> map (\<lambda>i. gdecode_nth t i) [0..<length f])"

lemma gdecode_gencode:
  "gdecode (gencode ts) = ts"
proof (cases "gencode ts")
  case (GFun f ts')
  have "length f = length ts" using arg_cong[OF GFun, of "\<lambda>t. gfun_at t []"]
    by (auto simp: gencode_def)
  then show ?thesis using gdecode_nth_gencode[of _ ts]
    by (auto intro!: nth_equalityI simp: gdecode_def GFun)
qed

definition gencode_impl :: "'f gterm option list \<Rightarrow> 'f option list gterm" where
  "gencode_impl ts = glabel (\<lambda>p. map (\<lambda>t. t \<bind> (\<lambda>t. gfun_at t p)) ts) (gunions (map (case_option (GFun () []) gdomain) ts))"

lemma gencode_code [code]:
  "gencode ts = gencode_impl (map Some ts)"
  by (auto simp: gencode_def gencode_impl_def comp_def)

lemma gencode_singleton:
  "gencode [t] = map_gterm (\<lambda>f. [Some f]) t"
  using glabel_map_gterm_conv[unfolded comp_def, of "\<lambda>t. [t]" t]
  by (simp add: gunions_def gencode_def)

lemma gencode_pair:
  "gencode [t, u] = map_gterm (\<lambda>(f, g). [f, g]) (gpair t u)"
  by (simp add: gunions_def gencode_def gpair_def map_gterm_glabel comp_def)


subsection \<open>RRn relations\<close>

definition RR1_spec where
  "RR1_spec A T \<longleftrightarrow> \<L> A = T"

definition RR2_spec where
  "RR2_spec A T \<longleftrightarrow> \<L> A = {gpair t u |t u. (t, u) \<in> T}"

definition RRn_spec where
  "RRn_spec n A R \<longleftrightarrow> \<L> A = gencode ` R \<and> (\<forall>ts \<in> R. length ts = n)"

lemma RR1_to_RRn_spec:
  assumes "RR1_spec A T"
  shows "RRn_spec 1 (fmap_funs_reg (\<lambda>f. [Some f]) A) ((\<lambda>t. [t]) ` T)"
proof -
  have [simp]: "inj_on (\<lambda>f. [Some f]) X" for X by (auto simp: inj_on_def)
  show ?thesis using assms
    by (auto simp: RR1_spec_def RRn_spec_def fmap_funs_\<L> image_comp comp_def gencode_singleton)
qed

lemma RR2_to_RRn_spec:
  assumes "RR2_spec A T"
  shows "RRn_spec 2 (fmap_funs_reg (\<lambda>(f, g). [f, g]) A) ((\<lambda>(t, u). [t, u]) ` T)"
proof -
  have [simp]: "inj_on (\<lambda>(f, g). [f, g]) X" for X by (auto simp: inj_on_def)
  show ?thesis using assms
    by (auto simp: RR2_spec_def RRn_spec_def fmap_funs_\<L> image_comp comp_def prod.case_distrib gencode_pair)
qed

lemma RRn_to_RR2_spec:
  assumes "RRn_spec 2 A T"
  shows "RR2_spec (fmap_funs_reg (\<lambda> f. (f ! 0 ,  f ! 1)) A) ((\<lambda> f. (f ! 0, f ! 1)) ` T)" (is "RR2_spec ?A ?T")
proof -
  {fix xs assume "xs \<in> T" then have "length xs = 2" using assms by (auto simp: RRn_spec_def)
    then obtain t u where *: "xs = [t, u]"
      by (metis (no_types, lifting) One_nat_def Suc_1 length_0_conv length_Suc_conv)
    have **: "(\<lambda>f. (f ! 0, f ! Suc 0)) \<circ> (\<lambda>(f, g). [f, g]) = id" by auto
    have "map_gterm (\<lambda>f. (f ! 0, f ! Suc 0)) (gencode xs) = gpair t u"
      unfolding * gencode_pair gterm.map_comp ** gterm.map_id ..
    then have "\<exists> t u. xs = [t, u] \<and> map_gterm (\<lambda>f. (f ! 0, f ! Suc 0)) (gencode xs) = gpair t u"
      using * by blast}
  then show ?thesis using assms
    by (force simp: RR2_spec_def RRn_spec_def fmap_funs_\<L> image_comp comp_def prod.case_distrib gencode_pair image_iff Bex_def)
qed

lemma relabel_RR1_spec [simp]:
  "RR1_spec (relabel_reg A) T \<longleftrightarrow> RR1_spec A T"
  by (simp add: RR1_spec_def)

lemma relabel_RR2_spec [simp]:
  "RR2_spec (relabel_reg A) T \<longleftrightarrow> RR2_spec A T"
  by (simp add: RR2_spec_def)

lemma relabel_RRn_spec [simp]:
  "RRn_spec n (relabel_reg A) T \<longleftrightarrow> RRn_spec n A T"
  by (simp add: RRn_spec_def)

lemma trim_RR1_spec [simp]:
  "RR1_spec (trim_reg A) T \<longleftrightarrow> RR1_spec A T"
  by (simp add: RR1_spec_def \<L>_trim)

lemma trim_RR2_spec [simp]:
  "RR2_spec (trim_reg A) T \<longleftrightarrow> RR2_spec A T"
  by (simp add: RR2_spec_def \<L>_trim)

lemma trim_RRn_spec [simp]:
  "RRn_spec n (trim_reg A) T \<longleftrightarrow> RRn_spec n A T"
  by (simp add: RRn_spec_def \<L>_trim)

lemma swap_RR2_spec:
  assumes "RR2_spec A R"
  shows "RR2_spec (fmap_funs_reg prod.swap A) (prod.swap ` R)" using assms
  by (force simp add: RR2_spec_def fmap_funs_\<L> gpair_swap image_iff)

subsection \<open>Nullary automata\<close>

lemma false_RRn_spec:
  "RRn_spec n empty_reg {}"
  by (auto simp: RRn_spec_def \<L>_epmty)

lemma true_RR0_spec:
  "RRn_spec 0 (Reg {|q|} (TA {|[] [] \<rightarrow> q|} {||})) {[]}"
  by (auto simp: RRn_spec_def \<L>_def const_ta_lang gencode_def gunions_def)

subsection \<open>Pairing RR1 languages\<close>

text \<open>cf. @{const "gpair"}.\<close>

abbreviation "lift_Some_None s \<equiv> (Some s, None)"
abbreviation "lift_None_Some s \<equiv> (None, Some s)"
abbreviation "pair_eps A B \<equiv> (\<lambda> (p, q). ((Some (fst p), q), (Some (snd p), q))) |`| (eps A |\<times>| finsert None (Some |`| \<Q> B))"
abbreviation "pair_rule \<equiv> (\<lambda> (ra, rb). TA_rule (Some (r_root ra), Some (r_root rb)) (zip_fill (r_lhs_states ra) (r_lhs_states rb)) (Some (r_rhs ra), Some (r_rhs rb)))"

lemma lift_Some_None_pord_swap [simp]:
  "prod.swap \<circ> lift_Some_None = lift_None_Some"
  "prod.swap \<circ> lift_None_Some = lift_Some_None"
  by auto

lemma eps_to_pair_eps_Some_None:
  "(p, q) |\<in>| eps \<A> \<Longrightarrow> (lift_Some_None p, lift_Some_None q) |\<in>| pair_eps \<A> \<B>"
  by force

definition pair_automaton :: "('p, 'f) ta \<Rightarrow> ('q, 'g) ta \<Rightarrow> ('p option \<times> 'q option, 'f option \<times> 'g option) ta" where
  "pair_automaton A B = TA 
    (map_ta_rule lift_Some_None lift_Some_None |`| rules A |\<union>|
     map_ta_rule lift_None_Some lift_None_Some |`| rules B |\<union>|
     pair_rule |`| (rules A |\<times>| rules B))
    (pair_eps A B |\<union>| map_both prod.swap |`| (pair_eps B A))"

definition pair_automaton_reg where
  "pair_automaton_reg R L = Reg (Some |`| fin R |\<times>| Some |`| fin L) (pair_automaton (ta R) (ta L))"


lemma pair_automaton_eps_simps:
  "(lift_Some_None p, p') |\<in>| eps (pair_automaton A B) \<longleftrightarrow> (lift_Some_None p, p') |\<in>| pair_eps A B"
  "(q , lift_Some_None q') |\<in>| eps (pair_automaton A B) \<longleftrightarrow> (q , lift_Some_None q') |\<in>| pair_eps A B"
  by (auto simp: pair_automaton_def eps_to_pair_eps_Some_None)

lemma pair_automaton_eps_Some_SomeD:
  "((Some p, Some p'), r) |\<in>| eps (pair_automaton A B) \<Longrightarrow> fst r \<noteq> None \<and> snd r \<noteq> None \<and> (Some p = fst r \<or> Some p' = snd r) \<and>
     (Some p \<noteq> fst r \<longrightarrow> (p, the (fst r)) |\<in>| (eps A)) \<and> (Some p' \<noteq> snd r \<longrightarrow> (p', the (snd r)) |\<in>| (eps B))"
  by (auto simp: pair_automaton_def)

lemma pair_automaton_eps_Some_SomeD2:
  "(r, (Some p, Some p')) |\<in>| eps (pair_automaton A B) \<Longrightarrow> fst r \<noteq> None \<and> snd r \<noteq> None \<and> (fst r = Some p \<or> snd r = Some p') \<and>
     (fst r \<noteq> Some p \<longrightarrow> (the (fst r), p) |\<in>| (eps A)) \<and> (snd r \<noteq> Some p' \<longrightarrow> (the (snd r), p') |\<in>| (eps B))"
  by (auto simp: pair_automaton_def)

lemma pair_eps_Some_None:
  fixes p q q'
  defines "l \<equiv> (p, q)" and "r \<equiv> lift_Some_None q'"
  assumes "(l, r) |\<in>| (eps (pair_automaton A B))|\<^sup>+|"
  shows "q = None \<and> p \<noteq> None \<and> (the p, q') |\<in>| (eps A)|\<^sup>+|" using assms(3, 1, 2)
proof (induct arbitrary: q' q rule: ftrancl_induct)
  case (Step b)
  then show ?case unfolding pair_automaton_eps_simps
    by (auto simp: pair_automaton_eps_simps)
       (meson not_ftrancl_into)
qed (auto simp: pair_automaton_def)

lemma pair_eps_Some_Some:
  fixes p q
  defines "l \<equiv> (Some p, Some q)"
  assumes "(l, r) |\<in>| (eps (pair_automaton A B))|\<^sup>+|"
  shows "fst r \<noteq> None \<and> snd r \<noteq> None \<and>
      (fst l \<noteq> fst r \<longrightarrow> (p, the (fst r)) |\<in>| (eps A)|\<^sup>+|) \<and>
      (snd l \<noteq> snd r \<longrightarrow> (q, the (snd r)) |\<in>| (eps B)|\<^sup>+|)"
  using assms(2, 1)
proof (induct arbitrary: p q rule: ftrancl_induct)
  case (Step b c)
  then obtain r r' where *: "b = (Some r, Some r')" by (cases b) auto
  show ?case using Step(2)
    using pair_automaton_eps_Some_SomeD[OF  Step(3)[unfolded *]]
    by (auto simp: *) (meson not_ftrancl_into)+
qed (auto simp: pair_automaton_def)

lemma pair_eps_Some_Some2:
  fixes p q
  defines "r \<equiv> (Some p, Some q)"
  assumes "(l, r) |\<in>| (eps (pair_automaton A B))|\<^sup>+|"
  shows "fst l \<noteq> None \<and> snd l \<noteq> None \<and>
      (fst l \<noteq> fst r \<longrightarrow> (the (fst l), p) |\<in>| (eps A)|\<^sup>+|) \<and>
      (snd l \<noteq> snd r \<longrightarrow> (the (snd l), q) |\<in>| (eps B)|\<^sup>+|)"
  using assms(2, 1)
proof (induct arbitrary: p q rule: ftrancl_induct)
  case (Step b c)
  from pair_automaton_eps_Some_SomeD2[OF Step(3)]
  obtain r r' where *: "c = (Some r, Some r')" by (cases c) auto
  from Step(2)[OF this] show ?case
    using pair_automaton_eps_Some_SomeD[OF  Step(3)[unfolded *]]
    by (auto simp: *) (meson not_ftrancl_into)+
qed (auto simp: pair_automaton_def)


lemma map_pair_automaton:
  "pair_automaton (fmap_funs_ta f A) (fmap_funs_ta g B) =
   fmap_funs_ta (\<lambda>(a, b). (map_option f a, map_option g b)) (pair_automaton A B)" (is "?Ls = ?Rs")
proof -
  let ?ls = "pair_rule \<circ> map_prod (map_ta_rule id f) (map_ta_rule id g)"
  let ?rs = "map_ta_rule id (\<lambda>(a, b). (map_option f a, map_option g b)) \<circ> pair_rule"
  have *: "(\<lambda>(a, b). (map_option f a, map_option g b)) \<circ> lift_Some_None = lift_Some_None \<circ> f"
    "(\<lambda>(a, b). (map_option f a, map_option g b)) \<circ> lift_None_Some = lift_None_Some \<circ> g"
    by (auto simp: comp_def)
  have "?ls x = ?rs x" for x
    by (cases x) (auto simp: ta_rule.map_sel)
  then have [simp]: "?ls = ?rs" by blast
  then have "rules ?Ls = rules ?Rs"
    unfolding pair_automaton_def fmap_funs_ta_def
    by (simp add: fimage_funion map_ta_rule_comp * map_prod_ftimes)
  moreover have "eps ?Ls = eps ?Rs"
    unfolding pair_automaton_def fmap_funs_ta_def
    by (simp add: fimage_funion \<Q>_def)
  ultimately show ?thesis
    by (intro TA_equalityI) simp
qed

lemmas map_pair_automaton_12 =
  map_pair_automaton[of _ _ id, unfolded fmap_funs_ta_id option.map_id]
  map_pair_automaton[of id _ _, unfolded fmap_funs_ta_id option.map_id]

lemma fmap_states_funs_ta_commute:
  "fmap_states_ta f (fmap_funs_ta g A) = fmap_funs_ta g (fmap_states_ta f A)"
proof -
  have [simp]: "map_ta_rule f id (map_ta_rule id g r) = map_ta_rule id g (map_ta_rule f id r)" for r
    by (cases r) auto
  show ?thesis
    by (auto simp: ta_rule.case_distrib fmap_states_ta_def fmap_funs_ta_def fimage_iff fBex_def split: ta_rule.splits)
qed

lemma states_pair_automaton:
  "\<Q> (pair_automaton A B) |\<subseteq>| (finsert None (Some |`| \<Q> A) |\<times>| (finsert None (Some |`| \<Q> B)))"
  unfolding pair_automaton_def
  apply (intro \<Q>_subseteq_I)
  apply (auto simp: ta_rule.map_sel in_fset_conv_nth nth_zip_fill rule_statesD eps_statesD)
  apply (simp add: rule_statesD)+
  done


lemma swap_pair_automaton:
  assumes "(p, q) |\<in>| ta_der (pair_automaton A B) (term_of_gterm t)"
  shows "(q, p) |\<in>| ta_der (pair_automaton B A) (term_of_gterm (map_gterm prod.swap t))"
proof -
  let ?m = "map_ta_rule prod.swap prod.swap"
  have [simp]: "map prod.swap (zip_fill xs ys) = zip_fill ys xs" for xs ys
    by (auto simp: zip_fill_def zip_nth_conv comp_def intro!: nth_equalityI)
  let ?swp = "\<lambda>X. fmap_states_ta prod.swap (fmap_funs_ta prod.swap X)"
  { fix A B
    let ?AB = "?swp (pair_automaton A B)" and ?BA = "pair_automaton B A"
    have "eps ?AB |\<subseteq>| eps ?BA" "rules ?AB |\<subseteq>| rules ?BA"
      by (auto simp: fmap_states_ta_def fmap_funs_ta_def pair_automaton_def
          fimage_funion comp_def prod.map_comp ta_rule.map_comp)
  } note * = this
  let ?BA = "?swp (?swp (pair_automaton B A))" and ?AB = "?swp (pair_automaton A B)"
  have **: "r |\<in>| rules (pair_automaton B A) \<Longrightarrow> ?m r |\<in>| ?m |`| rules (pair_automaton B A)" for r
    by blast
  have "r |\<in>| rules ?BA \<Longrightarrow> r |\<in>| rules ?AB" "e |\<in>| eps ?BA \<Longrightarrow> e |\<in>| eps ?AB" for r e
    using *[of B A] map_ta_rule_prod_swap_id
    unfolding fmap_funs_ta_def fmap_states_ta_def ta.sel
    by (auto simp: map_ta_rule_comp image_iff ta_rule.map_id0 intro!: bexI[of _ "?m r"]) 
  then have "eps ?BA |\<subseteq>| eps ?AB" "rules ?BA |\<subseteq>| rules ?AB"
    by blast+
  then have "fmap_states_ta prod.swap (fmap_funs_ta prod.swap (pair_automaton A B)) = pair_automaton B A"
    using *[of A B] by (simp add: fmap_states_funs_ta_commute fmap_funs_ta_comp fmap_states_ta_comp TA_equalityI)
  then show ?thesis
    using ta_der_fmap_states_ta[OF ta_der_fmap_funs_ta[OF assms], of prod.swap prod.swap]
    by (simp add: gterm.map_comp comp_def)
qed

lemma to_ta_der_pair_automaton:
  "p |\<in>| ta_der A (term_of_gterm t) \<Longrightarrow>
    (Some p, None) |\<in>| ta_der (pair_automaton A B) (term_of_gterm (map_gterm (\<lambda>f. (Some f, None)) t))"
  "q |\<in>| ta_der B (term_of_gterm u) \<Longrightarrow>
    (None, Some q) |\<in>| ta_der (pair_automaton A B) (term_of_gterm (map_gterm (\<lambda>f. (None, Some f)) u))"
  "p |\<in>| ta_der A (term_of_gterm t) \<Longrightarrow> q |\<in>| ta_der B (term_of_gterm u) \<Longrightarrow>
    (Some p, Some q) |\<in>| ta_der (pair_automaton A B) (term_of_gterm (gpair t u))"
proof (goal_cases sn ns ss)
  let ?AB = "pair_automaton A B"
  have 1: "(Some p, None) |\<in>| ta_der (pair_automaton A B) (term_of_gterm (map_gterm (\<lambda>f. (Some f, None)) s))"
    if "p |\<in>| ta_der A (term_of_gterm s)" for A B p s
  proof (rule fsubsetD[OF ta_der_mono])
    show "rules (fmap_states_ta lift_Some_None (fmap_funs_ta lift_Some_None A)) |\<subseteq>|
      rules (pair_automaton A B)"
      by (auto simp: fmap_states_ta_def fmap_funs_ta_def comp_def ta_rule.map_comp
            pair_automaton_def)
  next
    show "eps (fmap_states_ta lift_Some_None (fmap_funs_ta lift_Some_None A)) |\<subseteq>|
      eps (pair_automaton A B)"
      by (rule fsubsetI)
        (auto simp: fmap_states_ta_def fmap_funs_ta_def pair_automaton_def comp_def fimage.rep_eq
          dest: eps_to_pair_eps_Some_None)
  next
    show "lift_Some_None p |\<in>| ta_der
      (fmap_states_ta lift_Some_None (fmap_funs_ta lift_Some_None A))
      (term_of_gterm (gterm_to_Some_None s))"
      using ta_der_fmap_states_ta[OF ta_der_fmap_funs_ta[OF that], of lift_Some_None]
      using ta_der_fmap_funs_ta ta_der_to_fmap_states_der that by fastforce
  qed
  have 2: "q |\<in>| ta_der B (term_of_gterm t) \<Longrightarrow>
    (None, Some q) |\<in>| ta_der ?AB (term_of_gterm (map_gterm (\<lambda>g. (None, Some g)) t))"
    for q t using swap_pair_automaton[OF 1[of q B t A]] by (simp add: gterm.map_comp comp_def)
  {
    case sn then show ?case by (rule 1)
  next
    case ns then show ?case by (rule 2)
  next
    case ss then show ?case
    proof (induct t arbitrary: p q u)
      case (GFun f ts)
      obtain g us where u [simp]: "u = GFun g us" by (cases u)
      obtain p' ps where p': "f ps \<rightarrow> p' |\<in>| rules A" "p' = p \<or> (p', p) |\<in>| (eps A)|\<^sup>+|" "length ps = length ts"
        "\<And>i. i < length ts \<Longrightarrow> ps ! i |\<in>| ta_der A (term_of_gterm (ts ! i))" using GFun(2) by auto
      obtain q' qs where q': "g qs \<rightarrow> q' |\<in>| rules B" "q' = q \<or> (q', q) |\<in>| (eps B)|\<^sup>+|" "length qs = length us"
        "\<And>i. i < length us \<Longrightarrow> qs ! i |\<in>| ta_der B (term_of_gterm (us ! i))" using GFun(3) by auto
      have *: "Some p |\<in>| Some |`| \<Q> A" "Some q' |\<in>| Some |`| \<Q> B"
        using p'(2,1) q'(1)
        by (auto simp: rule_statesD eps_trancl_statesD)
      have eps: "p' = p \<and> q' = q \<or> ((Some p', Some q'), (Some p, Some q)) |\<in>| (eps ?AB)|\<^sup>+|"
      proof (cases "p' = p")
        case True note p = this then show ?thesis
        proof (cases "q' = q")
          case False
          then have "(q', q) |\<in>| (eps B)|\<^sup>+|" using q'(2) by auto
          hence "((Some p', Some q'), Some p', Some q) |\<in>| (eps (pair_automaton A B))|\<^sup>+|"
          proof (rule ftrancl_map[rotated])
            fix x y
            assume "(x, y) |\<in>| eps B"
            thus "((Some p', Some x), Some p', Some y) |\<in>| eps (pair_automaton A B)"
              using p'(1)[THEN rule_statesD(1), simplified]
              apply (simp add: pair_automaton_def image_iff fSigma.rep_eq)
              by fastforce
          qed
          thus ?thesis
            by (simp add: p)
        qed (simp add: p)
      next
        case False note p = this
        then have *: "(p', p) |\<in>| (eps A)|\<^sup>+|" using p'(2) by auto
        then have eps: "((Some p', Some q'), Some p, Some q') |\<in>| (eps (pair_automaton A B))|\<^sup>+|"
        proof (rule ftrancl_map[rotated])
          fix x y
          assume "(x, y) |\<in>| eps A"
          then show "((Some x, Some q'), Some y, Some q') |\<in>| eps (pair_automaton A B)"
            using q'(1)[THEN rule_statesD(1), simplified]
            apply (simp add: pair_automaton_def image_iff fSigma.rep_eq)
            by fastforce
        qed
        then show ?thesis
        proof (cases "q' = q")
          case True then show ?thesis using eps
            by simp
        next
          case False
          then have "(q', q) |\<in>| (eps B)|\<^sup>+|" using q'(2) by auto
          then have "((Some p, Some q'), Some p, Some q) |\<in>| (eps (pair_automaton A B))|\<^sup>+|"
            apply (rule ftrancl_map[rotated])
            using *[THEN eps_trancl_statesD]
            apply (simp add: p pair_automaton_def image_iff fSigma.rep_eq)
            by fastforce
            
          then show ?thesis using eps
            by (meson ftrancl_trans)
        qed
      qed
      have "(Some f, Some g) zip_fill ps qs \<rightarrow> (Some p', Some q') |\<in>| rules ?AB"
        using p'(1) q'(1) by (force simp: pair_automaton_def)
      then show ?case using GFun(1)[OF nth_mem p'(4) q'(4)] p'(1 - 3)  q'(1 - 3) eps
        using 1[OF p'(4), of _ B] 2[OF q'(4)]
        by (auto simp: gpair_code nth_zip_fill less_max_iff_disj
                    intro!: exI[of _ "zip_fill ps qs"] exI[of _ "Some p'"] exI[of _ "Some q'"])
    qed
  }
qed

lemma from_ta_der_pair_automaton:
  "(None, None) |\<notin>| ta_der (pair_automaton A B) (term_of_gterm s)"
  "(Some p, None) |\<in>| ta_der (pair_automaton A B) (term_of_gterm s) \<Longrightarrow>
    \<exists>t. p |\<in>| ta_der A (term_of_gterm t) \<and> s = map_gterm (\<lambda>f. (Some f, None)) t"
  "(None, Some q) |\<in>| ta_der (pair_automaton A B) (term_of_gterm s) \<Longrightarrow>
    \<exists>u. q |\<in>| ta_der B (term_of_gterm u) \<and> s = map_gterm (\<lambda>f. (None, Some f)) u"
  "(Some p, Some q) |\<in>| ta_der (pair_automaton A B) (term_of_gterm s) \<Longrightarrow>
   \<exists>t u. p |\<in>| ta_der A (term_of_gterm t) \<and> q |\<in>| ta_der B (term_of_gterm u) \<and> s = gpair t u"
proof (goal_cases nn sn ns ss)
  let ?AB = "pair_automaton A B"
  { fix p s A B assume "(Some p, None) |\<in>| ta_der (pair_automaton A B) (term_of_gterm s)"
    then have "\<exists>t. p |\<in>| ta_der A (term_of_gterm t) \<and> s = map_gterm (\<lambda>f. (Some f, None)) t"
    proof (induct s arbitrary: p)
      case (GFun h ss)
      obtain rs sp nq where r: "h rs \<rightarrow> (sp, nq) |\<in>| rules (pair_automaton A B)"
        "sp = Some p \<and> nq = None \<or> ((sp, nq), (Some p, None)) |\<in>| (eps (pair_automaton A B))|\<^sup>+|" "length rs = length ss"
        "\<And>i. i < length ss \<Longrightarrow> rs ! i |\<in>| ta_der (pair_automaton A B) (term_of_gterm (ss ! i))"
        using GFun(2) by auto
      obtain p' where pq: "sp = Some p'" "nq = None" "p' = p \<or> (p', p) |\<in>| (eps A)|\<^sup>+|"
        using r(2) pair_eps_Some_None[of sp nq p A B]
        by (cases sp) auto
      obtain f ps where h: "h = lift_Some_None f" "rs = map lift_Some_None ps"
        "f ps \<rightarrow> p' |\<in>| rules A"
        using r(1) unfolding pq(1, 2) by (auto simp: pair_automaton_def map_ta_rule_cases)
      obtain ts where "\<And>i. i < length ss \<Longrightarrow>
        ps ! i |\<in>| ta_der A (term_of_gterm (ts i)) \<and> ss ! i = map_gterm (\<lambda>f. (Some f, None)) (ts i)"
        using GFun(1)[OF nth_mem, of i "ps ! i" for i] r(4)[unfolded h(2)] r(3)[unfolded h(2) length_map]
        by auto metis
      then show ?case using h(3) pq(3) r(3)[unfolded h(2) length_map]
        by (intro exI[of _ "GFun f (map ts [0..<length ss])"]) (auto simp: h(1) intro!: nth_equalityI)
    qed
  } note 1 = this
  have 2: "\<exists>u. q |\<in>| ta_der B (term_of_gterm u) \<and> s = map_gterm (\<lambda>g. (None, Some g)) u"
    if "(None, Some q) |\<in>| ta_der ?AB (term_of_gterm s)" for q s
    using 1[OF swap_pair_automaton, OF that]
    by (auto simp: gterm.map_comp comp_def gterm.map_ident
      dest!: arg_cong[of "map_gterm prod.swap _" _ "map_gterm prod.swap", unfolded gterm.map_comp])
  {
    case nn
    then show ?case
      by (intro ta_der_not_reach) (auto simp: pair_automaton_def map_ta_rule_cases)
  next
    case sn then show ?case by (rule 1)
  next
    case ns then show ?case by (rule 2)
  next
    case ss then show ?case
    proof (induct s arbitrary: p q)
      case (GFun h ss)
      obtain rs sp sq where r: "h rs \<rightarrow> (sp, sq) |\<in>| rules ?AB"
        "sp = Some p \<and> sq = Some q \<or> ((sp, sq), (Some p, Some q)) |\<in>| (eps ?AB)|\<^sup>+|" "length rs = length ss"
        "\<And>i. i < length ss \<Longrightarrow> rs ! i |\<in>| ta_der ?AB (term_of_gterm (ss ! i))"
        using GFun(2) by auto
      from r(2) have "sp \<noteq> None" "sq \<noteq> None" using pair_eps_Some_Some2[of "(sp, sq)" p q]
        by auto
      then obtain p' q' where pq: "sp = Some p'" "sq = Some q'"
        "p' = p \<or> (p', p) |\<in>| (eps A)|\<^sup>+|" "q' = q \<or> (q', q) |\<in>| (eps B)|\<^sup>+|"
        using r(2) pair_eps_Some_Some[where ?r = "(Some p, Some q)" and ?A = A and ?B = B]
        using pair_eps_Some_Some2[of "(sp, sq)" p q]
        by (cases sp; cases sq) auto
      obtain f g ps qs where h: "h = (Some f, Some g)" "rs = zip_fill ps qs"
        "f ps \<rightarrow> p' |\<in>| rules A" "g qs \<rightarrow> q' |\<in>| rules B"
        using r(1) unfolding pq(1,2) by (auto simp: pair_automaton_def map_ta_rule_cases)
      have *: "\<exists>t u. ps ! i |\<in>| ta_der A (term_of_gterm t) \<and> qs ! i |\<in>| ta_der B (term_of_gterm u) \<and> ss ! i = gpair t u"
        if "i < length ps" "i < length qs" for i
        using GFun(1)[OF nth_mem, of i "ps ! i" "qs ! i"] r(4)[unfolded pq(1,2) h(2), of i] that
          r(3)[symmetric] by (auto simp: nth_zip_fill h(2))
      { fix i assume "i < length ss"
        then have "\<exists>t u. (i < length ps \<longrightarrow> ps ! i |\<in>| ta_der A (term_of_gterm t)) \<and>
            (i < length qs \<longrightarrow> qs ! i |\<in>| ta_der B (term_of_gterm u)) \<and>
            ss ! i = gpair_impl (if i < length ps then Some t else None) (if i < length qs then Some u else None)"
          using *[of i] 1[of "ps ! i" A B "ss ! i"] 2[of "qs ! i" "ss ! i"] r(4)[of i] r(3)[symmetric]
          by (cases "i < length ps"; cases "i < length qs")
            (auto simp add: h(2) nth_zip_fill less_max_iff_disj gpair_code split: gterm.splits) }
      then obtain ts us where "\<And>i. i < length ss \<Longrightarrow>
          (i < length ps \<longrightarrow> ps ! i |\<in>| ta_der A (term_of_gterm (ts i))) \<and>
          (i < length qs \<longrightarrow> qs ! i |\<in>| ta_der B (term_of_gterm (us i))) \<and>
          ss ! i = gpair_impl (if i < length ps then Some (ts i) else None) (if i < length qs then Some (us i) else None)"
        by metis
      moreover then have "\<And>i. i < length ps \<Longrightarrow> ps ! i |\<in>| ta_der A (term_of_gterm (ts i))"
         "\<And>i. i < length qs \<Longrightarrow> qs ! i |\<in>| ta_der B (term_of_gterm (us i))"
        using r(3)[unfolded h(2)] by auto
      ultimately show ?case using h(3,4) pq(3,4) r(3)[symmetric]
        by (intro exI[of _ "GFun f (map ts [0..<length ps])"] exI[of _ "GFun g (map us [0..<length qs])"])
          (auto simp: gpair_code h(1,2) less_max_iff_disj nth_zip_fill intro!: nth_equalityI split: prod.splits gterm.splits)
    qed
  }
qed


lemma diagonal_automaton:
  assumes "RR1_spec A R"
  shows "RR2_spec (fmap_funs_reg (\<lambda>f. (Some f, Some f)) A) {(s, s) | s. s \<in> R}" using assms
  by (auto simp: RR2_spec_def RR1_spec_def fmap_funs_reg_def fmap_funs_gta_lang map_funs_term_some_gpair \<L>_def)

lemma pair_automaton:
  assumes "RR1_spec A T" "RR1_spec B U"
  shows "RR2_spec (pair_automaton_reg A B) (T \<times> U)"
proof -
  let ?AB = "pair_automaton (ta A) (ta B)"
  { fix t u assume t: "t \<in> T" and u: "u \<in> U"
    obtain p where p: "p |\<in>| fin A" "p |\<in>| ta_der (ta A) (term_of_gterm t)" using t assms(1)
      by (auto simp: RR1_spec_def gta_lang_def \<L>_def gta_der_def)
    obtain q where q: "q |\<in>| fin B" "q |\<in>| ta_der (ta B) (term_of_gterm u)" using u assms(2)
      by (auto simp: RR1_spec_def gta_lang_def \<L>_def gta_der_def)
    have "gpair t u \<in> \<L> (pair_automaton_reg A B)" using p(1) q(1) to_ta_der_pair_automaton(3)[OF p(2) q(2)]
      by (auto simp: pair_automaton_reg_def \<L>_def)
  } moreover
  { fix s assume "s \<in> \<L> (pair_automaton_reg A B)"
    from this[unfolded gta_lang_def \<L>_def]
    obtain r where r: "r |\<in>| fin (pair_automaton_reg A B)" "r |\<in>| gta_der ?AB s"
      by (auto simp: pair_automaton_reg_def)
    obtain p q where pq: "r = (Some p, Some q)" "p |\<in>| fin A" "q |\<in>| fin B"
      using r(1) by (auto simp: pair_automaton_reg_def)
    from from_ta_der_pair_automaton(4)[OF r(2)[unfolded pq(1) gta_der_def]]
    obtain t u where "p |\<in>| ta_der (ta A) (term_of_gterm t)" "q |\<in>| ta_der (ta B) (term_of_gterm u)" "s = gpair t u"
      by (elim exE conjE) note * = this
    then have "t \<in> \<L> A" "u \<in> \<L> B" using pq(2,3)
      by (auto simp: \<L>_def)
    then have "\<exists>t u. s = gpair t u \<and> t \<in> T \<and> u \<in> U" using assms
      by (auto simp: RR1_spec_def *(3) intro!: exI[of _ t, OF exI[of _ u]])
  } ultimately show ?thesis by (auto simp: RR2_spec_def)
qed

lemma pair_automaton':
  shows "\<L> (pair_automaton_reg A B) = case_prod gpair ` (\<L> A \<times> \<L> B)"
  using pair_automaton[of A _ B] by (auto simp: RR1_spec_def RR2_spec_def)


subsection \<open>Collapsing\<close>

text \<open>cf. @{const "gcollapse"}.\<close>

fun collapse_state_list where
  "collapse_state_list Qn Qs [] = [[]]"
| "collapse_state_list Qn Qs (q # qs) = (let rec = collapse_state_list Qn Qs qs in
    (if q |\<in>| Qn \<and> q |\<in>| Qs then map (Cons None) rec @ map (Cons (Some q)) rec
     else if q |\<in>| Qn then map (Cons None) rec
     else if q |\<in>| Qs then map (Cons (Some q)) rec
     else [[]]))"

lemma collapse_state_list_inner_length:
  assumes "qss = collapse_state_list Qn Qs qs"
    and "\<forall> i < length qs. qs ! i |\<in>| Qn \<or> qs ! i |\<in>| Qs"
    and "i < length qss"
  shows "length (qss ! i) = length qs" using assms
proof (induct qs arbitrary: qss i)
  case (Cons q qs)
  have "\<forall>i<length qs. qs ! i |\<in>| Qn \<or> qs ! i |\<in>| Qs" using Cons(3) by auto
  then show ?case using Cons(1)[of "collapse_state_list Qn Qs qs"] Cons(2-)
    by (auto simp: Let_def nth_append)
qed auto

lemma collapse_fset_inv_constr:
  assumes "\<forall> i < length qs'. qs ! i |\<in>| Qn \<and> qs' ! i = None \<or>
    qs ! i |\<in>| Qs \<and> qs' ! i = Some (qs ! i)"
    and "length qs = length qs'"
  shows "qs' |\<in>| fset_of_list (collapse_state_list Qn Qs qs)" using assms
proof (induct qs arbitrary: qs')
  case (Cons q qs)
  have "(tl qs') |\<in>| fset_of_list (collapse_state_list Qn Qs qs)" using Cons(2-)
    by (intro Cons(1)[of "tl qs'"]) (cases qs', auto)
  then show ?case using Cons(2-)
    by (cases qs') (auto simp: Let_def image_def)
qed auto

lemma collapse_fset_inv_constr2:
  assumes "\<forall> i < length qs. qs ! i |\<in>| Qn \<or> qs ! i |\<in>| Qs"
    and "qs' |\<in>| fset_of_list (collapse_state_list Qn Qs qs)" and "i < length qs'"
  shows "qs ! i |\<in>| Qn \<and> qs' ! i = None \<or> qs ! i |\<in>| Qs \<and> qs' ! i = Some (qs ! i)"
  using assms
proof (induct qs arbitrary: qs' i)
  case (Cons a qs)
  have "i \<noteq> 0 \<Longrightarrow> qs ! (i - 1) |\<in>| Qn \<and> tl qs' ! (i - 1) = None \<or> qs ! (i - 1) |\<in>| Qs \<and> tl qs' ! (i - 1) = Some (qs ! (i - 1))"
    using Cons(2-)
    by (intro Cons(1)[of "tl qs'" "i - 1"]) (auto simp: Let_def split: if_splits)
  then show ?case using Cons(2-)
    by (cases i) (auto simp: Let_def split: if_splits)
qed auto

definition collapse_rule where
  "collapse_rule A Qn Qs =
    |\<Union>| ((\<lambda> r. fset_of_list (map (\<lambda> qs. TA_rule (r_root r) qs (Some (r_rhs r))) (collapse_state_list Qn Qs (r_lhs_states r)))) |`|
    ffilter (\<lambda> r. (\<forall> i < length (r_lhs_states r). r_lhs_states r ! i |\<in>| Qn \<or> r_lhs_states r ! i |\<in>| Qs))
      (ffilter (\<lambda> r. r_root r \<noteq> None) (rules A)))"

definition collapse_rule_fset where
  "collapse_rule_fset A Qn Qs = (\<lambda> r. TA_rule (the (r_root r)) (map the (filter (\<lambda>q. \<not> Option.is_none q) (r_lhs_states r))) (the (r_rhs r))) |`|
     collapse_rule A Qn Qs"

lemma collapse_rule_set_conv:
  "fset (collapse_rule_fset A Qn Qs) = {TA_rule f (map the (filter (\<lambda>q. \<not> Option.is_none q) qs')) q | f qs qs' q.
      TA_rule (Some f) qs q |\<in>| rules A \<and> length qs = length qs' \<and>
      (\<forall>i < length qs. qs ! i |\<in>| Qn \<and> qs' ! i = None \<or> qs ! i |\<in>| Qs \<and> (qs' ! i) = Some (qs ! i))} " (is "?Ls = ?Rs")
proof
  {fix f qs' q qs assume ass: "TA_rule (Some f) qs q |\<in>| rules A"
    "length qs = length qs'"
    "\<forall>i < length qs. qs ! i |\<in>| Qn \<and> qs' ! i = None \<or> qs ! i |\<in>| Qs \<and> (qs' ! i) = Some (qs ! i)"
    then have "TA_rule (Some f) qs' (Some q) |\<in>| collapse_rule A Qn Qs"
      using collapse_fset_inv_constr[of qs' qs Qn Qs] unfolding collapse_rule_def
      by (auto simp: fset_of_list.rep_eq fimage_iff intro!: bexI[of _ "TA_rule (Some f) qs q"])
    then have "TA_rule f (map the (filter (\<lambda>q. \<not> Option.is_none q) qs')) q \<in> ?Ls"
      unfolding collapse_rule_fset_def
      by (auto simp: image_iff Bex_def intro!: exI[of _"TA_rule (Some f) qs' (Some q)"])}
  then show "?Rs \<subseteq> ?Ls" by blast
next
  {fix f qs q assume ass: "TA_rule f qs q \<in> ?Ls"
    then obtain ps qs' where w: "TA_rule (Some f) ps q |\<in>| rules A"
      "\<forall> i < length ps. ps ! i |\<in>| Qn \<or> ps ! i |\<in>| Qs" 
      "qs' |\<in>| fset_of_list (collapse_state_list Qn Qs ps)"
      "qs = map the (filter (\<lambda>q. \<not> Option.is_none q) qs')"
      unfolding collapse_rule_fset_def collapse_rule_def
        by (auto simp: ffUnion.rep_eq fset_of_list.rep_eq) (metis ta_rule.collapse)
    then have "\<forall> i < length qs'. ps ! i |\<in>| Qn \<and> qs' ! i = None \<or> ps ! i |\<in>| Qs \<and> qs' ! i = Some (ps ! i)"
      using collapse_fset_inv_constr2
      by metis
    moreover have "length ps = length qs'"
      using collapse_state_list_inner_length[of _ Qn Qs ps]
      using w(2, 3) calculation(1)
      by (auto simp: in_fset_conv_nth)
    ultimately have "TA_rule f qs q \<in> ?Rs"
      using w(1) unfolding w(4)
      by auto fastforce}
  then show "?Ls \<subseteq> ?Rs" 
    by (intro subsetI) (metis (no_types, lifting) ta_rule.collapse) 
qed


lemma collapse_rule_fmember [simp]:
  "TA_rule f qs q |\<in>| (collapse_rule_fset A Qn Qs) \<longleftrightarrow> (\<exists> qs' ps.
   qs = map the (filter (\<lambda>q. \<not> Option.is_none q) qs') \<and> TA_rule (Some f) ps q |\<in>| rules A \<and> length ps = length qs' \<and>
  (\<forall>i < length ps. ps ! i |\<in>| Qn \<and> qs' ! i = None \<or> ps ! i |\<in>| Qs \<and> (qs' ! i) = Some (ps ! i)))"
  unfolding collapse_rule_set_conv
  by auto

definition "Qn A \<equiv> (let S = (r_rhs |`| ffilter (\<lambda> r. r_root r = None) (rules A)) in (eps A)|\<^sup>+| |``| S |\<union>| S)"
definition "Qs A \<equiv> (let S = (r_rhs |`| ffilter (\<lambda> r. r_root r \<noteq> None) (rules A)) in (eps A)|\<^sup>+| |``| S |\<union>| S)"

lemma Qn_member_iff [simp]:
  "q |\<in>| Qn A \<longleftrightarrow> (\<exists> ps p. TA_rule None ps p |\<in>| rules A \<and> (p = q \<or> (p, q) |\<in>| (eps A)|\<^sup>+|))" (is "?Ls \<longleftrightarrow> ?Rs")
proof -
  {assume ass: "q |\<in>| Qn A" then obtain r where
      "r_rhs r = q \<or> (r_rhs r, q) |\<in>| (eps A)|\<^sup>+|" "r |\<in>| rules A" "r_root r = None"
      by (force simp: Qn_def Image_def image_def Let_def fImage.rep_eq)
    then have "?Ls \<Longrightarrow> ?Rs"  by (cases r) auto}
  moreover have "?Rs \<Longrightarrow> ?Ls" by (force simp: Qn_def Image_def image_def Let_def fImage.rep_eq)
  ultimately show ?thesis by blast
qed

lemma Qs_member_iff [simp]:
  "q |\<in>| Qs A \<longleftrightarrow> (\<exists> f ps p. TA_rule (Some f) ps p |\<in>| rules A \<and> (p = q \<or> (p, q) |\<in>| (eps A)|\<^sup>+|))"  (is "?Ls \<longleftrightarrow> ?Rs")
proof -
  {assume ass: "q |\<in>| Qs A" then obtain f r where
      "r_rhs r = q \<or> (r_rhs r, q) |\<in>| (eps A)|\<^sup>+|" "r |\<in>| rules A" "r_root r = Some f"
      by (force simp: Qs_def Image_def image_def Let_def fImage.rep_eq)
    then have "?Ls \<Longrightarrow> ?Rs"  by (cases r) auto}
  moreover have "?Rs \<Longrightarrow> ?Ls" by (force simp: Qs_def Image_def image_def Let_def fImage.rep_eq)
  ultimately show ?thesis by blast
qed


lemma collapse_Qn_Qs_set_conv:
  "fset (Qn A) = {q' |qs q q'. TA_rule None qs q |\<in>| rules A \<and> (q = q' \<or> (q, q') |\<in>| (eps A)|\<^sup>+|)}" (is "?Ls1 = ?Rs1")
  "fset (Qs A) = {q' |f qs q q'. TA_rule (Some f) qs q |\<in>| rules A \<and> (q = q' \<or> (q, q') |\<in>| (eps A)|\<^sup>+|)}"  (is "?Ls2 = ?Rs2")
  by auto force+

definition collapse_automaton :: "('q, 'f option) ta \<Rightarrow> ('q, 'f) ta" where
  "collapse_automaton A = TA (collapse_rule_fset A (Qn A) (Qs A)) (eps A)"

definition collapse_automaton_reg where
  "collapse_automaton_reg R = Reg (fin R) (collapse_automaton (ta R))"

lemma ta_states_collapse_automaton:
  "\<Q> (collapse_automaton A) |\<subseteq>| \<Q> A"
  apply (intro \<Q>_subseteq_I)
  apply (auto simp: collapse_automaton_def collapse_Qn_Qs_set_conv collapse_rule_set_conv
    fset_of_list.rep_eq in_set_conv_nth rule_statesD eps_statesD[unfolded])
  apply (metis Option.is_none_def fnth_mem option.sel rule_statesD(3) ta_rule.sel(2))
  done

lemma last_nthI:
  assumes "i < length ts" "\<not> i < length ts - Suc 0"
  shows "ts ! i = last ts" using assms
  by (induct ts arbitrary: i)
    (auto, metis last_conv_nth length_0_conv less_antisym nth_Cons')

lemma collapse_automaton':
  assumes "\<Q> A |\<subseteq>| ta_reachable A" (* cf. ta_trim *)
  shows "gta_lang Q (collapse_automaton A) = the ` (gcollapse ` gta_lang Q A - {None})"
proof -
  define Qn' where "Qn' = Qn A"
  define Qs' where "Qs' = Qs A"
  {fix t assume t: "t \<in> gta_lang Q (collapse_automaton A)"
    then obtain q where q: "q |\<in>| Q" "q |\<in>| ta_der (collapse_automaton A) (term_of_gterm t)" by auto
    have "\<exists> t'. q |\<in>| ta_der A (term_of_gterm t') \<and> gcollapse t' \<noteq> None \<and> t = the (gcollapse t')" using q(2)
    proof (induct rule: ta_der_gterm_induct)
      case (GFun f ts ps p q)
      from GFun(1 - 3) obtain qs rs where ps: "TA_rule (Some f) qs p |\<in>| rules A" "length qs = length rs"
        "\<And>i. i < length qs \<Longrightarrow> qs ! i |\<in>| Qn' \<and> rs ! i = None \<or> qs ! i |\<in>| Qs' \<and> rs ! i = Some (qs ! i)"
        "ps = map the (filter (\<lambda>q. \<not> Option.is_none q) rs)"
        by (auto simp: collapse_automaton_def Qn'_def Qs'_def)
      obtain ts' where ts':
        "ps ! i |\<in>| ta_der A (term_of_gterm (ts' i))" "gcollapse (ts' i) \<noteq> None" "ts ! i = the (gcollapse (ts' i))"
        if "i < length ts" for i using GFun(5) by metis
      from ps(2, 3, 4) have rs: "i < length qs \<Longrightarrow> rs ! i = None \<or> rs ! i = Some (qs ! i)" for i
        by auto
      {fix i assume "i < length qs" "rs ! i = None"
        then have "\<exists> t'. groot_sym t' = None \<and> qs ! i |\<in>| ta_der A (term_of_gterm t')"
          using ps(1, 2) ps(3)[of i]
          by (auto simp: ta_der_trancl_eps Qn'_def groot_sym_groot_conv elim!: ta_reachable_rule_gtermE[OF assms])
             (force dest: ta_der_trancl_eps)+}
      note None = this
      {fix i assume i: "i < length qs" "rs ! i = Some (qs ! i)"
        have "map Some ps = filter (\<lambda>q. \<not> Option.is_none q) rs" using ps(4)
          by (induct rs arbitrary: ps) (auto simp add: Option.is_none_def)
        from filter_rev_nth_idx[OF _ _ this, of i]
        have *: "rs ! i = map Some ps ! filter_rev_nth (\<lambda>q. \<not> Option.is_none q) rs i"
          "filter_rev_nth (\<lambda>q. \<not> Option.is_none q) rs i < length ps"
          using ps(2, 4) i by auto
        then have "the (rs ! i) = ps ! filter_rev_nth (\<lambda>q. \<not> Option.is_none q) rs i"
          "filter_rev_nth (\<lambda>q. \<not> Option.is_none q) rs i < length ps"
          by auto} note Some = this
      let ?P = "\<lambda> t i. qs ! i |\<in>| ta_der A (term_of_gterm t) \<and>
          (rs ! i = None \<longrightarrow> groot_sym t = None) \<and>
          (rs ! i = Some (qs ! i) \<longrightarrow> t = ts' (filter_rev_nth (\<lambda>q. \<not> Option.is_none q) rs i))"
      {fix i assume i: "i < length qs"
        then have "\<exists> t. ?P t i" using Some[OF i] None[OF i] ts' ps(2, 4) GFun(2) rs[OF i]
          by (cases "rs ! i") auto}
      then obtain ts'' where ts'': "length ts'' = length qs"
        "i < length qs \<Longrightarrow> qs ! i |\<in>| ta_der A (term_of_gterm (ts'' ! i))"
        "i < length qs \<Longrightarrow> rs ! i = None \<Longrightarrow> groot_sym (ts'' ! i) = None"
        "i < length qs \<Longrightarrow> rs ! i = Some (qs ! i) \<Longrightarrow> ts'' ! i = ts' (filter_rev_nth (\<lambda>q. \<not> Option.is_none q) rs i)"
      for i using that Ex_list_of_length_P[of "length qs" ?P] by auto
      from  ts''(1, 3, 4) Some ps(2, 4) GFun(2) rs ts'(2-)
      have "map Some ts = (filter (\<lambda>q. \<not> Option.is_none q) (map gcollapse ts''))"
      proof (induct ts'' arbitrary: qs rs ps ts rule: rev_induct)
        case (snoc a us)
        from snoc(2, 7) obtain r rs' where [simp]: "rs = rs' @ [r]"
          by (metis append_butlast_last_id append_is_Nil_conv length_0_conv not_Cons_self2)
        have l: "length us = length (butlast qs)" "length (butlast qs) = length (butlast rs)"
          using snoc(2, 7) by auto
        have *: "i < length (butlast qs) \<Longrightarrow> butlast rs ! i = None \<Longrightarrow> groot_sym (us ! i) = None" for i
          using snoc(3)[of i] snoc(2, 7)
          by (auto simp:nth_append l(1) nth_butlast split!: if_splits)
        have **: "i < length (butlast qs) \<Longrightarrow> butlast rs ! i = None \<or> butlast rs ! i = Some (butlast qs ! i)" for i
          using snoc(10)[of i] snoc(2, 7) l by (auto simp: nth_append nth_butlast)
        have "i < length (butlast qs) \<Longrightarrow> butlast rs ! i = Some (butlast qs ! i) \<Longrightarrow>
           us ! i = ts' (filter_rev_nth (\<lambda>q. \<not> Option.is_none q) (butlast rs) i)" for i
          using snoc(4)[of i] snoc(2, 7) l
          by (auto simp: nth_append nth_butlast filter_rev_nth_def take_butlast)
        note IH = snoc(1)[OF l(1) * this _ _ l(2) _ _ **]
        show ?case
        proof (cases "r = None")
          case True
          then have "map Some ts = filter (\<lambda>q. \<not> Option.is_none q) (map gcollapse us)"
            using snoc(2, 5-)
            by (intro IH[of ps ts]) (auto simp: nth_append nth_butlast filter_rev_nth_butlast)
          then show ?thesis using True snoc(2, 7) snoc(3)[of "length (butlast rs)"]
            by (auto simp: nth_append l(1) last_nthI split!: if_splits)
        next
          case False
          then obtain t' ss where *: "ts = ss @ [t']" using snoc(2, 7, 8, 9)
            by (cases ts) (auto, metis append_butlast_last_id list.distinct(1))
          let ?i = "filter_rev_nth (\<lambda>q. \<not> Option.is_none q) rs (length us)"
          have "map Some (butlast ts) = filter (\<lambda>q. \<not> Option.is_none q) (map gcollapse us)"
            using False snoc(2, 5-) l filter_rev_nth_idx
            by (intro IH[of "butlast ps" "butlast ts"])
               (fastforce simp: nth_butlast filter_rev_nth_butlast)+
          moreover have "a = ts' ?i" "?i < length ps"
            using False snoc(2, 9) l snoc(4, 6, 10)[of "length us"]
            by (auto simp: nth_append)
          moreover have "filter_rev_nth (\<lambda>q. \<not> Option.is_none q) (rs' @ [r]) (length rs') = length ss"
            using l snoc(2, 7, 8, 9) False unfolding *
            by (auto simp: filter_rev_nth_def)
          ultimately show ?thesis using l snoc(2, 7, 9) snoc(11-)[of ?i]
            by (auto simp: nth_append *)
        qed
      qed simp
      then have "ts = map the (filter (\<lambda>t. \<not> Option.is_none t) (map gcollapse ts''))"
        by (metis comp_the_Some list.map_id map_map)
      then show ?case using ps(1, 2) ts''(1, 2) GFun(3)
        by (auto simp: collapse_automaton_def intro!: exI[of _ "GFun (Some f) ts''"] exI[of _ qs] exI[of _ p])
    qed
    then have "t \<in> the ` (gcollapse ` gta_lang Q A - {None})"
      by (meson Diff_iff gta_langI imageI q(1) singletonD)
  } moreover
  { fix t assume t: "t \<in> gta_lang Q A" "gcollapse t \<noteq> None"
    obtain q where q: "q |\<in>| Q" "q |\<in>| ta_der A (term_of_gterm t)" using t(1) by auto
    have "q |\<in>| ta_der (collapse_automaton A) (term_of_gterm (the (gcollapse t)))" using q(2) t(2)
    proof (induct t arbitrary: q)
      case (GFun f ts)
      obtain qs q' where q: "TA_rule f qs q' |\<in>| rules A" "q' = q \<or> (q', q) |\<in>| (eps (collapse_automaton A))|\<^sup>+|"
        "length qs = length ts" "\<And>i. i < length ts \<Longrightarrow> qs ! i |\<in>| ta_der A (term_of_gterm (ts ! i))"
        using GFun(2) by (auto simp: collapse_automaton_def)
      obtain f' where f [simp]: "f = Some f'" using GFun(3) by (cases f) auto
      define qs' where
        "qs' = map (\<lambda>i. if Option.is_none (gcollapse (ts ! i)) then None else Some (qs ! i)) [0..<length qs]"
      have "Option.is_none (gcollapse (ts ! i)) \<Longrightarrow> qs ! i |\<in>| Qn'" if "i < length qs" for i
        using q(4)[of i] that
        by (cases "ts ! i" rule: gcollapse.cases)
           (auto simp: q(3) Qn'_def collapse_Qn_Qs_set_conv)
      moreover have "\<not> Option.is_none (gcollapse (ts ! i)) \<Longrightarrow> qs ! i |\<in>| Qs'" if "i < length qs" for i
        using q(4)[of i] that
        by (cases "ts ! i" rule: gcollapse.cases)
           (auto simp: q(3) Qs'_def collapse_Qn_Qs_set_conv)
      ultimately have "f' (map the (filter (\<lambda>q. \<not> Option.is_none q) qs')) \<rightarrow> q' |\<in>| rules (collapse_automaton A)"
        using q(1, 4) unfolding collapse_automaton_def Qn'_def[symmetric] Qs'_def[symmetric]
        by (fastforce simp: qs'_def q(3) intro: exI[of _ qs] exI[of _ qs'] split: if_splits)
      moreover have ***: "length (filter (\<lambda>i.\<not> Option.is_none (gcollapse (ts ! i))) [0..<length ts]) =
        length (filter (\<lambda>t. \<not> Option.is_none (gcollapse t)) ts)" for ts
        by (subst length_map[of "(!) ts", symmetric] filter_map[unfolded comp_def, symmetric] map_nth)+
          (rule refl)
      note this[of ts]
      moreover have "the (filter (\<lambda>q. \<not> Option.is_none q) qs' ! i) |\<in>| ta_der (collapse_automaton A)
        (term_of_gterm (the (filter (\<lambda>t. \<not> Option.is_none t) (map gcollapse ts) ! i)))"
        if "i < length [x\<leftarrow>ts . \<not> Option.is_none (gcollapse x)]" for i
        unfolding qs'_def using that q(3) GFun(1)[OF nth_mem q(4)]
      proof (induct ts arbitrary: qs rule: List.rev_induct)
        case (snoc t ts)
        have x1 [simp]: "i < length xs \<Longrightarrow> (xs @ ys) ! i = xs ! i" for xs ys i by (auto simp: nth_append)
        have x2: "i = length xs \<Longrightarrow> (xs @ ys) ! i = ys ! 0" for xs ys i by (auto simp: nth_append)
        obtain q qs' where qs [simp]: "qs = qs' @ [q]" using snoc(3) by (cases "rev qs") auto
        have [simp]:
          "map (\<lambda>x. if Option.is_none (gcollapse ((ts @ [t]) ! x)) then None else Some ((qs' @ [q]) ! x)) [0..<length ts] =
           map (\<lambda>x. if Option.is_none (gcollapse (ts ! x)) then None else Some (qs' ! x)) [0..<length ts]"
          using snoc(3) by auto
        show ?case
        proof (cases "Option.is_none (gcollapse t)")
          case True then show ?thesis using snoc(1)[of qs'] snoc(2,3)
            snoc(4)[unfolded length_append list.size add_0 add_0_right add_Suc_right, OF less_SucI]
            by (auto cong: if_cong)
        next
          case False note False' = this
          show ?thesis
          proof (cases "i = length [x\<leftarrow>ts . \<not> Option.is_none (gcollapse x)]")
            case True
            then show ?thesis using snoc(3) snoc(4)[of "length ts"]
              unfolding qs length_append list.size add_0 add_0_right add_Suc_right
                upt_Suc_append[OF zero_le] filter_append map_append
              by (subst (5 6) x2) (auto simp: comp_def *** False' Option.is_none_def[symmetric])
          next
            case False
            then show ?thesis using snoc(1)[of qs'] snoc(2,3)
              snoc(4)[unfolded length_append list.size add_0 add_0_right add_Suc_right, OF less_SucI]
              unfolding qs length_append list.size add_0 add_0_right add_Suc_right
                upt_Suc_append[OF zero_le] filter_append map_append
              by (subst (5 6) x1) (auto simp: comp_def *** False')
          qed
        qed
      qed auto
      ultimately show ?case using q(2) by (auto simp: qs'_def comp_def q(3)
        intro!: exI[of _ q'] exI[of _ "map the (filter (\<lambda>q. \<not> Option.is_none q) qs')"])
    qed
    then have "the (gcollapse t) \<in> gta_lang Q (collapse_automaton A)"
      by (metis q(1) gta_langI)
  } ultimately show ?thesis by blast
qed

lemma \<L>_collapse_automaton':
  assumes "\<Q>\<^sub>r A |\<subseteq>| ta_reachable (ta A)" (* cf. ta_trim *)
  shows "\<L> (collapse_automaton_reg A) = the ` (gcollapse ` \<L> A - {None})"
  using assms by (auto simp: collapse_automaton_reg_def \<L>_def collapse_automaton')

lemma collapse_automaton:
  assumes "\<Q>\<^sub>r A |\<subseteq>| ta_reachable (ta A)" "RR1_spec A T"
  shows "RR1_spec (collapse_automaton_reg A) (the ` (gcollapse ` \<L> A - {None}))"
  using collapse_automaton'[OF assms(1)] assms(2)
  by (simp add: collapse_automaton_reg_def \<L>_def RR1_spec_def)


subsection \<open>Cylindrification\<close>

(* cylindrification is a product ("pairing") of a RR1 language accepting all terms, and an RRn language,
modulo some fairly trivial renaming of symbols. *)

definition pad_with_Nones where
  "pad_with_Nones n m = (\<lambda>(f, g). case_option (replicate n None) id f @ case_option (replicate m None) id g)"

lemma gencode_append:
  "gencode (ss @ ts) = map_gterm (pad_with_Nones (length ss) (length ts)) (gpair (gencode ss) (gencode ts))"
proof -
  have [simp]: "p \<notin> gposs (gunions (map gdomain ts)) \<Longrightarrow> map (\<lambda>t. gfun_at t p) ts = replicate (length ts) None"
    for p ts by (intro nth_equalityI) 
        (fastforce simp: poss_gposs_mem_conv fun_at_def' image_def all_set_conv_all_nth)+
  note [simp] = glabel_map_gterm_conv[of "\<lambda>(_ :: unit option). ()", unfolded comp_def gdomain_id]
  show ?thesis by (auto intro!: arg_cong[of _ _ "\<lambda>x. glabel x _"] simp del: gposs_gunions
    simp: pad_with_Nones_def gencode_def gunions_append gpair_def map_gterm_glabel comp_def)
qed

lemma append_automaton:
  assumes "RRn_spec n A T" "RRn_spec m B U"
  shows "RRn_spec (n + m) (fmap_funs_reg (pad_with_Nones n m) (pair_automaton_reg A B)) {ts @ us |ts us. ts \<in> T \<and> us \<in> U}"
  using assms pair_automaton[of A "gencode ` T" B "gencode ` U"]
  unfolding RRn_spec_def
proof (intro conjI set_eqI iffI, goal_cases)
  case (1 s)
  then obtain ts us where "ts \<in> T" "us \<in> U" "s = gencode (ts @ us)"
    by (fastforce simp: \<L>_def fmap_funs_reg_def RR1_spec_def RR2_spec_def gencode_append fmap_funs_gta_lang)
  then show ?case by blast
qed (fastforce simp: RR1_spec_def RR2_spec_def fmap_funs_reg_def \<L>_def gencode_append fmap_funs_gta_lang)+

lemma cons_automaton:
  assumes "RR1_spec A T" "RRn_spec m B U"
  shows "RRn_spec (Suc m) (fmap_funs_reg (\<lambda>(f, g). pad_with_Nones 1 m (map_option (\<lambda>f. [Some f]) f, g))
   (pair_automaton_reg A B)) {t # us |t us. t \<in> T \<and> us \<in> U}"
proof -
  have [simp]: "{ts @ us |ts us. ts \<in> (\<lambda>t. [t]) ` T \<and> us \<in> U} = {t # us |t us. t \<in> T \<and> us \<in> U}"
    by (auto intro: exI[of _ "[_]", OF exI])
  show ?thesis using append_automaton[OF RR1_to_RRn_spec, OF assms]
    by (auto simp: \<L>_def fmap_funs_reg_def pair_automaton_reg_def comp_def
      fmap_funs_gta_lang map_pair_automaton_12 fmap_funs_ta_comp prod.case_distrib
      gencode_append[of "[_]", unfolded gencode_singleton List.append.simps])
qed

subsection \<open>Projection\<close>

(* projection is composed from fmap_funs_ta and collapse_automaton, corresponding to gsnd *)

abbreviation "drop_none_rule m fs \<equiv> if list_all (Option.is_none) (drop m fs) then None else Some (drop m fs)"

lemma drop_automaton_reg:
  assumes "\<Q>\<^sub>r A |\<subseteq>| ta_reachable (ta A)" "m < n" "RRn_spec n A T"
  defines "f \<equiv> \<lambda>fs. drop_none_rule m fs"
  shows "RRn_spec (n - m) (collapse_automaton_reg (fmap_funs_reg f A)) (drop m ` T)"
proof -
  have [simp]: "length ts = n - m ==> p \<in> gposs (gencode ts) \<Longrightarrow> \<exists>f. \<exists>t\<in>set ts. Some f = gfun_at t p" for p ts
  proof (cases p, goal_cases Empty PCons)
    case Empty
    obtain t where "t \<in> set ts" using assms(2) Empty(1) by (cases ts) auto
    moreover then obtain f where "Some f = gfun_at t p" using Empty(3) by (cases t rule: gterm.exhaust) auto
    ultimately show ?thesis by auto
  next
    case (PCons i p')
    then have "p \<noteq> []" by auto
    then show ?thesis using PCons(2)
      by (auto 0 3 simp: gencode_def eq_commute[of "gfun_at _ _" "Some _"] elim!: gfun_at_possE)
  qed
  { fix p ts y assume that: "gfun_at (gencode ts) p = Some y"
    have "p \<in> gposs (gencode ts) \<Longrightarrow> gfun_at (gencode ts) p = Some (map (\<lambda>t. gfun_at t p) ts)"
      by (auto simp: gencode_def)
    moreover have "gfun_at (gencode ts) p = Some y \<Longrightarrow> p \<in> gposs (gencode ts)"
      using gfun_at_nongposs by force
    ultimately have "y = map (\<lambda>t. gfun_at t p) ts \<and> p \<in> gposs (gencode ts)" by (simp add: that)
  } note [dest!] = this
  have [simp]: "list_all f (replicate n x) \<longleftrightarrow> n = 0 \<or> f x" for f n x by (induct n) auto
  have [dest]: "x \<in> set xs \<Longrightarrow> list_all f xs \<Longrightarrow> f x" for f x xs by (induct xs) auto
  have *: "f (pad_with_Nones m' n' z) = snd z"
    if  "fst z = None \<or> fst z \<noteq> None \<and> length (the (fst z)) = m"
      "snd z = None \<or> snd z \<noteq> None \<and> length (the (snd z)) = n - m \<and> (\<exists>y. Some y \<in> set (the (snd z)))"
      "m' = m" "n' = n - m" for z m' n'
    using that by (auto simp: f_def pad_with_Nones_def split: option.splits prod.splits)
  { fix ts assume ts: "ts \<in> T" "length ts = n"
    have "gencode (drop m ts) = the (gcollapse (map_gterm f (gencode ts)))"
      "gcollapse (map_gterm f (gencode ts)) \<noteq> None"
    proof (goal_cases)
      case 1 show ?case
        using ts assms(2)
        apply (subst gsnd_gpair[of "gencode (take m ts)", symmetric])
        apply (subst gencode_append[of "take m ts" "drop m ts", unfolded append_take_drop_id])
        unfolding gsnd_def comp_def gterm.map_comp
        apply (intro arg_cong[where f = "\<lambda>x. the (gcollapse x)"] gterm.map_cong refl)
        by (subst *) (auto simp: gpair_def set_gterm_gposs_conv image_def)
    next
      case 2
      have [simp]: "gcollapse t = None \<longleftrightarrow> gfun_at t [] = Some None" for t
        by (cases t rule: gcollapse.cases) auto
      obtain t where "t \<in> set (drop m ts)" using ts(2) assms(2) by (cases "drop m ts") auto
      moreover then have "\<not> Option.is_none (gfun_at t [])" by (cases t rule: gterm.exhaust) auto
      ultimately show ?case
        by (auto simp: f_def gencode_def list_all_def drop_map)
    qed
  }
  then show ?thesis using assms(3)
    by (fastforce simp: \<L>_def collapse_automaton_reg_def fmap_funs_reg_def
      RRn_spec_def fmap_funs_gta_lang gsnd_def gpair_def gterm.map_comp comp_def
      glabel_map_gterm_conv[unfolded comp_def] assms(1) collapse_automaton')
qed

lemma gfst_collapse_simp:
  "the (gcollapse (map_gterm fst t)) = gfst t"
  by (simp add: gfst_def)

lemma gsnd_collapse_simp:
  "the (gcollapse (map_gterm snd t)) = gsnd t"
  by (simp add: gsnd_def)

definition proj_1_reg where
  "proj_1_reg A = collapse_automaton_reg (fmap_funs_reg fst (trim_reg A))"
definition proj_2_reg where
  "proj_2_reg A = collapse_automaton_reg (fmap_funs_reg snd (trim_reg A))"

lemmas proj_1_reg_simp = proj_1_reg_def collapse_automaton_reg_def fmap_funs_reg_def trim_reg_def
lemmas proj_2_reg_simp = proj_2_reg_def collapse_automaton_reg_def fmap_funs_reg_def trim_reg_def

lemma \<L>_proj_1_reg_collapse:
  "\<L> (proj_1_reg \<A>) = the ` (gcollapse ` map_gterm fst ` (\<L> \<A>) - {None})"
proof -
  have "\<Q>\<^sub>r (fmap_funs_reg fst (trim_reg \<A>)) |\<subseteq>| ta_reachable (ta (fmap_funs_reg fst (trim_reg \<A>)))"
    by (auto simp: fmap_funs_reg_def)
  note [simp] = \<L>_collapse_automaton'[OF this]
  show ?thesis by (auto simp: proj_1_reg_def fmap_funs_\<L> \<L>_trim)
qed

lemma \<L>_proj_2_reg_collapse:
  "\<L> (proj_2_reg \<A>) = the ` (gcollapse ` map_gterm snd ` (\<L> \<A>) - {None})"
proof -
  have "\<Q>\<^sub>r (fmap_funs_reg snd (trim_reg \<A>)) |\<subseteq>| ta_reachable (ta (fmap_funs_reg snd (trim_reg \<A>)))"
    by (auto simp: fmap_funs_reg_def)
  note [simp] = \<L>_collapse_automaton'[OF this]
  show ?thesis by (auto simp: proj_2_reg_def fmap_funs_\<L> \<L>_trim)
qed

lemma proj_1:
  assumes "RR2_spec A R"
  shows "RR1_spec (proj_1_reg A) (fst ` R)"
proof -
  {fix s t assume ass: "(s, t) \<in> R"
    from ass have s: "s = the (gcollapse (map_gterm fst (gpair s t)))"
      by (auto simp: gfst_gpair gfst_collapse_simp)
    then have "Some s = gcollapse (map_gterm fst (gpair s t))"
      by (cases s; cases t) (auto simp: gpair_def)
    then have "s \<in> \<L> (proj_1_reg A)" using assms ass s
      by (auto simp: proj_1_reg_simp \<L>_def trim_ta_reach trim_gta_lang
        image_def image_Collect RR2_spec_def fmap_funs_gta_lang
        collapse_automaton'[of "fmap_funs_ta fst (trim_ta (fin A) (ta A))"])
         force}
  moreover
  {fix s assume "s \<in> \<L> (proj_1_reg A)" then have "s \<in> fst ` R" using assms
      by (auto simp: gfst_collapse_simp gfst_gpair rev_image_eqI RR2_spec_def trim_ta_reach trim_gta_lang
        \<L>_def proj_1_reg_simp fmap_funs_gta_lang collapse_automaton'[of "fmap_funs_ta fst (trim_ta (fin A) (ta A))"])}
  ultimately show ?thesis using assms unfolding RR2_spec_def RR1_spec_def \<L>_def proj_1_reg_simp
    by auto
qed

lemma proj_2:
  assumes "RR2_spec A R"
  shows "RR1_spec (proj_2_reg A) (snd ` R)"
proof -
  {fix s t assume ass: "(s, t) \<in> R"
    then have s: "t = the (gcollapse (map_gterm snd (gpair s t)))"
      by (auto simp: gsnd_gpair gsnd_collapse_simp)
    then have "Some t = gcollapse (map_gterm snd (gpair s t))"
      by (cases s; cases t) (auto simp: gpair_def)
    then have "t \<in> \<L> (proj_2_reg A)" using assms ass s
      by (auto simp: \<L>_def trim_ta_reach trim_gta_lang proj_2_reg_simp
        image_def image_Collect RR2_spec_def fmap_funs_gta_lang
        collapse_automaton'[of "fmap_funs_ta snd (trim_ta (fin A) (ta A))"])
        fastforce}
  moreover
  {fix s assume "s \<in> \<L> (proj_2_reg A)" then have "s \<in> snd ` R" using assms
      by (auto simp: \<L>_def gsnd_collapse_simp gsnd_gpair rev_image_eqI RR2_spec_def
        trim_ta_reach trim_gta_lang proj_2_reg_simp
        fmap_funs_gta_lang collapse_automaton'[of "fmap_funs_ta snd (trim_ta (fin A) (ta A))"])}
  ultimately show ?thesis using assms unfolding RR2_spec_def RR1_spec_def
    by auto
qed

lemma \<L>_proj:
  assumes "RR2_spec A R"
  shows "\<L> (proj_1_reg A) = gfst ` \<L> A" "\<L> (proj_2_reg A) = gsnd ` \<L> A"
proof -
  have [simp]: "gfst ` {gpair t u |t u. (t, u) \<in> R} = fst ` R"
    by (force simp: gfst_gpair image_def)
  have [simp]: "gsnd ` {gpair t u |t u. (t, u) \<in> R} = snd ` R"
    by (force simp: gsnd_gpair image_def)
  show "\<L> (proj_1_reg A) = gfst ` \<L> A" "\<L> (proj_2_reg A) = gsnd ` \<L> A"
    using proj_1[OF assms] proj_2[OF assms] assms gfst_gpair gsnd_gpair
    by (auto simp: RR1_spec_def RR2_spec_def)
qed

lemmas proj_automaton_gta_lang = proj_1 proj_2

subsection \<open>Permutation\<close>

(* permutations are a direct application of fmap_funs_ta *)

lemma gencode_permute:
  assumes "set ps = {0..<length ts}"
  shows "gencode (map ((!) ts) ps) = map_gterm (\<lambda>xs. map ((!) xs) ps) (gencode ts)"
proof -
  have *: "(!) ts ` set ps = set ts" using assms by (auto simp: image_def set_conv_nth)
  show ?thesis using subsetD[OF equalityD1[OF assms]]
    apply (intro eq_gterm_by_gposs_gfun_at)
    unfolding gencode_def gposs_glabel gposs_map_gterm gposs_gunions gfun_at_map_gterm gfun_at_glabel
      set_map * by auto
qed

lemma permute_automaton:
  assumes "RRn_spec n A T" "set ps = {0..<n}"
  shows "RRn_spec (length ps) (fmap_funs_reg (\<lambda>xs. map ((!) xs) ps) A) ((\<lambda>xs. map ((!) xs) ps) ` T)"
  using assms by (auto simp: RRn_spec_def gencode_permute fmap_funs_reg_def \<L>_def fmap_funs_gta_lang image_def)


subsection \<open>Intersection\<close>

(* intersection is already defined in IsaFoR *)

lemma intersect_automaton:
  assumes "RRn_spec n A T" "RRn_spec n B U"
  shows "RRn_spec n (reg_intersect A B) (T \<inter> U)" using assms
  by (simp add: RRn_spec_def \<L>_intersect)
     (metis gdecode_gencode image_Int inj_on_def)

(*
lemma swap_union_automaton:
  "fmap_states_ta (case_sum Inr Inl) (union_automaton B A) = union_automaton A B"
  by (simp add: fmap_states_ta_def' union_automaton_def image_Un image_comp case_sum_o_inj
    ta_rule.map_comp prod.map_comp comp_def id_def ac_simps)
*)

lemma union_automaton:
  assumes "RRn_spec n A T" "RRn_spec n B U"
  shows "RRn_spec n (reg_union A B) (T \<union> U)"
  using assms by (auto simp: RRn_spec_def \<L>_union)

subsection \<open>Difference\<close>

lemma RR1_difference:
  assumes "RR1_spec A T" "RR1_spec B U"
  shows "RR1_spec (difference_reg A B) (T - U)"
  using assms by (auto simp: RR1_spec_def \<L>_difference_reg)

lemma RR2_difference:
  assumes "RR2_spec A T" "RR2_spec B U"
  shows "RR2_spec (difference_reg A B) (T - U)"
  using assms by (auto simp: RR2_spec_def \<L>_difference_reg)

lemma RRn_difference:
  assumes "RRn_spec n A T" "RRn_spec n B U"
  shows "RRn_spec n (difference_reg A B) (T - U)"
  using assms by (auto simp: RRn_spec_def \<L>_difference_reg) (metis gdecode_gencode)+

subsection \<open>All terms over a signature\<close>

definition term_automaton :: "('f \<times> nat) fset \<Rightarrow> (unit, 'f) ta" where
  "term_automaton \<F> = TA ((\<lambda> (f, n). TA_rule f (replicate n ()) ()) |`| \<F>) {||}"
definition term_reg where
  "term_reg \<F> = Reg {|()|} (term_automaton \<F>)"

lemma term_automaton:
  "RR1_spec (term_reg \<F>) (\<T>\<^sub>G (fset \<F>))"
  unfolding RR1_spec_def gta_lang_def term_reg_def \<L>_def
proof (intro set_eqI iffI, goal_cases lr rl)
  case (lr t)
  then have "() |\<in>| ta_der (term_automaton \<F>) (term_of_gterm t)"
    by (auto simp: gta_der_def)
  then show ?case
    by (induct t) (auto simp: term_automaton_def split: if_splits)
next
  case (rl t)
  then have "() |\<in>| ta_der (term_automaton \<F>) (term_of_gterm t)"
  proof (induct t rule: \<T>\<^sub>G.induct)
    case (const a) then show ?case
      by (auto simp: term_automaton_def image_iff intro: bexI[of _ "(a, 0)"])
  next
    case (ind f n ss) then show ?case
      by (auto simp: term_automaton_def image_iff intro: bexI[of _ "(f, n)"])
  qed
  then show ?case
    by (auto simp: gta_der_def)
qed

fun true_RRn :: "('f \<times> nat) fset \<Rightarrow> nat \<Rightarrow> (nat, 'f option list) reg" where
  "true_RRn \<F> 0 = Reg {|0|} (TA {|TA_rule [] [] 0|} {||})"
| "true_RRn \<F> (Suc 0) = relabel_reg (fmap_funs_reg (\<lambda>f. [Some f]) (term_reg \<F>))"
| "true_RRn \<F> (Suc n) = relabel_reg
  (trim_reg (fmap_funs_reg (pad_with_Nones 1 n) (pair_automaton_reg (true_RRn \<F> 1) (true_RRn \<F> n))))"

lemma true_RRn_spec:
  "RRn_spec n (true_RRn \<F> n) {ts. length ts = n \<and> set ts \<subseteq> \<T>\<^sub>G (fset \<F>)}"
proof (induct \<F> n rule: true_RRn.induct)
  case (1 \<F>) show ?case
    by (simp cong: conj_cong add: true_RR0_spec)
next
  case (2 \<F>)
  moreover have "{ts. length ts = 1 \<and> set ts \<subseteq> \<T>\<^sub>G (fset \<F>)} = (\<lambda>t. [t]) ` \<T>\<^sub>G (fset \<F>)"
    apply (intro equalityI subsetI)
    subgoal for ts by (cases ts) auto
    by auto
  ultimately show ?case
    using RR1_to_RRn_spec[OF term_automaton, of \<F>] by auto
next
  case (3 \<F> n)
  have [simp]: "{ts @ us |ts us. length ts = n \<and> set ts \<subseteq> \<T>\<^sub>G (fset \<F>) \<and> length us = m \<and>
    set us \<subseteq> \<T>\<^sub>G (fset \<F>)} = {ss. length ss = n + m \<and> set ss \<subseteq> \<T>\<^sub>G (fset \<F>)}" for n m
    by (auto 0 4 intro!: exI[of _ "take n _", OF exI[of _ "drop n _"], of _ xs xs for xs]
      dest!: subsetD[OF set_take_subset] subsetD[OF set_drop_subset])
  show ?case using append_automaton[OF 3]
    by simp
qed


subsection \<open>RR2 composition\<close>

abbreviation "RR2_to_RRn A \<equiv> fmap_funs_reg (\<lambda>(f, g). [f, g]) A"
abbreviation "RRn_to_RR2 A \<equiv> fmap_funs_reg (\<lambda>f. (f ! 0, f ! 1)) A"
definition rr2_compositon where
  "rr2_compositon \<F> A B =
   (let A' = RR2_to_RRn A in
    let B' = RR2_to_RRn B in
    let F = true_RRn \<F> 1 in
    let CA = trim_reg (fmap_funs_reg (pad_with_Nones 2 1) (pair_automaton_reg A' F)) in
    let CB = trim_reg (fmap_funs_reg (pad_with_Nones 1 2) (pair_automaton_reg F B')) in
    let PI = trim_reg (fmap_funs_reg (\<lambda>xs. map ((!) xs) [1, 0, 2]) (reg_intersect CA CB)) in
    RRn_to_RR2 (collapse_automaton_reg (fmap_funs_reg (drop_none_rule 1) PI))
   )"

lemma list_length1E:
  assumes "length xs = Suc 0" obtains x where "xs = [x]" using assms
  by (cases xs) auto

lemma rr2_compositon:
  assumes "\<R> \<subseteq> \<T>\<^sub>G (fset \<F>) \<times> \<T>\<^sub>G (fset \<F>)" "\<LL> \<subseteq> \<T>\<^sub>G (fset \<F>) \<times> \<T>\<^sub>G (fset \<F>)"
    and "RR2_spec A \<R>" and "RR2_spec B \<LL>"
  shows "RR2_spec (rr2_compositon \<F> A B) (\<R> O \<LL>)"
proof -
  let ?R = "(\<lambda>(t, u). [t, u]) ` \<R>" let ?L = "(\<lambda>(t, u). [t, u]) ` \<LL>"
  let ?A = "RR2_to_RRn A" let ?B = "RR2_to_RRn B" let ?F = "true_RRn \<F> 1"
  let ?CA = "trim_reg (fmap_funs_reg (pad_with_Nones 2 1) (pair_automaton_reg ?A ?F))"
  let ?CB = "trim_reg (fmap_funs_reg (pad_with_Nones 1 2) (pair_automaton_reg ?F ?B))"
  let ?PI = "trim_reg (fmap_funs_reg (\<lambda>xs. map ((!) xs) [1, 0, 2]) (reg_intersect ?CA ?CB))"
  let ?DR = "collapse_automaton_reg (fmap_funs_reg (drop_none_rule 1) ?PI)"
  let ?Rs = "{ts @ us | ts us. ts \<in> ?R \<and> (\<exists>t. us = [t] \<and> t \<in> \<T>\<^sub>G (fset \<F>))}"
  let ?Ls = "{us @ ts | ts us. ts \<in> ?L \<and> (\<exists>t. us = [t] \<and> t \<in> \<T>\<^sub>G (fset \<F>))}"
  from RR2_to_RRn_spec assms(3, 4)
  have rr2: "RRn_spec 2 ?A ?R" "RRn_spec 2 ?B ?L" by auto
  have *: "{ts. length ts = 1 \<and> set ts \<subseteq> \<T>\<^sub>G (fset \<F>)} = {[t] | t. t \<in> \<T>\<^sub>G (fset \<F>)}"
    by (auto elim!: list_length1E)
  have F: "RRn_spec 1 ?F {[t] | t. t \<in> \<T>\<^sub>G (fset \<F>)}" using true_RRn_spec[of 1 \<F>] unfolding * .
  have "RRn_spec 3 ?CA ?Rs" "RRn_spec 3 ?CB ?Ls"
    using append_automaton[OF rr2(1) F] append_automaton[OF F rr2(2)]
    by (auto simp: numeral_3_eq_3) (smt Collect_cong)
  from permute_automaton[OF intersect_automaton[OF this], of "[1, 0, 2]"]
  have "RRn_spec 3 ?PI ((\<lambda>xs. map ((!) xs) [1, 0, 2]) ` (?Rs \<inter> ?Ls))"
    by (auto simp: atLeast0_lessThan_Suc insert_commute numeral_2_eq_2 numeral_3_eq_3)
  from drop_automaton_reg[OF _ _ this, of 1]
  have sp: "RRn_spec 2 ?DR (drop 1 ` (\<lambda>xs. map ((!) xs) [1, 0, 2]) ` (?Rs \<inter> ?Ls))"
    by auto
  {fix s assume "s \<in> (\<lambda>(t, u). [t, u]) ` (\<R> O \<LL>)"
    then obtain t u v where comp: "s = [t, u]" "(t, v) \<in> \<R>" "(v, u) \<in> \<LL>"
      by (auto simp: image_iff relcomp_unfold split!: prod.split)
    then have "[t, v] \<in> ?R" "[v , u] \<in> ?L" "u \<in> \<T>\<^sub>G (fset \<F>)" "v \<in> \<T>\<^sub>G (fset \<F>)" "t \<in> \<T>\<^sub>G (fset \<F>)" using assms(1, 2)
      by (auto simp: image_iff relcomp_unfold split!: prod.splits)
    then have "[t, v, u] \<in> ?Rs" "[t, v, u] \<in> ?Ls"
      apply (simp_all)
      subgoal
        apply (rule exI[of _ "[t, v]"], rule exI[of _ "[u]"])
        apply simp
        done
      subgoal
        apply (rule exI[of _ "[v, u]"], rule exI[of _ "[t]"])
        apply simp
        done
      done
    then have "s \<in> drop 1 ` (\<lambda>xs. map ((!) xs) [1, 0, 2]) ` (?Rs \<inter> ?Ls)" unfolding comp(1)
      apply (simp add: image_def Bex_def)
      apply (rule exI[of _ "[v, t, u]"]) apply simp
      apply (rule exI[of _ "[t, v, u]"]) apply simp
      done}
  moreover have "drop 1 ` (\<lambda>xs. map ((!) xs) [1, 0, 2]) ` (?Rs \<inter> ?Ls) \<subseteq> (\<lambda>(t, u). [t, u]) ` (\<R> O \<LL>)"
    by (auto simp: image_iff relcomp_unfold Bex_def split!: prod.splits)
  ultimately have *: "drop 1 ` (\<lambda>xs. map ((!) xs) [1, 0, 2]) ` (?Rs \<inter> ?Ls) = (\<lambda>(t, u). [t, u]) ` (\<R> O \<LL>)"
    by (simp add: subsetI subset_antisym)
  have **: "(\<lambda>f. (f ! 0, f ! 1)) ` (\<lambda>(t, u). [t, u]) ` (\<R> O \<LL>) = \<R> O \<LL>"
    by (force simp: image_def relcomp_unfold split!: prod.splits)
  show ?thesis using sp unfolding *
    using RRn_to_RR2_spec[where ?T = "(\<lambda>(t, u). [t, u]) ` (\<R> O \<LL>)" and ?A = ?DR]
    unfolding ** by (auto simp: rr2_compositon_def Let_def image_iff)
qed

end