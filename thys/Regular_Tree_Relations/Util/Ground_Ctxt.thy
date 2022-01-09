theory Ground_Ctxt
  imports Ground_Terms
begin

subsubsection \<open>Ground context\<close>

datatype (gfuns_ctxt: 'f) gctxt =
  GHole ("\<box>\<^sub>G") | GMore 'f "'f gterm list" "'f gctxt" "'f gterm list"
declare gctxt.map_comp[simp]

fun gctxt_apply_term :: "'f gctxt \<Rightarrow> 'f gterm \<Rightarrow> 'f gterm" ("_\<langle>_\<rangle>\<^sub>G" [1000, 0] 1000) where
  "\<box>\<^sub>G\<langle>s\<rangle>\<^sub>G = s" |
  "(GMore f ss1 C ss2)\<langle>s\<rangle>\<^sub>G = GFun f (ss1 @ C\<langle>s\<rangle>\<^sub>G # ss2)"

fun hole_gpos where
  "hole_gpos \<box>\<^sub>G = []" |
  "hole_gpos (GMore f ss1 C ss2) = length ss1 # hole_gpos C"

lemma gctxt_eq [simp]: "(C\<langle>s\<rangle>\<^sub>G = C\<langle>t\<rangle>\<^sub>G) = (s = t)"
  by (induct C) auto

fun gctxt_compose :: "'f gctxt \<Rightarrow> 'f gctxt \<Rightarrow> 'f gctxt" (infixl "\<circ>\<^sub>G\<^sub>c" 75) where
  "\<box>\<^sub>G \<circ>\<^sub>G\<^sub>c D = D" |
  "(GMore f ss1 C ss2) \<circ>\<^sub>G\<^sub>c D = GMore f ss1 (C \<circ>\<^sub>G\<^sub>c D) ss2"

fun gctxt_at_pos :: "'f gterm \<Rightarrow> pos \<Rightarrow> 'f gctxt" where
  "gctxt_at_pos t [] = \<box>\<^sub>G" |
  "gctxt_at_pos (GFun f ts) (i # ps) =
    GMore f (take i ts) (gctxt_at_pos (ts ! i) ps) (drop (Suc i) ts)"

interpretation ctxt_monoid_mult: monoid_mult "\<box>\<^sub>G" "(\<circ>\<^sub>G\<^sub>c)"
proof
  fix C D E :: "'f gctxt"
  show "C \<circ>\<^sub>G\<^sub>c D \<circ>\<^sub>G\<^sub>c E = C \<circ>\<^sub>G\<^sub>c (D \<circ>\<^sub>G\<^sub>c E)" by (induct C) simp_all
  show "\<box>\<^sub>G \<circ>\<^sub>G\<^sub>c C = C" by simp
  show "C \<circ>\<^sub>G\<^sub>c \<box>\<^sub>G = C" by (induct C) simp_all
qed

instantiation gctxt :: (type) monoid_mult
begin
  definition [simp]: "1 = \<box>\<^sub>G"
  definition [simp]: "(*) = (\<circ>\<^sub>G\<^sub>c)"
  instance by (intro_classes) (simp_all add: ac_simps)
end

lemma ctxt_ctxt_compose [simp]: "(C \<circ>\<^sub>G\<^sub>c D)\<langle>t\<rangle>\<^sub>G = C\<langle>D\<langle>t\<rangle>\<^sub>G\<rangle>\<^sub>G"
  by (induct C) simp_all

lemmas ctxt_ctxt = ctxt_ctxt_compose [symmetric]

fun ctxt_of_gctxt where
   "ctxt_of_gctxt \<box>\<^sub>G = \<box>"
|  "ctxt_of_gctxt (GMore f ss C ts) = More f (map term_of_gterm ss) (ctxt_of_gctxt C) (map term_of_gterm ts)"

fun gctxt_of_ctxt where
   "gctxt_of_ctxt \<box> = \<box>\<^sub>G"
|  "gctxt_of_ctxt (More f ss C ts) = GMore f (map gterm_of_term ss) (gctxt_of_ctxt C) (map gterm_of_term ts)"

lemma ground_ctxt_of_gctxt [simp]:
  "ground_ctxt (ctxt_of_gctxt s)"
  by (induct s) auto

lemma ground_ctxt_of_gctxt' [simp]:
  "ctxt_of_gctxt C = More f ss D ts \<Longrightarrow> ground_ctxt (More f ss D ts)"
  by (induct C) auto

lemma ctxt_of_gctxt_inv [simp]:
  "gctxt_of_ctxt (ctxt_of_gctxt t) = t"
  by (induct t) (auto intro!: nth_equalityI)

lemma inj_ctxt_of_gctxt: "inj_on ctxt_of_gctxt X"
  by (metis inj_on_def ctxt_of_gctxt_inv)

lemma gctxt_of_ctxt_inv [simp]:
  "ground_ctxt C \<Longrightarrow> ctxt_of_gctxt (gctxt_of_ctxt C) = C"
  by (induct C) (auto 0 0 intro!: nth_equalityI)

lemma map_ctxt_of_gctxt [simp]:
  "map_ctxt f g (ctxt_of_gctxt C) = ctxt_of_gctxt (map_gctxt f C)"
  by (induct C) auto

lemma map_gctxt_of_ctxt [simp]:
  "ground_ctxt C \<Longrightarrow> gctxt_of_ctxt (map_ctxt f g C) = map_gctxt f (gctxt_of_ctxt C)"
  by (induct C) auto

lemma map_gctxt_nempty [simp]:
  "C \<noteq> \<box>\<^sub>G \<Longrightarrow> map_gctxt f C \<noteq> \<box>\<^sub>G"
  by (cases C) auto

lemma gctxt_set_funs_ctxt:
  "gfuns_ctxt C = funs_ctxt (ctxt_of_gctxt C)"
  using gterm_set_gterm_funs_terms 
  by (induct C) fastforce+

lemma ctxt_set_funs_gctxt:
  assumes "ground_ctxt C"
  shows "gfuns_ctxt (gctxt_of_ctxt C) = funs_ctxt C"
  using assms term_set_gterm_funs_terms
  by (induct C) fastforce+

lemma vars_ctxt_of_gctxt [simp]:
  "vars_ctxt (ctxt_of_gctxt C) = {}"
  by (induct C) auto

lemma vars_ctxt_of_gctxt_subseteq [simp]:
  "vars_ctxt (ctxt_of_gctxt C) \<subseteq> Q \<longleftrightarrow> True"
  by auto

lemma term_of_gterm_ctxt_apply_ground [simp]:
  "term_of_gterm s = C\<langle>l\<rangle> \<Longrightarrow> ground_ctxt C"
  "term_of_gterm s = C\<langle>l\<rangle> \<Longrightarrow> ground l"
  by (metis ground_ctxt_apply ground_term_of_gterm)+

lemma term_of_gterm_ctxt_subst_apply_ground [simp]:
  "term_of_gterm s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> x \<in> vars_term l \<Longrightarrow> ground (\<sigma> x)"
  by (meson ground_substD term_of_gterm_ctxt_apply_ground(2))

lemma gctxt_compose_HoleE:
 "C \<circ>\<^sub>G\<^sub>c D = \<box>\<^sub>G \<Longrightarrow> C = \<box>\<^sub>G"
 "C \<circ>\<^sub>G\<^sub>c D = \<box>\<^sub>G \<Longrightarrow> D = \<box>\<^sub>G"
  by (cases C; cases D, auto)+


\<comment> \<open>Relations between ground contexts and contexts\<close>

lemma nempty_ground_ctxt_gctxt [simp]:
  "C \<noteq> \<box> \<Longrightarrow> ground_ctxt C \<Longrightarrow> gctxt_of_ctxt C \<noteq> \<box>\<^sub>G"
  by (induct C) auto

lemma ctxt_of_gctxt_apply [simp]:
  "gterm_of_term (ctxt_of_gctxt C)\<langle>term_of_gterm t\<rangle> = C\<langle>t\<rangle>\<^sub>G"
  by (induct C) (auto simp: comp_def map_idI)

lemma ctxt_of_gctxt_apply_gterm:
  "gterm_of_term (ctxt_of_gctxt C)\<langle>t\<rangle> = C\<langle>gterm_of_term t\<rangle>\<^sub>G"
  by (induct C) (auto simp: comp_def map_idI)

lemma ground_gctxt_of_ctxt_apply_gterm:
  assumes "ground_ctxt C"
  shows "term_of_gterm (gctxt_of_ctxt C)\<langle>t\<rangle>\<^sub>G = C\<langle>term_of_gterm t\<rangle>" using assms
  by (induct C) (auto simp: comp_def map_idI)

lemma ground_gctxt_of_ctxt_apply [simp]:
  assumes "ground_ctxt C" "ground t"  
  shows "term_of_gterm (gctxt_of_ctxt C)\<langle>gterm_of_term t\<rangle>\<^sub>G = C\<langle>t\<rangle>" using assms
  by (induct C) (auto simp: comp_def map_idI)

lemma term_of_gterm_ctxt_apply [simp]:
  "term_of_gterm s = C\<langle>l\<rangle> \<Longrightarrow> (gctxt_of_ctxt C)\<langle>gterm_of_term l\<rangle>\<^sub>G = s"
  by (metis ctxt_of_gctxt_apply_gterm gctxt_of_ctxt_inv term_of_gterm_ctxt_apply_ground(1) term_of_gterm_inv)

lemma gctxt_apply_inj_term: "inj (gctxt_apply_term C)"
  by (auto simp: inj_on_def)

lemma gctxt_apply_inj_on_term: "inj_on (gctxt_apply_term C) S"
  by (auto simp: inj_on_def)

lemma ctxt_of_pos_gterm [simp]:
  "p \<in> gposs t \<Longrightarrow> ctxt_at_pos (term_of_gterm t) p = ctxt_of_gctxt (gctxt_at_pos t p)"
  by (induct t arbitrary: p) (auto simp add: take_map drop_map)

lemma gctxt_of_gpos_gterm_gsubt_at_to_gterm [simp]:
  assumes "p \<in> gposs t"
  shows "(gctxt_at_pos t p)\<langle>gsubt_at t p\<rangle>\<^sub>G = t" using assms
  by (induct t arbitrary: p) (auto simp: comp_def min_def nth_append_Cons intro!: nth_equalityI)  

text \<open>The position of the hole in a context is uniquely determined\<close>
fun ghole_pos :: "'f gctxt \<Rightarrow> pos" where
  "ghole_pos \<box>\<^sub>G = []" |
  "ghole_pos (GMore f ss D ts) = length ss # ghole_pos D"

lemma ghole_pos_gctxt_at_pos [simp]:
  "p \<in> gposs t \<Longrightarrow> ghole_pos (gctxt_at_pos t p) = p"
  by (induct t arbitrary: p) auto

lemma ghole_pos_id_ctxt [simp]:
  "C\<langle>s\<rangle>\<^sub>G = t \<Longrightarrow> gctxt_at_pos t (ghole_pos C) = C"
  by (induct C arbitrary: t) auto

lemma ghole_pos_in_apply:
  "ghole_pos C = p \<Longrightarrow> p \<in> gposs C\<langle>u\<rangle>\<^sub>G"
  by (induct C arbitrary: p) (auto simp: nth_append)

lemma ground_hole_pos_to_ghole:
  "ground_ctxt C \<Longrightarrow> ghole_pos (gctxt_of_ctxt C) = hole_pos C"
  by (induct C) auto

lemma gsubst_at_gctxt_at_eq_gtermD:
  assumes "s = t" "p \<in> gposs t"
  shows "gsubt_at s p = gsubt_at t p \<and> gctxt_at_pos s p = gctxt_at_pos t p" using assms
  by auto

lemma gsubst_at_gctxt_at_eq_gtermI:
  assumes "p \<in> gposs s" "p \<in> gposs t"
    and "gsubt_at s p = gsubt_at t p"
    and "gctxt_at_pos s p = gctxt_at_pos t p"
  shows "s = t" using assms
  using gctxt_of_gpos_gterm_gsubt_at_to_gterm by force


lemma gsubt_at_gctxt_apply_ghole [simp]:
  "gsubt_at C\<langle>u\<rangle>\<^sub>G (ghole_pos C) = u"
  by (induct C) auto

lemma gctxt_at_pos_gsubt_at_pos [simp]:
  "p \<in> gposs t \<Longrightarrow> gsubt_at (gctxt_at_pos t p)\<langle>u\<rangle>\<^sub>G p = u"
proof (induct p arbitrary: t)
  case (Cons i p)
  then show ?case using id_take_nth_drop
    by (cases t) (auto simp: nth_append)
qed auto

lemma gfun_at_gctxt_at_pos_not_after:
  assumes "p \<in> gposs t" "q \<in> gposs t" "\<not> (p \<le>\<^sub>p q)"
  shows "gfun_at (gctxt_at_pos t p)\<langle>v\<rangle>\<^sub>G q = gfun_at t q" using assms
proof (induct q arbitrary: p t)
  case Nil
  then show ?case
    by (cases p; cases t) auto
next
  case (Cons i q)
  from Cons(4) obtain j r where [simp]: "p = j # r" by (cases p) auto
  from Cons(4) have "j = i \<Longrightarrow> \<not> (r \<le>\<^sub>p q)" by auto
  from this Cons(2-) Cons(1)[of r "gargs t ! j"]
  have "j = i \<Longrightarrow> gfun_at (gctxt_at_pos (gargs t ! j) r)\<langle>v\<rangle>\<^sub>G q = gfun_at (gargs t ! j) q"
    by (cases t) auto
  then show ?case using Cons(2, 3)
    by (cases t) (auto simp: nth_append_Cons min_def)
qed

lemma gpos_less_eq_append [simp]: "p \<le>\<^sub>p (p @ q)"
  unfolding position_less_eq_def
  by blast

lemma gposs_ConsE [elim]:
  assumes "i # p \<in> gposs t"
  obtains f ts where "t = GFun f ts" "ts \<noteq> []" "i < length ts" "p \<in> gposs (ts ! i)" using assms
  by (cases t) force+

lemma gposs_gctxt_at_pos_not_after:
  assumes "p \<in> gposs t" "q \<in> gposs t" "\<not> (p \<le>\<^sub>p q)"
  shows "q \<in> gposs (gctxt_at_pos t p)\<langle>v\<rangle>\<^sub>G \<longleftrightarrow> q \<in> gposs t" using assms
proof (induct q arbitrary: p t)
  case Nil then show ?case
    by (cases p; cases t) auto
next
  case (Cons i q)
  from Cons(4) obtain j r where [simp]: "p = j # r" by (cases p) auto
  from Cons(4) have "j = i \<Longrightarrow> \<not> (r \<le>\<^sub>p q)" by auto
  from this Cons(2-) Cons(1)[of r "gargs t ! j"]
  have "j = i \<Longrightarrow> q \<in> gposs (gctxt_at_pos (gargs t ! j) r)\<langle>v\<rangle>\<^sub>G \<longleftrightarrow> q \<in> gposs (gargs t ! j)"
    by (cases t) auto
  then show ?case using Cons(2, 3)
    by (cases t) (auto simp: nth_append_Cons min_def)
qed

lemma gposs_gctxt_at_pos:
  "p \<in> gposs t \<Longrightarrow> gposs (gctxt_at_pos t p)\<langle>v\<rangle>\<^sub>G = {q. q \<in> gposs t \<and> \<not> (p \<le>\<^sub>p q)} \<union> (@) p ` gposs v"
proof (induct p arbitrary: t)
  case (Cons i p)
  show ?case using Cons(1)[of "gargs t ! i"] Cons(2) gposs_gctxt_at_pos_not_after[OF Cons(2)]
    by (auto simp: min_def nth_append_Cons split: if_splits elim!: gposs_ConsE)
qed auto

lemma eq_gctxt_at_pos:
  assumes "p \<in> gposs s" "p \<in> gposs t"
    and "\<And> q. \<not> (p \<le>\<^sub>p q) \<Longrightarrow> q \<in> gposs s \<longleftrightarrow> q \<in> gposs t"
    and "(\<And> q. q \<in> gposs s \<Longrightarrow> \<not> (p \<le>\<^sub>p q) \<Longrightarrow> gfun_at s q = gfun_at t q)"
  shows "gctxt_at_pos s p = gctxt_at_pos t p" using assms(1, 2)
  using arg_cong[where ?f = gctxt_of_ctxt, OF eq_ctxt_at_pos_by_poss, of _ "term_of_gterm s :: (_, unit) term"
   "term_of_gterm t :: (_, unit) term" for s t, unfolded poss_gposs_conv fun_at_gfun_at_conv ctxt_of_pos_gterm,
   OF assms]
  by simp

text \<open>Signature of a ground context\<close>

fun funas_gctxt :: "'f gctxt \<Rightarrow> ('f \<times> nat) set" where
  "funas_gctxt GHole = {}" |
  "funas_gctxt (GMore f ss1 D ss2) = {(f, Suc (length (ss1 @ ss2)))}
     \<union> funas_gctxt D \<union> \<Union>(set (map funas_gterm (ss1 @ ss2)))"

lemma funas_gctxt_of_ctxt [simp]:
  "ground_ctxt C \<Longrightarrow> funas_gctxt (gctxt_of_ctxt C) = funas_ctxt C"
  by (induct C) (auto simp: funas_gterm_gterm_of_term)

lemma funas_ctxt_of_gctxt_conv [simp]:
  "funas_ctxt (ctxt_of_gctxt C) = funas_gctxt C"
  by (induct C) (auto simp flip: funas_gterm_gterm_of_term)

lemma inj_gctxt_of_ctxt_on_ground:
  "inj_on gctxt_of_ctxt (Collect ground_ctxt)"
  using gctxt_of_ctxt_inv by (fastforce simp: inj_on_def)

lemma funas_gterm_ctxt_apply [simp]:
  "funas_gterm C\<langle>s\<rangle>\<^sub>G = funas_gctxt C \<union> funas_gterm s"
  by (induct C) auto

lemma funas_gctxt_compose [simp]:
  "funas_gctxt (C \<circ>\<^sub>G\<^sub>c D) = funas_gctxt C \<union> funas_gctxt D"
  by (induct C arbitrary: D) auto

end