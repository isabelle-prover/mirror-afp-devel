(*<*)
theory Galois
imports
  Closures
begin

(*>*)
section\<open> Galois connections\label{sec:galois} \<close>

text\<open>

Here we collect some classical results for Galois connections. These are drawn from
\<^citet>\<open> "Backhouse:2000" and "DaveyPriestley:2002" and
"MeltonSchmidtStrecker:1985" and "MuellerOlm:1997"\<close> amongst others.
The canonical reference is likely \<^citet>\<open>"GierzEtAl:2003"\<close>.

Our focus is on constructing closures (\S\ref{sec:closures}) conveniently; we are less
interested in the fixed-point story. Many of these results hold for preorders; we simply
work with partial orders (via the \<^locale>\<open>ordering\<close> locale).
Similarly \<^emph>\<open>conditionally complete lattices\<close> are often sufficient, but for convenience we
just assume (unconditional) completeness.

\<close>

(* This is less general than we might hope as \<open>ordering\<close> already quantifies over the entire type.
   Therefore it cannot handle lattices where we hoist the bottom up a bit, like the \<open>prog\<close> lattice.
   Generalising is probably be too much hassle. *)
locale galois =
  orda: ordering less_eqa lessa
+ ordb: ordering less_eqb lessb
    for less_eqa (infix "\<le>\<^sub>a" 50)
    and lessa (infix "<\<^sub>a" 50)
    and less_eqb (infix "\<le>\<^sub>b" 50)
    and lessb (infix "<\<^sub>b" 50)
+ fixes lower :: "'a \<Rightarrow> 'b"
  fixes upper :: "'b \<Rightarrow> 'a"
  assumes galois: "lower x \<le>\<^sub>b y \<longleftrightarrow> x \<le>\<^sub>a upper y"
begin

lemma monotone_lower:
  shows "monotone (\<le>\<^sub>a) (\<le>\<^sub>b) lower"
by (rule monotoneI) (use galois orda.trans ordb.refl in blast)

lemma monotone_upper:
  shows "monotone (\<le>\<^sub>b) (\<le>\<^sub>a) upper"
by (rule monotoneI) (use galois ordb.trans orda.refl in blast)

lemmas strengthen_lower[strg] = st_monotone[OF monotone_lower]
lemmas strengthen_upper[strg] = st_monotone[OF monotone_upper]

lemma upper_lower_expansive:
  shows "x \<le>\<^sub>a upper (lower x)"
using galois ordb.refl by blast

lemma lower_upper_contractive:
  shows "lower (upper x) \<le>\<^sub>b x"
using galois orda.refl by blast

lemma comp_galois: \<comment>\<open> \<^citet>\<open>\<open>Lemma~19\<close> in "Backhouse:2000"\<close>. Observe that the roles of upper and lower have swapped. \<close>
  fixes less_eqc :: "'c \<Rightarrow> 'c \<Rightarrow> bool" (infix "\<le>\<^sub>c" 50)
  fixes lessc :: "'c \<Rightarrow> 'c \<Rightarrow> bool" (infix "<\<^sub>c" 50)
  fixes h :: "'a \<Rightarrow> 'c"
  fixes k :: "'b \<Rightarrow> 'c"
  assumes "partial_preordering (\<le>\<^sub>c)"
  assumes "monotone (\<le>\<^sub>a) (\<le>\<^sub>c) h"
  assumes "monotone (\<le>\<^sub>b) (\<le>\<^sub>c) k"
  shows "(\<forall>x. h (upper x) \<le>\<^sub>c k x)  \<longleftrightarrow> (\<forall>x. h x \<le>\<^sub>c k (lower x))"
using assms(1) monotoneD[OF assms(2)] monotoneD[OF assms(3)]
by (meson lower_upper_contractive partial_preordering.trans upper_lower_expansive)

lemma lower_upper_le_iff: \<comment>\<open> \<^citet>\<open>\<open>Lemma~23\<close> in "Backhouse:2000"\<close> \<close>
  assumes "\<forall>x y. lower' x \<le>\<^sub>b y \<longleftrightarrow> x \<le>\<^sub>a upper' y"
  shows "(\<forall>x. lower' x \<le>\<^sub>b lower x) \<longleftrightarrow> (\<forall>y. upper y \<le>\<^sub>a upper' y)"
using assms by (meson lower_upper_contractive orda.trans ordb.trans upper_lower_expansive)

lemma lower_upper_unique: \<comment>\<open> \<^citet>\<open>\<open>Lemma~24\<close> in "Backhouse:2000"\<close> \<close>
  assumes "\<forall>x y. lower' x \<le>\<^sub>b y \<longleftrightarrow> x \<le>\<^sub>a upper' y"
  shows "lower' = lower \<longleftrightarrow> upper' = upper"
using assms galois lower_upper_contractive orda.eq_iff ordb.eq_iff upper_lower_expansive by blast

lemma upper_lower_idem:
  shows "upper (lower (upper (lower x))) = upper (lower x)"
by (meson galois lower_upper_contractive orda.antisym ordb.trans upper_lower_expansive)

lemma lower_upper_idem:
  shows "lower (upper (lower (upper x))) = lower (upper x)"
by (metis galois ordb.antisym upper_lower_expansive upper_lower_idem)

lemma lower_upper_lower: \<comment>\<open> \<^citet>\<open>\<open>Proposition~1.2(2)\<close> in "MeltonSchmidtStrecker:1985"\<close> \<close>
  shows "lower \<circ> upper \<circ> lower = lower"
    and "lower (upper (lower x)) = lower x"
using galois lower_upper_contractive ordb.antisym upper_lower_expansive upper_lower_idem by auto

lemma upper_lower_upper:  \<comment>\<open> \<^citet>\<open>\<open>Proposition~1.2(2)\<close> in "MeltonSchmidtStrecker:1985"\<close> \<close>
  shows "upper \<circ> lower \<circ> upper = upper"
    and "upper (lower (upper x)) = upper x"
by (simp_all add: fun_eq_iff)
   (metis galois monotone_upper monotoneD orda.antisym orda.refl upper_lower_expansive)+

definition cl :: "'a \<Rightarrow> 'a" where \<comment>\<open> The opposite composition yields a kernel operator \<close>
  "cl x = upper (lower x)"

lemma cl_axiom:
  shows "(x \<le>\<^sub>a cl y) = (cl x \<le>\<^sub>a cl y)"
by (metis cl_def galois lower_upper_lower(2))

sublocale closure "(\<le>\<^sub>a)" "(<\<^sub>a)" cl \<comment>\<open> incorporates definitions and lemmas into this namespace \<close>
by standard (rule cl_axiom)

lemma cl_upper:
  shows "cl (upper P) = upper P"
by (simp add: cl_def upper_lower_upper)

lemma closed_upper:
  shows "upper P \<in> closed"
by (simp add: closed_def cl_upper orda.refl)

lemma inj_lower_iff_surj_upper:
  shows "inj lower \<longleftrightarrow> surj upper"
by (metis inj_def surj_def lower_upper_lower(2) upper_lower_upper(2))

lemma inj_lower_iff_upper_lower_id:
  shows "inj lower \<longleftrightarrow> upper \<circ> lower = id"
by (metis fun.map_comp id_comp inj_iff inj_on_id inj_on_imageI2 lower_upper_lower(1))

lemma upper_inj_iff_surj_lower:
  shows "inj upper \<longleftrightarrow> surj lower"
by (metis inj_def surj_def lower_upper_lower(2) upper_lower_upper(2))

lemma inj_upper_iff_lower_upper_id:
  shows "inj upper \<longleftrightarrow> lower \<circ> upper = id"
by (metis fun.map_comp id_comp inj_iff inj_on_id inj_on_imageI2 upper_lower_upper(1))

lemma lower_downset_upper: \<comment>\<open> \<^citet>\<open>\<open>Lemma~7.32\<close> in "DaveyPriestley:2002"\<close>: inverse image of lower on a downset is the downset of upper \<close>
  shows "lower -` {a. a \<le>\<^sub>b y} = {a. a \<le>\<^sub>a upper y}"
by (simp add: galois)

lemma lower_downset: \<comment>\<open> \<^citet>\<open>\<open>Lemma~7.32\<close> in "DaveyPriestley:2002"\<close>; equivalent to the Galois axiom \<close>
  shows "\<exists>!x. lower -` {a. a \<le>\<^sub>b y} = {a. a \<le>\<^sub>a x}"
by (metis lower_downset_upper mem_Collect_eq orda.antisym orda.refl)

end

setup \<open>Sign.mandatory_path "galois"\<close>

lemma axioms_alt:
  fixes less_eqa (infix "\<le>\<^sub>a" 50)
  fixes less_eqb (infix "\<le>\<^sub>b" 50)
  fixes lower :: "'a \<Rightarrow> 'b"
  fixes upper :: "'b \<Rightarrow> 'a"
  assumes oa: "ordering less_eqa lessa"
  assumes ob: "ordering less_eqb lessb"
  assumes ul: "\<forall>x. x \<le>\<^sub>a upper (lower x)"
  assumes lu: "\<forall>x. lower (upper x) \<le>\<^sub>b x"
  assumes ml: "monotone (\<le>\<^sub>a) (\<le>\<^sub>b) lower"
  assumes mu: "monotone (\<le>\<^sub>b) (\<le>\<^sub>a) upper"
  shows "lower x \<le>\<^sub>b y \<longleftrightarrow> x \<le>\<^sub>a upper y"
by (metis lu ml monotoneD mu oa ob ordering.axioms(1) partial_preordering.trans ul)

lemma compose:
  fixes lower\<^sub>1 :: "'b \<Rightarrow> 'c"
  fixes lower\<^sub>2 :: "'a \<Rightarrow> 'b"
  fixes less_eqa :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "galois less_eqb lessb less_eqc lessc lower\<^sub>1 upper\<^sub>1"
  assumes "galois less_eqa lessa less_eqb lessb lower\<^sub>2 upper\<^sub>2"
  shows "galois less_eqa lessa less_eqc lessc (lower\<^sub>1 \<circ> lower\<^sub>2) (upper\<^sub>2 \<circ> upper\<^sub>1)"
using assms unfolding galois_def galois_axioms_def by simp

locale complete_lattice =
  cla: complete_lattice "Inf\<^sub>a" "Sup\<^sub>a" "(\<sqinter>\<^sub>a)" "(\<le>\<^sub>a)" "(<\<^sub>a)" "(\<squnion>\<^sub>a)" "\<bottom>\<^sub>a" "\<top>\<^sub>a"
+ clb: complete_lattice "Inf\<^sub>b" "Sup\<^sub>b" "(\<sqinter>\<^sub>b)" "(\<le>\<^sub>b)" "(<\<^sub>b)" "(\<squnion>\<^sub>b)" "\<bottom>\<^sub>b" "\<top>\<^sub>b"
+ galois "(\<le>\<^sub>a)" "(<\<^sub>a)" "(\<le>\<^sub>b)" "(<\<^sub>b)" lower upper
    for less_eqa :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<le>\<^sub>a" 50)
    and lessa (infix "<\<^sub>a" 50)
    and infa (infixl "\<sqinter>\<^sub>a" 70)
    and supa (infixl "\<squnion>\<^sub>a" 65)
    and bota ("\<bottom>\<^sub>a")
    and topa ("\<top>\<^sub>a")
    and Inf\<^sub>a Sup\<^sub>a
    and less_eqb :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<le>\<^sub>b" 50)
    and lessb (infix "<\<^sub>b" 50)
    and infb (infixl "\<sqinter>\<^sub>b" 70)
    and supb (infixl "\<squnion>\<^sub>b" 65)
    and botb ("\<bottom>\<^sub>b")
    and topb ("\<top>\<^sub>b")
    and Inf\<^sub>b Sup\<^sub>b
    and lower :: "'a \<Rightarrow> 'b"
    and upper :: "'b \<Rightarrow> 'a"
begin

lemma lower_bot:
  shows "lower \<bottom>\<^sub>a = \<bottom>\<^sub>b"
by (simp add: clb.le_bot galois)

lemmas mono2mono_lower[cont_intro, partial_function_mono] = monotone2monotone[OF monotone_lower, simplified]

lemma lower_Sup: \<comment>\<open> \<^citet>\<open>\<open>Proposition~1.2(6)\<close> in "MeltonSchmidtStrecker:1985"\<close>: \<^term>\<open>lower\<close> is always a distributive operation \<close>
  shows "lower (Sup\<^sub>a X) = Sup\<^sub>b (lower ` X)" (is "?lhs = ?rhs")
proof(rule clb.order.antisym)
  show "?lhs \<le>\<^sub>b ?rhs" by (meson cla.Sup_least clb.SUP_upper galois)
  show "?rhs \<le>\<^sub>b ?lhs" by (meson cla.Sup_le_iff clb.SUP_le_iff galois upper_lower_expansive)
qed

lemma lower_SUP:
  shows "lower (Sup\<^sub>a (f ` X)) = Sup\<^sub>b ((\<lambda>x. lower (f x)) ` X)"
by (simp add: lower_Sup image_image)

lemma lower_sup:
  shows "lower (X \<squnion>\<^sub>a Y) = lower X \<squnion>\<^sub>b lower Y"
using lower_Sup[where X="{X, Y}"] by simp

lemma lower_Inf_le:
  shows "lower (Inf\<^sub>a X) \<le>\<^sub>b Inf\<^sub>b (lower ` X)"
by (simp add: cla.Inf_lower2 clb.le_INF_iff galois upper_lower_expansive)

lemma lower_INF_le:
  shows "lower (Inf\<^sub>a (f ` X)) \<le>\<^sub>b Inf\<^sub>b ((\<lambda>x. lower (f x)) ` X)"
by (simp add: clb.order.trans[OF lower_Inf_le] image_image)

lemma lower_inf_le:
  shows "lower (x \<sqinter>\<^sub>a y) \<le>\<^sub>b lower x \<sqinter>\<^sub>b lower y"
using lower_Inf_le[where X="{x, y}"] by simp

lemma mcont_lower: \<comment>\<open> \<^citet>\<open>"Backhouse:2000"\<close>: fixed point theory based on Galois connections is less general than using countable chains \<close>
  shows "mcont Sup\<^sub>a (\<le>\<^sub>a) Sup\<^sub>b (\<le>\<^sub>b) lower"
by (meson contI lower_Sup mcontI monotone_lower)

lemma mcont2mcont_lower[cont_intro]:
  assumes "mcont luba orda Sup\<^sub>a (\<le>\<^sub>a) P"
  shows "mcont luba orda Sup\<^sub>b (\<le>\<^sub>b) (\<lambda>x. lower (P x))"
using assms mcont_lower
      partial_function_definitions.mcont2mcont[OF clb.complete_lattice_partial_function_definitions]
by blast

lemma upper_top:
  shows "upper \<top>\<^sub>b = \<top>\<^sub>a"
by (simp add: cla.top_le flip: galois)

lemma Sup_upper_le:
  shows "Sup\<^sub>a (upper ` X) \<le>\<^sub>a upper (Sup\<^sub>b X)"
by (meson cla.SUP_le_iff clb.Sup_upper2 galois lower_upper_contractive)

lemma sup_upper_le:
  shows "upper x \<squnion>\<^sub>a upper y \<le>\<^sub>a upper (x \<squnion>\<^sub>b y)"
using Sup_upper_le[where X="{x, y}"] by simp

lemma upper_Inf: \<comment>\<open> \<^citet>\<open>\<open>Proposition~1.2(6)\<close> in "MeltonSchmidtStrecker:1985"\<close> \<close>
  shows "upper (Inf\<^sub>b X) = Inf\<^sub>a (upper ` X)" (is "?lhs = ?rhs")
proof(rule cla.order.antisym)
  show "?lhs \<le>\<^sub>a ?rhs" by (meson cla.INF_greatest clb.le_Inf_iff galois lower_upper_contractive)
  show "?rhs \<le>\<^sub>a ?lhs" by (meson cla.INF_lower clb.le_Inf_iff galois)
qed

lemma upper_INF:
  shows "upper (Inf\<^sub>b (f ` X)) = Inf\<^sub>a ((\<lambda>x. upper (f x)) ` X)"
by (simp add: image_image upper_Inf)

lemma upper_inf:
  shows "upper (X \<sqinter>\<^sub>b Y) = upper X \<sqinter>\<^sub>a upper Y"
using upper_Inf[where X="{X, Y}"] by simp

text\<open>

In a complete lattice \<open>lower\<close> is determined by \<open>upper\<close> and vice-versa.

\<close>

lemma lower_Inf_upper:
  shows "lower X = Inf\<^sub>b {Y. X \<le>\<^sub>a upper Y}"
by (auto simp flip: galois intro: clb.Inf_eqI[symmetric])

lemma upper_Sup_lower:
  shows "upper X = Sup\<^sub>a {Y. lower Y \<le>\<^sub>b X}"
by (auto simp: galois intro: cla.Sup_eqI[symmetric])

lemma upper_downwards_closure_lower: \<comment>\<open> \<^citet>\<open>\<open>Lemma~2.1\<close> in "MeltonSchmidtStrecker:1985"\<close> \<close>
  shows "upper x = Sup\<^sub>a (lower -` {y. y \<le>\<^sub>b x})"
by (simp add: upper_Sup_lower)

sublocale closure_complete_lattice "(\<le>\<^sub>a)" "(<\<^sub>a)" "(\<sqinter>\<^sub>a)" "(\<squnion>\<^sub>a)" "\<bottom>\<^sub>a" "\<top>\<^sub>a" "Inf\<^sub>a" "Sup\<^sub>a" cl
by (rule closure_complete_lattice.intro[OF cla.complete_lattice_axioms closure_axioms])

end

locale complete_lattice_distributive =
  galois.complete_lattice
+ assumes upper_Sup_le: "upper (Sup\<^sub>b X) \<le>\<^sub>a Sup\<^sub>a (upper ` X)" \<comment>\<open> Stronger than Scott continuity, which only asks for this for chain or directed \<open>X\<close>. \<close>
begin

lemma upper_Sup:
  shows "upper (Sup\<^sub>b X) = Sup\<^sub>a (upper ` X)"
by (simp add: Sup_upper_le cla.dual_order.antisym upper_Sup_le)

lemma upper_bot:
  shows "upper \<bottom>\<^sub>b = \<bottom>\<^sub>a"
using upper_Sup[where X="{}"] by simp

lemma upper_sup:
  shows "upper (x \<squnion>\<^sub>b y) = upper x \<squnion>\<^sub>a upper y"
by (rule upper_Sup[where X="{x, y}", simplified])

lemmas mono2mono_upper[cont_intro, partial_function_mono] = monotone2monotone[OF monotone_upper, simplified]

lemma mcont_upper:
  shows "mcont Sup\<^sub>b (\<le>\<^sub>b) Sup\<^sub>a (\<le>\<^sub>a) upper"
by (meson contI upper_Sup mcontI monotone_upper)

lemma mcont2mcont_upper[cont_intro]:
  assumes "mcont luba orda Sup\<^sub>b (\<le>\<^sub>b) P"
  shows "mcont luba orda Sup\<^sub>a (\<le>\<^sub>a) (\<lambda>x. upper (P x))"
by (simp add: ccpo.mcont2mcont'[OF cla.complete_lattice_ccpo mcont_upper _ assms])

sublocale closure_complete_lattice_distributive "(\<le>\<^sub>a)" "(<\<^sub>a)" "(\<sqinter>\<^sub>a)" "(\<squnion>\<^sub>a)" "\<bottom>\<^sub>a" "\<top>\<^sub>a" "Inf\<^sub>a" "Sup\<^sub>a" cl
by standard (simp add: cl_def upper_Sup lower_Sup image_image)

lemma cl_bot:
  shows "cl \<bottom>\<^sub>a = \<bottom>\<^sub>a"
by (simp add: cl_def lower_bot upper_bot)

lemma closed_bot[iff]:
  shows "\<bottom>\<^sub>a \<in> closed"
by (simp add: cl_bot closed_clI)

end

locale complete_lattice_class =
  galois.complete_lattice
    "(\<le>)" "(<)" "(\<sqinter>)" "(\<squnion>)" "\<bottom> :: _ :: complete_lattice" "\<top>" "Inf" "Sup"
    "(\<le>)" "(<)" "(\<sqinter>)" "(\<squnion>)" "\<bottom> :: _ :: complete_lattice" "\<top>" "Inf" "Sup"
begin

sublocale closure_complete_lattice_class cl ..

end

locale complete_lattice_distributive_class =
  galois.complete_lattice_distributive
    "(\<le>)" "(<)" "(\<sqinter>)" "(\<squnion>)" "\<bottom> :: _ :: complete_lattice" "\<top>" "Inf" "Sup"
    "(\<le>)" "(<)" "(\<sqinter>)" "(\<squnion>)" "\<bottom> :: _ :: complete_lattice" "\<top>" "Inf" "Sup"
begin

sublocale galois.complete_lattice_class ..
sublocale closure_complete_lattice_distributive_class cl ..

end

lemma existence_lower_preserves_Sup: \<comment>\<open> \<^citet>\<open>\<open>p8 of Oxford TR PRG-44\<close> in "HoareHe:1987"\<close> amongst others \<close>
  fixes lower :: "_::complete_lattice \<Rightarrow> _::complete_lattice"
  assumes "mono lower"
  shows "(\<forall>x y. lower x \<le> y \<longleftrightarrow> x \<le> \<Squnion>{Y. lower Y \<le> y}) \<longleftrightarrow> (\<forall>X. lower (\<Squnion>X) \<le> \<Squnion>(lower ` X))" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (metis SUP_upper Sup_least)
  show "?rhs \<Longrightarrow> ?lhs"
    by (fastforce intro: Sup_upper SUP_least order.trans elim: order.trans[OF monoD[OF assms]])
qed

lemma lower_preserves_SupI:
  assumes "mono lower"
  assumes "\<And>X. lower (\<Squnion>X) \<le> \<Squnion>(lower ` X)"
  assumes "\<And>x. upper x = \<Squnion>{X. lower X \<le> x}"
  shows "galois.complete_lattice_class lower upper"
by standard (metis assms galois.existence_lower_preserves_Sup)

lemma existence_upper_preserves_Inf:
  fixes upper :: "_::complete_lattice \<Rightarrow> _::complete_lattice"
  assumes "mono upper"
  shows "(\<forall>x y.  \<Sqinter>{Y. x \<le> upper Y} \<le> y \<longleftrightarrow> x \<le> upper y) \<longleftrightarrow> (\<forall>X. \<Sqinter>(upper ` X) \<le> upper (\<Sqinter>X))" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs
  interpret gcl: galois.complete_lattice_class "\<lambda>x. \<Sqinter>{Y. x \<le> upper Y}" upper
    by standard (use \<open>?lhs\<close> in blast)
  from gcl.upper_Inf show ?rhs by simp
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (auto intro: Inf_lower order.trans[rotated] INF_greatest order.trans[OF _ monoD[OF assms], rotated])
qed

lemma upper_preserves_InfI:
  assumes "mono upper"
  assumes "\<And>X. \<Sqinter>(upper ` X) \<le> upper (\<Sqinter>X)"
  assumes "\<And>x. lower x = \<Sqinter>{X. x \<le> upper X}"
  shows "galois.complete_lattice_class lower upper"
by standard (metis assms galois.existence_upper_preserves_Inf)

locale powerset =
  galois.complete_lattice_class lower upper
for lower :: "'a set \<Rightarrow> 'b set"
and upper :: "'b set \<Rightarrow> 'a set"
begin

lemma lower_insert:
  shows "lower (insert x X) = lower {x} \<union> lower X"
by (metis insert_is_Un lower_sup)

lemma lower_distributive:
  shows "lower X = (\<Union>x\<in>X. lower {x})"
using lower_Sup[where X="{{x} |x. x \<in> X}"] by (auto simp: Union_singleton)

sublocale closure_powerset cl ..

end

locale powerset_distributive =
  galois.powerset
+ galois.complete_lattice_distributive_class
begin

lemma upper_insert:
  shows "upper (insert x X) = upper {x} \<union> upper X"
by (metis insert_is_Un upper_sup)

lemma cl_distributive_axiom:
  shows "cl (\<Union> X) \<subseteq> \<Union> (cl ` X)"
by (simp add: cl_def lower_Sup upper_Sup)

sublocale closure_powerset_distributive cl
by standard (simp add: cl_distributive_axiom cla.le_supI1)

end

text\<open>

\<^citet>\<open>\<open>Theorems~3.3.1, 3.3.2\<close> in "MuellerOlm:1997"\<close>: relation image forms a Galois connection.
See also \<^citet>\<open>\<open>Exercise~7.18\<close> in "DaveyPriestley:2002"\<close>.

\<close>

definition lower\<^sub>R :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" where
  "lower\<^sub>R R A = R `` A"

definition upper\<^sub>R :: "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> 'a set" where
  "upper\<^sub>R R B = {a. \<forall>b. (a, b) \<in> R \<longrightarrow> b \<in> B}"

interpretation relation: galois.powerset "galois.lower\<^sub>R R" "galois.upper\<^sub>R R"
unfolding galois.lower\<^sub>R_def galois.upper\<^sub>R_def by standard blast

context galois.powerset
begin

lemma relations_galois:
  defines "R \<equiv> {(a, b). b \<in> lower {a}}"
  shows "lower = galois.lower\<^sub>R R"
    and "upper = galois.upper\<^sub>R R"
proof -
  show "lower = galois.lower\<^sub>R R"
  proof(rule HOL.ext)
    fix X
    have "lower X = (\<Union>x\<in>X. lower {x})" by (rule lower_distributive)
    also have "\<dots> = (\<Union>x\<in>X. galois.lower\<^sub>R R {x})" by (simp add: galois.lower\<^sub>R_def R_def)
    also have "\<dots> = galois.lower\<^sub>R R X" unfolding galois.lower\<^sub>R_def R_def by blast
    finally show "lower X = galois.lower\<^sub>R R X" .
  qed
  then show "upper = galois.upper\<^sub>R R"
    using galois galois.relation.lower_upper_unique by blast
qed

end

setup \<open>Sign.parent_path\<close>


subsection\<open> Some Galois connections\label{sec:galois-concrete} \<close>

setup \<open>Sign.mandatory_path "galois"\<close>

locale complete_lattice_class_monomorphic
  = galois.complete_lattice_class upper lower
      for upper :: "'a::complete_lattice \<Rightarrow> 'a" and lower :: "'a \<Rightarrow> 'a"  \<comment>\<open> Avoid \<open>'a itself\<close> parameters \<close>

interpretation conj_imp: galois.complete_lattice_class "(\<sqinter>) x" "(\<^bold>\<longrightarrow>\<^sub>B) x" for x :: "_::boolean_algebra" \<comment>\<open> Classic example \<close>
by standard (simp add: boolean_implication.conv_sup inf_commute shunt1)

text\<open>

There are very well-behaved Galois connections arising from the image
(and inverse image) of sets under a function; stuttering is one
instance (\S\ref{sec:safety_logic-stuttering}).

\<close>

locale image_vimage =
  fixes f :: "'a \<Rightarrow> 'b"
begin

definition lower :: "'a set \<Rightarrow> 'b set" where
  "lower X = f ` X"

definition upper :: "'b set \<Rightarrow> 'a set" where
  "upper X = f -` X"

lemma upper_empty[iff]:
  shows "upper {} = {}"
unfolding upper_def by simp

sublocale galois.powerset_distributive lower upper
unfolding lower_def upper_def by standard (simp_all add: image_subset_iff_subset_vimage vimage_Union)

abbreviation equivalent :: "'a relp" where
  "equivalent x y \<equiv> f x = f y"

lemma equiv:
  shows "Equiv_Relations.equivp equivalent"
by (simp add: equivpI reflpI symp_def transp_def)

lemma equiv_cl_singleton:
  assumes "equivalent x y"
  shows "cl {x} = cl {y}"
using assms by (simp add: cl_def galois.image_vimage.lower_def)

lemma cl_alt_def:
  shows "cl X = {(x, y). equivalent x y} `` X"
by (simp add: cl_def lower_def upper_def vimage_image_eq)

sublocale closure_powerset_distributive_exchange cl
by standard (auto simp: cl_alt_def intro: exchangeI)

lemma closed_in:
  assumes "x \<in> P"
  assumes "equivalent x y"
  assumes P: "P \<in> closed"
  shows "y \<in> P"
using assms(1-2) closed_conv[OF P] unfolding cl_alt_def by blast

lemma clE:
  assumes "x \<in> cl P"
  obtains y where "equivalent y x" and "y \<in> P"
using assms unfolding cl_alt_def by blast

lemma clI[intro]:
  assumes "x \<in> P"
  assumes "equivalent x y"
  shows "y \<in> cl P"
unfolding cl_alt_def using assms by blast

lemma closed_diff[intro]:
  assumes "X \<in> closed"
  assumes "Y \<in> closed"
  shows "X - Y \<in> closed"
by (rule closedI) (metis Diff_iff assms clE closed_in)

lemma closed_uminus[intro]:
  assumes "X \<in> closed"
  shows "-X \<in> closed"
using closed_diff[where X=UNIV, OF _ assms] by fastforce

end

locale image_vimage_monomorphic
  = galois.image_vimage f
      for f :: "'a \<Rightarrow> 'a" \<comment>\<open> Avoid \<open>'a itself\<close> parameters \<close>

locale image_vimage_idempotent
  = galois.image_vimage_monomorphic +
    assumes f_idempotent: "\<And>x. f (f x) = f x"
begin

lemma f_idempotent_comp:
  shows "f \<circ> f = f"
by (simp add: comp_def f_idempotent)

lemma idemI:
  assumes "f x \<in> P"
  shows "x \<in> cl P"
using assms f_idempotent by (auto simp: cl_alt_def)

lemma f_cl:
  shows "f x \<in> cl P \<longleftrightarrow> x \<in> cl P"
by (simp add: cl_alt_def f_idempotent)

lemma f_closed:
  assumes "P \<in> closed"
  shows "f x \<in> P \<longleftrightarrow> x \<in> P"
by (metis assms closed_conv f_cl)

lemmas f_closedI = iffD1[OF f_closed]

end

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
