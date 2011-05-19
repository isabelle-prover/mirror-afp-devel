
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

header "Kripke Structures"

theory Kripke
imports Main
begin

datatype ('a, 'p) Kform = Kprop "'p" | Knot "('a, 'p) Kform"
         | Kand "('a, 'p) Kform" "('a, 'p) Kform" | Knows "'a" "('a, 'p) Kform" ("\<^bold>K\<^sub>_ _")

record ('a, 'p, 'w) KripkeStructure =
  worlds :: "'w set"
  relations :: "'a \<Rightarrow> ('w \<times> 'w) set"
  valuation :: "'w \<Rightarrow> 'p \<Rightarrow> bool"

type_synonym 'w Relation = "('w \<times> 'w) set"

definition
  kripke :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> bool"
where
  "kripke M \<equiv> \<forall>a. relations M a \<subseteq> worlds M \<times> worlds M"

definition
  mkKripke :: "'w set \<Rightarrow> ('a \<Rightarrow> 'w Relation) \<Rightarrow> ('w \<Rightarrow> 'p \<Rightarrow> bool)
             \<Rightarrow> ('a, 'p, 'w) KripkeStructure"
where
  "mkKripke ws rels val \<equiv>
     \<lparr> worlds = ws, relations = \<lambda>a. rels a \<inter> ws \<times> ws, valuation = val \<rparr>"

lemma kripkeI[intro]:
  assumes "\<And>a. relations M a \<subseteq> worlds M \<times> worlds M"
  shows "kripke M"
  using assms unfolding kripke_def by simp

lemma kripke_rels_worlds[dest]:
  assumes "(w, w') \<in> relations M a"
      and M: "kripke M"
  shows "w \<in> worlds M \<and> w' \<in> worlds M"
  using assms unfolding kripke_def by auto

lemma kripke_tc_rels_worlds[dest]:
  assumes R: "(w, w') \<in> (\<Union>a \<in> as. relations M a)\<^sup>+"
      and M: "kripke M"
  shows "w \<in> worlds M \<and> w' \<in> worlds M"
  using assms by (induct rule: trancl_induct) auto

lemma kripke_rels_trc_worlds:
  assumes R: "(w, w') \<in> (\<Union>a. relations M a)\<^sup>*"
      and w: "w \<in> worlds M"
      and M: "kripke M"
      and W: "W = worlds M"
  shows "w' \<in> W"
  using assms by (induct rule: rtrancl_induct) auto

lemma mkKripke_kripke[intro, simp]:
  "kripke (mkKripke ws rels val)"
  unfolding kripke_def mkKripke_def by clarsimp

lemma mkKripke_simps[simp]:
  "worlds (mkKripke ws rels val) = ws"
  "relations (mkKripke ws rels val) = (\<lambda>a. rels a \<inter> ws \<times> ws)"
  "valuation (mkKripke ws rels val) = val"
  unfolding mkKripke_def by simp_all

definition S5n :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> bool" where
  "S5n M \<equiv> \<forall>a. equiv (worlds M) (relations M a)"

lemma S5nI[intro]: "\<lbrakk> \<And>a. equiv (worlds M) (relations M a) \<rbrakk> \<Longrightarrow> S5n M"
  by (simp add: S5n_def)

lemma S5nD[dest]: "S5n M \<Longrightarrow> equiv (worlds M) (relations M a)"
  by (simp add: S5n_def)

lemma S5n_kripke[intro]: "S5n M \<Longrightarrow> kripke M"
  by (rule kripkeI, erule equivE[OF S5nD], auto simp add: refl_on_def)

fun models :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> 'w \<Rightarrow> ('a, 'p) Kform \<Rightarrow> bool" ("(_, _ \<Turnstile> _)" [80,0,80] 80) where
  "M, w \<Turnstile> (Kprop p)      = valuation M w p"
| "M, w \<Turnstile> (Knot \<phi>)       = (\<not> M, w \<Turnstile> \<phi>)"
| "M, w \<Turnstile> (Kand \<phi> \<psi>)     = (M, w \<Turnstile> \<phi> \<and> M, w \<Turnstile> \<psi>)"
| "M, w \<Turnstile> (\<^bold>K\<^sub>a \<phi>)         = (\<forall>w' \<in> relations M a `` {w}. M, w' \<Turnstile> \<phi>)"

lemma S5n_rels_eq:
  assumes S5n: "S5n M"
      and ww': "(w, w') \<in> relations M a"
  shows "relations M a `` {w} = relations M a `` {w'}"
  using S5nD[OF S5n] ww' by - (rule equiv_class_eq, blast+)

lemma tc_equiv:
  assumes E: "\<And>i. i \<in> is \<Longrightarrow> equiv A (f i)"
      and is_nempty: "is \<noteq> {}"
  shows "equiv A ((\<Union>i\<in>is. f i)\<^sup>+)"
proof(rule equivI)
  from E is_nempty show "refl_on A ((\<Union>i\<in>is. f i)\<^sup>+)"
    unfolding equiv_def
    apply -
    apply (rule refl_onI)
    apply (rule trancl_Int_subset)
    apply (auto dest: refl_onD refl_onD1 refl_onD2)
    done
  from E show "sym ((\<Union>i\<in>is. f i)\<^sup>+)"
    apply -
    apply (rule sym_trancl)
    unfolding equiv_def sym_def by blast
  show "trans  ((\<Union>i\<in>is. f i)\<^sup>+)" by (rule trans_trancl)
qed

lemma S5n_tc_rels_eq:
  assumes S5n: "S5n M"
      and ww': "(w, w') \<in> (\<Union>a \<in> as. relations M a)\<^sup>+"
  shows "(\<Union>a \<in> as. relations M a)\<^sup>+ `` {w} = (\<Union>a \<in> as. relations M a)\<^sup>+ `` {w'}"
  apply (cases "as = {}")
   apply fastsimp
  apply (rule equiv_class_eq[OF _ ww'])
  apply (erule tc_equiv[OF S5nD[OF S5n]])
  done

(* Generated sub models. *)

definition
  sub_model :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> 'w \<Rightarrow> ('a, 'p, 'w) KripkeStructure"
where
  "sub_model M w \<equiv>
    let worlds' = worlds M \<inter> (\<Union>a. relations M a)\<^sup>* `` {w}
     in \<lparr> worlds = worlds',
          relations = \<lambda>a. relations M a \<inter> (worlds' \<times> worlds'),
          valuation = valuation M \<rparr>"

lemma sub_model_worldsD[dest]:
  "w' \<in> worlds (sub_model M w) \<Longrightarrow> w' \<in> worlds M"
  unfolding sub_model_def by simp

lemma sub_model_world_refl:
  "w \<in> worlds M \<Longrightarrow> w \<in> worlds (sub_model M w)"
  unfolding sub_model_def by simp

lemma sub_model_rels_worlds[dest]:
  assumes "(w', w'') \<in> relations (sub_model M w) a"
  shows "w' \<in> worlds (sub_model M w) \<and> w'' \<in> worlds (sub_model M w)"
  using assms unfolding sub_model_def by simp

lemma sub_model_rels_tc_worlds[dest]:
  assumes "(w', w'') \<in> (\<Union>a \<in> as. relations (sub_model M w) a)\<^sup>+"
  shows "w'' \<in> worlds (sub_model M w)"
  using assms by (induct rule: trancl_induct) auto

lemma sub_model_rels[dest]:
  assumes "(w', w'') \<in> relations (sub_model M w) a"
  shows "(w', w'') \<in> relations M a"
  using assms unfolding sub_model_def by simp

lemma sub_model_worlds:
  "worlds (sub_model M w) = worlds M \<inter> (\<Union>a. relations M a)\<^sup>* `` {w}"
  unfolding sub_model_def by simp

lemma sub_model_tc_rels[dest]:
  assumes M: "kripke M"
      and R: "(w', w'') \<in> (\<Union>a \<in> as. relations (sub_model M w) a)\<^sup>+"
  shows "(w', w'') \<in> (\<Union>a \<in> as. relations M a)\<^sup>+"
using R
proof(induct rule: trancl_induct)
  case (base y) with M show ?case by auto
next
  case (step y z)
  with M have "y \<in> worlds (sub_model M w)"
          and "z \<in> worlds (sub_model M w)" by auto
  with M step show ?case by (auto intro: trancl_into_trancl)
qed

lemma sub_model_rels_rev[dest]:
  assumes M: "kripke M"
      and "w' \<in> worlds (sub_model M w)"
      and "(w', w'') \<in> relations M a"
  shows "(w', w'') \<in> relations (sub_model M w) a"
  using assms
  unfolding sub_model_def by (auto intro: rtrancl_into_rtrancl)

lemma sub_model_tc_rels_rev[dest]:
  assumes M: "kripke M"
      and R: "(w', w'') \<in> (\<Union>a \<in> as. relations M a)\<^sup>+"
      and W: "w' \<in> worlds (sub_model M w)"
  shows "(w', w'') \<in> (\<Union>a \<in> as. relations (sub_model M w) a)\<^sup>+"
using R W
proof(induct rule: trancl_induct)
  case (base y) with M show ?case by auto
next
  case (step y z)
  with M have "y \<in> worlds (sub_model M w)"
          and "z \<in> worlds (sub_model M w)" by auto
  with M step show ?case by (auto intro: trancl_into_trancl)
qed

lemma sub_model_kripke:
  shows "kripke (sub_model M w)"
  unfolding sub_model_def by auto

lemma sub_model_S5n:
  assumes S5n: "S5n M"
  shows "S5n (sub_model M w)"
proof(rule S5nI, rule equivI)
  show "\<And>n. refl_on (worlds (sub_model M w)) (relations (sub_model M w) n)"
    apply (rule equivE[OF S5nD[OF S5n]])
    by - (rule refl_onI, auto simp add: refl_on_def sub_model_def)
  show "\<And>n. sym (relations (sub_model M w) n)"
    apply (rule equivE[OF S5nD[OF S5n]])
    by (unfold sub_model_def sym_def, auto)
  show "\<And>n. trans (relations (sub_model M w) n)"
    apply (rule equivE[OF S5nD[OF S5n]])
    by - (rule transI, simp add: sub_model_def, unfold trans_def, blast)
qed

lemma sub_model_semantic_equivalence:
  assumes M: "kripke M"
      and w': "w' \<in> worlds (sub_model M w)"
  shows "M, w' \<Turnstile> \<phi> \<longleftrightarrow> (sub_model M w), w' \<Turnstile> \<phi>"
proof -
  { fix w w' assume "w' \<in> worlds (sub_model M w)"
    hence "M, w' \<Turnstile> \<phi> \<longleftrightarrow> (sub_model M w), w' \<Turnstile> \<phi>"
    proof(induct \<phi> arbitrary: w')
      case (Knows a f w') show ?case
      proof
        assume lhs: "M, w' \<Turnstile> Knows a f"
        with Knows show "sub_model M w, w' \<Turnstile> Knows a f" by auto
      next
        assume rhs: "sub_model M w, w' \<Turnstile> Knows a f"
        with M Knows show "M, w' \<Turnstile> Knows a f"
          by (simp, blast)
      qed
    qed (simp_all add: sub_model_def) }
  with w' show ?thesis by simp
qed

lemma sub_model_eq:
  assumes M: "kripke M"
      and M': "kripke M'"
      and "sub_model M w = sub_model M' w"
      and "w' \<in> worlds (sub_model M' w)"
  shows "M, w' \<Turnstile> \<phi> \<longleftrightarrow> M', w' \<Turnstile> \<phi>"
  using assms sub_model_semantic_equivalence[OF M, where w=w]
              sub_model_semantic_equivalence[OF M', where w=w]
  by auto

lemma sub_model_subset_aux:
  assumes R: "\<And>a. relations M a \<inter> T \<times> T = relations M' a \<inter> T \<times> T"
      and T: "(\<Union>a. relations M a)\<^sup>* `` {t} \<subseteq> T"
  shows "(\<Union>x. relations M x)\<^sup>* `` {t} \<subseteq> (\<Union>x. relations M' x)\<^sup>* `` {t}"
proof -
  { fix x assume "(t, x) \<in> (\<Union>x. relations M x)\<^sup>*"
    hence "(t, x) \<in> (\<Union>x. relations M' x)\<^sup>*"
    proof(induct rule: rtrancl_induct)
      case (step y z)
      with R T have "(y, z) \<in> (\<Union>a. relations M' a)"
        by (blast dest: rtrancl_trans)
      with step show ?case by (blast intro: rtrancl_trans)
    qed simp }
  thus ?thesis by blast
qed

lemma sub_model_subset:
  assumes M: "kripke M"
      and M': "kripke M'"
      and R: "\<And>a. relations M a \<inter> T \<times> T = relations M' a \<inter> T \<times> T"
      and tMT: "(\<Union>a. relations M a)\<^sup>* `` {t} \<subseteq> T"
      and tM'T: "(\<Union>a. relations M' a)\<^sup>* `` {t} \<subseteq> T"
      and tM: "t \<in> worlds M"
      and tM': "t \<in> worlds M'"
      and V: "valuation M = valuation M'"
  shows "sub_model M t = sub_model M' t"
proof -
  from tMT tM'T sub_model_subset_aux[OF R] sub_model_subset_aux[OF R[symmetric]]
  have F: "(\<Union>a. relations M a)\<^sup>* `` {t} = (\<Union>a. relations M' a)\<^sup>* `` {t}"
    by - (rule, simp_all)

  from M tMT tM have G: "(\<Union>a. relations M a)\<^sup>* `` {t} \<subseteq> worlds M"
    by (auto dest: kripke_rels_trc_worlds)
  from M' tM'T tM' have H: "(\<Union>a. relations M' a)\<^sup>* `` {t} \<subseteq> worlds M'"
    by (auto dest: kripke_rels_trc_worlds)

  from F G H have WORLDS: "worlds (sub_model M t) = worlds (sub_model M' t)"
    unfolding sub_model_def by (auto iff: Int_absorb1)

  { fix a x y
    assume XY: "(x, y) \<in> relations M a \<inter> (\<Union>x. relations M x)\<^sup>* `` {t} \<times> (\<Union>x. relations M x)\<^sup>* `` {t}"
    from XY tMT
    have "(x, y) \<in> relations M a \<inter> T \<times> T" by blast
    with R
    have "(x, y) \<in> relations M' a \<inter> T \<times> T" by blast
    with F XY tM'T
    have "(x, y) \<in> relations M' a \<inter> (\<Union>x. relations M' x)\<^sup>* `` {t} \<times> (\<Union>x. relations M' x)\<^sup>* `` {t}"
      by blast }
  moreover
  { fix a x y
    assume XY: "(x, y) \<in> relations M' a \<inter> (\<Union>x. relations M' x)\<^sup>* `` {t} \<times> (\<Union>x. relations M' x)\<^sup>* `` {t}"
    from XY tM'T
    have "(x, y) \<in> relations M' a \<inter> T \<times> T" by blast
    with R
    have "(x, y) \<in> relations M a \<inter> T \<times> T" by blast
    with F XY tMT
    have "(x, y) \<in> relations M a \<inter> (\<Union>x. relations M x)\<^sup>* `` {t} \<times> (\<Union>x. relations M x)\<^sup>* `` {t}"
      by blast }
  ultimately
  have RELATIONS: "\<And>a. relations (sub_model M t) a = relations (sub_model M' t) a"
    unfolding sub_model_def
    apply -
    apply (simp (no_asm) add: Int_absorb1 G H)
    apply rule
     apply rule
     apply auto[1]
    apply rule
    apply (case_tac x)
    apply blast
    done

  from WORLDS RELATIONS V show ?thesis
    unfolding sub_model_def by simp
qed

(* Simulations *)

definition
  sim_range :: "('a, 'p, 'w1) KripkeStructure
              \<Rightarrow> ('a, 'p, 'w2) KripkeStructure \<Rightarrow> ('w1 \<Rightarrow> 'w2) \<Rightarrow> bool"
where
  "sim_range M M' f \<equiv> worlds M' = f ` worlds M
                    \<and> (\<forall>a. relations M' a \<subseteq> worlds M' \<times> worlds M')"

definition
  sim_val :: "('a, 'p, 'w1) KripkeStructure
           \<Rightarrow> ('a, 'p, 'w2) KripkeStructure \<Rightarrow> ('w1 \<Rightarrow> 'w2) \<Rightarrow> bool"
where
  "sim_val M M' f \<equiv> \<forall>u \<in> worlds M. valuation M u = valuation M' (f u)"

definition
  sim_f :: "('a, 'p, 'w1) KripkeStructure
         \<Rightarrow> ('a, 'p, 'w2) KripkeStructure \<Rightarrow> ('w1 \<Rightarrow> 'w2) \<Rightarrow> bool"
where
  "sim_f M M' f \<equiv>
     \<forall>a u v. (u, v) \<in> relations M a \<longrightarrow> (f u, f v) \<in> relations M' a"

definition
  sim_r :: "('a, 'p, 'w1) KripkeStructure
         \<Rightarrow> ('a, 'p, 'w2) KripkeStructure \<Rightarrow> ('w1 \<Rightarrow> 'w2) \<Rightarrow> bool"
where
  "sim_r M M' f \<equiv> \<forall>a. \<forall>u \<in> worlds M. \<forall>v'.
              (f u, v') \<in> relations M' a
           \<longrightarrow> (\<exists>v. (u, v) \<in> relations M a \<and> f v = v')"

definition
  "sim M M' f \<equiv> sim_range M M' f
              \<and> sim_val M M' f
              \<and> sim_f M M' f
              \<and> sim_r M M' f"

lemma sim_rangeI[intro]:
  "\<lbrakk> worlds M' = f ` worlds M; (\<And>a. relations M' a \<subseteq> worlds M' \<times> worlds M') \<rbrakk>
     \<Longrightarrow> sim_range M M' f"
  unfolding sim_range_def by simp

lemma sim_valI[intro]:
  "(\<And>u. u \<in> worlds M \<Longrightarrow> valuation M u = valuation M' (f u))
   \<Longrightarrow> sim_val M M' f"
  unfolding sim_val_def by simp

lemma sim_fI[intro]:
  "(\<And>a u v. (u, v) \<in> relations M a \<Longrightarrow> (f u, f v) \<in> relations M' a)
   \<Longrightarrow> sim_f M M' f"
  unfolding sim_f_def by simp

lemma sim_fD:
  "\<lbrakk> (u, v) \<in> relations M a; sim M M' f \<rbrakk>
     \<Longrightarrow> (f u, f v) \<in> relations M' a"
  unfolding sim_def sim_f_def by blast

lemma sim_rI[intro]:
  "(\<And>a u v'.
    \<lbrakk>u \<in> worlds M; (f u, v') \<in> relations M' a\<rbrakk>
    \<Longrightarrow> (\<exists>v. (u, v) \<in> relations M a \<and> f v = v'))
  \<Longrightarrow> sim_r M M' f"
  unfolding sim_r_def by simp

lemma sim_rD:
  "\<lbrakk> (f u, v') \<in> relations M' a; sim M M' f; u \<in> worlds M \<rbrakk>
     \<Longrightarrow> (\<exists>v. (u, v) \<in> relations M a \<and> f v = v')"
  unfolding sim_def sim_r_def by blast

lemma simI[intro]:
  "\<lbrakk> sim_range M M' f; sim_val M M' f; sim_f M M' f; sim_r M M' f \<rbrakk>
     \<Longrightarrow> sim M M' f"
  unfolding sim_def by simp

lemma sim_f_trc:
  assumes uv': "(u, v) \<in> (\<Union>a. relations M a)\<^sup>*"
      and s: "sim M M' f"
  shows "(f u, f v) \<in> (\<Union>a. relations M' a)\<^sup>*"
  using assms
  by - ( induct rule: rtrancl_induct[OF uv']
       , auto dest: sim_fD intro: rtrancl_into_rtrancl )

lemma sim_r_trc:
  assumes s: "sim M M' f"
      and fuv': "(f u, v') \<in> (\<Union>a. relations M' a)\<^sup>*"
      and M: "kripke M"
      and u: "u \<in> worlds M"
  obtains v
    where "f v = v'"
      and "(u, v) \<in> (\<Union>a. relations M a)\<^sup>*"
proof -
  assume E: "\<And>v. \<lbrakk>f v = v'; (u, v) \<in> (\<Union>a. relations M a)\<^sup>*\<rbrakk> \<Longrightarrow> thesis"
  from fuv' have "\<exists>v. f v = v' \<and> (u, v) \<in> (\<Union>a. relations M a)\<^sup>*"
  proof(induct rule: rtrancl_induct)
    case base show ?case by blast
  next
    case (step v' w')
    hence fuv': "(f u, v') \<in> (\<Union>a. relations M' a)\<^sup>*"
      and v'w': "(v', w') \<in> (\<Union>a. relations M' a)" by fast+
    from step
    obtain v where vv': "f v = v'"
               and uv: "(u, v) \<in> (\<Union>a. relations M a)\<^sup>*"
      by blast
    from s v'w' vv' kripke_rels_trc_worlds[OF uv u M]
    obtain w where ww': "f w = w'"
               and vw: "(v, w) \<in> (\<Union>a. relations M a)"
      by (blast dest: sim_rD)
    from uv vw ww' show ?case by (blast intro: rtrancl_trans)
  qed
  with E show thesis by blast
qed

text{* FIXME Simulations commute with the transitive-reflexive closure
of the Kripke structure relations in the obvious way. *}

lemma sim_trc_commute:
  assumes M: "kripke M"
      and s: "sim M M' f"
      and t: "t \<in> worlds M"
  shows "f ` ((\<Union>a. relations M a)\<^sup>* `` {t})
       = (\<Union>a. relations M' a)\<^sup>* `` {f t}" (is "?lhs = ?rhs")
proof
  from M s show "?lhs \<subseteq> ?rhs" by (auto intro: sim_f_trc)
next
  from M s t show "?rhs \<subseteq> ?lhs" by (auto elim: sim_r_trc)
qed

lemma sim_kripke: "\<lbrakk> sim M M' f; kripke M \<rbrakk> \<Longrightarrow> kripke M'"
  unfolding sim_def sim_range_def by (rule kripkeI, blast)

(* Simulations preserve $S5_n$ structure. *)

lemma sim_S5n:
  assumes S5n: "S5n M"
      and sim: "sim M M' f"
  shows "S5n M'"
proof(rule S5nI, rule equivI)
  fix a from S5n sim show "refl_on (worlds M') (relations M' a)"
     using sim_kripke S5n_kripke
     unfolding S5n_def equiv_def sim_def sim_f_def sim_range_def
     by - (rule refl_onI, (simp, blast dest: refl_onD)+)
next
  fix a
  { fix u v assume uv: "(u, v) \<in> relations M' a"
    from sim uv
    obtain u' where uw: "u' \<in> worlds M"
                and fu: "u = f u'"
      unfolding sim_def sim_range_def by bestsimp
    from sim uv fu uw
    obtain v' where u'v': "(u', v') \<in> relations M a"
                and fv: "v = f v'"
      unfolding sim_def sim_r_def sim_range_def by best
    from S5n u'v' have "(v', u') \<in> relations M a"
      unfolding S5n_def equiv_def by (blast dest: symD)
    with sim fu fv have "(v, u) \<in> relations M' a"
      unfolding sim_def sim_f_def by simp }
  thus "sym (relations M' a)" by (blast intro: symI)
next
  fix a
  { fix x y z
    assume xy: "(x, y) \<in> relations M' a"
       and yz: "(y, z) \<in> relations M' a"
    from sim xy
    obtain x' where xw: "x' \<in> worlds M"
                and fx: "x = f x'"
      unfolding sim_def sim_range_def by bestsimp
    from sim xy fx xw
    obtain y' where x'y': "(x', y') \<in> relations M a"
                and fy: "y = f y'"
      unfolding sim_def sim_r_def sim_range_def by best
    from S5n sim yz fy x'y'
    obtain z' where y'z': "(y', z') \<in> relations M a"
                and fz: "z = f z'"
      unfolding sim_def sim_r_def sim_range_def by best
    from S5n x'y' y'z' have "(x', z') \<in> relations M a"
      unfolding S5n_def equiv_def by (blast dest: transD)
    with sim fx fy fz have "(x, z) \<in> relations M' a"
      unfolding sim_def sim_f_def by simp }
  thus "trans (relations M' a)" by (blast intro: transI)
qed

lemma sim_semantic_equivalence:
  assumes M: "kripke M" and s: "sim M M' f" and u: "u \<in> worlds M"
  shows "M, u \<Turnstile> \<phi> \<longleftrightarrow> M', f u \<Turnstile> \<phi>"
using u
proof(induct \<phi> arbitrary: u)
  case (Knows a \<psi> u)
  hence u: "u \<in> worlds M" by fast
  show ?case
  proof
    assume lhs: "M, u \<Turnstile> Knows a \<psi>"
    { fix v' assume "(f u, v') \<in> relations M' a"
      with s u obtain v where uv:  "(u, v) \<in> relations M a"
                          and vv': "f v = v'"
        by (blast dest: sim_rD)
      from lhs uv have "M, v \<Turnstile> \<psi>" by simp
      with kripke_rels_worlds[OF uv M] vv' Knows
      have "M', v' \<Turnstile> \<psi>" by auto }
    thus "M', f u \<Turnstile> Knows a \<psi>" by simp
  next
    assume rhs: "M', f u \<Turnstile> Knows a \<psi>"
    { fix v assume uv: "(u, v) \<in> relations M a"
      with s have "(f u, f v) \<in> relations M' a"
        by (blast dest: sim_fD)
      with rhs have "M', f v \<Turnstile> \<psi>" by simp
      with kripke_rels_worlds[OF uv M] Knows s
      have "M, v \<Turnstile> \<psi>" by auto }
    thus "M, u \<Turnstile> Knows a \<psi>" by simp
  qed
qed (insert s,
     auto simp add: sim_range_def sim_def sim_val_def)

end

