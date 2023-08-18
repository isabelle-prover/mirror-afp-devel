(*  Title:      Stateful_Protocol_Model.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section\<open>Stateful Protocol Model\<close>
theory Stateful_Protocol_Model
  imports Stateful_Protocol_Composition_and_Typing.Stateful_Compositionality
          Transactions Term_Abstraction
begin

subsection \<open>Locale Setup\<close>
locale stateful_protocol_model =
  fixes arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets,'lbl) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  assumes Ana\<^sub>f_assm1: "\<forall>f. let (K, M) = Ana\<^sub>f f in (\<forall>k \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K).
      is_Fun k \<longrightarrow> (is_Fu (the_Fun k)) \<and> length (args k) = arity\<^sub>f (the_Fu (the_Fun k)))"
    and Ana\<^sub>f_assm2: "\<forall>f. let (K, M) = Ana\<^sub>f f in \<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K) \<union> set M. i < arity\<^sub>f f"
    and public\<^sub>f_assm: "\<forall>f. arity\<^sub>f f > (0::nat) \<longrightarrow> public\<^sub>f f"
    and \<Gamma>\<^sub>f_assm: "\<forall>f. arity\<^sub>f f = (0::nat) \<longrightarrow> \<Gamma>\<^sub>f f \<noteq> None"
    and label_witness_assm: "label_witness1 \<noteq> label_witness2"
begin

lemma Ana\<^sub>f_assm1_alt: 
  assumes "Ana\<^sub>f f = (K,M)" "k \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K)"
  shows "(\<exists>x. k = Var x) \<or> (\<exists>h T. k = Fun (Fu h) T \<and> length T = arity\<^sub>f h)"
proof (cases k)
  case (Fun g T)
  let ?P = "\<lambda>k. is_Fun k \<longrightarrow> is_Fu (the_Fun k) \<and> length (args k) = arity\<^sub>f (the_Fu (the_Fun k))"
  let ?Q = "\<lambda>K M. \<forall>k \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K). ?P k"

  have "?Q (fst (Ana\<^sub>f f)) (snd (Ana\<^sub>f f))" using Ana\<^sub>f_assm1 split_beta[of ?Q "Ana\<^sub>f f"] by meson
  hence "?Q K M" using assms(1) by simp
  hence "?P k" using assms(2) by blast
  thus ?thesis using Fun by (cases g) auto
qed simp

lemma Ana\<^sub>f_assm2_alt:
  assumes "Ana\<^sub>f f = (K,M)" "i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K) \<union> set M"
  shows "i < arity\<^sub>f f"
using Ana\<^sub>f_assm2 assms by fastforce


subsection \<open>Definitions\<close>
fun arity where
  "arity (Fu f) = arity\<^sub>f f"
| "arity (Set s) = arity\<^sub>s s"
| "arity (Val _) = 0"
| "arity (Abs _) = 0"
| "arity Pair = 2"
| "arity (Attack _) = 0"
| "arity OccursFact = 2"
| "arity OccursSec = 0"
| "arity (PubConst _ _) = 0"

fun public where
  "public (Fu f) = public\<^sub>f f"
| "public (Set s) = (arity\<^sub>s s > 0)"
| "public (Val n) = False"
| "public (Abs _) = False"
| "public Pair = True"
| "public (Attack _) = False"
| "public OccursFact = True"
| "public OccursSec = False"
| "public (PubConst _ _) = True"

fun Ana where
  "Ana (Fun (Fu f) T) = (
    if arity\<^sub>f f = length T \<and> arity\<^sub>f f > 0
    then let (K,M) = Ana\<^sub>f f in (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M)
    else ([], []))"
| "Ana _ = ([], [])"

definition \<Gamma>\<^sub>v where
  "\<Gamma>\<^sub>v v \<equiv> (
    if (\<forall>t \<in> subterms (fst v).
          case t of (TComp f T) \<Rightarrow> arity f > 0 \<and> arity f = length T | _ \<Rightarrow> True)
    then fst v
    else TAtom Bottom)"

fun \<Gamma> where
  "\<Gamma> (Var v) = \<Gamma>\<^sub>v v"
| "\<Gamma> (Fun f T) = (
    if arity f = 0
    then case f of
      (Fu g) \<Rightarrow> TAtom (case \<Gamma>\<^sub>f g of Some a \<Rightarrow> Atom a | None \<Rightarrow> Bottom)
    | (Val _) \<Rightarrow> TAtom Value
    | (Abs _) \<Rightarrow> TAtom AbsValue
    | (Set _) \<Rightarrow> TAtom SetType
    | (Attack _) \<Rightarrow> TAtom AttackType
    | OccursSec \<Rightarrow> TAtom OccursSecType
    | (PubConst a _) \<Rightarrow> TAtom a
    | _ \<Rightarrow> TAtom Bottom
    else TComp f (map \<Gamma> T))"

lemma \<Gamma>_consts_simps[simp]:
  "arity\<^sub>f g = 0 \<Longrightarrow> \<Gamma> (Fun (Fu g) []::('fun,'atom,'sets,'lbl) prot_term)
                    = TAtom (case \<Gamma>\<^sub>f g of Some a \<Rightarrow> Atom a | None \<Rightarrow> Bottom)"
  "\<Gamma> (Fun (Val n) []::('fun,'atom,'sets,'lbl) prot_term) = TAtom Value"
  "\<Gamma> (Fun (Abs b) []::('fun,'atom,'sets,'lbl) prot_term) = TAtom AbsValue"
  "arity\<^sub>s s = 0 \<Longrightarrow> \<Gamma> (Fun (Set s) []::('fun,'atom,'sets,'lbl) prot_term) = TAtom SetType"
  "\<Gamma> (Fun (Attack x) []::('fun,'atom,'sets,'lbl) prot_term) = TAtom AttackType"
  "\<Gamma> (Fun OccursSec []::('fun,'atom,'sets,'lbl) prot_term) = TAtom OccursSecType"
  "\<Gamma> (Fun (PubConst a t) []::('fun,'atom,'sets,'lbl) prot_term) = TAtom a"
by simp+

lemma \<Gamma>_Fu_simps[simp]:
  "arity\<^sub>f f \<noteq> 0 \<Longrightarrow> \<Gamma> (Fun (Fu f) T) = TComp (Fu f) (map \<Gamma> T)" (is "?A1 \<Longrightarrow> ?A2")
  "arity\<^sub>f f = 0 \<Longrightarrow> \<Gamma>\<^sub>f f = Some a \<Longrightarrow> \<Gamma> (Fun (Fu f) T) = TAtom (Atom a)" (is "?B1 \<Longrightarrow> ?B2 \<Longrightarrow> ?B3")
  "arity\<^sub>f f = 0 \<Longrightarrow> \<Gamma>\<^sub>f f = None \<Longrightarrow> \<Gamma> (Fun (Fu f) T) = TAtom Bottom" (is "?C1 \<Longrightarrow> ?C2 \<Longrightarrow> ?C3")
  "\<Gamma> (Fun (Fu f) T) \<noteq> TAtom Value" (is ?D)
  "\<Gamma> (Fun (Fu f) T) \<noteq> TAtom AttackType" (is ?E)
  "\<Gamma> (Fun (Fu f) T) \<noteq> TAtom OccursSecType" (is ?F)
proof -
  show "?A1 \<Longrightarrow> ?A2" by simp
  show "?B1 \<Longrightarrow> ?B2 \<Longrightarrow> ?B3" by simp
  show "?C1 \<Longrightarrow> ?C2 \<Longrightarrow> ?C3" by simp
  show ?D by (cases "\<Gamma>\<^sub>f f") simp_all
  show ?E by (cases "\<Gamma>\<^sub>f f") simp_all
  show ?F by (cases "\<Gamma>\<^sub>f f") simp_all
qed

lemma \<Gamma>_Set_simps[simp]:
  "arity\<^sub>s s \<noteq> 0 \<Longrightarrow> \<Gamma> (Fun (Set s) T) = TComp (Set s) (map \<Gamma> T)"
  "\<Gamma> (Fun (Set s) T) = TAtom SetType \<or> \<Gamma> (Fun (Set s) T) = TComp (Set s) (map \<Gamma> T)"
  "\<Gamma> (Fun (Set s) T) \<noteq> TAtom Value"
  "\<Gamma> (Fun (Set s) T) \<noteq> TAtom (Atom a)"
  "\<Gamma> (Fun (Set s) T) \<noteq> TAtom AttackType"
  "\<Gamma> (Fun (Set s) T) \<noteq> TAtom OccursSecType"
  "\<Gamma> (Fun (Set s) T) \<noteq> TAtom Bottom"
by auto


subsection \<open>Locale Interpretations\<close>
lemma Ana_Fu_cases:
  assumes "Ana (Fun f T) = (K,M)"
    and "f = Fu g"
    and "Ana\<^sub>f g = (K',M')"
  shows "(K,M) = (if arity\<^sub>f g = length T \<and> arity\<^sub>f g > 0
                  then (K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M')
                  else ([],[]))" (is ?A)
    and "(K,M) = (K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M') \<or> (K,M) = ([],[])" (is ?B)
proof -
  show ?A using assms by (cases "arity\<^sub>f g = length T \<and> arity\<^sub>f g > 0") auto
  thus ?B by metis
qed

lemma Ana_Fu_intro:
  assumes "arity\<^sub>f f = length T" "arity\<^sub>f f > 0"
    and "Ana\<^sub>f f = (K',M')"
  shows "Ana (Fun (Fu f) T) = (K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M')"
using assms by simp

lemma Ana_Fu_elim:
  assumes "Ana (Fun f T) = (K,M)"
    and "f = Fu g"
    and "Ana\<^sub>f g = (K',M')"
    and "(K,M) \<noteq> ([],[])"
  shows "arity\<^sub>f g = length T" (is ?A)
    and "(K,M) = (K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M')" (is ?B)
proof -
  show ?A using assms by force
  moreover have "arity\<^sub>f g > 0" using assms by force
  ultimately show ?B using assms by auto
qed

lemma Ana_nonempty_inv:
  assumes "Ana t \<noteq> ([],[])"
  shows "\<exists>f T. t = Fun (Fu f) T \<and> arity\<^sub>f f = length T \<and> arity\<^sub>f f > 0 \<and>
               (\<exists>K M. Ana\<^sub>f f = (K, M) \<and> Ana t = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M))"
using assms
proof (induction t rule: Ana.induct)
  case (1 f T)
  hence *: "arity\<^sub>f f = length T" "0 < arity\<^sub>f f"
           "Ana (Fun (Fu f) T) = (case Ana\<^sub>f f of (K, M) \<Rightarrow> (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M))"
    using Ana.simps(1)[of f T] unfolding Let_def by metis+

  obtain K M where **: "Ana\<^sub>f f = (K, M)" by (metis surj_pair)
  hence "Ana (Fun (Fu f) T) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M)" using *(3) by simp
  thus ?case using ** *(1,2) by blast
qed simp_all

lemma assm1:
  assumes "Ana t = (K,M)"
  shows "fv\<^sub>s\<^sub>e\<^sub>t (set K) \<subseteq> fv t"
using assms
proof (induction t rule: term.induct)
  case (Fun f T)
  have aux: "fv\<^sub>s\<^sub>e\<^sub>t (set K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) T) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (set T)"
    when K: "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K). i < length T"
    for K::"(('fun,'atom,'sets,'lbl) prot_fun, nat) term list"
  proof
    fix x assume "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) T)"
    then obtain k where k: "k \<in> set K" "x \<in> fv (k \<cdot> (!) T)" by moura
    have "\<forall>i \<in> fv k. i < length T" using K k(1) by simp
    thus "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set T)"
      by (metis (no_types, lifting) k(2) contra_subsetD fv_set_mono image_subsetI nth_mem
                                    subst_apply_fv_unfold)
  qed

  { fix g assume f: "f = Fu g" and K: "K \<noteq> []"
    obtain K' M' where *: "Ana\<^sub>f g = (K',M')" by moura
    have "(K, M) \<noteq> ([], [])" using K by simp
    hence "(K, M) = (K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M')" "arity\<^sub>f g = length T"
      using Ana_Fu_cases(1)[OF Fun.prems f *]
      by presburger+
    hence ?case using aux[of K'] Ana\<^sub>f_assm2_alt[OF *] by auto
  } thus ?case using Fun by (cases f) fastforce+
qed simp

lemma assm2:
  assumes "Ana t = (K,M)"
  and "\<And>g S'. Fun g S' \<sqsubseteq> t \<Longrightarrow> length S' = arity g"
  and "k \<in> set K"
  and "Fun f T' \<sqsubseteq> k"
  shows "length T' = arity f"
using assms
proof (induction t rule: term.induct)
  case (Fun g T)
  obtain h where 2: "g = Fu h"
    using Fun.prems(1,3) by (cases g) auto
  obtain K' M' where 1: "Ana\<^sub>f h = (K',M')" by moura
  have "(K,M) \<noteq> ([],[])" using Fun.prems(3) by auto
  hence "(K,M) = (K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) M')"
        "\<And>i. i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K') \<union> set M' \<Longrightarrow> i < length T"
    using Ana_Fu_cases(1)[OF Fun.prems(1) 2 1] Ana\<^sub>f_assm2_alt[OF 1]
    by presburger+
  hence "K = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T" and 3: "\<forall>i\<in>fv\<^sub>s\<^sub>e\<^sub>t (set K'). i < length T" by simp_all
  then obtain k' where k': "k' \<in> set K'" "k = k' \<cdot> (!) T" using Fun.prems(3) by moura
  hence 4: "Fun f T' \<in> subterms (k' \<cdot> (!) T)" "fv k' \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (set K')"
    using Fun.prems(4) by auto
  show ?case
  proof (cases "\<exists>i \<in> fv k'. Fun f T' \<in> subterms (T ! i)")
    case True
    hence "Fun f T' \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set T)" using k' Fun.prems(4) 3 by auto
    thus ?thesis using Fun.prems(2) by auto
  next
    case False
    then obtain S where "Fun f S \<in> subterms k'" "Fun f T' = Fun f S \<cdot> (!) T"
      using k'(2) Fun.prems(4) subterm_subst_not_img_subterm by force
    thus ?thesis using Ana\<^sub>f_assm1_alt[OF 1, of "Fun f S"] k'(1) by (cases f) auto
  qed
qed simp

lemma assm4:
  assumes "Ana (Fun f T) = (K, M)"
  shows "set M \<subseteq> set T"
using assms
proof (cases f)
  case (Fu g)
  obtain K' M' where *: "Ana\<^sub>f g = (K',M')" by moura
  have "M = [] \<or> (arity\<^sub>f g = length T \<and> M = map ((!) T) M')"
    using Ana_Fu_cases(1)[OF assms Fu *]
    by (meson prod.inject)
  thus ?thesis using Ana\<^sub>f_assm2_alt[OF *] by auto
qed auto

lemma assm5: "Ana t = (K,M) \<Longrightarrow> K \<noteq> [] \<or> M \<noteq> [] \<Longrightarrow> Ana (t \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>, M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
proof (induction t rule: term.induct)
  case (Fun f T) thus ?case
  proof (cases f)
    case (Fu g)
    obtain K' M' where *: "Ana\<^sub>f g = (K',M')" by moura
    have **: "K = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T" "M = map ((!) T) M'"
             "arity\<^sub>f g = length T" "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K') \<union> set M'. i < arity\<^sub>f g" "0 < arity\<^sub>f g"
      using Fun.prems(2) Ana_Fu_cases(1)[OF Fun.prems(1) Fu *] Ana\<^sub>f_assm2_alt[OF *]
      by (meson prod.inject)+

    have ***: "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K'). i < length T" "\<forall>i \<in> set M'. i < length T" using **(3,4) by auto
    
    have "K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta> = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) (map (\<lambda>t. t \<cdot> \<delta>) T)"
         "M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta> = map ((!) (map (\<lambda>t. t \<cdot> \<delta>) T)) M'"
      using subst_idx_map[OF ***(2), of \<delta>]
            subst_idx_map'[OF ***(1), of \<delta>]
            **(1,2)
      by fast+
    thus ?thesis using Fu * **(3,5) by auto
  qed auto
qed simp

sublocale intruder_model arity public Ana
apply unfold_locales
by (metis assm1, metis assm2, rule Ana.simps, metis assm4, metis assm5)

adhoc_overloading INTRUDER_SYNTH intruder_synth
adhoc_overloading INTRUDER_DEDUCT intruder_deduct

lemma assm6: "arity c = 0 \<Longrightarrow> \<exists>a. \<forall>X. \<Gamma> (Fun c X) = TAtom a" by (cases c) auto

lemma assm7: "0 < arity f \<Longrightarrow> \<Gamma> (Fun f T) = TComp f (map \<Gamma> T)" by auto

lemma assm8: "infinite {c. \<Gamma> (Fun c []::('fun,'atom,'sets,'lbl) prot_term) = TAtom a \<and> public c}"
  (is "?P a")
proof -
  let ?T = "\<lambda>f. (range f)::('fun,'atom,'sets,'lbl) prot_fun set"
  let ?A = "\<lambda>f. \<forall>x::nat \<in> UNIV. \<forall>y::nat \<in> UNIV. (f x = f y) = (x = y)"
  let ?B = "\<lambda>f. \<forall>x::nat \<in> UNIV. f x \<in> ?T f"
  let ?C = "\<lambda>f. \<forall>y::('fun,'atom,'sets,'lbl) prot_fun \<in> ?T f. \<exists>x \<in> UNIV. y = f x"
  let ?D = "\<lambda>f b. ?T f \<subseteq> {c. \<Gamma> (Fun c []::('fun,'atom,'sets,'lbl) prot_term) = TAtom b \<and> public c}"

  have sub_lmm: "?P b" when "?A f" "?C f" "?C f" "?D f b" for b f
  proof -
    have "\<exists>g::nat \<Rightarrow> ('fun,'atom,'sets,'lbl) prot_fun. bij_betw g UNIV (?T f)"
      using bij_betwI'[of UNIV f "?T f"] that(1,2,3) by blast
    hence "infinite (?T f)" by (metis nat_not_finite bij_betw_finite)
    thus ?thesis using infinite_super[OF that(4)] by blast
  qed

  show ?thesis
  proof (cases a)
    case (Atom b) thus ?thesis using sub_lmm[of "PubConst (Atom b)" a] by force
  next
    case Value thus ?thesis using sub_lmm[of "PubConst Value" a] by force
  next
    case SetType thus ?thesis using sub_lmm[of "PubConst SetType" a] by fastforce
  next
    case AttackType thus ?thesis using sub_lmm[of "PubConst AttackType" a] by fastforce
  next
    case Bottom thus ?thesis using sub_lmm[of "PubConst Bottom" a] by fastforce
  next
    case OccursSecType thus ?thesis using sub_lmm[of "PubConst OccursSecType" a] by fastforce
  next
    case AbsValue thus ?thesis using sub_lmm[of "PubConst AbsValue" a] by force
  qed
qed

lemma assm9: "TComp f T \<sqsubseteq> \<Gamma> t \<Longrightarrow> arity f > 0"
proof (induction t rule: term.induct)
  case (Var x)
  hence "\<Gamma> (Var x) \<noteq> TAtom Bottom" by force
  hence "\<forall>t \<in> subterms (fst x). case t of
            TComp f T \<Rightarrow> arity f > 0 \<and> arity f = length T
          | _ \<Rightarrow> True"
    using Var \<Gamma>.simps(1)[of x] unfolding \<Gamma>\<^sub>v_def by meson
  thus ?case using Var by (fastforce simp add: \<Gamma>\<^sub>v_def)
next
  case (Fun g S)
  have "arity g \<noteq> 0" using Fun.prems Var_subtermeq assm6 by force
  thus ?case using Fun by (cases "TComp f T = TComp g (map \<Gamma> S)") auto
qed

lemma assm10: "wf\<^sub>t\<^sub>r\<^sub>m (\<Gamma> (Var x))"
unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by (auto simp add: \<Gamma>\<^sub>v_def)

lemma assm11: "arity f > 0 \<Longrightarrow> public f" using public\<^sub>f_assm by (cases f) auto

lemma assm12: "\<Gamma> (Var (\<tau>, n)) = \<Gamma> (Var (\<tau>, m))" by (simp add: \<Gamma>\<^sub>v_def)

lemma assm13: "arity c = 0 \<Longrightarrow> Ana (Fun c T) = ([],[])" by (cases c) simp_all

lemma assm14:
  assumes "Ana (Fun f T) = (K,M)"
  shows "Ana (Fun f T \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>, M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
proof -
  show ?thesis
  proof (cases "(K, M) = ([],[])")
    case True
    { fix g assume f: "f = Fu g"
      obtain K' M' where "Ana\<^sub>f g = (K',M')" by moura
      hence ?thesis using assms f True by auto
    } thus ?thesis using True assms by (cases f) auto
  next
    case False
    then obtain g where **: "f = Fu g" using assms by (cases f) auto
    obtain K' M' where *: "Ana\<^sub>f g = (K',M')" by moura
    have ***: "K = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T" "M = map ((!) T) M'" "arity\<^sub>f g = length T"
              "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K') \<union> set M'. i < arity\<^sub>f g"
      using Ana_Fu_cases(1)[OF assms ** *] False Ana\<^sub>f_assm2_alt[OF *]
      by (meson prod.inject)+
    have ****: "\<forall>i\<in>fv\<^sub>s\<^sub>e\<^sub>t (set K'). i < length T" "\<forall>i\<in>set M'. i < length T" using ***(3,4) by auto
    have "K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta> = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) (map (\<lambda>t. t \<cdot> \<delta>) T)"
         "M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta> = map ((!) (map (\<lambda>t. t \<cdot> \<delta>) T)) M'"
      using subst_idx_map[OF ****(2), of \<delta>]
            subst_idx_map'[OF ****(1), of \<delta>]
            ***(1,2)
      by auto
    thus ?thesis using assms * ** ***(3) by auto
  qed
qed

sublocale labeled_stateful_typing' arity public Ana \<Gamma> Pair label_witness1 label_witness2
  apply unfold_locales
  subgoal by (metis assm6)
  subgoal by (metis assm7)
  subgoal by (metis assm9)
  subgoal by (rule assm10)
  subgoal by (metis assm12)
  subgoal by (metis assm13)
  subgoal by (metis assm14)
  subgoal by (rule label_witness_assm)
  subgoal by (rule arity.simps(5))
  subgoal by (metis assm14)
  subgoal by (metis assm8)
  subgoal by (metis assm11)
  done


subsection \<open>The Protocol Transition System, Defined in Terms of the Reachable Constraints\<close>
definition transaction_decl_subst where
  "transaction_decl_subst (\<xi>::('fun,'atom,'sets,'lbl) prot_subst) T \<equiv>
    subst_domain \<xi> = fst ` set (transaction_decl T ()) \<and>
    (\<forall>(x,cs) \<in> set (transaction_decl T ()). \<exists>c \<in> cs.
      \<xi> x = Fun (Fu c) [] \<and>
      arity (Fu c::('fun,'atom,'sets,'lbl) prot_fun) = 0) \<and>
    wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<xi>"

definition transaction_fresh_subst where
  "transaction_fresh_subst \<sigma> T M \<equiv>
    subst_domain \<sigma> = set (transaction_fresh T) \<and>
    (\<forall>t \<in> subst_range \<sigma>. \<exists>c. t = Fun c [] \<and> \<not>public c \<and> arity c = 0) \<and>
    (\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t M) \<and>
    (\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms_transaction T)) \<and>
    wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma> \<and> inj_on \<sigma> (subst_domain \<sigma>)"

(* NB: We need the protocol P as a parameter for this definition---even though we will only apply \<alpha>
       to a single transaction T of P---because we have to ensure that \<alpha>(fv(T)) is disjoint from
       the bound variables of P and \<A>. *)
definition transaction_renaming_subst where
  "transaction_renaming_subst \<alpha> P X \<equiv>
    \<exists>n \<ge> max_var_set (\<Union>(vars_transaction ` set P) \<union> X). \<alpha> = var_rename n"

definition (in intruder_model) constraint_model where
  "constraint_model \<I> \<A> \<equiv> 
    constr_sem_stateful \<I> (unlabel \<A>) \<and>
    interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I> \<and>
    wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"

definition (in typed_model) welltyped_constraint_model where
  "welltyped_constraint_model \<I> \<A> \<equiv> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I> \<and> constraint_model \<I> \<A>"

text \<open>
  The set of symbolic constraints reachable in any symbolic run of the protocol \<open>P\<close>.
  
  \<open>\<xi>\<close> instantiates the "declared variables" of transaction \<open>T\<close> with ground terms.
  \<open>\<sigma>\<close> instantiates the fresh variables of transaction \<open>T\<close> with fresh terms.
  \<open>\<alpha>\<close> is a variable-renaming whose range consists of fresh variables.
\<close>
inductive_set reachable_constraints::
  "('fun,'atom,'sets,'lbl) prot \<Rightarrow> ('fun,'atom,'sets,'lbl) prot_constr set"
  for P::"('fun,'atom,'sets,'lbl) prot"
where
  init[simp]:
  "[] \<in> reachable_constraints P"
| step:
  "\<lbrakk>\<A> \<in> reachable_constraints P;
    T \<in> set P;
    transaction_decl_subst \<xi> T;
    transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>);
    transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)
   \<rbrakk> \<Longrightarrow> \<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<in> reachable_constraints P"


subsection \<open>Minor Lemmata\<close>
lemma \<Gamma>\<^sub>v_TAtom[simp]: "\<Gamma>\<^sub>v (TAtom a, n) = TAtom a"
unfolding \<Gamma>\<^sub>v_def by simp

lemma \<Gamma>\<^sub>v_TAtom':
  assumes "a \<noteq> Bottom"
  shows "\<Gamma>\<^sub>v (\<tau>, n) = TAtom a \<longleftrightarrow> \<tau> = TAtom a"
proof
  assume "\<Gamma>\<^sub>v (\<tau>, n) = TAtom a"
  thus "\<tau> = TAtom a" by (metis (no_types, lifting) assms \<Gamma>\<^sub>v_def fst_conv term.inject(1)) 
qed simp

lemma \<Gamma>\<^sub>v_TAtom_inv:
  "\<Gamma>\<^sub>v x = TAtom (Atom a) \<Longrightarrow> \<exists>m. x = (TAtom (Atom a), m)"
  "\<Gamma>\<^sub>v x = TAtom Value \<Longrightarrow> \<exists>m. x = (TAtom Value, m)"
  "\<Gamma>\<^sub>v x = TAtom SetType \<Longrightarrow> \<exists>m. x = (TAtom SetType, m)"
  "\<Gamma>\<^sub>v x = TAtom AttackType \<Longrightarrow> \<exists>m. x = (TAtom AttackType, m)"
  "\<Gamma>\<^sub>v x = TAtom OccursSecType \<Longrightarrow> \<exists>m. x = (TAtom OccursSecType, m)"
by (metis \<Gamma>\<^sub>v_TAtom' surj_pair prot_atom.distinct(7),
    metis \<Gamma>\<^sub>v_TAtom' surj_pair prot_atom.distinct(18),
    metis \<Gamma>\<^sub>v_TAtom' surj_pair prot_atom.distinct(26),
    metis \<Gamma>\<^sub>v_TAtom' surj_pair prot_atom.distinct(32),
    metis \<Gamma>\<^sub>v_TAtom' surj_pair prot_atom.distinct(38))

lemma \<Gamma>\<^sub>v_TAtom'':
  "(fst x = TAtom (Atom a)) = (\<Gamma>\<^sub>v x = TAtom (Atom a))" (is "?A = ?A'")
  "(fst x = TAtom Value) = (\<Gamma>\<^sub>v x = TAtom Value)" (is "?B = ?B'")
  "(fst x = TAtom SetType) = (\<Gamma>\<^sub>v x = TAtom SetType)" (is "?C = ?C'")
  "(fst x = TAtom AttackType) = (\<Gamma>\<^sub>v x = TAtom AttackType)" (is "?D = ?D'")
  "(fst x = TAtom OccursSecType) = (\<Gamma>\<^sub>v x = TAtom OccursSecType)" (is "?E = ?E'")
proof -
  have 1: "?A \<Longrightarrow> ?A'" "?B \<Longrightarrow> ?B'" "?C \<Longrightarrow> ?C'" "?D \<Longrightarrow> ?D'" "?E \<Longrightarrow> ?E'"
    by (metis \<Gamma>\<^sub>v_TAtom prod.collapse)+

  have 2: "?A' \<Longrightarrow> ?A" "?B' \<Longrightarrow> ?B" "?C' \<Longrightarrow> ?C" "?D' \<Longrightarrow> ?D" "?E' \<Longrightarrow> ?E"
    using \<Gamma>\<^sub>v_TAtom \<Gamma>\<^sub>v_TAtom_inv(1) apply fastforce
    using \<Gamma>\<^sub>v_TAtom \<Gamma>\<^sub>v_TAtom_inv(2) apply fastforce
    using \<Gamma>\<^sub>v_TAtom \<Gamma>\<^sub>v_TAtom_inv(3) apply fastforce
    using \<Gamma>\<^sub>v_TAtom \<Gamma>\<^sub>v_TAtom_inv(4) apply fastforce
    using \<Gamma>\<^sub>v_TAtom \<Gamma>\<^sub>v_TAtom_inv(5) by fastforce

  show "?A = ?A'" "?B = ?B'" "?C = ?C'" "?D = ?D'" "?E = ?E'"
    using 1 2 by metis+
qed

lemma \<Gamma>\<^sub>v_Var_image:
  "\<Gamma>\<^sub>v ` X = \<Gamma> ` Var ` X"
by force

lemma \<Gamma>_Fu_const:
  assumes "arity\<^sub>f g = 0"
  shows "\<exists>a. \<Gamma> (Fun (Fu g) T) = TAtom (Atom a)"
proof -
  have "\<Gamma>\<^sub>f g \<noteq> None" using assms \<Gamma>\<^sub>f_assm by blast
  thus ?thesis using assms by force
qed

lemma Fun_Value_type_inv:
  fixes T::"('fun,'atom,'sets,'lbl) prot_term list"
  assumes "\<Gamma> (Fun f T) = TAtom Value"
  shows "(\<exists>n. f = Val n) \<or> (\<exists>bs. f = Abs bs) \<or> (\<exists>n. f = PubConst Value n)"
proof -
  have *: "arity f = 0" by (metis const_type_inv assms) 
  show ?thesis  using assms
  proof (cases f)
    case (Fu g)
    hence "arity\<^sub>f g = 0" using * by simp
    hence False using Fu \<Gamma>_Fu_const[of g T] assms by auto
    thus ?thesis by metis
  next
    case (Set s)
    hence "arity\<^sub>s s = 0" using * by simp
    hence False using Set assms by auto
    thus ?thesis by metis
  qed simp_all
qed

lemma Ana\<^sub>f_keys_not_val_terms:
  assumes "Ana\<^sub>f f = (K, T)"
    and "k \<in> set K"
    and "g \<in> funs_term k"
  shows "\<not>is_Val g"
    and "\<not>is_PubConstValue g"
    and "\<not>is_Abs g"
proof -
  { assume "is_Val g"
    then obtain n S where *: "Fun (Val n) S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K)"
      using assms(2) funs_term_Fun_subterm[OF assms(3)]
      by (cases g) auto
    hence False using Ana\<^sub>f_assm1_alt[OF assms(1) *] by simp
  } moreover {
    assume "is_PubConstValue g"
    then obtain n S where *: "Fun (PubConst Value n) S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K)"
      using assms(2) funs_term_Fun_subterm[OF assms(3)]
      unfolding is_PubConstValue_def by (cases g) auto
    hence False using Ana\<^sub>f_assm1_alt[OF assms(1) *] by simp
  } moreover {
    assume "is_Abs g"
    then obtain a S where *: "Fun (Abs a) S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K)"
      using assms(2) funs_term_Fun_subterm[OF assms(3)]
      by (cases g) auto
    hence False using Ana\<^sub>f_assm1_alt[OF assms(1) *] by simp
  } ultimately show "\<not>is_Val g" "\<not>is_PubConstValue g" "\<not>is_Abs g" by metis+
qed

lemma Ana\<^sub>f_keys_not_pairs:
  assumes "Ana\<^sub>f f = (K, T)"
    and "k \<in> set K"
    and "g \<in> funs_term k"
  shows "g \<noteq> Pair"
proof
  assume "g = Pair"
  then obtain S where *: "Fun Pair S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K)"
    using assms(2) funs_term_Fun_subterm[OF assms(3)]
    by (cases g) auto
  show False using Ana\<^sub>f_assm1_alt[OF assms(1) *] by simp
qed

lemma Ana_Fu_keys_funs_term_subset:
  fixes K::"('fun,'atom,'sets,'lbl) prot_term list"
  assumes "Ana (Fun (Fu f) S) = (K, T)"
    and "Ana\<^sub>f f = (K', T')"
  shows "\<Union>(funs_term ` set K) \<subseteq> \<Union>(funs_term ` set K') \<union> funs_term (Fun (Fu f) S)"
proof -
  { fix k assume k: "k \<in> set K"
    then obtain k' where k':
        "k' \<in> set K'" "k = k' \<cdot> (!) S" "arity\<^sub>f f = length S"
        "subterms k' \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (set K')"
      using assms Ana_Fu_elim[OF assms(1) _ assms(2)] by fastforce

    have 1: "funs_term k' \<subseteq> \<Union>(funs_term ` set K')" using k'(1) by auto

    have "i < length S" when "i \<in> fv k'" for i
      using that Ana\<^sub>f_assm2_alt[OF assms(2), of i] k'(1,3)
      by auto
    hence 2: "funs_term (S ! i) \<subseteq> funs_term (Fun (Fu f) S)" when "i \<in> fv k'" for i
      using that by force
  
    have "funs_term k \<subseteq> \<Union>(funs_term ` set K') \<union> funs_term (Fun (Fu f) S)"
      using funs_term_subst[of k' "(!) S"] k'(2) 1 2 by fast
  } thus ?thesis by blast
qed

lemma Ana_Fu_keys_not_pubval_terms:
  fixes k::"('fun,'atom,'sets,'lbl) prot_term"
  assumes "Ana (Fun (Fu f) S) = (K, T)"
    and "Ana\<^sub>f f = (K', T')"
    and "k \<in> set K"
    and "\<forall>g \<in> funs_term (Fun (Fu f) S). \<not>is_PubConstValue g"
  shows "\<forall>g \<in> funs_term k. \<not>is_PubConstValue g"
using assms(3,4) Ana\<^sub>f_keys_not_val_terms(1,2)[OF assms(2)]
      Ana_Fu_keys_funs_term_subset[OF assms(1,2)]
by blast

lemma Ana_Fu_keys_not_abs_terms:
  fixes k::"('fun,'atom,'sets,'lbl) prot_term"
  assumes "Ana (Fun (Fu f) S) = (K, T)"
    and "Ana\<^sub>f f = (K', T')"
    and "k \<in> set K"
    and "\<forall>g \<in> funs_term (Fun (Fu f) S). \<not>is_Abs g"
  shows "\<forall>g \<in> funs_term k. \<not>is_Abs g"
using assms(3,4) Ana\<^sub>f_keys_not_val_terms(3)[OF assms(2)]
      Ana_Fu_keys_funs_term_subset[OF assms(1,2)]
by blast

lemma Ana_Fu_keys_not_pairs:
  fixes k::"('fun,'atom,'sets,'lbl) prot_term"
  assumes "Ana (Fun (Fu f) S) = (K, T)"
    and "Ana\<^sub>f f = (K', T')"
    and "k \<in> set K"
    and "\<forall>g \<in> funs_term (Fun (Fu f) S). g \<noteq> Pair"
  shows "\<forall>g \<in> funs_term k. g \<noteq> Pair"
using assms(3,4) Ana\<^sub>f_keys_not_pairs[OF assms(2)]
      Ana_Fu_keys_funs_term_subset[OF assms(1,2)]
by blast

lemma Ana_Fu_keys_length_eq:
  assumes "length T = length S"
  shows "length (fst (Ana (Fun (Fu f) T))) = length (fst (Ana (Fun (Fu f) S)))"
proof (cases "arity\<^sub>f f = length T \<and> arity\<^sub>f f > 0")
  case True thus ?thesis using assms by (cases "Ana\<^sub>f f") auto
next
  case False thus ?thesis using assms by force
qed

lemma Ana_key_PubConstValue_subterm_in_term: 
  fixes k::"('fun,'atom,'sets,'lbl) prot_term"
  assumes KR: "Ana t = (K, R)"
    and k: "k \<in> set K"
    and n: "Fun (PubConst Value n) [] \<sqsubseteq> k"
  shows "Fun (PubConst Value n) [] \<sqsubseteq> t"
proof (cases t)
  case (Var x) thus ?thesis using KR k n by force
next
  case (Fun f ts)
  note t = this
  then obtain g where f: "f = Fu g" using KR k by (cases f) auto
  obtain K' R' where KR': "Ana\<^sub>f g = (K', R')" by fastforce

  have K: "K = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) ts"
    using k Ana_Fu_elim(2)[OF KR[unfolded t] f KR'] by force

  obtain k' where k': "k' \<in> set K'" "k = k' \<cdot> (!) ts" using k K by auto

  have 0: "\<not>(Fun (PubConst Value n) [] \<sqsubseteq> k')"
  proof
    assume *: "Fun (PubConst Value n) [] \<sqsubseteq> k'"
    have **: "PubConst Value n \<in> funs_term k'"
      using funs_term_Fun_subterm'[OF *] by (cases k') auto
    show False
      using Ana\<^sub>f_keys_not_val_terms(2)[OF KR' k'(1) **]
      unfolding is_PubConstValue_def by force
  qed
  hence "\<exists>i \<in> fv k'. Fun (PubConst Value n) [] \<sqsubseteq> ts ! i"
    by (metis n const_subterm_subst_var_obtain k'(2))
  then obtain i where i: "i \<in> fv k'" "Fun (PubConst Value n) [] \<sqsubseteq> ts ! i" by blast

  have "i < length ts"
    using i(1) KR' k'(1) Ana\<^sub>f_assm2_alt[OF KR', of i]
          Ana_Fu_elim(1)[OF KR[unfolded t] f KR'] k
    by fastforce
  thus ?thesis using i(2) unfolding t by force
qed

lemma deduct_occurs_in_ik:
  fixes t::"('fun,'atom,'sets,'lbl) prot_term"
  assumes t: "M \<turnstile> occurs t"
    and M: "\<forall>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t M. OccursFact \<notin> \<Union>(funs_term ` set (snd (Ana s)))"
           "\<forall>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t M. OccursSec \<notin> \<Union>(funs_term ` set (snd (Ana s)))"
           "Fun OccursSec [] \<notin> M"
  shows "occurs t \<in> M"
using private_fun_deduct_in_ik''[of M OccursFact "[Fun OccursSec [], t]" OccursSec] t M 
by fastforce

lemma deduct_val_const_swap:
  fixes \<theta> \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> \<turnstile> t \<cdot> \<theta>"
    and "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv t. (\<exists>n. \<theta> x = Fun (Val n) []) \<or> (\<exists>n. \<theta> x = Fun (PubConst Value n) [])"
    and "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv t. (\<exists>n. \<sigma> x = Fun (Val n) [])"
    and "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv t. (\<exists>n. \<theta> x = Fun (PubConst Value n) []) \<longrightarrow> \<sigma> x \<in> M \<union> N"
    and "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv t. (\<exists>n. \<theta> x = Fun (Val n) []) \<longrightarrow> \<theta> x = \<sigma> x"
    and "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv t. \<forall>y \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv t. \<theta> x = \<theta> y \<longleftrightarrow> \<sigma> x = \<sigma> y"
    and "\<forall>n. \<not>(Fun (PubConst Value n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t insert t M)"
  shows "(M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N \<turnstile> t \<cdot> \<sigma>"
proof -
  obtain n where n: "intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) n (t \<cdot> \<theta>)"
    using assms(1) deduct_num_if_deduct by blast
  hence "\<exists>m \<le> n. intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) m (t \<cdot> \<sigma>)" using assms(2-)
  proof (induction n arbitrary: t rule: nat_less_induct)
    case (1 n)
    note prems = "1.prems"
    note IH = "1.IH"

    show ?case
    proof (cases "t \<cdot> \<theta> \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>")
      case True
      note 2 = this
      have 3: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv t. \<exists>c. \<theta> x = Fun c []"
              "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv t. \<exists>c. \<sigma> x = Fun c []"
        using prems(2,3) by (blast, blast)
      have "t \<cdot> \<sigma> \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>"
        using subst_const_swap_eq_mem[OF 2 _ 3 prems(6)] prems(2,5,7) by metis
      thus ?thesis using intruder_deduct_num.AxiomN by auto
    next
      case False
      then obtain n' where n: "n = Suc n'" using prems(1) deduct_zero_in_ik by (cases n) fast+

      have M_subterms_eq:
          "subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) = subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
          "subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) = subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>"
        subgoal using prems(2) subterms_subst''[of M \<theta>] by blast
        subgoal using prems(3) subterms_subst''[of M \<sigma>] by blast
        done

      from deduct_inv[OF prems(1)] show ?thesis
      proof (elim disjE)
        assume "t \<cdot> \<theta> \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>" thus ?thesis using False by argo
      next
        assume "\<exists>f ts. t \<cdot> \<theta> = Fun f ts \<and> public f \<and> length ts = arity f \<and>
                     (\<forall>t \<in> set ts. \<exists>l < n. intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) l t)"
        then obtain f ts where t:
            "t \<cdot> \<theta> = Fun f ts" "public f" "length ts = arity f"
            "\<forall>t \<in> set ts. \<exists>l < n. intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) l t"
          by blast
  
        show ?thesis
        proof (cases t)
          case (Var x)
          hence ts: "ts = []" and f: "\<exists>c. f = PubConst Value c"
            using t(1,2) prems(2) by (force, auto)
          have "\<sigma> x \<in> M \<union> N" using prems(4) Var f ts t(1) by auto
          moreover have "fv (\<sigma> x) = {}" using prems(3) Var by auto
          hence "\<sigma> x \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>" when "\<sigma> x \<in> M" using that subst_ground_ident[of "\<sigma> x" \<sigma>] by force
          ultimately have "\<sigma> x \<in> (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N" by fast
          thus ?thesis using intruder_deduct_num.AxiomN Var by force
        next
          case (Fun g ss)
          hence f: "f = g" and ts: "ts = ss \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>" using t(1) by auto
  
          have ss: "\<exists>l < n. intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) l (s \<cdot> \<theta>)" when s: "s \<in> set ss" for s
            using t(4) ts s by auto
  
          have IH': "\<exists>l < n. intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l (s \<cdot> \<sigma>)"
            when s: "s \<in> set ss" for s
          proof -
            obtain l where l: "l < n" "intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) l (s \<cdot> \<theta>)"
              using ss s by blast
            
            have *: "fv s \<subseteq> fv t" "subterms\<^sub>s\<^sub>e\<^sub>t (insert s M) \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (insert t M)"
              using s unfolding Fun f ts by auto

            have "\<exists>l' \<le> l. intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l' (s \<cdot> \<sigma>)"
            proof -
              have "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv s.
                      (\<exists>n. \<theta> x = Fun (Val n) []) \<or> (\<exists>n. \<theta> x = Fun (PubConst Value n) [])"
                   "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv s. \<exists>n. \<sigma> x = Fun (Val n) []"
                   "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv s. (\<exists>n. \<theta> x = Fun (PubConst Value n) []) \<longrightarrow> \<sigma> x \<in> M \<union> N"
                   "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv s. (\<exists>n. \<theta> x = Fun (Val n) []) \<longrightarrow> \<theta> x = \<sigma> x"
                   "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv s. \<forall>y \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv s. \<theta> x = \<theta> y \<longleftrightarrow> \<sigma> x = \<sigma> y"
                   "\<forall>n. Fun (PubConst Value n) [] \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (insert s M)"
                subgoal using prems(2) *(1) by blast
                subgoal using prems(3) *(1) by blast
                subgoal using prems(4) *(1) by blast
                subgoal using prems(5) *(1) by blast
                subgoal using prems(6) *(1) by blast
                subgoal using prems(7) *(2) by blast
                done
              thus ?thesis using IH l by presburger
            qed
            then obtain l' where l': "l' \<le> l" "intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l' (s \<cdot> \<sigma>)"
              by blast

            have "l' < n" using l'(1) l(1) by linarith
            thus ?thesis using l'(2) by blast
          qed
  
          have g: "length (ss \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>) = arity g" "public g"
            using t(2,3) unfolding f ts by auto

          let ?P = "\<lambda>s l. l < n \<and> intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l s"
          define steps where "steps \<equiv> \<lambda>s. SOME l. ?P s l"
  
          have 2: "steps (s \<cdot> \<sigma>) < n" "intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) (steps (s \<cdot> \<sigma>)) (s \<cdot> \<sigma>)"
            when s: "s \<in> set ss" for s
            using someI_ex[OF IH'[OF s]] unfolding steps_def by (blast, blast)
  
          have 3: "Suc (Max (insert 0 (steps ` set (ss \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>)))) \<le> n"
          proof (cases "ss = []")
            case True show ?thesis unfolding True n by simp
          next
            case False thus ?thesis
              using 2 Max_nat_finite_lt[of "set (ss \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>)" steps n] by (simp add: Suc_leI)
          qed
  
          show ?thesis
            using intruder_deduct_num.ComposeN[OF g, of "(M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N" steps] 2(2) 3
            unfolding Fun by auto
        qed
      next
        assume "\<exists>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>).
                  (\<exists>l < n. intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) l s) \<and>
                  (\<forall>k \<in> set (fst (Ana s)). \<exists>l < n. intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) l k) \<and>
                  t \<cdot> \<theta> \<in> set (snd (Ana s))"
        then obtain s l
            where s:
              "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
              "\<forall>k \<in> set (fst (Ana s)). \<exists>l < n. intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) l k"
              "t \<cdot> \<theta> \<in> set (snd (Ana s))"
            and l: "l < n" "intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) l s"
          by (metis (no_types, lifting) M_subterms_eq(1))

        obtain u where u: "u \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t M" "s = u \<cdot> \<theta>" using s(1) by blast

        have u_fv: "fv u \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M" by (metis fv_subset_subterms u(1))

        have "\<nexists>x. u = Var x"
        proof
          assume "\<exists>x. u = Var x"
          then obtain x where x: "u = Var x" by blast
          then obtain c where c: "s = Fun c []" using u prems(2) u_fv by auto
          thus False using s(3) Ana_subterm by (cases "Ana s") force
        qed
        then obtain f ts where u': "u = Fun f ts" by (cases u) auto

        obtain K R where KR: "Ana u = (K,R)" by (metis surj_pair)

        have KR': "Ana s = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>, R \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>)"
          using KR Ana_subst'[OF KR[unfolded u'], of \<theta>] unfolding u(2) u' by blast
        hence s': 
            "\<forall>k \<in> set K. \<exists>l < n. intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) l (k \<cdot> \<theta>)"
            "t \<cdot> \<theta> \<in> set (R \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>)"
          using s(2,3) by auto

        have IH1: "\<exists>l < n. intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l (u \<cdot> \<sigma>)"
        proof -
          have "subterms u \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t M" using u(1) subterms_subset by auto
          hence "subterms\<^sub>s\<^sub>e\<^sub>t (insert u M) = subterms\<^sub>s\<^sub>e\<^sub>t M" by blast
          hence *: "subterms\<^sub>s\<^sub>e\<^sub>t (insert u M) \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (insert t M)" by auto

          have "\<exists>l' \<le> l. intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l' (u \<cdot> \<sigma>)"
          proof -
            have "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv u.
                    (\<exists>n. \<theta> x = Fun (Val n) []) \<or> (\<exists>n. \<theta> x = Fun (PubConst Value n) [])"
                 "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv u. \<exists>n. \<sigma> x = Fun (Val n) []"
                 "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv u. (\<exists>n. \<theta> x = Fun (PubConst Value n) []) \<longrightarrow> \<sigma> x \<in> M \<union> N"
                 "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv u. (\<exists>n. \<theta> x = Fun (Val n) []) \<longrightarrow> \<theta> x = \<sigma> x"
                 "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv u. \<forall>y \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv u. \<theta> x = \<theta> y \<longleftrightarrow> \<sigma> x = \<sigma> y"
                 "\<forall>n. Fun (PubConst Value n) [] \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (insert u M)"
              subgoal using prems(2) u_fv by blast
              subgoal using prems(3) u_fv by blast
              subgoal using prems(4) u_fv by blast
              subgoal using prems(5) u_fv by blast
              subgoal using prems(6) u_fv by blast
              subgoal using prems(7) * by blast
              done
            thus ?thesis using IH l unfolding u(2) by presburger
          qed
          then obtain l' where l': "l' \<le> l" "intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l' (u \<cdot> \<sigma>)"
            by blast

          have "l' < n" using l'(1) l(1) by linarith
          thus ?thesis using l'(2) by blast
        qed

        have IH2: "\<exists>l < n. intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l (k \<cdot> \<sigma>)" when k: "k \<in> set K" for k
          using k IH prems(2-) Ana\<^sub>f_keys_not_val_terms s'(1) KR u(1)
        proof -
          have *: "fv k \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M" using k KR Ana_keys_fv u(1) fv_subset_subterms by blast

          have **: "Fun (PubConst Value n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t M" when "Fun (PubConst Value n) [] \<sqsubseteq> k" for n
            using in_subterms_subset_Union[OF u(1)]
                  Ana_key_PubConstValue_subterm_in_term[OF KR k that]
            by fast

          obtain lk where lk: "lk < n" "intruder_deduct_num (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) lk (k \<cdot> \<theta>)"
            using s'(1) k by fast

          have "\<exists>l' \<le> lk. intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l' (k \<cdot> \<sigma>)"
          proof -
            have "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv k.
                    (\<exists>n. \<theta> x = Fun (Val n) []) \<or> (\<exists>n. \<theta> x = Fun (PubConst Value n) [])"
                 "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv k. \<exists>n. \<sigma> x = Fun (Val n) []"
                 "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv k. (\<exists>n. \<theta> x = Fun (PubConst Value n) []) \<longrightarrow> \<sigma> x \<in> M \<union> N"
                 "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv k. (\<exists>n. \<theta> x = Fun (Val n) []) \<longrightarrow> \<theta> x = \<sigma> x"
                 "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv k. \<forall>y \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv k. \<theta> x = \<theta> y \<longleftrightarrow> \<sigma> x = \<sigma> y"
                 "\<forall>n. Fun (PubConst Value n) [] \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (insert k M)"
              subgoal using prems(2) * by blast
              subgoal using prems(3) * by blast
              subgoal using prems(4) * by blast
              subgoal using prems(5) * by blast
              subgoal using prems(6) * by blast
              subgoal using prems(7) ** by blast
              done
            thus ?thesis using IH lk by presburger
          qed
          then obtain lk' where lk': "lk' \<le> lk" "intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) lk' (k \<cdot> \<sigma>)"
            by blast

          have "lk' < n" using lk'(1) lk(1) by linarith
          thus ?thesis using lk'(2) by blast
        qed

        have KR'': "Ana (u \<cdot> \<sigma>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>, R \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>)"
          using Ana_subst' KR unfolding u' by blast

        obtain r where r: "r \<in> set R" "t \<cdot> \<theta> = r \<cdot> \<theta>"
          using s'(2) by fastforce

        have r': "t \<cdot> \<sigma> \<in> set (R \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>)"
        proof -
          have r_subterm_u: "r \<sqsubseteq> u" using r(1) KR Ana_subterm by blast

          have r_fv: "fv r \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
            by (meson r_subterm_u u(1) fv_subset_subterms in_mono in_subterms_subset_Union)

          have t_subterms_M: "subterms t \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (insert t M)"
            by blast

          have r_subterm_M: "subterms r \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (insert t M)"
            using subterms_subset[OF r_subterm_u] in_subterms_subset_Union[OF u(1)]
            by (auto intro: subterms\<^sub>s\<^sub>e\<^sub>t_mono)

          have *: "\<forall>x \<in> fv t \<union> fv r. \<theta> x = \<sigma> x \<or> \<not>(\<theta> x \<sqsubseteq> t) \<and> \<not>(\<theta> x \<sqsubseteq> r)"
          proof
            fix x assume "x \<in> fv t \<union> fv r"
            hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv t" using r_fv by blast
            thus "\<theta> x = \<sigma> x \<or> \<not>(\<theta> x \<sqsubseteq> t) \<and> \<not>(\<theta> x \<sqsubseteq> r)"
              using prems(2,5,7) r_subterm_M t_subterms_M
              by (metis (no_types, opaque_lifting) in_mono)
          qed

          have **: "\<forall>x \<in> fv t \<union> fv r. \<exists>c. \<theta> x = Fun c []"
                   "\<forall>x \<in> fv t \<union> fv r. \<exists>c. \<sigma> x = Fun c []"
                   "\<forall>x \<in> fv t \<union> fv r. \<forall>y \<in> fv t \<union> fv r. \<theta> x = \<theta> y \<longleftrightarrow> \<sigma> x = \<sigma> y"
            subgoal using prems(2) r_fv by blast
            subgoal using prems(3) r_fv by blast
            subgoal using prems(6) r_fv by blast
            done
          
          have "t \<cdot> \<sigma> = r \<cdot> \<sigma>" by (rule subst_const_swap_eq'[OF r(2) * **])
          thus ?thesis using r(1) by simp
        qed

        obtain l1 where l1: "l1 < n" "intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l1 (u \<cdot> \<sigma>)"
          using IH1 by blast

        let ?P = "\<lambda>s l. l < n \<and> intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) l s"
        define steps where "steps \<equiv> \<lambda>s. SOME l. ?P s l"

        have 2: "steps (k \<cdot> \<sigma>) < n" "intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) (steps (k \<cdot> \<sigma>)) (k \<cdot> \<sigma>)"
          when k: "k \<in> set K" for k
          using someI_ex[OF IH2[OF k]] unfolding steps_def by (blast, blast)

        have 3: "Suc (Max (insert l1 (steps ` set (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>)))) \<le> n"
        proof (cases "K = []")
          case True show ?thesis using l1(1) unfolding True n by simp
        next
          case False thus ?thesis
            using l1(1) 2 Max_nat_finite_lt[of "set (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>)" steps n] by (simp add: Suc_leI)
        qed

        have IH2': "intruder_deduct_num ((M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<union> N) (steps k) k"
          when k: "k \<in> set (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>)" for k
          using IH2 k 2 by auto

        show ?thesis
          using l1(1) intruder_deduct_num.DecomposeN[OF l1(2) KR'' IH2' r'] 3 by fast
      qed
    qed
  qed
  thus ?thesis using deduct_if_deduct_num by blast
qed

lemma constraint_model_Nil:
  assumes I: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
  shows "constraint_model I []"
using I unfolding constraint_model_def by simp

lemma welltyped_constraint_model_Nil:
  assumes I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
  shows "welltyped_constraint_model I []"
using I(1) constraint_model_Nil[OF I(2,3)] unfolding welltyped_constraint_model_def by simp

lemma constraint_model_prefix:
  assumes "constraint_model I (A@B)"
  shows "constraint_model I A"
by (metis assms strand_sem_append_stateful unlabel_append constraint_model_def)

lemma welltyped_constraint_model_prefix:
  assumes "welltyped_constraint_model I (A@B)"
  shows "welltyped_constraint_model I A"
by (metis assms constraint_model_prefix welltyped_constraint_model_def)

lemma welltyped_constraint_model_deduct_append:
  assumes "welltyped_constraint_model I A"
    and "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> s \<cdot> I"
  shows "welltyped_constraint_model I (A@[(l,send\<langle>[s]\<rangle>)])"
using assms strand_sem_append_stateful[of "{}" "{}" "unlabel A" _ I]
unfolding welltyped_constraint_model_def constraint_model_def by simp

lemma welltyped_constraint_model_deduct_split:
  assumes "welltyped_constraint_model I (A@[(l,send\<langle>[s]\<rangle>)])"
  shows "welltyped_constraint_model I A"
    and "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> s \<cdot> I"
using assms strand_sem_append_stateful[of "{}" "{}" "unlabel A" _ I]
unfolding welltyped_constraint_model_def constraint_model_def by simp_all

lemma welltyped_constraint_model_deduct_iff:
  "welltyped_constraint_model I (A@[(l,send\<langle>[s]\<rangle>)]) \<longleftrightarrow>
    welltyped_constraint_model I A \<and> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> s \<cdot> I"
by (metis welltyped_constraint_model_deduct_append welltyped_constraint_model_deduct_split)  

lemma welltyped_constraint_model_attack_if_receive_attack:
  assumes I: "welltyped_constraint_model \<I> \<A>"
    and rcv_attack: "receive\<langle>ts\<rangle> \<in> set (unlabel \<A>)" "attack\<langle>n\<rangle> \<in> set ts"
  shows "welltyped_constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
proof -
  have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> attack\<langle>n\<rangle>"
    using rcv_attack in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of "attack\<langle>n\<rangle>" "unlabel \<A>"]
          ideduct_subst[OF intruder_deduct.Axiom[of "attack\<langle>n\<rangle>" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"], of \<I>]
    by auto
  thus ?thesis
    using I strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" "[send\<langle>[attack\<langle>n\<rangle>]\<rangle>]" \<I>]
    unfolding welltyped_constraint_model_def constraint_model_def by auto
qed

lemma constraint_model_Val_is_Value_term:
  assumes "welltyped_constraint_model I A"
    and "t \<cdot> I = Fun (Val n) []"
  shows "t = Fun (Val n) [] \<or> (\<exists>m. t = Var (TAtom Value, m))"
proof -
  have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" using assms(1) unfolding welltyped_constraint_model_def by simp
  moreover have "\<Gamma> (Fun (Val n) []) = TAtom Value" by auto
  ultimately have *: "\<Gamma> t = TAtom Value" by (metis (no_types) assms(2) wt_subst_trm'')

  show ?thesis
  proof (cases t)
    case (Var x)
    obtain \<tau> m where x: "x = (\<tau>, m)" by (metis surj_pair)
    have "\<Gamma>\<^sub>v x = TAtom Value" using * Var by auto
    hence "\<tau> = TAtom Value" using x \<Gamma>\<^sub>v_TAtom'[of Value \<tau> m] by simp
    thus ?thesis using x Var by metis
  next
    case (Fun f T) thus ?thesis using assms(2) by auto
  qed
qed

lemma wellformed_transaction_sem_receives:
  fixes T::"('fun,'atom,'sets,'lbl) prot_transaction"
  assumes T_valid: "wellformed_transaction T"
    and \<I>: "strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) \<I>"
    and s: "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  shows "\<forall>t \<in> set ts. IK \<turnstile> t \<cdot> \<I>"
proof -
  let ?R = "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  let ?S = "\<lambda>A. unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  let ?S' = "?S (transaction_receive T)"

  obtain l B s where B:
      "(l,send\<langle>ts\<rangle>) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
      "prefix ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]) (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
    using s dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(2)[of ts "transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>"]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_set_prefix_obtain_subst[of "send\<langle>ts\<rangle>" "transaction_receive T" \<theta>]
    by blast

  have 1: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>])) = unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))@[send\<langle>ts\<rangle>]"
    using B(1) unlabel_append dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst singleton_lst_proj(4)
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_snoc subst_lsst_append subst_lsst_singleton
    by (metis (no_types, lifting) subst_apply_labeled_stateful_strand_step.simps)

  have "strand_sem_stateful IK DB ?S' \<I>"
    using \<I> strand_sem_append_stateful[of IK DB _ _ \<I>] transaction_dual_subst_unfold[of T \<theta>]
    by fastforce
  hence "strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))@[send\<langle>ts\<rangle>]) \<I>"
    using B 1 unfolding prefix_def unlabel_def
    by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def map_append strand_sem_append_stateful) 
  hence t_deduct: "\<forall>t \<in> set ts. IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile> t \<cdot> \<I>"
    using strand_sem_append_stateful[of IK DB "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" "[send\<langle>ts\<rangle>]" \<I>]
    by simp

  have "\<forall>s \<in> set (unlabel (transaction_receive T)). \<exists>t. s = receive\<langle>t\<rangle>"
    using T_valid wellformed_transaction_unlabel_cases(1)[OF T_valid] by auto
  moreover { fix A::"('fun,'atom,'sets,'lbl) prot_strand" and \<theta>
    assume "\<forall>s \<in> set (unlabel A). \<exists>t. s = receive\<langle>t\<rangle>"
    hence "\<forall>s \<in> set (unlabel (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)). \<exists>t. s = receive\<langle>t\<rangle>"
    proof (induction A)
      case (Cons a A) thus ?case using subst_lsst_cons[of a A \<theta>] by (cases a) auto
    qed simp
    hence "\<forall>s \<in> set (unlabel (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)). \<exists>t. s = receive\<langle>t\<rangle>"
      by (simp add: list.pred_set is_Receive_def)
    hence "\<forall>s \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))). \<exists>t. s = send\<langle>t\<rangle>"
      by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_memberD dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_inv(2) unlabel_in unlabel_mem_has_label)
  }
  ultimately have "\<forall>s \<in> set ?R. \<exists>ts. s = send\<langle>ts\<rangle>" by simp
  hence "ik\<^sub>s\<^sub>s\<^sub>t ?R = {}" unfolding unlabel_def ik\<^sub>s\<^sub>s\<^sub>t_def by fast
  hence "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) = {}"
    using B(2) 1 ik\<^sub>s\<^sub>s\<^sub>t_append dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append
    by (metis (no_types, lifting) Un_empty map_append prefix_def unlabel_def) 
  thus ?thesis using t_deduct by simp
qed

lemma wellformed_transaction_sem_pos_checks:
  assumes T_valid: "wellformed_transaction T"
    and \<I>: "strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) \<I>"
  shows "\<langle>ac: t \<in> u\<rangle> \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<Longrightarrow> (t \<cdot> \<I>, u \<cdot> \<I>) \<in> DB"
    and "\<langle>ac: t \<doteq> u\<rangle> \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<Longrightarrow> t \<cdot> \<I> = u \<cdot> \<I>"
proof -
  let ?s = "\<langle>ac: t \<in> u\<rangle>"
  let ?s' = "\<langle>ac: t \<doteq> u\<rangle>"
  let ?C = "set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  let ?R = "transaction_receive T@transaction_checks T"
  let ?R' = "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  let ?S = "\<lambda>A. unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  let ?S' = "?S (transaction_receive T)@?S (transaction_checks T)"
  let ?P = "\<lambda>a. is_Receive a \<or> is_Check_or_Assignment a"
  let ?Q = "\<lambda>a. is_Send a \<or> is_Check_or_Assignment a"
  let ?dbupd = "\<lambda>B. dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) \<I> DB"

  have s_in: "?s \<in> ?C \<Longrightarrow> ?s \<in> set (unlabel (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
             "?s' \<in> ?C \<Longrightarrow> ?s' \<in> set (unlabel (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    using subst_lsst_append[of "transaction_receive T"]
          unlabel_append[of "transaction_receive T"]
    by auto

  have 1: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>])) = unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))@[s']"
    when B: "(l,s') = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)" "s' = \<langle>ac: t \<in> u\<rangle> \<or> s' = \<langle>ac: t \<doteq> u\<rangle>"
    for l s s' and B::"('fun,'atom,'sets,'lbl) prot_strand"
    using B unlabel_append dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst singleton_lst_proj(4)
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_snoc subst_lsst_append subst_lsst_singleton
    by (metis (no_types, lifting) subst_apply_labeled_stateful_strand_step.simps)


  have 2: "strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))@[s']) \<I>"
    when B: "(l,s') = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
            "prefix ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]) (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
            "s' = \<langle>ac: t \<in> u\<rangle> \<or> s' = \<langle>ac: t \<doteq> u\<rangle>"
    for l s s' and B::"('fun,'atom,'sets,'lbl) prot_strand"
  proof -
    have "strand_sem_stateful IK DB ?S' \<I>"
      using \<I> strand_sem_append_stateful[of IK DB _ _ \<I>] transaction_dual_subst_unfold[of T \<theta>]
      by fastforce
    thus ?thesis
      using B(2) 1[OF B(1,3)] strand_sem_append_stateful subst_lsst_append
      unfolding prefix_def unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by (metis (no_types) map_append)
  qed

  have s_sem:
      "?s \<in> ?C \<Longrightarrow> (l,?s) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) \<Longrightarrow> (t \<cdot> \<I>, u \<cdot> \<I>) \<in> ?dbupd B"
      "?s' \<in> ?C \<Longrightarrow> (l,?s') = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) \<Longrightarrow> t \<cdot> \<I> = u \<cdot> \<I>"
    when B: "prefix ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]) (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
    for l s and B::"('fun,'atom,'sets,'lbl) prot_strand"
    using 2[OF _ B] strand_sem_append_stateful[of IK DB "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" _ \<I>]
    by (fastforce, fastforce)

  have 3: "\<forall>a \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))). \<not>is_Insert a \<and> \<not>is_Delete a"
    when B: "prefix ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]) (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
    for l s and B::"('fun,'atom,'sets,'lbl) prot_strand"
  proof -
    have "\<forall>a \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))). ?Q a"
    proof
      fix a assume a: "a \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
  
      have "?P a" when a: "a \<in> set (unlabel ?R)" for a
        using a wellformed_transaction_unlabel_cases(1,2)[OF T_valid]
        unfolding unlabel_def by fastforce
      hence "?P a" when a: "a \<in> set (unlabel (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" for a
        using a stateful_strand_step_cases_subst(2,11)[of _ \<theta>] subst_lsst_unlabel[of ?R \<theta>]
        unfolding subst_apply_stateful_strand_def by auto
      hence B_P: "\<forall>a \<in> set (unlabel (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)). ?P a"
        using unlabel_mono[OF set_mono_prefix[OF append_prefixD[OF B]]]  by blast
  
      obtain l where "(l,a) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
        using a by (meson unlabel_mem_has_label)
      then obtain b where b: "(l,b) \<in> set (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)" "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (l,b) = (l,a)"
        using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_memberD by blast
      hence "?P b" using B_P unfolding unlabel_def by fastforce
      thus "?Q a" using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_inv[OF b(2)] by (cases b) auto
    qed
    thus ?thesis by fastforce
  qed

  show "(t \<cdot> \<I>, u \<cdot> \<I>) \<in> DB" when s: "?s \<in> ?C"
  proof -
    obtain l B s where B:
        "(l,?s) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
        "prefix ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]) (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
      using s_in(1)[OF s] dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(6)[of _ t u]
            dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_set_prefix_obtain_subst[of ?s ?R \<theta>]
      by blast

    show ?thesis
      using 3[OF B(2)] s_sem(1)[OF B(2) s B(1)]
            dbupd\<^sub>s\<^sub>s\<^sub>t_no_upd[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" \<I> DB]
      by simp
  qed

  show "t \<cdot> \<I> = u \<cdot> \<I>" when s: "?s' \<in> ?C"
  proof -
    obtain l B s where B:
        "(l,?s') = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
        "prefix ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]) (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
      using s_in(2)[OF s] dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(3)[of _ t u]
            dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_set_prefix_obtain_subst[of ?s' ?R \<theta>]
      by blast

    show ?thesis
      using 3[OF B(2)] s_sem(2)[OF B(2) s B(1)]
            dbupd\<^sub>s\<^sub>s\<^sub>t_no_upd[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" \<I> DB]
      by simp
  qed
qed

lemma wellformed_transaction_sem_neg_checks:
  assumes T_valid: "wellformed_transaction T"
    and \<I>: "strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) \<I>"
    and "NegChecks X F G \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  shows "negchecks_model \<I> DB X F G"
proof -
  let ?s = "NegChecks X F G"
  let ?R = "transaction_receive T@transaction_checks T"
  let ?R' = "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  let ?S = "\<lambda>A. unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  let ?S' = "?S (transaction_receive T)@?S (transaction_checks T)"
  let ?P = "\<lambda>a. is_Receive a \<or> is_Check_or_Assignment a"
  let ?Q = "\<lambda>a. is_Send a \<or> is_Check_or_Assignment a"
  let ?U = "\<lambda>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)"

  have s: "?s \<in> set (unlabel (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    using assms(3) subst_lsst_append[of "transaction_receive T"]
          unlabel_append[of "transaction_receive T"]
    by auto

  obtain l B s where B:
      "(l,?s) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
      "prefix ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]) (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
    using s dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(7)[of X F G]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_set_prefix_obtain_subst[of ?s ?R \<theta>]
    by blast

  have 1: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>])) = unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))@[?s]"
    using B(1) unlabel_append dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst singleton_lst_proj(4)
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_snoc subst_lsst_append subst_lsst_singleton
    by (metis (no_types, lifting) subst_apply_labeled_stateful_strand_step.simps)

  have "strand_sem_stateful IK DB ?S' \<I>"
    using \<I> strand_sem_append_stateful[of IK DB _ _ \<I>] transaction_dual_subst_unfold[of T \<theta>]
    by fastforce
  hence "strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))@[?s]) \<I>"
    using B 1 strand_sem_append_stateful subst_lsst_append
    unfolding prefix_def unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def
    by (metis (no_types) map_append)
  hence s_sem: "negchecks_model \<I> (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) \<I> DB) X F G"
    using strand_sem_append_stateful[of IK DB "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" "[?s]" \<I>]
    by fastforce

  have "\<forall>a \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))). ?Q a"
  proof
    fix a assume a: "a \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"

    have "?P a" when a: "a \<in> set (unlabel ?R)" for a
      using a wellformed_transaction_unlabel_cases(1,2,3)[OF T_valid]
      unfolding unlabel_def by fastforce
    hence "?P a" when a: "a \<in> set (unlabel (?R \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" for a
      using a stateful_strand_step_cases_subst(2,11)[of _ \<theta>] subst_lsst_unlabel[of ?R \<theta>]
      unfolding subst_apply_stateful_strand_def by auto
    hence B_P: "\<forall>a \<in> set (unlabel (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)). ?P a"
      using unlabel_mono[OF set_mono_prefix[OF append_prefixD[OF B(2)]]]
      by blast

    obtain l where "(l,a) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
      using a by (meson unlabel_mem_has_label)
    then obtain b where b: "(l,b) \<in> set (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)" "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (l,b) = (l,a)"
      using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_memberD by blast
    hence "?P b" using B_P unfolding unlabel_def by fastforce
    thus "?Q a" using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_inv[OF b(2)] by (cases b) auto
  qed
  hence "\<forall>a \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))). \<not>is_Insert a \<and> \<not>is_Delete a" by fastforce
  thus ?thesis using dbupd\<^sub>s\<^sub>s\<^sub>t_no_upd[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" \<I> DB] s_sem by simp
qed

lemma wellformed_transaction_sem_neg_checks':
  assumes T_valid: "wellformed_transaction T"
    and \<I>: "strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) \<I>"
    and c: "NegChecks X [] [(t,u)] \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  shows "\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow> (t \<cdot> \<delta> \<cdot> \<I>, u \<cdot> \<delta> \<cdot> \<I>) \<notin> DB" (is ?A)
    and "X = [] \<Longrightarrow> (t \<cdot> \<I>, u \<cdot> \<I>) \<notin> DB" (is "?B \<Longrightarrow> ?B'")
proof -
  show ?A
    using wellformed_transaction_sem_neg_checks[OF T_valid \<I> c]
    unfolding negchecks_model_def by auto
  moreover have "\<delta> = Var" "t \<cdot> \<delta> = t"
    when "subst_domain \<delta> = set []" for t and \<delta>::"('fun, 'atom, 'sets, 'lbl) prot_subst"
    using that by auto
  moreover have "subst_domain Var = set []" "range_vars Var = {}"
    by simp_all
  ultimately show "?B \<Longrightarrow> ?B'" unfolding range_vars_alt_def by metis
qed

lemma wellformed_transaction_sem_iff:
  fixes T \<theta>
  defines "A \<equiv> unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    and "rm \<equiv> \<lambda>X. rm_vars (set X)"
  assumes T: "wellformed_transaction T"
    and I: " interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
  shows "strand_sem_stateful M D A I \<longleftrightarrow> (
    (\<forall>l ts. (l,receive\<langle>ts\<rangle>) \<in> set (transaction_receive T) \<longrightarrow> (\<forall>t \<in> set ts. M \<turnstile> t \<cdot> \<theta> \<cdot> I)) \<and>
    (\<forall>l ac t s. (l,\<langle>ac: t \<doteq> s\<rangle>) \<in> set (transaction_checks T) \<longrightarrow> t \<cdot> \<theta> \<cdot> I = s \<cdot> \<theta> \<cdot> I) \<and>
    (\<forall>l ac t s. (l,\<langle>ac: t \<in> s\<rangle>) \<in> set (transaction_checks T) \<longrightarrow> (t \<cdot> \<theta> \<cdot> I, s \<cdot> \<theta> \<cdot> I) \<in> D) \<and>
    (\<forall>l X F G. (l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<in> set (transaction_checks T) \<longrightarrow>
      (\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow>
            (\<exists>(t,s) \<in> set F. t \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I \<noteq> s \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I) \<or>
            (\<exists>(t,s) \<in> set G. (t \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I, s \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I) \<notin> D))))"
    (is "?A \<longleftrightarrow> ?B")
proof
  note 0 = A_def transaction_dual_subst_unlabel_unfold
  note 1 = wellformed_transaction_sem_receives[OF T, of M D \<theta> I, unfolded A_def[symmetric]]
           wellformed_transaction_sem_pos_checks[OF T, of M D \<theta> I, unfolded A_def[symmetric]]
           wellformed_transaction_sem_neg_checks[OF T, of M D \<theta> I, unfolded A_def[symmetric]]
  note 2 = stateful_strand_step_subst_inI[OF unlabel_in]
  note 3 = unlabel_subst
  note 4 = strand_sem_append_stateful[of M D _ _ I]

  let ?C = "\<lambda>T. unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  let ?P = "\<lambda>X \<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)"
  let ?sem = "\<lambda>M D T. strand_sem_stateful M D (?C T) I"
  let ?negchecks = "\<lambda>X F G. \<forall>\<delta>. ?P X \<delta> \<longrightarrow>
                                 (\<exists>(t,s) \<in> set F. t \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I \<noteq> s \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I) \<or>
                                 (\<exists>(t,s) \<in> set G. (t \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I, s \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I) \<notin> D)"

  have "list_all is_Receive (unlabel (transaction_receive T))"
       "list_all is_Check_or_Assignment (unlabel (transaction_checks T))"
       "list_all is_Update (unlabel (transaction_updates T))"
       "list_all is_Send (unlabel (transaction_send T))"
    using T unfolding wellformed_transaction_def by (blast, blast, blast, blast)
  hence 5: "list_all is_Send (?C (transaction_receive T))"
           "list_all is_Check_or_Assignment (?C (transaction_checks T))"
           "list_all is_Update (?C (transaction_updates T))"
           "list_all is_Receive (?C (transaction_send T))"
    by (metis (no_types) subst_sst_list_all(2) unlabel_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all(1),
        metis (no_types) subst_sst_list_all(11) unlabel_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all(11),
        metis (no_types) subst_sst_list_all(10) unlabel_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all(10),
        metis (no_types) subst_sst_list_all(1) unlabel_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all(2))
  
  have "\<forall>a \<in> set (?C (transaction_receive T)). \<not>is_Receive a \<and> \<not>is_Insert a \<and> \<not>is_Delete a"
       "\<forall>a \<in> set (?C (transaction_checks T)). \<not>is_Receive a \<and> \<not>is_Insert a \<and> \<not>is_Delete a"
    using 5(1,2) unfolding list_all_iff by (blast,blast)
  hence 6:
      "M \<union> (ik\<^sub>s\<^sub>s\<^sub>t (?C (transaction_receive T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t I) = M"
      "dbupd\<^sub>s\<^sub>s\<^sub>t (?C (transaction_receive T)) I D = D"
      "M \<union> (ik\<^sub>s\<^sub>s\<^sub>t (?C (transaction_checks T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t I) = M"
      "dbupd\<^sub>s\<^sub>s\<^sub>t (?C (transaction_checks T)) I D = D"
    by (metis ik\<^sub>s\<^sub>s\<^sub>t_snoc_no_receive_empty sup_bot.right_neutral, metis dbupd\<^sub>s\<^sub>s\<^sub>t_no_upd,
        metis ik\<^sub>s\<^sub>s\<^sub>t_snoc_no_receive_empty sup_bot.right_neutral, metis dbupd\<^sub>s\<^sub>s\<^sub>t_no_upd)

  have ?B when A: ?A
  proof -
    have "M \<turnstile> t \<cdot> \<theta> \<cdot> I"
      when "(l, receive\<langle>ts\<rangle>) \<in> set (transaction_receive T)" "t \<in> set ts" for l ts t
      using that(2) 1(1)[OF A, of "ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>"] 2(2)[OF that(1)] unfolding 3 by auto
    moreover have "t \<cdot> \<theta> \<cdot> I = s \<cdot> \<theta> \<cdot> I"
      when "(l, \<langle>ac: t \<doteq> s\<rangle>) \<in> set (transaction_checks T)" for l ac t s
      using 1(3)[OF A] 2(3)[OF that] unfolding 3 by blast
    moreover have "(t \<cdot> \<theta> \<cdot> I, s \<cdot> \<theta> \<cdot> I) \<in> D"
      when "(l, \<langle>ac: t \<in> s\<rangle>) \<in> set (transaction_checks T)" for l ac t s
      using 1(2)[OF A] 2(6)[OF that] unfolding 3 by blast
    moreover have "?negchecks X F G"
      when "(l, \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<in> set (transaction_checks T)" for l X F G
      using 1(4)[OF A 2(7)[OF that, of \<theta>, unfolded 3]]
      unfolding negchecks_model_def rm_def subst_apply_pairs_def by fastforce
    ultimately show ?B by blast
  qed
  thus "?A \<Longrightarrow> ?B" by fast

  have ?A when B: ?B
  proof -
    have 7: "\<forall>t \<in> set ts. M \<turnstile> t \<cdot> I" when ts: "send\<langle>ts\<rangle> \<in> set (?C (transaction_receive T))" for ts
    proof -
      obtain l ss where "(l,receive\<langle>ss\<rangle>) \<in> set (transaction_receive T)" "ts = ss \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>"
        by (metis ts dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(2) subst_lsst_memD(1) unlabel_mem_has_label)
      thus ?thesis using B by auto
    qed

    have 8: "t \<cdot> I = s \<cdot> I" when ts: "\<langle>ac: t \<doteq> s\<rangle> \<in> set (?C (transaction_checks T))" for ac t s
    proof -
      obtain l t' s' where "(l,\<langle>ac: t' \<doteq> s'\<rangle>) \<in> set (transaction_checks T)" "t = t' \<cdot> \<theta>" "s = s' \<cdot> \<theta>"
        by (metis ts dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(3) subst_lsst_memD(3) unlabel_mem_has_label)
      thus ?thesis using B by auto
    qed

    have 9: "(t \<cdot> I, s \<cdot> I) \<in> D" when ts: "\<langle>ac: t \<in> s\<rangle> \<in> set (?C (transaction_checks T))" for ac t s
    proof -
      obtain l t' s' where "(l,\<langle>ac: t' \<in> s'\<rangle>) \<in> set (transaction_checks T)" "t = t' \<cdot> \<theta>" "s = s' \<cdot> \<theta>"
        by (metis ts dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(6) subst_lsst_memD(6) unlabel_mem_has_label)
      thus ?thesis using B by auto
    qed

    have 10: "negchecks_model I D X F G"
      when ts: "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set (?C (transaction_checks T))" for X F G
    proof -
      obtain l F' G' where *:
          "(l,\<forall>X\<langle>\<or>\<noteq>: F' \<or>\<notin>: G'\<rangle>) \<in> set (transaction_checks T)"
          "F = F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>" "G = G' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>"
        using unlabel_mem_has_label[OF iffD2[OF dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(7) ts]]
              subst_lsst_memD(7)[of _ X F G "transaction_checks T" \<theta>]
        by fast

      have "?negchecks X F' G'" using *(1) B by blast
      moreover have "\<exists>(t,s) \<in> set F. t \<cdot> \<delta> \<circ>\<^sub>s I \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s I"
        when "(t,s) \<in> set F'" "t \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I \<noteq> s \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I" for \<delta> t s
        using that unfolding rm_def *(2) subst_apply_pairs_def by force
      moreover have "\<exists>(t,s) \<in> set G. (t,s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s I \<notin> D"
        when "(t,s) \<in> set G'" "(t \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I, s \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I) \<notin> D" for \<delta> t s
        using that unfolding rm_def *(3) subst_apply_pairs_def by force
      ultimately show ?thesis
        unfolding negchecks_model_def by auto
    qed
    
    have "?sem M D (transaction_receive T)"
      using 7 strand_sem_stateful_if_sends_deduct[OF 5(1)] by blast
    moreover have "?sem M D (transaction_checks T)"
      using 8 9 10 strand_sem_stateful_if_checks[OF 5(2)] by blast
    moreover have "?sem M D (transaction_updates T)" for M D
      using 5(3) strand_sem_stateful_if_no_send_or_check unfolding list_all_iff by blast
    moreover have "?sem M D (transaction_send T)" for M D
      using 5(4) strand_sem_stateful_if_no_send_or_check unfolding list_all_iff by blast
    ultimately show ?thesis
      using 4[of "?C (transaction_receive T)"
                 "?C (transaction_checks T)@?C (transaction_updates T)@?C (transaction_send T)"]
            4[of "?C (transaction_checks T)" "?C (transaction_updates T)@?C (transaction_send T)"]
            4[of "?C (transaction_updates T)" "?C (transaction_send T)"]
      unfolding 0 6 by blast
  qed
  thus "?B \<Longrightarrow> ?A" by fast
qed

lemma wellformed_transaction_unlabel_sem_iff:
  fixes T \<theta>
  defines "A \<equiv> unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    and "rm \<equiv> \<lambda>X. rm_vars (set X)"
  assumes T: "wellformed_transaction T"
    and I: " interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
  shows "strand_sem_stateful M D A I \<longleftrightarrow> (
    (\<forall>ts. receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T)) \<longrightarrow> (\<forall>t \<in> set ts. M \<turnstile> t \<cdot> \<theta> \<cdot> I)) \<and>
    (\<forall>ac t s. \<langle>ac: t \<doteq> s\<rangle> \<in> set (unlabel (transaction_checks T)) \<longrightarrow> t \<cdot> \<theta> \<cdot> I = s \<cdot> \<theta> \<cdot> I) \<and>
    (\<forall>ac t s. \<langle>ac: t \<in> s\<rangle> \<in> set (unlabel (transaction_checks T)) \<longrightarrow> (t \<cdot> \<theta> \<cdot> I, s \<cdot> \<theta> \<cdot> I) \<in> D) \<and>
    (\<forall>X F G. \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set (unlabel (transaction_checks T)) \<longrightarrow>
      (\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow>
            (\<exists>(t,s) \<in> set F. t \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I \<noteq> s \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I) \<or>
            (\<exists>(t,s) \<in> set G. (t \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I, s \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I) \<notin> D))))"
using wellformed_transaction_sem_iff[OF T I, of M D \<theta>]
      unlabel_in[of _ _ "transaction_receive T"] unlabel_mem_has_label[of _ "transaction_receive T"]
      unlabel_in[of _ _ "transaction_checks T"] unlabel_mem_has_label[of _ "transaction_checks T"]
unfolding A_def[symmetric] rm_def by meson

lemma dual_transaction_ik_is_transaction_send'':
  fixes \<delta> \<I>::"('a,'b,'c,'d) prot_subst"
  assumes "wellformed_transaction T"
  shows "(ik\<^sub>s\<^sub>s\<^sub>t (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>))) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a =
         (trms\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a" (is "?A = ?B")
using dual_transaction_ik_is_transaction_send[OF assms]
      subst_lsst_unlabel[of "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)" \<delta>]
      ik\<^sub>s\<^sub>s\<^sub>t_subst[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))" \<delta>]
      dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst[of "transaction_strand T" \<delta>]
by (auto simp add: abs_apply_terms_def)

lemma while_prot_terms_fun_mono:
  "mono (\<lambda>M'. M \<union> \<Union>(subterms ` M') \<union> \<Union>((set \<circ> fst \<circ> Ana) ` M'))"
unfolding mono_def by fast

lemma while_prot_terms_SMP_overapprox:
  fixes M::"('fun,'atom,'sets,'lbl) prot_terms"
  assumes N_supset: "M \<union> \<Union>(subterms ` N) \<union> \<Union>((set \<circ> fst \<circ> Ana) ` N) \<subseteq> N"
    and Value_vars_only: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t N. \<Gamma>\<^sub>v x = TAtom Value"
  shows "SMP M \<subseteq> {a \<cdot> \<delta> | a \<delta>. a \<in> N \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)}"
proof -
  define f where "f \<equiv> \<lambda>M'. M \<union> \<Union>(subterms ` M') \<union> \<Union>((set \<circ> fst \<circ> Ana) ` M')"
  define S where "S \<equiv> {a \<cdot> \<delta> | a \<delta>. a \<in> N \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)}"

  note 0 = Value_vars_only
  
  have "t \<in> S" when "t \<in> SMP M" for t
  using that
  proof (induction t rule: SMP.induct)
    case (MP t)
    hence "t \<in> N" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range Var)" using N_supset by auto
    hence "t \<cdot> Var \<in> S" unfolding S_def by blast
    thus ?case by simp
  next
    case (Subterm t t')
    then obtain \<delta> a where a: "a \<cdot> \<delta> = t" "a \<in> N" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
      by (auto simp add: S_def)
    hence "\<forall>x \<in> fv a. \<exists>\<tau>. \<Gamma> (Var x) = TAtom \<tau>" using 0 by auto
    hence *: "\<forall>x \<in> fv a. (\<exists>f. \<delta> x = Fun f []) \<or> (\<exists>y. \<delta> x = Var y)"
      using a(3) TAtom_term_cases[OF wf_trm_subst_rangeD[OF a(4)]]
      by (metis wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
    obtain b where b: "b \<cdot> \<delta> = t'" "b \<in> subterms a"
      using subterms_subst_subterm[OF *, of t'] Subterm.hyps(2) a(1)
      by fast
    hence "b \<in> N" using N_supset a(2) by blast
    thus ?case using a b(1) unfolding S_def by blast
  next
    case (Substitution t \<theta>)
    then obtain \<delta> a where a: "a \<cdot> \<delta> = t" "a \<in> N" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
      by (auto simp add: S_def)
    have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<delta> \<circ>\<^sub>s \<theta>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<delta> \<circ>\<^sub>s \<theta>))"
      by (fact wt_subst_compose[OF a(3) Substitution.hyps(2)],
          fact wf_trms_subst_compose[OF a(4) Substitution.hyps(3)])
    moreover have "t \<cdot> \<theta> = a \<cdot> \<delta> \<circ>\<^sub>s \<theta>" using a(1) subst_subst_compose[of a \<delta> \<theta>] by simp
    ultimately show ?case using a(2) unfolding S_def by blast
  next
    case (Ana t K T k)
    then obtain \<delta> a where a: "a \<cdot> \<delta> = t" "a \<in> N" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
      by (auto simp add: S_def)
    obtain Ka Ta where a': "Ana a = (Ka,Ta)" by moura
    have *: "K = Ka \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>"
    proof (cases a)
      case (Var x)
      then obtain g U where gU: "t = Fun g U"
        using a(1) Ana.hyps(2,3) Ana_var
        by (cases t) simp_all
      have "\<Gamma> (Var x) = TAtom Value" using Var a(2) 0 by auto
      hence "\<Gamma> (Fun g U) = TAtom Value"
        using a(1,3) Var gU wt_subst_trm''[OF a(3), of a]
        by argo
      thus ?thesis using gU Fun_Value_type_inv Ana.hyps(2,3) by fastforce  
    next
      case (Fun g U) thus ?thesis using a(1) a' Ana.hyps(2) Ana_subst'[of g U] by simp
    qed
    then obtain ka where ka: "k = ka \<cdot> \<delta>" "ka \<in> set Ka" using Ana.hyps(3) by auto
    have "ka \<in> set ((fst \<circ> Ana) a)" using ka(2) a' by simp
    hence "ka \<in> N" using a(2) N_supset by auto
    thus ?case using ka a(3,4) unfolding S_def by blast
  qed
  thus ?thesis unfolding S_def by blast
qed


subsection \<open>Admissible Transactions\<close>
definition admissible_transaction_checks where
  "admissible_transaction_checks T \<equiv>
    \<forall>x \<in> set (unlabel (transaction_checks T)).
      (is_InSet x \<longrightarrow>
          is_Var (the_elem_term x) \<and> is_Fun_Set (the_set_term x) \<and>
          fst (the_Var (the_elem_term x)) = TAtom Value) \<and>
      (is_NegChecks x \<longrightarrow>
          bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x = [] \<and>
          ((the_eqs x = [] \<and> length (the_ins x) = 1) \<or>
           (the_ins x = [] \<and> length (the_eqs x) = 1))) \<and>
      (is_NegChecks x \<and> the_eqs x = [] \<longrightarrow> (let h = hd (the_ins x) in
          is_Var (fst h) \<and> is_Fun_Set (snd h) \<and>
          fst (the_Var (fst h)) = TAtom Value))"

definition admissible_transaction_updates where
  "admissible_transaction_updates T \<equiv>
    \<forall>x \<in> set (unlabel (transaction_updates T)).
      is_Update x \<and> is_Var (the_elem_term x) \<and> is_Fun_Set (the_set_term x) \<and>
      fst (the_Var (the_elem_term x)) = TAtom Value"

definition admissible_transaction_terms where
  "admissible_transaction_terms T \<equiv>
    wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)) \<and>
    (\<forall>f \<in> \<Union>(funs_term ` trms_transaction T).
      \<not>is_Val f \<and> \<not>is_Abs f \<and> \<not>is_PubConst f \<and> f \<noteq> Pair) \<and>
    (\<forall>r \<in> set (unlabel (transaction_strand T)).
      (\<exists>f \<in> \<Union>(funs_term ` (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p r)). is_Attack f) \<longrightarrow>
        transaction_fresh T = [] \<and>
        is_Send r \<and> length (the_msgs r) = 1 \<and> is_Fun_Attack (hd (the_msgs r)))"

definition admissible_transaction_send_occurs_form where
  "admissible_transaction_send_occurs_form T \<equiv> (
    let snds = transaction_send T;
        frsh = transaction_fresh T
    in \<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t snds. OccursFact \<in> funs_term t \<or> OccursSec \<in> funs_term t \<longrightarrow>
        (\<exists>x \<in> set frsh. t = occurs (Var x))
)"

definition admissible_transaction_occurs_checks where
  "admissible_transaction_occurs_checks T \<equiv> (
    let occ_in = \<lambda>x S. occurs (Var x) \<in> set (the_msgs (hd (unlabel S)));
        rcvs = transaction_receive T;
        snds = transaction_send T;
        frsh = transaction_fresh T;
        fvs = fv_transaction T
    in admissible_transaction_send_occurs_form T \<and>
       ((\<exists>x \<in> fvs - set frsh. fst x = TAtom Value) \<longrightarrow> (
          rcvs \<noteq> [] \<and> is_Receive (hd (unlabel rcvs)) \<and>
          (\<forall>x \<in> fvs - set frsh. fst x = TAtom Value \<longrightarrow> occ_in x rcvs))) \<and>
       (frsh \<noteq> [] \<longrightarrow> (
          snds \<noteq> [] \<and> is_Send (hd (unlabel snds)) \<and>
          (\<forall>x \<in> set frsh. occ_in x snds)))
)"

definition admissible_transaction_no_occurs_msgs where
  "admissible_transaction_no_occurs_msgs T \<equiv> (
    let no_occ = \<lambda>t. is_Fun t \<longrightarrow> the_Fun t \<noteq> OccursFact;
        rcvs = transaction_receive T;
        snds = transaction_send T
    in list_all (\<lambda>a. is_Receive (snd a) \<longrightarrow> list_all no_occ (the_msgs (snd a))) rcvs \<and>
       list_all (\<lambda>a. is_Send (snd a)    \<longrightarrow> list_all no_occ (the_msgs (snd a))) snds
)"

definition admissible_transaction' where
  "admissible_transaction' T \<equiv> (
    wellformed_transaction T \<and>
    transaction_decl T () = [] \<and>
    list_all (\<lambda>x. fst x = TAtom Value) (transaction_fresh T) \<and>
    (\<forall>x \<in> vars_transaction T. is_Var (fst x) \<and> (the_Var (fst x) = Value)) \<and>
    bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) = {} \<and>
    set (transaction_fresh T) \<subseteq>
      fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (filter (is_Insert \<circ> snd) (transaction_updates T)) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<and>
    (\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
     \<forall>y \<in> fv_transaction T - set (transaction_fresh T).
      x \<noteq> y \<longrightarrow> \<langle>Var x != Var y\<rangle> \<in> set (unlabel (transaction_checks T)) \<or>
                \<langle>Var y != Var x\<rangle> \<in> set (unlabel (transaction_checks T))) \<and>
    fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) - set (transaction_fresh T)
      \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<and>
    (\<forall>r \<in> set (unlabel (transaction_checks T)).
      is_Equality r \<longrightarrow> fv (the_rhs r) \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)) \<and>
    fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<subseteq>
      fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<union>
      fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (filter (\<lambda>s. is_InSet (snd s) \<and> the_check (snd s) = Assign) (transaction_checks T)) \<and>
    list_all (\<lambda>a. is_Receive (snd a) \<longrightarrow> the_msgs (snd a) \<noteq> []) (transaction_receive T) \<and>
    list_all (\<lambda>a. is_Send (snd a) \<longrightarrow> the_msgs (snd a) \<noteq> []) (transaction_send T) \<and>
    admissible_transaction_checks T \<and>
    admissible_transaction_updates T \<and>
    admissible_transaction_terms T \<and>
    admissible_transaction_send_occurs_form T
)"

definition admissible_transaction where
  "admissible_transaction T \<equiv>
    admissible_transaction' T \<and>
    admissible_transaction_no_occurs_msgs T"

definition has_initial_value_producing_transaction where
  "has_initial_value_producing_transaction P \<equiv>
    let f = \<lambda>s.
      list_all (\<lambda>T. list_all (\<lambda>a. ((is_Delete a \<or> is_InSet a) \<longrightarrow> the_set_term a \<noteq> \<langle>s\<rangle>\<^sub>s) \<and>
                                  (is_NegChecks a \<longrightarrow> list_all (\<lambda>(_,t). t \<noteq> \<langle>s\<rangle>\<^sub>s) (the_ins a)))
                             (unlabel (transaction_checks T@transaction_updates T)))
               P
    in list_ex (\<lambda>T.
        length (transaction_fresh T) = 1 \<and> transaction_receive T = [] \<and>
        transaction_checks T = [] \<and> length (transaction_send T) = 1 \<and>
        (let x = hd (transaction_fresh T); a = hd (transaction_send T); u = transaction_updates T
         in is_Send (snd a) \<and> Var x \<in> set (the_msgs (snd a)) \<and>
            fv\<^sub>s\<^sub>e\<^sub>t (set (the_msgs (snd a))) = {x} \<and>
            (u \<noteq> [] \<longrightarrow> (
              let b = hd u; c = snd b
              in tl u = [] \<and> is_Insert c \<and> the_elem_term c = Var x \<and>
                 is_Fun_Set (the_set_term c) \<and> f (the_Set (the_Fun (the_set_term c))))))
       ) P"


lemma admissible_transaction_is_wellformed_transaction:
  assumes "admissible_transaction' T"
  shows "wellformed_transaction T"
    and "admissible_transaction_checks T"
    and "admissible_transaction_updates T"
    and "admissible_transaction_terms T"
    and "admissible_transaction_send_occurs_form T"
using assms unfolding admissible_transaction'_def by blast+

lemma admissible_transaction_no_occurs_msgsE:
  assumes T: "admissible_transaction' T" "admissible_transaction_no_occurs_msgs T"
  shows "\<forall>ts. send\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T)) \<or>
              receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T)) \<longrightarrow>
                (\<forall>t s. t \<in> set ts \<longrightarrow> t \<noteq> occurs s)"
proof -
  note 1 = admissible_transaction_is_wellformed_transaction(1)[OF T(1)]

  have 2: "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))"
    when "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T))" for ts
    using wellformed_transaction_strand_unlabel_memberD(8)[OF 1 that] by fast

  have 3: "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T))"
    when "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T))" for ts
    using wellformed_transaction_strand_unlabel_memberD(1)[OF 1 that] by fast

  show ?thesis
    using T(2) 2 3 wellformed_transaction_unlabel_cases(1,4)[OF 1]
    unfolding admissible_transaction_no_occurs_msgs_def Let_def list_all_iff
    by (metis sndI stateful_strand_step.discI(1,2) stateful_strand_step.sel(1,2)
              term.discI(2) term.sel(2) unlabel_mem_has_label)
qed

lemma admissible_transactionE:
  assumes T: "admissible_transaction' T"
  shows "transaction_decl T () = []" (is ?A)
    and "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value" (is ?B)
    and "\<forall>x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T). \<Gamma>\<^sub>v x = TAtom Value" (is ?C)
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) = {}" (is ?D1)
    and "fv_transaction T \<inter> bvars_transaction T = {}" (is ?D2)
    and "set (transaction_fresh T) \<subseteq>
          fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (filter (is_Insert \<circ> snd) (transaction_updates T)) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
      (is ?E)
    and "set (transaction_fresh T) \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
      (is ?F)
    and "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
         \<forall>y \<in> fv_transaction T - set (transaction_fresh T).
          x \<noteq> y \<longrightarrow> \<langle>Var x != Var y\<rangle> \<in> set (unlabel (transaction_checks T)) \<or>
                    \<langle>Var y != Var x\<rangle> \<in> set (unlabel (transaction_checks T))"
      (is ?G)
    and "\<forall>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T).
          x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<or>
          (\<exists>t s. select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_checks T)) \<and> x \<in> fv t \<union> fv s)"
      (is ?H)
    and "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) - set (transaction_fresh T) \<subseteq>
          fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)"
      (is ?I)
    and "\<forall>x \<in> set (unlabel (transaction_checks T)).
          is_Equality x \<longrightarrow> fv (the_rhs x) \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
      (is ?J) (* TODO: why do we need this requirement? *)
    and "set (transaction_fresh T) \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) = {}" (is ?K1)
    and "set (transaction_fresh T) \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) = {}" (is ?K2)
    and "list_all (\<lambda>x. fst x = Var Value) (transaction_fresh T)" (is ?K3)
    and "\<forall>x \<in> vars_transaction T. \<not>TAtom AttackType \<sqsubseteq> \<Gamma>\<^sub>v x" (is ?K4)
    and "\<forall>l ts. (l,receive\<langle>ts\<rangle>) \<in> set (transaction_receive T) \<longrightarrow> ts \<noteq> []" (is ?L1)
    and "\<forall>l ts. (l,send\<langle>ts\<rangle>) \<in> set (transaction_send T) \<longrightarrow> ts \<noteq> []" (is ?L2)
proof -
  show ?A ?D1 ?D2 ?G ?I ?J ?K3
    using T unfolding admissible_transaction'_def
    by (blast, blast, blast, blast, blast, blast, blast)

  have "list_all (\<lambda>a. is_Receive (snd a) \<longrightarrow> the_msgs (snd a) \<noteq> []) (transaction_receive T)"
       "list_all (\<lambda>a. is_Send (snd a) \<longrightarrow> the_msgs (snd a) \<noteq> []) (transaction_send T)"
    using T unfolding admissible_transaction'_def by auto
  thus ?L1 ?L2 unfolding list_all_iff by (force,force)

  have "list_all (\<lambda>x. fst x = Var Value) (transaction_fresh T)"
       "\<forall>x\<in>vars_transaction T. is_Var (fst x) \<and> the_Var (fst x) = Value"
    using T unfolding admissible_transaction'_def by (blast, blast)
  thus ?B ?C ?K4 using \<Gamma>\<^sub>v_TAtom''(2) unfolding list_all_iff by (blast, force, force)

  show ?E using T unfolding admissible_transaction'_def by argo
  thus ?F unfolding unlabel_def by auto

  show ?K1 ?K2
    using T unfolding admissible_transaction'_def wellformed_transaction_def by (argo, argo)

  let ?selects = "filter (\<lambda>s. is_InSet (snd s) \<and> the_check (snd s) = Assign) (transaction_checks T)"

  show ?H
  proof
    fix x assume "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)"
    hence "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<or> x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?selects"
      using T unfolding admissible_transaction'_def by blast
    thus "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<or>
          (\<exists>t s. select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_checks T)) \<and> x \<in> fv t \<union> fv s)"
    proof
      assume "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?selects"
      then obtain r where r: "x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p r" "r \<in> set (unlabel (transaction_checks T))"
                             "is_InSet r" "the_check r = Assign"
        unfolding unlabel_def by force
      thus ?thesis by (cases r) auto
    qed simp
  qed
qed

lemma admissible_transactionE':
  assumes T: "admissible_transaction T"
  shows "admissible_transaction' T" (is ?A)
    and "admissible_transaction_no_occurs_msgs T" (is ?B)
    and "\<forall>ts. send\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T)) \<or>
              receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T)) \<longrightarrow>
                (\<forall>t s. t \<in> set ts \<longrightarrow> t \<noteq> occurs s)"
      (is ?C)
proof -
  show 0: ?A ?B using T unfolding admissible_transaction_def by (blast, blast)
  show ?C using admissible_transaction_no_occurs_msgsE[OF 0] by blast
qed

lemma transaction_inserts_are_Value_vars:
  assumes T_valid: "wellformed_transaction T"
    and "admissible_transaction_updates T"
    and "insert\<langle>t,s\<rangle> \<in> set (unlabel (transaction_strand T))"
  shows "\<exists>n. t = Var (TAtom Value, n)"
    and "\<exists>u. s = Fun (Set u) []"
proof -
  let ?x = "insert\<langle>t,s\<rangle>"

  have "?x \<in> set (unlabel (transaction_updates T))"
    using assms(3) wellformed_transaction_unlabel_cases[OF T_valid, of ?x]    
    by (auto simp add: transaction_strand_def unlabel_def)
  hence *: "is_Var (the_elem_term ?x)" "fst (the_Var (the_elem_term ?x)) = TAtom Value"
           "is_Fun (the_set_term ?x)" "args (the_set_term ?x) = []"
           "is_Set (the_Fun (the_set_term ?x))"
    using assms(2) unfolding admissible_transaction_updates_def is_Fun_Set_def by fastforce+
  
  show "\<exists>n. t = Var (TAtom Value, n)" using *(1,2) by (cases t) auto
  show "\<exists>u. s = Fun (Set u) []" using *(3,4,5) unfolding is_Set_def by (cases s) auto
qed

lemma transaction_deletes_are_Value_vars:
  assumes T_valid: "wellformed_transaction T"
    and "admissible_transaction_updates T"
    and "delete\<langle>t,s\<rangle> \<in> set (unlabel (transaction_strand T))"
  shows "\<exists>n. t = Var (TAtom Value, n)"
    and "\<exists>u. s = Fun (Set u) []"
proof -
  let ?x = "delete\<langle>t,s\<rangle>"

  have "?x \<in> set (unlabel (transaction_updates T))"
    using assms(3) wellformed_transaction_unlabel_cases[OF T_valid, of ?x]    
    by (auto simp add: transaction_strand_def unlabel_def)
  hence *: "is_Var (the_elem_term ?x)" "fst (the_Var (the_elem_term ?x)) = TAtom Value"
           "is_Fun (the_set_term ?x)" "args (the_set_term ?x) = []"
           "is_Set (the_Fun (the_set_term ?x))"
    using assms(2) unfolding admissible_transaction_updates_def is_Fun_Set_def by fastforce+
  
  show "\<exists>n. t = Var (TAtom Value, n)" using *(1,2) by (cases t) auto
  show "\<exists>u. s = Fun (Set u) []" using *(3,4,5) unfolding is_Set_def by (cases s) auto
qed

lemma transaction_selects_are_Value_vars:
  assumes T_valid: "wellformed_transaction T"
    and "admissible_transaction_checks T"
    and "select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_strand T))"
  shows "\<exists>n. t = Var (TAtom Value, n) \<and> (TAtom Value, n) \<notin> set (transaction_fresh T)" (is ?A)
    and "\<exists>u. s = Fun (Set u) []" (is ?B)
proof -
  let ?x = "select\<langle>t,s\<rangle>"

  have *: "?x \<in> set (unlabel (transaction_checks T))"
    using assms(3) wellformed_transaction_unlabel_cases[OF T_valid, of ?x]    
    by (auto simp add: transaction_strand_def unlabel_def)
  
  have **: "is_Var (the_elem_term ?x)" "fst (the_Var (the_elem_term ?x)) = TAtom Value"
           "is_Fun (the_set_term ?x)" "args (the_set_term ?x) = []"
           "is_Set (the_Fun (the_set_term ?x))"
    using * assms(2) unfolding admissible_transaction_checks_def is_Fun_Set_def by fastforce+

  have "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p ?x \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)"
    using * by force
  hence ***: "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p ?x \<inter> set (transaction_fresh T) = {}"
    using T_valid unfolding wellformed_transaction_def by fast

  show ?A using **(1,2) *** by (cases t) auto
  show ?B using **(3,4,5) unfolding is_Set_def by (cases s) auto
qed

lemma transaction_inset_checks_are_Value_vars:
  assumes T_valid: "admissible_transaction' T"
    and t: "\<langle>t in s\<rangle> \<in> set (unlabel (transaction_strand T))"
  shows "\<exists>n. t = Var (TAtom Value, n) \<and> (TAtom Value, n) \<notin> set (transaction_fresh T)" (is ?A)
    and "\<exists>u. s = Fun (Set u) []" (is ?B)
proof -
  let ?x = "\<langle>t in s\<rangle>"

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_valid]
  note T_adm_checks = admissible_transaction_is_wellformed_transaction(2)[OF T_valid]

  have *: "?x \<in> set (unlabel (transaction_checks T))"
    using t wellformed_transaction_unlabel_cases[OF T_wf, of ?x]
    unfolding transaction_strand_def unlabel_def by fastforce
  
  have **: "is_Var (the_elem_term ?x)" "fst (the_Var (the_elem_term ?x)) = TAtom Value"
           "is_Fun (the_set_term ?x)" "args (the_set_term ?x) = []"
           "is_Set (the_Fun (the_set_term ?x))"
    using * T_adm_checks unfolding admissible_transaction_checks_def is_Fun_Set_def by fastforce+

  have "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p ?x \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)"
    using * by force
  hence ***: "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p ?x \<inter> set (transaction_fresh T) = {}"
    using T_wf unfolding wellformed_transaction_def by fast

  show ?A using **(1,2) *** by (cases t) auto
  show ?B using **(3,4,5) unfolding is_Set_def by (cases s) auto
qed

lemma transaction_notinset_checks_are_Value_vars:
  assumes T_adm: "admissible_transaction' T"
    and FG: "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set (unlabel (transaction_strand T))"
    and t: "(t,s) \<in> set G"
  shows "\<exists>n. t = Var (TAtom Value, n) \<and> (TAtom Value, n) \<notin> set (transaction_fresh T)" (is ?A)
    and "\<exists>u. s = Fun (Set u) []" (is ?B)
    and "F = []" (is ?C)
    and "G = [(t,s)]" (is ?D)
proof -
  let ?x = "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>"

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]
  note T_adm_checks = admissible_transaction_is_wellformed_transaction(2)[OF T_adm]

  have 0: "?x \<in> set (unlabel (transaction_checks T))"
    using FG wellformed_transaction_unlabel_cases[OF T_wf, of ?x]    
    by (auto simp add: transaction_strand_def unlabel_def)
  hence 1: "F = [] \<and> length G = 1"
    using T_adm_checks t unfolding admissible_transaction_checks_def by fastforce
  hence "hd G = (t,s)" using t by (cases "the_ins ?x") auto
  hence **: "is_Var t" "fst (the_Var t) = TAtom Value" "is_Fun s" "args s = []" "is_Set (the_Fun s)"
    using 1 Set.bspec[OF T_adm_checks[unfolded admissible_transaction_checks_def] 0]
    unfolding is_Fun_Set_def by auto

  show ?C using 1 by blast
  show ?D using 1 t by force

  have "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p ?x \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)"
       "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p ?x) \<subseteq> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)"
    using 0 by force+
  moreover have
      "set (transaction_fresh T) \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) = {}"
      "set (transaction_fresh T) \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) = {}"
    using T_wf unfolding wellformed_transaction_def by fast+
  ultimately have
      "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p ?x \<inter> set (transaction_fresh T) = {}"
      "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p ?x) \<inter> set (transaction_fresh T) = {}"
    using admissible_transactionE(7)[OF T_adm]
          wellformed_transaction_wf\<^sub>s\<^sub>s\<^sub>t(2)[OF T_wf]
          fv_transaction_unfold[of T] bvars_transaction_unfold[of T]
    by (blast, blast)
  hence ***: "fv t \<inter> set (transaction_fresh T) = {}"
    using t by auto

  show ?A using **(1,2) *** by (cases t) auto
  show ?B using **(3,4,5) unfolding is_Set_def by (cases s) auto
qed

lemma transaction_noteqs_checks_case:
  assumes T_adm: "admissible_transaction' T"
    and FG: "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set (unlabel (transaction_strand T))"
    and G: "G = []"
  shows "\<exists>t s. F = [(t,s)]" (is ?A)
proof -
  let ?x = "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>"

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]
  note T_adm_checks = admissible_transaction_is_wellformed_transaction(2)[OF T_adm]

  have "?x \<in> set (unlabel (transaction_checks T))"
    using FG wellformed_transaction_unlabel_cases[OF T_wf, of ?x]    
    by (auto simp add: transaction_strand_def unlabel_def)
  hence "length F = 1"
    using T_adm_checks unfolding admissible_transaction_checks_def G by fastforce
  thus ?thesis by fast
qed

lemma admissible_transaction_fresh_vars_notin:
  assumes T: "admissible_transaction' T"
    and x: "x \<in> set (transaction_fresh T)"
  shows "x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)" (is ?A)
    and "x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)" (is ?B)
    and "x \<notin> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)" (is ?C)
    and "x \<notin> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)" (is ?D)
    and "x \<notin> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)" (is ?E)
    and "x \<notin> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)" (is ?F)
proof -
  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T]

  have 0:
      "set (transaction_fresh T) \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
      "set (transaction_fresh T) \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) = {}"
      "set (transaction_fresh T) \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) = {}"
      "fv_transaction T \<inter> bvars_transaction T = {}"
    using admissible_transactionE[OF T] by argo+

  have 1: "set (transaction_fresh T) \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) = {}"
    using 0(1,4) fv_transaction_unfold[of T] bvars_transaction_unfold[of T] by blast

  have 2:
      "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) = fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
      "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) = {}"
    using bvars_wellformed_transaction_unfold[OF T_wf]
          vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_receive T)"]
    by blast+
  
  show ?A ?B ?C ?E ?F using 0 1 2 x by (fast, fast, fast, fast, fast)

  show ?D using 0(3) 1 x vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_checks T)"] by fast
qed

lemma admissible_transaction_fv_in_receives_or_selects:
  assumes T: "admissible_transaction' T"
    and x: "x \<in> fv_transaction T" "x \<notin> set (transaction_fresh T)"
  shows "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<or>
         (x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<and>
          (\<exists>t s. select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_checks T)) \<and> x \<in> fv t \<union> fv s))"
proof -
  have "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<union>
            fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
    using x(1) fv\<^sub>s\<^sub>s\<^sub>t_append unlabel_append 
    by (metis transaction_strand_def append_assoc)
  thus ?thesis using x(2) admissible_transactionE(9,10)[OF T] by blast
qed

lemma admissible_transaction_fv_in_receives_or_selects':
  assumes T: "admissible_transaction' T"
    and x: "x \<in> fv_transaction T" "x \<notin> set (transaction_fresh T)"
  shows "(\<exists>ts. receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T)) \<and> x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set ts)) \<or>
         (\<exists>s. select\<langle>Var x, s\<rangle> \<in> set (unlabel (transaction_checks T)))"
proof (cases "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)")
  case True thus ?thesis
    using wellformed_transaction_unlabel_cases(1)[
            OF admissible_transaction_is_wellformed_transaction(1)[OF T]]
    by force
next
  case False
  then obtain t s where t: "select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_checks T))" "x \<in> fv t \<union> fv s"
    using admissible_transaction_fv_in_receives_or_selects[OF T x] by blast

  have t': "select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_strand T))"
    using t(1) unfolding transaction_strand_def by simp

  show ?thesis
    using t transaction_selects_are_Value_vars[
              OF admissible_transaction_is_wellformed_transaction(1,2)[OF T] t']
    by force
qed

lemma admissible_transaction_fv_in_receives_or_selects_subst:
  assumes T: "admissible_transaction' T"
    and x: "x \<in> fv_transaction T" "x \<notin> set (transaction_fresh T)"
  shows "(\<exists>ts. receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<and> \<theta> x \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set ts) \<or>
         (\<exists>s. select\<langle>\<theta> x, s\<rangle> \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
proof -
  note 0 = admissible_transaction_fv_in_receives_or_selects'[OF T x]

  have 1: "\<theta> x \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set (ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>)" when ts: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set ts)" for ts
    using that subst_mono_fv[of x _ \<theta>] by auto

  have 2: "receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)" when "receive\<langle>ts\<rangle> \<in> set A" for ts A
    using that by fast

  have 3: "select\<langle>t \<cdot> \<theta>,s \<cdot> \<theta>\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)" when "select\<langle>t,s\<rangle> \<in> set A" for t s A
    using that by fast

  show ?thesis
    using 0 1 2[of _ "unlabel (transaction_receive T)"]
          3[of _ _ "unlabel (transaction_checks T)"]
    unfolding unlabel_subst by (metis eval_term.simps(1)) 
qed

lemma admissible_transaction_fv_in_receives_or_selects_dual_subst:
  defines "f \<equiv> \<lambda>S. unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S)"
  assumes T: "admissible_transaction' T"
    and x: "x \<in> fv_transaction T" "x \<notin> set (transaction_fresh T)"
  shows "(\<exists>ts. send\<langle>ts\<rangle> \<in> set (f (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<and> \<theta> x \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set ts) \<or>
         (\<exists>s. select\<langle>\<theta> x, s\<rangle> \<in> set (f (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
using admissible_transaction_fv_in_receives_or_selects_subst[OF T x, of \<theta>]
by (metis (no_types, lifting) f_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(2) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(6)) 

lemma admissible_transaction_decl_subst_empty':
  assumes T: "transaction_decl T () = []"
    and \<xi>: "transaction_decl_subst \<xi> T"
  shows "\<xi> = Var"
proof -
  have "subst_domain \<xi> = {}"
    using \<xi> T unfolding transaction_decl_subst_def by auto
  thus ?thesis by auto
qed

lemma admissible_transaction_decl_subst_empty:
  assumes T: "admissible_transaction' T"
    and \<xi>: "transaction_decl_subst \<xi> T"
  shows "\<xi> = Var"
by (rule admissible_transaction_decl_subst_empty'[OF admissible_transactionE(1)[OF T] \<xi>])

lemma admissible_transaction_no_bvars:
  assumes "admissible_transaction' T"
  shows "fv_transaction T = vars_transaction T"
    and "bvars_transaction T = {}"
using admissible_transactionE(4)[OF assms]
      bvars_wellformed_transaction_unfold vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t
by (fast, fast)

lemma admissible_transactions_fv_bvars_disj:
  assumes "\<forall>T \<in> set P. admissible_transaction' T"
  shows "(\<Union>T \<in> set P. fv_transaction T) \<inter> (\<Union>T \<in> set P. bvars_transaction T) = {}"
using assms admissible_transaction_no_bvars(2) by fast

lemma admissible_transaction_occurs_fv_types:
  assumes "admissible_transaction' T"
    and "x \<in> vars_transaction T"
  shows "\<exists>a. \<Gamma> (Var x) = TAtom a \<and> \<Gamma> (Var x) \<noteq> TAtom OccursSecType"
proof -
  have "is_Var (fst x)" "the_Var (fst x) = Value"
    using assms unfolding admissible_transaction'_def by blast+
  thus ?thesis using \<Gamma>\<^sub>v_TAtom''(2)[of x] by force
qed

lemma admissible_transaction_Value_vars_are_fv:
  assumes "admissible_transaction' T"
    and "x \<in> vars_transaction T"
    and "\<Gamma>\<^sub>v x = TAtom Value"
  shows "x \<in> fv_transaction T"
using assms(2,3) \<Gamma>\<^sub>v_TAtom''(2)[of x] vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
      admissible_transactionE(4)[OF assms(1)]
by fast

lemma transaction_receive_deduct:
  assumes T_wf: "wellformed_transaction T"
    and \<I>: "constraint_model \<I> (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T M"
    and \<alpha>: "transaction_renaming_subst \<alpha> P X"
    and t: "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
  shows "\<forall>t \<in> set ts. ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>"
proof -
  define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  have t': "send\<langle>ts\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
    using t dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(2) unfolding \<theta>_def by blast
  then obtain T1 T2 where T: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) = T1@send\<langle>ts\<rangle>#T2"
    using t' by (meson split_list)

  have "constr_sem_stateful \<I> (unlabel A@unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
    using \<I> unlabel_append[of A] unfolding constraint_model_def \<theta>_def by simp
  hence "constr_sem_stateful \<I> (unlabel A@T1@[send\<langle>ts\<rangle>])"
    using strand_sem_append_stateful[of "{}" "{}" "unlabel A@T1@[send\<langle>ts\<rangle>]" _ \<I>]
          transaction_dual_subst_unlabel_unfold[of T \<theta>] T
    by (metis append.assoc append_Cons append_Nil)
  hence "\<forall>t \<in> set ts. ik\<^sub>s\<^sub>s\<^sub>t (unlabel A@T1) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>"
    using strand_sem_append_stateful[of "{}" "{}" "unlabel A@T1" "[send\<langle>ts\<rangle>]" \<I>] T
    by force
  moreover have "\<not>is_Receive x"
    when x: "x \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))" for x
  proof -
    have *: "is_Receive a" when "a \<in> set (unlabel (transaction_receive T))" for a
      using T_wf Ball_set[of "unlabel (transaction_receive T)" is_Receive] that
      unfolding wellformed_transaction_def
      by blast

    obtain l where l: "(l,x) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
      using x unfolding unlabel_def by fastforce
    then obtain ly where ly: "ly \<in> set (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)" "(l,x) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ly"
      unfolding dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto

    obtain j y where j: "ly = (j,y)" by (metis surj_pair)
    hence "j = l" using ly(2) by (cases y) auto
    hence y: "(l,y) \<in> set (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)" "(l,x) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (l,y)"
      by (metis j ly(1), metis j ly(2))

    obtain z where z:
        "z \<in> set (unlabel (transaction_receive T))"
        "(l,z) \<in> set (transaction_receive T)"
        "(l,y) = (l,z) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>"
      using y(1) unfolding subst_apply_labeled_stateful_strand_def unlabel_def by force

    have "is_Receive y" using *[OF z(1)] z(3) by (cases z) auto
    thus "\<not>is_Receive x" using l y by (cases y) auto
  qed
  hence "\<not>is_Receive x" when "x \<in> set T1" for x using T that by simp
  hence "ik\<^sub>s\<^sub>s\<^sub>t T1 = {}" unfolding ik\<^sub>s\<^sub>s\<^sub>t_def is_Receive_def by fast
  hence "ik\<^sub>s\<^sub>s\<^sub>t (unlabel A@T1) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" using ik\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel A" T1] by simp
  ultimately show ?thesis by (simp add: \<theta>_def)
qed

lemma transaction_checks_db:
  assumes T: "admissible_transaction' T"
    and \<I>: "constraint_model \<I> (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T M"
    and \<alpha>: "transaction_renaming_subst \<alpha> P X"
  shows "\<langle>Var (TAtom Value, n) in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))
          \<Longrightarrow> (\<alpha> (TAtom Value, n) \<cdot> \<I>, Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<I>)"
      (is "?A \<Longrightarrow> ?B")
    and "\<langle>Var (TAtom Value, n) not in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))
          \<Longrightarrow> (\<alpha> (TAtom Value, n) \<cdot> \<I>, Fun (Set s) []) \<notin> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<I>)"
      (is "?C \<Longrightarrow> ?D")
proof -
  let ?x = "\<lambda>n. (TAtom Value, n)"
  let ?s = "Fun (Set s) []"
  let ?T = "transaction_receive T@transaction_checks T"
  let ?T' = "?T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
  let ?S = "\<lambda>S. transaction_receive T@S"
  let ?S' = "\<lambda>S. ?S S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T \<xi>]

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T]

  have "constr_sem_stateful \<I> (unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)))"
    using \<I> unfolding constraint_model_def by simp
  moreover have
      "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) =
       dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S (T1@[c]) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)@
       dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T2@transaction_updates T@transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
    when "transaction_checks T = T1@c#T2" for T1 T2 c \<delta>
    using that dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append subst_lsst_append
    unfolding transaction_strand_def
    by (metis append.assoc append_Cons append_Nil)
  ultimately have T'_model: "constr_sem_stateful \<I> (unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' (T1@[(l,c)]))))"
    when "transaction_checks T = T1@(l,c)#T2" for T1 T2 l c
    using strand_sem_append_stateful[of _ _ _ _ \<I>]
    by (simp add: that transaction_strand_def)

  show "?A \<Longrightarrow> ?B"
  proof -
    assume a: ?A
    hence *: "\<langle>Var (?x n) in ?s\<rangle> \<in> set (unlabel ?T)"
      unfolding transaction_strand_def unlabel_def by simp
    then obtain l T1 T2 where T1: "transaction_checks T = T1@(l,\<langle>Var (?x n) in ?s\<rangle>)#T2"
      by (metis a split_list unlabel_mem_has_label)

    have "?x n \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)"
      using a by force
    hence "?x n \<notin> set (transaction_fresh T)"
      using a admissible_transaction_fresh_vars_notin[OF T] by fast
    hence "unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' (T1@[(l,\<langle>Var (?x n) in ?s\<rangle>)]))) =
           unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' T1))@[\<langle>\<alpha> (?x n) in ?s\<rangle>]"
      using T a \<sigma> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append subst_lsst_append unlabel_append \<xi>_empty
      by (fastforce simp add: transaction_fresh_subst_def unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def
                              subst_apply_labeled_stateful_strand_def subst_compose)
    moreover have "db\<^sub>s\<^sub>s\<^sub>t (unlabel A) = db\<^sub>s\<^sub>s\<^sub>t (unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' T1)))"
      by (simp add: T1 db\<^sub>s\<^sub>s\<^sub>t_transaction_prefix_eq[OF T_wf] del: unlabel_append)
    ultimately have "\<exists>M. strand_sem_stateful M (set (db\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<I>)) [\<langle>\<alpha> (?x n) in ?s\<rangle>] \<I>"
      using T'_model[OF T1] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of _ \<I>] strand_sem_append_stateful[of _ _ _ _ \<I>]
      by (simp add: db\<^sub>s\<^sub>s\<^sub>t_def del: unlabel_append)
    thus ?B by simp
  qed

  show "?C \<Longrightarrow> ?D"
  proof -
    assume a: ?C
    hence *: "\<langle>Var (?x n) not in ?s\<rangle> \<in> set (unlabel ?T)"
      unfolding transaction_strand_def unlabel_def by simp
    then obtain l T1 T2 where T1: "transaction_checks T = T1@(l,\<langle>Var (?x n) not in ?s\<rangle>)#T2"
      by (metis a split_list unlabel_mem_has_label)

    have "?x n \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<langle>Var (?x n) not in ?s\<rangle>"
      using vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_cases(9)[of "[]" "Var (?x n)" ?s] by auto
    hence "?x n \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)"
      using a unfolding vars\<^sub>s\<^sub>s\<^sub>t_def by force
    hence "?x n \<notin> set (transaction_fresh T)"
      using a admissible_transaction_fresh_vars_notin[OF T] by fast
    hence "unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' (T1@[(l,\<langle>Var (?x n) not in ?s\<rangle>)]))) =
           unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' T1))@[\<langle>\<alpha> (?x n) not in ?s\<rangle>]"
      using T a \<sigma> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append subst_lsst_append unlabel_append \<xi>_empty
      by (fastforce simp add: transaction_fresh_subst_def unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def
                              subst_apply_labeled_stateful_strand_def subst_compose)
    moreover have "db\<^sub>s\<^sub>s\<^sub>t (unlabel A) = db\<^sub>s\<^sub>s\<^sub>t (unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' T1)))"
      by (simp add: T1 db\<^sub>s\<^sub>s\<^sub>t_transaction_prefix_eq[OF T_wf] del: unlabel_append)
    ultimately have "\<exists>M. strand_sem_stateful M (set (db\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<I>)) [\<langle>\<alpha> (?x n) not in ?s\<rangle>] \<I>"
      using T'_model[OF T1] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of _ \<I>] strand_sem_append_stateful[of _ _ _ _ \<I>]
      by (simp add: db\<^sub>s\<^sub>s\<^sub>t_def del: unlabel_append)
    thus ?D using stateful_strand_sem_NegChecks_no_bvars(1)[of _ _ _ ?s \<I>] by simp
  qed
qed

lemma transaction_selects_db:
  assumes T: "admissible_transaction' T"
    and \<I>: "constraint_model \<I> (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T M"
    and \<alpha>: "transaction_renaming_subst \<alpha> P X"
  shows "select\<langle>Var (TAtom Value, n), Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))
          \<Longrightarrow> (\<alpha> (TAtom Value, n) \<cdot> \<I>, Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<I>)"
      (is "?A \<Longrightarrow> ?B")
proof -
  let ?x = "\<lambda>n. (TAtom Value, n)"
  let ?s = "Fun (Set s) []"
  let ?T = "transaction_receive T@transaction_checks T"
  let ?T' = "?T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
  let ?S = "\<lambda>S. transaction_receive T@S"
  let ?S' = "\<lambda>S. ?S S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T \<xi>]

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T]

  have "constr_sem_stateful \<I> (unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)))"
    using \<I> unfolding constraint_model_def by simp
  moreover have
      "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) =
       dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S (T1@[c]) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)@
       dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T2@transaction_updates T@transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
    when "transaction_checks T = T1@c#T2" for T1 T2 c \<delta>
    using that dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append subst_lsst_append
    unfolding transaction_strand_def by (metis append.assoc append_Cons append_Nil)
  ultimately have T'_model: "constr_sem_stateful \<I> (unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' (T1@[(l,c)]))))"
    when "transaction_checks T = T1@(l,c)#T2" for T1 T2 l c
    using strand_sem_append_stateful[of _ _ _ _ \<I>]
    by (simp add: that transaction_strand_def)

  show "?A \<Longrightarrow> ?B"
  proof -
    assume a: ?A
    hence *: "select\<langle>Var (?x n), ?s\<rangle> \<in> set (unlabel ?T)"
      unfolding transaction_strand_def unlabel_def by simp
    then obtain l T1 T2 where T1: "transaction_checks T = T1@(l,select\<langle>Var (?x n), ?s\<rangle>)#T2"
      by (metis a split_list unlabel_mem_has_label)

    have "?x n \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)"
      using a by force
    hence "?x n \<notin> set (transaction_fresh T)"
      using a admissible_transaction_fresh_vars_notin[OF T] by fast
    hence "unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' (T1@[(l,select\<langle>Var (?x n), ?s\<rangle>)]))) =
           unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' T1))@[select\<langle>\<alpha> (?x n), ?s\<rangle>]"
      using T a \<sigma> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append subst_lsst_append unlabel_append \<xi>_empty
      by (fastforce simp add: transaction_fresh_subst_def unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def
                              subst_apply_labeled_stateful_strand_def subst_compose)
    moreover have "db\<^sub>s\<^sub>s\<^sub>t (unlabel A) = db\<^sub>s\<^sub>s\<^sub>t (unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (?S' T1)))"
      by (simp add: T1 db\<^sub>s\<^sub>s\<^sub>t_transaction_prefix_eq[OF T_wf] del: unlabel_append)
    ultimately have "\<exists>M. strand_sem_stateful M (set (db\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<I>)) [\<langle>\<alpha> (?x n) in ?s\<rangle>] \<I>"
      using T'_model[OF T1] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of _ \<I>] strand_sem_append_stateful[of _ _ _ _ \<I>]
      by (simp add: db\<^sub>s\<^sub>s\<^sub>t_def del: unlabel_append)
    thus ?B by simp
  qed
qed

lemma admissible_transaction_terms_no_Value_consts:
  assumes "admissible_transaction_terms T"
    and "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"
  shows "\<nexists>a T. t = Fun (Val a) T" (is ?A)
    and "\<nexists>a T. t = Fun (Abs a) T" (is ?B)
    and "\<nexists>a T. t = Fun (PubConst Value a) T" (is ?C)
proof -
  have "\<not>is_Val f" "\<not>is_Abs f" "\<not>is_PubConstValue f"
    when "f \<in> \<Union>(funs_term ` (trms_transaction T))" for f
    using that assms(1)[unfolded admissible_transaction_terms_def]
    unfolding is_PubConstValue_def by (blast,blast,blast)
  moreover have "f \<in> \<Union>(funs_term ` (trms_transaction T))"
    when "f \<in> funs_term t" for f
    using that assms(2) funs_term_subterms_eq(2)[of "trms_transaction T"] by blast+
  ultimately have *: "\<not>is_Val f" "\<not>is_Abs f" "\<not>is_PubConstValue f"
    when "f \<in> funs_term t" for f
    using that by presburger+

  show ?A using *(1) by force
  show ?B using *(2) by force
  show ?C using *(3) unfolding is_PubConstValue_def by force
qed

lemma admissible_transactions_no_Value_consts:
  assumes "admissible_transaction' T"
    and "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"
  shows "\<nexists>a T. t = Fun (Val a) T" (is ?A)
    and "\<nexists>a T. t = Fun (Abs a) T" (is ?B)
    and "\<nexists>a T. t = Fun (PubConst Value a) T" (is ?C)
using admissible_transaction_terms_no_Value_consts[OF
        admissible_transaction_is_wellformed_transaction(4)[OF assms(1)] assms(2)]
by auto

lemma admissible_transactions_no_Value_consts':
  assumes "admissible_transaction' T"
    and "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)"
  shows "\<nexists>a T. Fun (Val a) T \<in> subterms t"
    and "\<nexists>a T. Fun (Abs a) T \<in> subterms t"
using admissible_transactions_no_Value_consts[OF assms(1)] assms(2) by fast+

lemma admissible_transactions_no_Value_consts'':
  assumes "admissible_transaction' T"
  shows "\<forall>n. PubConst Value n \<notin> \<Union>(funs_term ` trms_transaction T)"
    and "\<forall>n. Abs n \<notin> \<Union>(funs_term ` trms_transaction T)"
using assms
unfolding admissible_transaction'_def admissible_transaction_terms_def
by (meson prot_fun.discI(6), meson prot_fun.discI(4))

lemma admissible_transactions_no_PubConsts:
  assumes "admissible_transaction' T"
    and "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"
  shows "\<nexists>a n T. t = Fun (PubConst a n) T"
proof -
  have "\<not>is_PubConst f"
    when "f \<in> \<Union>(funs_term ` (trms_transaction T))" for f
    using that conjunct1[OF conjunct2[OF admissible_transaction_is_wellformed_transaction(4)[
            OF assms(1), unfolded admissible_transaction_terms_def]]]
    by blast
  moreover have "f \<in> \<Union>(funs_term ` (trms_transaction T))"
    when "f \<in> funs_term t" for f
    using that assms(2) funs_term_subterms_eq(2)[of "trms_transaction T"] by blast+
  ultimately have *: "\<not>is_PubConst f"
    when "f \<in> funs_term t" for f
    using that by presburger+

  show ?thesis using * by force
qed

lemma admissible_transactions_no_PubConsts':
  assumes "admissible_transaction' T"
    and "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)"
  shows "\<nexists>a n T. Fun (PubConst a n) T \<in> subterms t"
using admissible_transactions_no_PubConsts[OF assms(1)] assms(2) by fast+

lemma admissible_transaction_strand_step_cases:
  assumes T_adm: "admissible_transaction' T"
  shows "r \<in> set (unlabel (transaction_receive T)) \<Longrightarrow> \<exists>t. r = receive\<langle>t\<rangle>"
        (is "?A \<Longrightarrow> ?A'")
    and "r \<in> set (unlabel (transaction_checks T)) \<Longrightarrow>
            (\<exists>x s. (r = \<langle>Var x in Fun (Set s) []\<rangle> \<or> r = select\<langle>Var x, Fun (Set s) []\<rangle> \<or>
                   r = \<langle>Var x not in Fun (Set s) []\<rangle>) \<and>
                   fst x = TAtom Value \<and> x \<in> fv_transaction T - set (transaction_fresh T)) \<or>
            (\<exists>s t. r = \<langle>s == t\<rangle> \<or> r = \<langle>s := t\<rangle> \<or> r = \<langle>s != t\<rangle>)"
        (is "?B \<Longrightarrow> ?B'")
    and "r \<in> set (unlabel (transaction_updates T)) \<Longrightarrow>
            \<exists>x s. (r = insert\<langle>Var x, Fun (Set s) []\<rangle> \<or> r = delete\<langle>Var x, Fun (Set s) []\<rangle>) \<and>
                  fst x = TAtom Value"
        (is "?C \<Longrightarrow> ?C'")
    and "r \<in> set (unlabel (transaction_send T)) \<Longrightarrow> \<exists>t. r = send\<langle>t\<rangle>"
        (is "?D \<Longrightarrow> ?D'")
proof -
  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  show "?A \<Longrightarrow> ?A'"
    using T_wf Ball_set[of "unlabel (transaction_receive T)" is_Receive]
    unfolding wellformed_transaction_def is_Receive_def
    by blast

  show "?D \<Longrightarrow> ?D'"
    using T_wf Ball_set[of "unlabel (transaction_send T)" is_Send]
    unfolding wellformed_transaction_def is_Send_def
    by blast

  show "?B \<Longrightarrow> ?B'"
  proof -
    assume r: ?B
    note adm_checks = admissible_transaction_is_wellformed_transaction(1,2)[OF T_adm]

    have fv_r1: "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p r \<subseteq> fv_transaction T"
      using r fv_transaction_unfold[of T] by auto
  
    have fv_r2: "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p r \<inter> set (transaction_fresh T) = {}"
      using r T_wf unfolding wellformed_transaction_def by fastforce

    have "list_all is_Check_or_Assignment (unlabel (transaction_checks T))"
      using adm_checks(1) unfolding wellformed_transaction_def by blast
    hence "is_InSet r \<or> is_Equality r \<or> is_NegChecks r"
      using r unfolding list_all_iff by blast
    thus ?B'
    proof (elim disjE conjE)
      assume *: "is_InSet r"
      hence **: "is_Var (the_elem_term r)" "is_Fun (the_set_term r)"
                "is_Set (the_Fun (the_set_term r))" "args (the_set_term r) = []"
                "fst (the_Var (the_elem_term r)) = TAtom Value"
        using r adm_checks unfolding admissible_transaction_checks_def is_Fun_Set_def
        by fast+
      
      obtain ac rt rs where r': "r = \<langle>ac: rt \<in> rs\<rangle>" using * by (cases r) auto
      obtain x where x: "rt = Var x" "fst x = TAtom Value" using **(1,5) r' by auto
      obtain f S where fS: "rs = Fun f S" using **(2) r' by auto
      obtain s where s: "f = Set s" using **(3) fS r' by (cases f) auto
      hence S: "S = []" using **(4) fS r' by auto
  
      show ?B' using r' x fS s S fv_r1 fv_r2 by (cases ac) simp_all
    next
      assume *: "is_NegChecks r"
      hence **: "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p r = []"
                "(the_eqs r = [] \<and> length (the_ins r) = 1) \<or>
                 (the_ins r = [] \<and> length (the_eqs r) = 1)"
        using r adm_checks unfolding admissible_transaction_checks_def by fast+
      show ?B' using **(2)
      proof (elim disjE conjE)
        assume ***: "the_eqs r = []" "length (the_ins r) = 1"
        then obtain t s where ts: "the_ins r = [(t,s)]" by (cases "the_ins r") auto
        hence "hd (the_ins r) = (t,s)" by simp
        hence ****: "is_Var (fst (t,s))" "is_Fun (snd (t,s))"
                    "is_Set (the_Fun (snd (t,s)))" "args (snd (t,s)) = []"
                    "fst (the_Var (fst (t,s))) = TAtom Value"
          using * ***(1) Set.bspec[OF adm_checks(2)[unfolded admissible_transaction_checks_def] r]
          unfolding is_Fun_Set_def by simp_all
        obtain x where x: "t = Var x" "fst x = TAtom Value" using ts ****(1,5) by (cases t) simp_all
        obtain f S where fS: "s = Fun f S" using ts ****(2) by (cases s) simp_all
        obtain ss where ss: "f = Set ss" using fS ****(3) by (cases f) simp_all
        have S: "S = []" using ts fS ss ****(4) by simp
        
        show ?B' using ts x fS ss S *** **(1) * fv_r1 fv_r2 by (cases r) auto
      next
        assume ***: "the_ins r = []" "length (the_eqs r) = 1"
        then obtain t s where "the_eqs r = [(t,s)]" by (cases "the_eqs r") auto
        thus ?B' using *** **(1) * by (cases r) auto
      qed
    qed (auto simp add: is_Equality_def the_check_def intro: poscheckvariant.exhaust)
  qed

  show "?C \<Longrightarrow> ?C'"
  proof -
    assume r: ?C
    note adm_upds = admissible_transaction_is_wellformed_transaction(3)[OF T_adm]

    have *: "is_Update r" "is_Var (the_elem_term r)" "is_Fun (the_set_term r)"
            "is_Set (the_Fun (the_set_term r))" "args (the_set_term r) = []"
            "fst (the_Var (the_elem_term r)) = TAtom Value"
      using r adm_upds unfolding admissible_transaction_updates_def is_Fun_Set_def by fast+

    obtain t s where ts: "r = insert\<langle>t,s\<rangle> \<or> r = delete\<langle>t,s\<rangle>" using *(1) by (cases r) auto
    obtain x where x: "t = Var x" "fst x = TAtom Value" using ts *(2,6) by (cases t) auto
    obtain f T where fT: "s = Fun f T" using ts *(3) by (cases s) auto
    obtain ss where ss: "f = Set ss" using ts fT *(4) by (cases f) fastforce+
    have T: "T = []" using ts fT *(5) ss by (cases T) auto

    show ?C'
      using ts x fT ss T by blast
  qed
qed

lemma protocol_transaction_vars_TAtom_typed:
  assumes T_adm: "admissible_transaction' T"
  shows "\<forall>x \<in> vars_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    and "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    and "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
proof -
  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  show "\<forall>x \<in> vars_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    using admissible_transactionE(3)[OF T_adm] by fast
  thus "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    using vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t by fast

  show "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    using admissible_transactionE(2)[OF T_adm] by argo
qed

lemma protocol_transactions_no_pubconsts:
  assumes "admissible_transaction' T"
  shows "Fun (Val n) S \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms_transaction T)"
    and "Fun (PubConst Value n) S \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms_transaction T)"
using assms admissible_transactions_no_Value_consts(1,3) by (blast, blast)

lemma protocol_transactions_no_abss:
  assumes "admissible_transaction' T"
  shows "Fun (Abs n) S \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms_transaction T)"
using assms admissible_transactions_no_Value_consts(2)
by fast

lemma admissible_transaction_strand_sem_fv_ineq:
  assumes T_adm: "admissible_transaction' T"
    and \<I>: "strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) \<I>"
    and x: "x \<in> fv_transaction T - set (transaction_fresh T)"
    and y: "y \<in> fv_transaction T - set (transaction_fresh T)"
    and x_not_y: "x \<noteq> y"
  shows "\<theta> x \<cdot> \<I> \<noteq> \<theta> y \<cdot> \<I>"
proof -
  have "\<langle>Var x != Var y\<rangle> \<in> set (unlabel (transaction_checks T)) \<or>
        \<langle>Var y != Var x\<rangle> \<in> set (unlabel (transaction_checks T))"
    using x y x_not_y admissible_transactionE(8)[OF T_adm] by auto
  hence "\<langle>Var x != Var y\<rangle> \<in> set (unlabel (transaction_strand T)) \<or>
         \<langle>Var y != Var x\<rangle> \<in> set (unlabel (transaction_strand T))"
    unfolding transaction_strand_def unlabel_def by auto
  hence "\<langle>\<theta> x != \<theta> y\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) \<or>
         \<langle>\<theta> y != \<theta> x\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
    using stateful_strand_step_subst_inI(8)[of _ _ "unlabel (transaction_strand T)" \<theta>]
          subst_lsst_unlabel[of "transaction_strand T" \<theta>]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(7)[of "[]" _ "[]"]
    by force
  then obtain B where B:
      "prefix (B@[\<langle>\<theta> x != \<theta> y\<rangle>]) (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) \<or>
       prefix (B@[\<langle>\<theta> y != \<theta> x\<rangle>]) (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
    unfolding prefix_def
    by (metis (no_types, opaque_lifting) append.assoc append_Cons append_Nil split_list)
  thus ?thesis
    using \<I> strand_sem_append_stateful[of IK DB _ _ \<I>]
          stateful_strand_sem_NegChecks_no_bvars(2)
    unfolding prefix_def
    by metis 
qed

lemma admissible_transaction_sem_iff:
  fixes \<theta> and T::"('fun,'atom,'sets,'lbl) prot_transaction"
  defines "A \<equiv> unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  assumes T: "admissible_transaction' T"
    and I: " interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
  shows "strand_sem_stateful M D A I \<longleftrightarrow> (
    (\<forall>l ts. (l,receive\<langle>ts\<rangle>) \<in> set (transaction_receive T) \<longrightarrow> (\<forall>t \<in> set ts. M \<turnstile> t \<cdot> \<theta> \<cdot> I)) \<and>
    (\<forall>l ac t s. (l,\<langle>ac: t \<doteq> s\<rangle>) \<in> set (transaction_checks T) \<longrightarrow> t \<cdot> \<theta> \<cdot> I = s \<cdot> \<theta> \<cdot> I) \<and>
    (\<forall>l ac t s. (l,\<langle>ac: t \<in> s\<rangle>) \<in> set (transaction_checks T) \<longrightarrow> (t \<cdot> \<theta> \<cdot> I, s \<cdot> \<theta> \<cdot> I) \<in> D) \<and>
    (\<forall>l t s. (l,\<langle>t != s\<rangle>) \<in> set (transaction_checks T) \<longrightarrow> t \<cdot> \<theta> \<cdot> I \<noteq> s \<cdot> \<theta> \<cdot> I) \<and>
    (\<forall>l t s. (l,\<langle>t not in s\<rangle>) \<in> set (transaction_checks T) \<longrightarrow> (t \<cdot> \<theta> \<cdot> I, s \<cdot> \<theta> \<cdot> I) \<notin> D))"
    (is "?A \<longleftrightarrow> ?B")
proof -
  define P where "P \<equiv>
    \<lambda>X. \<lambda>\<delta>::('fun,'atom,'sets,'lbl) prot_subst. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)"
  define rm where "rm \<equiv> \<lambda>X. \<lambda>\<delta>::('fun,'atom,'sets,'lbl) prot_subst. rm_vars (set X) \<delta>"
  define chks where "chks \<equiv> transaction_checks T"
  define q1 where "q1 \<equiv> \<lambda>t X \<delta>. t \<cdot> rm X \<theta> \<cdot> \<delta> \<cdot> I"
  define q2 where "q2 \<equiv> \<lambda>t. t \<cdot> \<theta> \<cdot> I"

  note 0 = admissible_transaction_is_wellformed_transaction[OF T]
  note 1 = wellformed_transaction_sem_iff[OF 0(1) I, of M D \<theta>, unfolded A_def[symmetric]]
  note 2 = admissible_transactionE[OF T]

  have 3: "rm X \<theta> = \<theta>" when "X = []" for X using that unfolding rm_def by auto

  have 4: "P X \<delta> \<longleftrightarrow> \<delta> = Var" when "X = []" for X and \<delta>
    using that unfolding P_def by auto

  have 5: "\<exists>t s. \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> = \<langle>t != s\<rangle> \<or> \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> = \<langle>t not in s\<rangle>"
    when X: "(l, \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<in> set chks" for l X F G
  proof -
    have *: "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set (unlabel (transaction_strand T))"
      using X transaction_strand_subsets(2)[of T] unlabel_in unfolding chks_def by fast
    hence **: "X = []" using 2(4) by auto

    note *** = transaction_notinset_checks_are_Value_vars(3,4)[OF T *]
               transaction_noteqs_checks_case[OF T *]

    show ?thesis
    proof (cases "G = []")
      case True thus ?thesis using ** ***(3) by blast
    next
      case False
      then obtain t s where g: "(t,s) \<in> set G" by (cases G) auto
      show ?thesis using ** ***(1,2)[OF g] by blast
    qed
  qed

  have 6: "q1 t X \<delta> = q2 t" when "P X \<delta>" "X = []" for X \<delta> t
    using that 3 4 unfolding q1_def q2_def by simp

  let ?negcheck_sem = "\<lambda>X F G. \<forall>\<delta>. P X \<delta> \<longrightarrow>
                                (\<exists>(t,s) \<in> set F. q1 t X \<delta> \<noteq> q1 s X \<delta>) \<or>
                                (\<exists>(t,s) \<in> set G. (q1 t X \<delta>, q1 s X \<delta>) \<notin> D)"

  have "(\<forall>l X F G. (l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<in> set chks \<longrightarrow> ?negcheck_sem X F G) \<longleftrightarrow>
        ((\<forall>l t s. (l,\<langle>t != s\<rangle>) \<in> set chks \<longrightarrow> q2 t \<noteq> q2 s) \<and>
         (\<forall>l t s. (l,\<langle>t not in s\<rangle>) \<in> set chks \<longrightarrow> (q2 t, q2 s) \<notin> D))"
    (is "?A \<longleftrightarrow> ?B")
  proof
    have "q2 t \<noteq> q2 s" when t: "(l,\<langle>t != s\<rangle>) \<in> set chks" ?A for l t s
    proof -
      have "?negcheck_sem [] [(t,s)] []" using t by blast
      thus ?thesis using 4[of "[]"] 6[of "[]"] by force
    qed
    moreover have "(q2 t, q2 s) \<notin> D" when t: "(l,\<langle>t not in s\<rangle>) \<in> set chks" ?A for l t s
    proof -
      have "?negcheck_sem [] [] [(t,s)]" using t by blast
      thus ?thesis using 4[of "[]"] 6[of "[]"] by force
    qed 
    ultimately show "?A \<Longrightarrow> ?B" by blast

    have "?negcheck_sem X F G"
      when t: "(l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<in> set chks" ?B for l X F G
    proof -
      obtain t s where ts: "(X = [] \<and> F = [(t,s)] \<and> G = []) \<or> (X = [] \<and> F = [] \<and> G = [(t,s)])"
        using 5[OF t(1)] by blast
      hence "(X = [] \<and> F = [(t,s)] \<and> G = [] \<and> q2 t \<noteq> q2 s) \<or>
             (X = [] \<and> F = [] \<and> G = [(t,s)] \<and> (q2 t, q2 s) \<notin> D)" using t by blast
      thus ?thesis using 4[of "[]"] 6[of "[]"] by fastforce
    qed
    thus "?B \<Longrightarrow> ?A" by simp
  qed
  thus ?thesis using 1 unfolding rm_def chks_def P_def q1_def q2_def by simp
qed

lemma admissible_transaction_terms_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s:
  assumes "admissible_transaction_terms T"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms_transaction T)"
by (rule conjunct1[OF assms[unfolded admissible_transaction_terms_def wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric]]])

lemma admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s:
  assumes "admissible_transaction' T"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms_transaction T)" 
proof -
  have "admissible_transaction_terms T" using assms[unfolded admissible_transaction'_def] by fast
  thus ?thesis by (metis admissible_transaction_terms_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s)
qed

lemma admissible_transaction_no_Ana_Attack:
  assumes "admissible_transaction_terms T"
    and "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms_transaction T)"
  shows "attack\<langle>n\<rangle> \<notin> set (snd (Ana t))"
proof -
  obtain r where r: "r \<in> set (unlabel (transaction_strand T))" "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p r)"
    using assms(2) by force

  obtain K M where t: "Ana t = (K, M)"
    by (metis surj_pair)

  show ?thesis
  proof
    assume n: "attack\<langle>n\<rangle> \<in> set (snd (Ana t))"
    hence "attack\<langle>n\<rangle> \<in> set M" using t by simp
    hence n': "attack\<langle>n\<rangle> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p r)"
      using Ana_subterm[OF t] r(2) subterms_subset by fast
    hence "\<exists>f \<in> \<Union>(funs_term ` trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p r). is_Attack f"
      using funs_term_Fun_subterm' unfolding is_Attack_def by fast
    hence "is_Send r" "length (the_msgs r) = 1" "is_Fun (hd (the_msgs r))"
          "is_Attack (the_Fun (hd (the_msgs r)))" "args (hd (the_msgs r)) = []"
      using assms(1) r(1) unfolding admissible_transaction_terms_def is_Fun_Attack_def by metis+
    hence "t = attack\<langle>n\<rangle>"
      using n' r(2) unfolding is_Send_def is_Attack_def by (cases "the_msgs r") auto
    thus False using n by fastforce
  qed
qed

lemma admissible_transaction_Value_vars:
  assumes T: "admissible_transaction' T"
    and x: "x \<in> fv_transaction T"
  shows "\<Gamma>\<^sub>v x = TAtom Value"
proof -
  have "x \<in> vars_transaction T"
    using x vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
    by blast
  thus "\<Gamma>\<^sub>v x = TAtom Value"
    using admissible_transactionE(3)[OF T] by simp
qed

lemma admissible_transaction_occurs_checksE1:
  assumes T: "admissible_transaction_occurs_checks T"
    and x: "x \<in> fv_transaction T - set (transaction_fresh T)" "\<Gamma>\<^sub>v x = TAtom Value"
  obtains l ts S where
    "transaction_receive T = (l,receive\<langle>ts\<rangle>)#S" "occurs (Var x) \<in> set ts"
proof -
  let ?rcvs = "transaction_receive T"
  let ?frsh = "transaction_fresh T"
  let ?fvs = "fv_transaction T"

  have *: "?rcvs \<noteq> []" "is_Receive (hd (unlabel ?rcvs))"
          "\<forall>x \<in> ?fvs - set ?frsh. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
            occurs (Var x) \<in> set (the_msgs (hd (unlabel ?rcvs)))"
    using T x unfolding admissible_transaction_occurs_checks_def \<Gamma>\<^sub>v_TAtom''(2) by meson+

  obtain r S where S: "?rcvs = r#S"
    using *(1) by (cases ?rcvs) auto

  obtain l ts where r: "r = (l,receive\<langle>ts\<rangle>)"
    by (metis *(1,2) S list.map_sel(1) list.sel(1) prod.collapse is_Receive_def unlabel_def) 

  have 0: "occurs (Var x) \<in> set ts" using *(3) x S r by fastforce

  show ?thesis using that[unfolded S r, of l ts S] 0 by blast
qed

lemma admissible_transaction_occurs_checksE2:
  assumes T: "admissible_transaction_occurs_checks T"
    and x: "x \<in> set (transaction_fresh T)"
  obtains l ts S where
    "transaction_send T = (l,send\<langle>ts\<rangle>)#S" "occurs (Var x) \<in> set ts"
proof -
  let ?snds = "transaction_send T"
  let ?frsh = "transaction_fresh T"
  let ?fvs = "fv_transaction T"
  define ts where "ts \<equiv> the_msgs (hd (unlabel ?snds))"

  let ?P = "\<forall>x \<in> set ?frsh. occurs (Var x) \<in> set ts"

  have "?frsh \<noteq> []" using x by auto
  hence *: "?snds \<noteq> []" "is_Send (hd (unlabel ?snds))" "?P"
    using T x unfolding admissible_transaction_occurs_checks_def ts_def by meson+

  obtain r S where S: "?snds = r#S"
    using *(1) by (cases ?snds) auto

  obtain l where r: "r = (l,send\<langle>ts\<rangle>)"
    by (metis *(1,2) S list.map_sel(1) list.sel(1) prod.collapse unlabel_def ts_def
              stateful_strand_step.collapse(1)) 

  have ts: "occurs (Var x) \<in> set ts"
    using x *(3) unfolding S by auto

  show ?thesis using that[unfolded S r, of l ts S] ts by blast
qed

lemma admissible_transaction_occurs_checksE3:
  assumes T: "admissible_transaction_occurs_checks T"
    and t: "OccursFact \<in> funs_term t \<or> OccursSec \<in> funs_term t" "t \<in> set ts"
    and ts: "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))"
  obtains x where "t = occurs (Var x)" "x \<in> set (transaction_fresh T)"
proof -
  let ?P = "\<lambda>t. \<exists>x \<in> set (transaction_fresh T). t = occurs (Var x)"

  have "?P t"
    when "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "OccursFact \<in> funs_term t \<or> OccursSec \<in> funs_term t"
    for t
    using assms that
    unfolding admissible_transaction_occurs_checks_def
              admissible_transaction_send_occurs_form_def
    by metis
  moreover have "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
    using t(2) ts unfolding trms\<^sub>s\<^sub>s\<^sub>t_def by fastforce
  ultimately have "?P t" using t(1) by blast
  thus thesis using that by blast
qed

lemma admissible_transaction_occurs_checksE4:
  assumes T: "admissible_transaction_occurs_checks T"
    and ts: "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))"
    and t: "occurs t \<in> set ts"
  obtains x where "t = Var x" "x \<in> set (transaction_fresh T)"
using admissible_transaction_occurs_checksE3[OF T _ t ts] by auto

lemma admissible_transaction_occurs_checksE5:
  assumes T: "admissible_transaction_occurs_checks T"
  shows "Fun OccursSec [] \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
proof -
  have "\<exists>x \<in> set (transaction_fresh T). t = occurs (Var x)"
    when "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "OccursFact \<in> funs_term t \<or> OccursSec \<in> funs_term t"
    for t
    using assms that
    unfolding admissible_transaction_occurs_checks_def
              admissible_transaction_send_occurs_form_def
    by metis
  thus ?thesis by fastforce
qed

lemma admissible_transaction_occurs_checksE6:
  assumes T: "admissible_transaction_occurs_checks T"
    and t: "t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
  shows "Fun OccursSec [] \<notin> set (snd (Ana t))" (is ?A)
    and "occurs k \<notin> set (snd (Ana t))" (is ?B)
proof -
  obtain t' where t': "t' \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "t \<sqsubseteq> t'" using t by blast
  have "?A \<and> ?B"
  proof (rule ccontr)
    assume *: "\<not>(?A \<and> ?B)"
    hence "OccursSec \<in> funs_term t' \<or> OccursFact \<in> funs_term t'"
      by (meson t'(2) Ana_subterm' funs_term_Fun_subterm' term.order.trans) 
    then obtain x where x: "x \<in> set (transaction_fresh T)" "t' = occurs (Var x)"
      using t'(1) T
      unfolding admissible_transaction_occurs_checks_def
                admissible_transaction_send_occurs_form_def
      by metis
    have "t = occurs (Var x) \<or> t = Var x \<or> t = Fun OccursSec []" using x(2) t'(2) by auto
    thus False using * by fastforce
  qed
  thus ?A ?B by simp_all
qed

lemma has_initial_value_producing_transactionE:
  fixes P::"('fun,'atom,'sets,'lbl) prot"
  assumes P: "has_initial_value_producing_transaction P"
    and P_adm: "\<forall>T \<in> set P. admissible_transaction' T"
  obtains T x s ts upds l l' where
    "\<Gamma>\<^sub>v x = TAtom Value" "Var x \<in> set ts" "fv\<^sub>s\<^sub>e\<^sub>t (set ts) = {x}"
    "\<forall>n. \<not>(Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set ts)" "T \<in> set P"
    "T = Transaction (\<lambda>(). []) [x] [] [] upds [(l, send\<langle>ts\<rangle>)]"
    "upds = [] \<or> (upds = [(l', insert\<langle>Var x, \<langle>s\<rangle>\<^sub>s\<rangle>)] \<and>
      (\<forall>T \<in> set P. \<forall>(l,a) \<in> set (transaction_strand T). \<forall>t.
        a \<noteq> select\<langle>t, \<langle>s\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t in \<langle>s\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t not in \<langle>s\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> delete\<langle>t, \<langle>s\<rangle>\<^sub>s\<rangle>)) \<or>
     T = Transaction (\<lambda>(). []) [x] [] [] [] [(l, send\<langle>ts\<rangle>)]"
proof -
  define f where "f \<equiv> \<lambda>s.
      list_all (\<lambda>T. list_all (\<lambda>a. ((is_Delete a \<or> is_InSet a) \<longrightarrow> the_set_term a \<noteq> \<langle>s\<rangle>\<^sub>s) \<and>
                                  (is_NegChecks a \<longrightarrow> list_all (\<lambda>(_,t). t \<noteq> \<langle>s\<rangle>\<^sub>s) (the_ins a)))
                             (unlabel (transaction_checks T@transaction_updates T)))
               P"

  obtain T where T0:
      "T \<in> set P"
      "length (transaction_fresh T) = 1" "transaction_receive T = []"
      "transaction_checks T = []" "length (transaction_send T) = 1"
      "let x = hd (transaction_fresh T); a = hd (transaction_send T); u = transaction_updates T
       in is_Send (snd a) \<and> Var x \<in> set (the_msgs (snd a)) \<and>
          fv\<^sub>s\<^sub>e\<^sub>t (set (the_msgs (snd a))) = {x} \<and>
          (u \<noteq> [] \<longrightarrow> (
            let b = hd u; c = snd b
            in tl u = [] \<and> is_Insert c \<and> the_elem_term c = Var x \<and>
               is_Fun_Set (the_set_term c) \<and> f (the_Set (the_Fun (the_set_term c)))))"
    using P unfolding has_initial_value_producing_transaction_def Let_def list_ex_iff f_def by blast

  obtain x upds ts h s l l' where T1:
      "T = Transaction h [x] [] [] upds [(l, send\<langle>ts\<rangle>)]"
      "Var x \<in> set ts" "fv\<^sub>s\<^sub>e\<^sub>t (set ts) = {x}"
      "upds = [] \<or> (upds = [(l', insert\<langle>Var x, \<langle>s\<rangle>\<^sub>s\<rangle>)] \<and> f s)"
  proof (cases T)
    case T: (Transaction A B C D E F)

    obtain x where B: "B = [x]" using T0(2) unfolding T by (cases B) auto
    have C: "C = []" using T0(3) unfolding T by simp
    have D: "D = []" using T0(4) unfolding T by simp
    obtain l a where F: "F = [(l,a)]" using T0(5) unfolding T by fastforce
    obtain ts where ts: "a = send\<langle>ts\<rangle>" using T0(6) unfolding T F by (cases a) auto
    obtain k u where E: "E = [] \<or> E = [(k,u)]" using T0(6) unfolding T by (cases E) fastforce+
    have x: "Var x \<in> set ts" "fv\<^sub>s\<^sub>e\<^sub>t (set ts) = {x}" using T0(6) unfolding T B F ts by auto

    from E show ?thesis
    proof
      assume E': "E = [(k,u)]"
      obtain t t' where u: "u = insert\<langle>t,t'\<rangle>" using T0(6) unfolding T E' by (cases u) auto
      have t: "t = Var x" using T0(6) unfolding T B E' u Let_def by simp
      obtain s where t': "t' = \<langle>s\<rangle>\<^sub>s" and s: "f s" using T0(6) unfolding T B E' u Let_def by auto
      show ?thesis using that[OF T[unfolded B C D F ts E' u t t'] x] s by blast
    qed (use that[OF T[unfolded B C D F ts] x] in blast)
  qed

  note T_adm = bspec[OF P_adm T0(1)]

  have "x \<in> set (transaction_fresh T)" using T1(1) by fastforce
  hence x: "\<Gamma>\<^sub>v x = TAtom Value" using admissible_transactionE(2)[OF T_adm] by fast

  have "set ts \<subseteq> trms_transaction T" unfolding T1(1) trms_transaction_unfold by simp
  hence ts: "\<forall>n. \<not>(Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set ts)"
    using admissible_transactions_no_Value_consts[OF T_adm] by blast

  have "a \<noteq> select\<langle>t, \<langle>s\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t in \<langle>s\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t not in \<langle>s\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> delete\<langle>t, \<langle>s\<rangle>\<^sub>s\<rangle>"
    when upds: "upds = [(k, insert\<langle>Var x,\<langle>s\<rangle>\<^sub>s\<rangle>)]"
      and T': "T' \<in> set P" and la: "(l,a) \<in> set (transaction_strand T')"
    for T' l k a t
  proof -
    note T'_wf = admissible_transaction_is_wellformed_transaction(1)[OF bspec[OF P_adm T']]

    have "a \<in> set (unlabel (transaction_checks T'@transaction_updates T'))"
      when a': "is_Check_or_Assignment a \<or> is_Update a"
      using that wellformed_transaction_strand_unlabel_memberD[OF T'_wf unlabel_in[OF la]]
      by (cases a) auto
    note 0 = this T1(4) T'

    note 1 = upds f_def list_all_iff

    show ?thesis
    proof (cases a)
      case (Delete t' s') thus ?thesis using 0 unfolding 1 by fastforce
    next
      case (InSet ac t' s') thus ?thesis using 0 unfolding 1 by fastforce
    next
      case (NegChecks X F G) thus ?thesis using 0 unfolding 1 by fastforce
    qed auto
  qed
  hence s: "\<forall>T \<in> set P. \<forall>(l,a) \<in> set (transaction_strand T). \<forall>t.
        a \<noteq> select\<langle>t, \<langle>s\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t in \<langle>s\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t not in \<langle>s\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> delete\<langle>t, \<langle>s\<rangle>\<^sub>s\<rangle>"
    when upds: "upds = [(k, insert\<langle>Var x,\<langle>s\<rangle>\<^sub>s\<rangle>)]" for k
    using upds by force

  have h: "h = (\<lambda>(). [])"
  proof -
    have "transaction_decl T = h" using T1(1) by fastforce
    hence "h a = []" for a using admissible_transactionE(1)[OF T_adm] by simp
    thus ?thesis using ext[of h "\<lambda>(). []"] by (metis case_unit_Unity)
  qed

  show ?thesis using that[OF x T1(2,3) ts T0(1)] T1(1,4) s unfolding h by auto
qed

lemma has_initial_value_producing_transaction_update_send_ex_filter:
  fixes P::"('a,'b,'c,'d) prot"
  defines "f \<equiv> \<lambda>T. transaction_fresh T = [] \<longrightarrow>
                      list_ex (\<lambda>a. is_Update (snd a) \<or> is_Send (snd a)) (transaction_strand T)"
  assumes P: "has_initial_value_producing_transaction P"
  shows "has_initial_value_producing_transaction (filter f P)"
proof -
  define g where "g \<equiv> \<lambda>P::('a,'b,'c,'d) prot. \<lambda>s.
      list_all (\<lambda>T. list_all (\<lambda>a. ((is_Delete a \<or> is_InSet a) \<longrightarrow> the_set_term a \<noteq> \<langle>s\<rangle>\<^sub>s) \<and>
                                  (is_NegChecks a \<longrightarrow> list_all (\<lambda>(_,t). t \<noteq> \<langle>s\<rangle>\<^sub>s) (the_ins a)))
                             (unlabel (transaction_checks T@transaction_updates T)))
               P"

  let ?Q = "\<lambda>P T.
     let x = hd (transaction_fresh T); a = hd (transaction_send T); u = transaction_updates T
     in is_Send (snd a) \<and> Var x \<in> set (the_msgs (snd a)) \<and>
        fv\<^sub>s\<^sub>e\<^sub>t (set (the_msgs (snd a))) = {x} \<and>
        (u \<noteq> [] \<longrightarrow> (
          let b = hd u; c = snd b
          in tl u = [] \<and> is_Insert c \<and> the_elem_term c = Var x \<and>
             is_Fun_Set (the_set_term c) \<and> g P (the_Set (the_Fun (the_set_term c)))))"

  have "set (filter f P) \<subseteq> set P" by simp
  hence "list_all h P \<Longrightarrow> list_all h (filter f P)" for h unfolding list_all_iff by blast
  hence g_f_subset: "g P s \<Longrightarrow> g (filter f P) s" for s unfolding g_def by blast

  obtain T where T:
    "T \<in> set P" "length (transaction_fresh T) = 1" "transaction_receive T = []"
    "transaction_checks T = []" "length (transaction_send T) = 1" "?Q P T"
    using P unfolding has_initial_value_producing_transaction_def Let_def list_ex_iff g_def by blast

  obtain x where x: "transaction_fresh T = [x]" using T(2) by blast
  obtain a where a: "transaction_send T = [a]" using T(5) by blast
  obtain l b where b: "a = (l,b)" by (cases a) auto
  obtain ts where ts: "b = send\<langle>ts\<rangle>" using T(6) unfolding Let_def a b by (cases b) auto

  have "T \<in> set (filter f P)" using T(1) x a unfolding b ts f_def by auto
  moreover have "?Q (filter f P) T" using T(6) g_f_subset by meson
  ultimately show ?thesis
    using T(2-5)
    unfolding has_initial_value_producing_transaction_def Let_def list_ex_iff g_def
    by blast
qed


subsection \<open>Lemmata: Renaming, Declaration, and Fresh Substitutions\<close>
lemma transaction_decl_subst_empty_inv:
  assumes "transaction_decl_subst Var T"
  shows "transaction_decl T () = []"
using assms unfolding transaction_decl_subst_def subst_domain_Var by blast

lemma transaction_decl_subst_domain:
  fixes \<xi>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_decl_subst \<xi> T"
  shows "subst_domain \<xi> = fst ` set (transaction_decl T ())"
using assms unfolding transaction_decl_subst_def by argo

lemma transaction_decl_subst_grounds_domain:
  fixes \<xi>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_decl_subst \<xi> T"
    and "x \<in> fst ` set (transaction_decl T ())"
  shows "fv (\<xi> x) = {}"
proof -
  obtain c where "\<xi> x = Fun c []"
    using assms unfolding transaction_decl_subst_def by moura
  thus ?thesis by simp
qed

lemma transaction_decl_subst_range_vars_empty:
  fixes \<xi>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_decl_subst \<xi> T"
  shows "range_vars \<xi> = {}"
using assms unfolding transaction_decl_subst_def range_vars_def by auto

lemma transaction_decl_subst_wt:
  fixes \<xi>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_decl_subst \<xi> T"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<xi>"
using assms unfolding transaction_decl_subst_def by blast

lemma transaction_decl_subst_is_wf_trm:
  fixes \<xi>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_decl_subst \<xi> P"
  shows "wf\<^sub>t\<^sub>r\<^sub>m (\<xi> v)"
proof (cases "v \<in> subst_domain \<xi>")
  case True thus ?thesis using assms unfolding transaction_decl_subst_def by fastforce
qed auto

lemma transaction_decl_subst_range_wf_trms:
  fixes \<xi>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_decl_subst \<xi> P"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<xi>)"
by (metis transaction_decl_subst_is_wf_trm[OF assms] wf_trm_subst_range_iff)

lemma transaction_renaming_subst_is_renaming:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<alpha>: "transaction_renaming_subst \<alpha> P A"
  shows "\<exists>m. \<forall>\<tau> n. \<alpha> (\<tau>,n) = Var (\<tau>,n+Suc m)" (is ?A)
    and "\<exists>y. \<alpha> x = Var y" (is ?B)
    and "\<alpha> x \<noteq> Var x" (is ?C)
    and "subst_domain \<alpha> = UNIV" (is ?D)
    and "subst_range \<alpha> \<subseteq> range Var" (is ?E)
    and "fv (t \<cdot> \<alpha>) \<subseteq> range_vars \<alpha>" (is ?F)
proof -
  show 0: ?A using \<alpha> unfolding transaction_renaming_subst_def var_rename_def by force
  show ?B using \<alpha> unfolding transaction_renaming_subst_def var_rename_def by blast
  show ?C using 0 by (cases x) auto
  show 1: ?D using 0 by fastforce
  show ?E using 0 by auto
  show ?F by (induct t) (auto simp add: 1 subst_dom_vars_in_subst subst_fv_imgI)
qed

lemma transaction_renaming_subst_is_injective:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_renaming_subst \<alpha> P A"
  shows "inj \<alpha>"
proof (intro injI)
  fix x y::"('fun,'atom,'sets,'lbl) prot_var"
  obtain \<tau>x nx where x: "x = (\<tau>x,nx)" by (metis surj_pair)
  obtain \<tau>y ny where y: "y = (\<tau>y,ny)" by (metis surj_pair)

  obtain m where m: "\<forall>\<tau>. \<forall>n. \<alpha> (\<tau>, n) = Var (\<tau>, n + Suc m)"
    using transaction_renaming_subst_is_renaming(1)[OF assms] by blast

  assume "\<alpha> x = \<alpha> y"
  hence "\<tau>x = \<tau>y" "nx = ny" using x y m by simp_all
  thus "x = y" using x y by argo
qed

lemma transaction_renaming_subst_vars_disj:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  shows "fv\<^sub>s\<^sub>e\<^sub>t (\<alpha> ` (\<Union>(vars_transaction ` set P))) \<inter> (\<Union>(vars_transaction ` set P)) = {}" (is ?A)
    and "fv\<^sub>s\<^sub>e\<^sub>t (\<alpha> ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<inter> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = {}" (is ?B)
    and "T \<in> set P \<Longrightarrow> vars_transaction T \<inter> range_vars \<alpha> = {}" (is "T \<in> set P \<Longrightarrow> ?C1")
    and "T \<in> set P \<Longrightarrow> bvars_transaction T \<inter> range_vars \<alpha> = {}" (is "T \<in> set P \<Longrightarrow> ?C2")
    and "T \<in> set P \<Longrightarrow> fv_transaction T \<inter> range_vars \<alpha> = {}" (is "T \<in> set P \<Longrightarrow> ?C3")
    and "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<inter> range_vars \<alpha> = {}" (is ?D1)
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<inter> range_vars \<alpha> = {}" (is ?D2)
    and "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<inter> range_vars \<alpha> = {}" (is ?D3)
proof -
  define X where "X \<equiv> \<Union>(vars_transaction ` set P) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"

  have 1: "finite X" by (simp add: X_def)

  obtain n where n: "n \<ge> max_var_set X" "\<alpha> = var_rename n"
    using assms unfolding transaction_renaming_subst_def X_def by moura
  hence 2: "\<forall>x \<in> X. snd x < Suc n"
    using less_Suc_max_var_set[OF _ 1] unfolding var_rename_def by fastforce
  
  have 3: "x \<notin> fv\<^sub>s\<^sub>e\<^sub>t (\<alpha> ` X)" "fv (\<alpha> x) \<inter> X = {}" "x \<notin> range_vars \<alpha>" when x: "x \<in> X" for x
    using 2 x n unfolding var_rename_def by force+

  show ?A ?B using 3(1,2) unfolding X_def by auto

  show ?C1 when T: "T \<in> set P" using T 3(3) unfolding X_def by blast
  thus ?C2 ?C3 when T: "T \<in> set P"
    using T by (simp_all add: disjoint_iff_not_equal vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t)

  show ?D1 using 3(3) unfolding X_def by auto
  thus ?D2 ?D3 by (simp_all add: disjoint_iff_not_equal vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t)
qed

lemma transaction_renaming_subst_wt:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_renaming_subst \<alpha> P X"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<alpha>"
proof -
  { fix x::"('fun,'atom,'sets,'lbl) prot_var"
    obtain \<tau> n where x: "x = (\<tau>,n)" by moura
    then obtain m where m: "\<alpha> x = Var (\<tau>,m)"
      using assms transaction_renaming_subst_is_renaming(1) by moura
    hence "\<Gamma> (\<alpha> x) = \<Gamma>\<^sub>v x" using x by (simp add: \<Gamma>\<^sub>v_def)
  } thus ?thesis by (simp add: wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
qed

lemma transaction_renaming_subst_is_wf_trm:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_renaming_subst \<alpha> P X"
  shows "wf\<^sub>t\<^sub>r\<^sub>m (\<alpha> v)"
proof -
  obtain \<tau> n where "v = (\<tau>, n)" by moura
  then obtain m where "\<alpha> v = Var (\<tau>, n + Suc m)"
    using transaction_renaming_subst_is_renaming(1)[OF assms]
    by moura
  thus ?thesis by (metis wf_trm_Var)
qed

lemma transaction_renaming_subst_range_wf_trms:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_renaming_subst \<alpha> P X"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<alpha>)"
by (metis transaction_renaming_subst_is_wf_trm[OF assms] wf_trm_subst_range_iff)

lemma transaction_renaming_subst_range_notin_vars:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  shows "\<exists>y. \<alpha> x = Var y \<and> y \<notin> \<Union>(vars_transaction ` set P) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof -
  obtain \<tau> n where x: "x = (\<tau>,n)" by (metis surj_pair)

  define y where "y \<equiv> \<lambda>m. (\<tau>,n+Suc m)"

  have "\<exists>m \<ge> max_var_set (\<Union>(vars_transaction ` set P) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A). \<alpha> x = Var (y m)"
    using assms x by (auto simp add: y_def transaction_renaming_subst_def var_rename_def)
  moreover have "finite (\<Union>(vars_transaction ` set P) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" by auto
  ultimately show ?thesis using x unfolding y_def by force
qed

lemma transaction_renaming_subst_var_obtain:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<alpha>: "transaction_renaming_subst \<alpha> P X"
  shows "x \<in> fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>) \<Longrightarrow> \<exists>y. \<alpha> y = Var x" (is "?A1 \<Longrightarrow> ?B1")
    and "x \<in> fv (t \<cdot> \<alpha>) \<Longrightarrow> \<exists>y \<in> fv t. \<alpha> y = Var x" (is "?A2 \<Longrightarrow> ?B2")
proof -
  assume x: ?A1
  obtain y where y: "y \<in> fv\<^sub>s\<^sub>s\<^sub>t S" "x \<in> fv (\<alpha> y)" using fv\<^sub>s\<^sub>s\<^sub>t_subst_obtain_var[OF x] by moura
  thus ?B1 using transaction_renaming_subst_is_renaming(2)[OF \<alpha>, of y] by fastforce
next
  assume x: ?A2
  obtain y where y: "y \<in> fv t" "x \<in> fv (\<alpha> y)" using fv_subst_obtain_var[OF x] by moura
  thus ?B2 using transaction_renaming_subst_is_renaming(2)[OF \<alpha>, of y] by fastforce
qed

lemma transaction_renaming_subst_set_eq:
  assumes "set P1 = set P2"
  shows "transaction_renaming_subst \<alpha> P1 X = transaction_renaming_subst \<alpha> P2 X" (is "?A = ?B")
using assms unfolding transaction_renaming_subst_def by presburger

lemma transaction_renaming_subst_vars_transaction_neq:
  assumes T: "T \<in> set P"
    and \<alpha>: "transaction_renaming_subst \<alpha> P vars"
    and vars:"finite vars"
    and x: "x \<in> vars_transaction T"
  shows "\<alpha> y \<noteq> Var x"
proof -
  have "\<exists>n. \<alpha> = var_rename n \<and> n \<ge> max_var_set (\<Union>(vars_transaction ` set P))"
    using T \<alpha> vars x unfolding transaction_renaming_subst_def by auto
  then obtain n where n_p: "\<alpha> = var_rename n" "n \<ge> max_var_set (\<Union>(vars_transaction ` set P))"
    by blast
  moreover
  have "\<Union>(vars_transaction ` set P) \<supseteq> vars_transaction T"
    using T by blast
  ultimately
  have n_gt: "n \<ge> max_var_set (vars_transaction T)"
    by auto
  obtain a b where ab: "x = (a,b)"
    by (cases x) auto
  obtain c d where cd: "y = (c,d)"
    by (cases y) auto

  have nb: "n \<ge> b"
    using n_gt x ab
    by auto

  have "\<alpha> y = \<alpha> (c, d)"
    using cd by auto
  moreover
  have "... = Var (c, Suc (d + n))"
    unfolding n_p(1) unfolding var_rename_def by simp 
  moreover
  have "... \<noteq> Var x"
    using nb ab by auto
  ultimately
  show ?thesis
    by auto
qed

lemma transaction_renaming_subst_fv_disj:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  shows "fv\<^sub>s\<^sub>e\<^sub>t (\<alpha> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t  A = {}"
proof -
  have "fv\<^sub>s\<^sub>e\<^sub>t (\<alpha> ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<inter> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t  A = {}"
    using assms transaction_renaming_subst_vars_disj(2) by blast
  moreover
  have "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<subseteq> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
    by (simp add: vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t)
  ultimately
  show ?thesis
    by auto
qed

lemma transaction_fresh_subst_is_wf_trm:
  fixes \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T X"
  shows "wf\<^sub>t\<^sub>r\<^sub>m (\<sigma> v)"
proof (cases "v \<in> subst_domain \<sigma>")
  case True
  then obtain c where "\<sigma> v = Fun c []" "arity c = 0"
    using assms unfolding transaction_fresh_subst_def
    by moura
  thus ?thesis by auto
qed auto

lemma transaction_fresh_subst_wt:
  fixes \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T X"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>"
using assms unfolding transaction_fresh_subst_def by blast

lemma transaction_fresh_subst_domain:
  fixes \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T X"
  shows "subst_domain \<sigma> = set (transaction_fresh T)"
using assms unfolding transaction_fresh_subst_def by fast

lemma transaction_fresh_subst_range_wf_trms:
  fixes \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T X"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
by (metis transaction_fresh_subst_is_wf_trm[OF assms] wf_trm_subst_range_iff)

lemma transaction_fresh_subst_range_fresh:
  fixes \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T M"
  shows "\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t M"
    and "\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"
using assms unfolding transaction_fresh_subst_def by meson+

lemma transaction_fresh_subst_sends_to_val:
  fixes \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<sigma>: "transaction_fresh_subst \<sigma> T X"
    and y: "y \<in> set (transaction_fresh T)" "\<Gamma>\<^sub>v y = TAtom Value"
  obtains n where "\<sigma> y = Fun (Val n) []" "Fun (Val n) [] \<in> subst_range \<sigma>"
proof -
  have "\<sigma> y \<in> subst_range \<sigma>" using assms unfolding transaction_fresh_subst_def by simp

  obtain c where c: "\<sigma> y = Fun c []" "\<not>public c" "arity c = 0"
    using \<sigma> y(1) unfolding transaction_fresh_subst_def by fastforce

  have "\<Gamma> (\<sigma> y) = TAtom Value"
    using \<sigma> y(2) \<Gamma>\<^sub>v_TAtom''(2)[of y] wt_subst_trm''[of \<sigma> "Var y"]
    unfolding transaction_fresh_subst_def by simp
  then obtain n where "c = Val n"
    using c by (cases c) (auto split: option.splits)
  thus ?thesis
    using c that unfolding transaction_fresh_subst_def
    by fastforce
qed

lemma transaction_fresh_subst_sends_to_val':
  fixes \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T X"
    and "y \<in> set (transaction_fresh T)" "\<Gamma>\<^sub>v y = TAtom Value"
  obtains n where "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val n) []" "Fun (Val n) [] \<in> subst_range \<sigma>" 
proof -
  obtain n where "\<sigma> y = Fun (Val n) []" "Fun (Val n) [] \<in> subst_range \<sigma>"
    using transaction_fresh_subst_sends_to_val[OF assms] by moura
  thus ?thesis using that by (fastforce simp add: subst_compose_def)
qed

lemma transaction_fresh_subst_grounds_domain:
  fixes \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T X"
    and "y \<in> set (transaction_fresh T)"
  shows "fv (\<sigma> y) = {}"
proof -
  obtain c where "\<sigma> y = Fun c []"
    using assms unfolding transaction_fresh_subst_def by moura
  thus ?thesis by simp
qed

lemma transaction_fresh_subst_range_vars_empty:
  fixes \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T X"
  shows "range_vars \<sigma> = {}"
proof -
  have "fv t = {}" when "t \<in> subst_range \<sigma>" for t
    using assms that unfolding transaction_fresh_subst_def by fastforce
  thus ?thesis unfolding range_vars_def by blast
qed

lemma transaction_decl_fresh_renaming_substs_range:
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T M"
    and \<alpha>: "transaction_renaming_subst \<alpha> P X"
  shows "x \<in> fst ` set (transaction_decl T ()) \<Longrightarrow>
          \<exists>c. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Fun c [] \<and> arity c = 0"
    and "x \<notin> fst ` set (transaction_decl T ()) \<Longrightarrow>
          x \<in> set (transaction_fresh T) \<Longrightarrow>
            \<exists>c. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Fun c [] \<and> \<not>public c \<and> arity c = 0"
    and "x \<notin> fst ` set (transaction_decl T ()) \<Longrightarrow>
          x \<in> set (transaction_fresh T) \<Longrightarrow>
          fst x = TAtom Value \<Longrightarrow>
            \<exists>n. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Fun (Val n) []"
    and "x \<notin> fst ` set (transaction_decl T ()) \<Longrightarrow>
          x \<notin> set (transaction_fresh T) \<Longrightarrow>
            \<exists>y. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Var y"
proof -
  assume "x \<in> fst ` set (transaction_decl T ())"
  then obtain c where c: "\<xi> x = Fun c []" "arity c = 0"
    using \<xi> unfolding transaction_decl_subst_def by fastforce
  thus "\<exists>c. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Fun c [] \<and> arity c = 0"
    using subst_compose[of "\<xi> \<circ>\<^sub>s \<sigma>" \<alpha> x] subst_compose[of \<xi> \<sigma> x] by simp
next
  assume x: "x \<notin> fst ` set (transaction_decl T ())"
            "x \<in> set (transaction_fresh T)"

  have *: "(\<xi> \<circ>\<^sub>s \<sigma>) x = \<sigma> x"
    using x(1) \<xi> unfolding transaction_decl_subst_def
    by (metis (no_types, opaque_lifting) subst_comp_notin_dom_eq)
  then obtain c where c: "(\<xi> \<circ>\<^sub>s \<sigma>) x = Fun c []" "\<not>public c" "arity c = 0"
    using \<sigma> x(2) unfolding transaction_fresh_subst_def by fastforce
  thus "\<exists>c. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Fun c [] \<and> \<not>public c \<and> arity c = 0"
    using subst_compose[of "\<xi> \<circ>\<^sub>s \<sigma>" \<alpha> x] subst_compose[of \<xi> \<sigma> x] by simp

  assume "fst x = TAtom Value"
  hence "\<Gamma> ((\<xi> \<circ>\<^sub>s \<sigma>) x) = TAtom Value"
    using * \<sigma> \<Gamma>\<^sub>v_TAtom''(2)[of x] wt_subst_trm''[of \<sigma> "Var x"]
    unfolding transaction_fresh_subst_def by simp
  then obtain n where "c = Val n"
    using c by (cases c) (auto split: option.splits)
  thus "\<exists>n. (\<xi> \<circ>\<^sub>s\<sigma> \<circ>\<^sub>s \<alpha>) x = Fun (Val n) []"
    using c subst_compose[of "\<xi> \<circ>\<^sub>s \<sigma>" \<alpha> x] subst_compose[of \<xi> \<sigma> x] by simp
next
  assume "x \<notin> fst ` set (transaction_decl T ())"
         "x \<notin> set (transaction_fresh T)"
  hence "(\<xi> \<circ>\<^sub>s \<sigma>) x = Var x"
    using \<xi> \<sigma>
    unfolding transaction_decl_subst_def transaction_fresh_subst_def
    by (metis (no_types, opaque_lifting) subst_comp_notin_dom_eq subst_domI)
  thus "\<exists>y. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Var y"
    using transaction_renaming_subst_is_renaming(1)[OF \<alpha>]
          subst_compose[of "\<xi> \<circ>\<^sub>s \<sigma>" \<alpha> x] subst_compose[of \<xi> \<sigma> x]
    by (cases x) force
qed

lemma transaction_decl_fresh_renaming_substs_range':
  fixes \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T M"
    and \<alpha>: "transaction_renaming_subst \<alpha> P X"
    and t: "t \<in> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  shows "(\<exists>c. t = Fun c [] \<and> arity c = 0) \<or> (\<exists>x. t = Var x)"
    and "\<xi> = Var \<Longrightarrow> (\<exists>c. t = Fun c [] \<and> \<not>public c \<and> arity c = 0) \<or> (\<exists>x. t = Var x)"
    and "\<xi> = Var \<Longrightarrow> \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<Longrightarrow>
                      (\<exists>n. t = Fun (Val n) []) \<or> (\<exists>x. t = Var x)"
    and "\<xi> = Var \<Longrightarrow> is_Fun t \<Longrightarrow> t \<in> subst_range \<sigma>"
proof -
  obtain x where x: "x \<in> subst_domain (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = t"
    using t by auto

  note 0 = x transaction_decl_fresh_renaming_substs_range[OF \<xi> \<sigma> \<alpha>, of x]

  show "(\<exists>c. t = Fun c [] \<and> arity c = 0) \<or> (\<exists>x. t = Var x)"
    using 0 unfolding \<Gamma>\<^sub>v_TAtom'' by auto

  assume 1: "\<xi> = Var"

  note 2 = transaction_decl_subst_empty_inv[OF \<xi>[unfolded 1]]

  show 3: "(\<exists>c. t = Fun c [] \<and> \<not>public c \<and> arity c = 0) \<or> (\<exists>x. t = Var x)"
    using 0 2 unfolding \<Gamma>\<^sub>v_TAtom'' by auto

  show "(\<exists>n. t = Fun (Val n) []) \<or> (\<exists>x. t = Var x)"
    when "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    using 0 2 that unfolding \<Gamma>\<^sub>v_TAtom'' by auto

  show "t \<in> subst_range \<sigma>" when t': "is_Fun t"
  proof -
    obtain x where x: "(\<sigma> \<circ>\<^sub>s \<alpha>) x = t" using t 1 by auto
    
    show ?thesis
    proof (cases "x \<in> subst_domain \<sigma>")
      case True thus ?thesis
        by (metis subst_dom_vars_in_subst subst_ground_ident_compose(1) subst_imgI x
                  transaction_fresh_subst_grounds_domain[OF \<sigma>]
                  transaction_fresh_subst_domain[OF \<sigma>]) 
    next
      case False thus ?thesis
        by (metis (no_types, lifting) subst_compose_def subst_domI term.disc(1) that
                  transaction_renaming_subst_is_renaming(5)[OF \<alpha>] var_renaming_is_Fun_iff x)
    qed
  qed
qed

lemma transaction_decl_fresh_renaming_substs_range'':
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and \<alpha>: "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and y: "y \<in> fv ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x)"
  shows "\<xi> x = Var x"
    and "\<sigma> x = Var x"
    and "\<alpha> x = Var y"
    and "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Var y"
proof -
  have "\<exists>z. z \<in> fv (\<xi> x)" by (metis y subst_compose_fv')
  hence "x \<notin> subst_domain \<xi>"
    using y transaction_decl_subst_domain[OF \<xi>]
          transaction_decl_subst_grounds_domain[OF \<xi>, of x]
    by blast
  thus 0: "\<xi> x = Var x" by blast
  hence "y \<in> fv ((\<sigma> \<circ>\<^sub>s \<alpha>) x)" using y by (simp add: subst_compose)
  hence "\<exists>z. z \<in> fv (\<sigma> x)" by (metis subst_compose_fv')
  hence "x \<notin> subst_domain \<sigma>"
    using y transaction_fresh_subst_domain[OF \<sigma>]
          transaction_fresh_subst_grounds_domain[OF \<sigma>, of x]
    by blast
  thus 1: "\<sigma> x = Var x" by blast
  
  show "\<alpha> x = Var y" "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Var y"
    using 0 1 y transaction_renaming_subst_is_renaming(2)[OF \<alpha>, of x]
    unfolding subst_compose_def by (fastforce,fastforce)
qed

lemma transaction_decl_fresh_renaming_substs_vars_subset:
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and \<alpha>: "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "\<Union>(fv_transaction ` set P) \<subseteq> subst_domain (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" (is ?A)
    and "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<subseteq> subst_domain (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" (is ?B)
    and "T' \<in> set P \<Longrightarrow> fv_transaction T' \<subseteq> subst_domain (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" (is "T' \<in> set P \<Longrightarrow> ?C")
    and "T' \<in> set P \<Longrightarrow> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T' \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<subseteq> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      (is "T' \<in> set P \<Longrightarrow> ?D")
proof -
  have *: "x \<in> subst_domain (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" for x
  proof (cases "x \<in> subst_domain \<xi>")
    case True thus ?thesis
      using transaction_decl_subst_domain[OF \<xi>] transaction_decl_subst_grounds_domain[OF \<xi>]
      by (simp add: subst_domI subst_dom_vars_in_subst subst_ground_ident_compose(1))
  next
    case False
    hence \<xi>_x_eq: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = (\<sigma> \<circ>\<^sub>s \<alpha>) x" by (auto simp add: subst_compose)

    show ?thesis
    proof (cases "x \<in> subst_domain \<sigma>")
      case True
      hence "x \<notin> {x. \<exists>y. \<sigma> x = Var y \<and> \<alpha> y = Var x}"
        using transaction_fresh_subst_domain[OF \<sigma>]
              transaction_fresh_subst_grounds_domain[OF \<sigma>, of x]
        by auto
      hence "x \<in> subst_domain (\<sigma> \<circ>\<^sub>s \<alpha>)" using subst_domain_subst_compose[of \<sigma> \<alpha>] by blast
      thus ?thesis using \<xi>_x_eq subst_dom_vars_in_subst by fastforce 
    next
      case False
      hence "(\<sigma> \<circ>\<^sub>s \<alpha>) x = \<alpha> x" unfolding subst_compose_def by fastforce
      moreover have "\<alpha> x \<noteq> Var x"
        using transaction_renaming_subst_is_renaming(1)[OF \<alpha>] by (cases x) auto
      ultimately show ?thesis using \<xi>_x_eq by fastforce
    qed
  qed
  
  show ?A ?B using * by blast+

  show ?C when T: "T' \<in> set P" using T * by blast
  hence "fv\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T') \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<subseteq> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    when T: "T' \<in> set P"
    using T fv\<^sub>s\<^sub>s\<^sub>t_subst_subset_range_vars_if_subset_domain by blast
  thus ?D when T: "T' \<in> set P" by (metis T unlabel_subst)
qed

lemma transaction_decl_fresh_renaming_substs_vars_disj:
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and \<alpha>: "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "fv\<^sub>s\<^sub>e\<^sub>t ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` (\<Union>(vars_transaction ` set P))) \<inter> (\<Union>(vars_transaction ` set P)) = {}"
      (is ?A)
    and "x \<in> \<Union>(vars_transaction ` set P) \<Longrightarrow> fv ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x) \<inter> (\<Union>(vars_transaction ` set P)) = {}"
      (is "?B' \<Longrightarrow> ?B")
    and "T' \<in> set P \<Longrightarrow> vars_transaction T' \<inter> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = {}" (is "T' \<in> set P \<Longrightarrow> ?C1")
    and "T' \<in> set P \<Longrightarrow> bvars_transaction T' \<inter> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = {}" (is "T' \<in> set P \<Longrightarrow> ?C2")
    and "T' \<in> set P \<Longrightarrow> fv_transaction T' \<inter> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = {}" (is "T' \<in> set P \<Longrightarrow> ?C3")
    and "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = {}" (is ?D1)
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = {}" (is ?D2)
    and "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = {}" (is ?D3)
    and "range_vars \<xi> = {}" (is ?E1)
    and "range_vars \<sigma> = {}" (is ?E2)
    and "range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<subseteq> range_vars \<alpha>" (is ?E3)
proof -
  note 0 = transaction_renaming_subst_vars_disj[OF \<alpha>]

  show ?A
  proof (cases "fv\<^sub>s\<^sub>e\<^sub>t ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` (\<Union>(vars_transaction ` set P))) = {}")
    case False
    hence "\<forall>x \<in> (\<Union>(vars_transaction ` set P)). (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = \<alpha> x \<or> fv ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x) = {}"
      using transaction_decl_fresh_renaming_substs_range''[OF \<xi> \<sigma> \<alpha>] by auto
    thus ?thesis using 0(1) by force
  qed blast
  thus "?B' \<Longrightarrow> ?B" by auto

  show ?E1 ?E2
    using transaction_fresh_subst_grounds_domain[OF \<sigma>]
          transaction_decl_subst_grounds_domain[OF \<xi>]
    unfolding transaction_fresh_subst_domain[OF \<sigma>, symmetric]
              transaction_decl_subst_domain[OF \<xi>, symmetric]
    by (fastforce, fastforce)
  thus 1: ?E3
    using range_vars_subst_compose_subset[of \<xi> \<sigma>]
          range_vars_subst_compose_subset[of "\<xi> \<circ>\<^sub>s \<sigma>" \<alpha>]
    by blast
  
  show ?C1 ?C2 ?C3 when T: "T' \<in> set P" using T 1 0(3,4,5)[of T'] by blast+

  show ?D1 ?D2 ?D3 using 1 0(6,7,8) by blast+
qed

lemma transaction_decl_fresh_renaming_substs_trms:
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and \<alpha>: "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<xi> = {}"
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<sigma> = {}"
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<alpha> = {}"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))) = subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
proof -
  have 1: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S). (\<exists>f. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Fun f []) \<or> (\<exists>y. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Var y)"
    using transaction_decl_fresh_renaming_substs_range'[OF \<xi> \<sigma> \<alpha>] by blast

  have 2: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = {}"
    using assms(4-6) subst_domain_compose[of \<xi> \<sigma>] subst_domain_compose[of "\<xi> \<circ>\<^sub>s \<sigma>" \<alpha>] by blast

  show ?thesis using subterms_subst_lsst[OF 1 2] by simp
qed

lemma transaction_decl_fresh_renaming_substs_wt:
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T M"
          "transaction_renaming_subst \<alpha> P X"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
using transaction_renaming_subst_wt[OF assms(3)]
      transaction_fresh_subst_wt[OF assms(2)]
      transaction_decl_subst_wt[OF assms(1)]
by (metis wt_subst_compose)

lemma transaction_decl_fresh_renaming_substs_range_wf_trms:
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T M"
          "transaction_renaming_subst \<alpha> P X"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
using transaction_renaming_subst_range_wf_trms[OF assms(3)]
      transaction_fresh_subst_range_wf_trms[OF assms(2)]
      transaction_decl_subst_range_wf_trms[OF assms(1)]
      wf_trms_subst_compose[of \<xi> \<sigma>]
      wf_trms_subst_compose[of "\<xi> \<circ>\<^sub>s \<sigma>" \<alpha>]
by metis

lemma transaction_decl_fresh_renaming_substs_fv:
  fixes \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T M"
    and \<alpha>: "transaction_renaming_subst \<alpha> P X"
    and x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
  shows "\<exists>y \<in> fv_transaction T - set (transaction_fresh T). (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y = Var x"
proof -
  have "x \<in> fv\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    using x fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
          unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
    by argo
  then obtain y where "y \<in> fv_transaction T" "x \<in> fv ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y)"
    by (metis fv\<^sub>s\<^sub>s\<^sub>t_subst_obtain_var)
  thus ?thesis
    using transaction_decl_fresh_renaming_substs_range[OF \<xi> \<sigma> \<alpha>, of y]
    by (cases "y \<in> set (transaction_fresh T)") force+
qed

lemma transaction_decl_fresh_renaming_substs_range_no_attack_const:
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T M"
    and \<alpha>: "transaction_renaming_subst \<alpha> P X"
    and T: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    and t: "t \<in> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  shows "\<nexists>n. t = attack\<langle>n\<rangle>"
proof -
  note \<xi>\<sigma>\<alpha>_wt = transaction_decl_fresh_renaming_substs_wt[OF \<xi> \<sigma> \<alpha>]

  obtain x where x: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = t" using t by auto

  have x_type: "\<Gamma> (Var x) = \<Gamma> (Var x \<cdot> \<xi>)" "\<Gamma> (Var x) = \<Gamma> (Var x \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    using \<xi> wt_subst_trm''[of \<xi> "Var x"] wt_subst_trm''[OF \<xi>\<sigma>\<alpha>_wt, of "Var x"]
    unfolding transaction_decl_subst_def by (blast, blast)

  show ?thesis
  proof (cases t)
    case (Fun f S)
    hence "x \<in> set (transaction_fresh T) \<or> x \<in> fst ` set (transaction_decl T ())"
      using transaction_decl_fresh_renaming_substs_range[OF \<xi> \<sigma> \<alpha>, of x] x by force
    thus ?thesis
    proof
      assume "x \<in> set (transaction_fresh T)"
      hence "\<Gamma> t = TAtom Value \<or> (\<exists>a. \<Gamma> t = TAtom (Atom a))"
        using T x_type(2) x by (metis \<Gamma>.simps(1) eval_term.simps(1))
      thus ?thesis by auto
    next
      assume "x \<in> fst ` set (transaction_decl T ())"
      then obtain c where c: "\<xi> x = Fun (Fu c) []" "arity\<^sub>f c = 0"
        using \<xi> unfolding transaction_decl_subst_def by auto

      have "\<Gamma> t = TAtom Bottom \<or> (\<exists>a. \<Gamma> t = TAtom (Atom a))"
        using c(1) \<Gamma>_consts_simps(1)[OF c(2)] x x_type
              eval_term.simps(1)[of _ x \<xi>] eval_term.simps(1)[of _ x "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
        by (cases "\<Gamma>\<^sub>f c") simp_all
      thus ?thesis by auto
    qed
  qed simp
qed

lemma transaction_decl_fresh_renaming_substs_occurs_fact_send_receive:
  fixes t::"('fun,'atom,'sets,'lbl) prot_term"
  assumes \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T M"
    and \<alpha>: "transaction_renaming_subst \<alpha> P X"
    and T: "admissible_transaction' T"
    and t: "occurs t \<in> set ts"
  shows "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))
          \<Longrightarrow> \<exists>ts' s. send\<langle>ts'\<rangle> \<in> set (unlabel (transaction_send T)) \<and>
                      occurs s \<in> set ts' \<and> t = s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      (is "?A \<Longrightarrow> ?A'")
    and "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))
          \<Longrightarrow> \<exists>ts' s. receive\<langle>ts'\<rangle> \<in> set (unlabel (transaction_receive T)) \<and>
                      occurs s \<in> set ts' \<and> t = s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      (is "?B \<Longrightarrow> ?B'")
proof -
  assume ?A
  then obtain s ts' where s:
      "s \<in> set ts'" "send\<langle>ts'\<rangle> \<in> set (unlabel (transaction_strand T))" "occurs t = s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
    using t stateful_strand_step_mem_substD(1)[
            of ts "unlabel (transaction_strand T)" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
          unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
    by auto

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T \<xi>]

  have T_decl_notin: "x \<notin> fst ` set (transaction_decl T ())" for x
    using transaction_decl_subst_empty_inv[OF \<xi>[unfolded \<xi>_empty]] by simp

  note 0 = s(3) transaction_decl_fresh_renaming_substs_range[OF \<xi> \<sigma> \<alpha>]

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T]
  note T_fresh = admissible_transactionE(14)[OF T]

  have "\<exists>u. s = occurs u"
  proof (cases s)
    case (Var x) 
    hence "(\<exists>c. s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = Fun c []) \<or> (\<exists>y. s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = Var y)"
      using 0(2-5)[of x] \<xi>_empty by (auto simp del: subst_subst_compose)
    thus ?thesis
      using 0(1) by simp
  next
    case (Fun f T)
    hence 1: "f = OccursFact" "length T = 2" "T ! 0 \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = Fun OccursSec []"
             "T ! 1 \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = t"
      using 0(1) by auto
    have "T ! 0 = Fun OccursSec []"
    proof (cases "T ! 0")
      case (Var x) thus ?thesis
        using 0(2-5)[of x] 1(3) T_fresh T_decl_notin
        unfolding list_all_iff by (auto simp del: subst_subst_compose)
    qed (use 1(3) in simp)
    thus ?thesis using Fun 1 0(1) by (auto simp del: subst_subst_compose)
  qed
  then obtain u where u: "s = occurs u" by moura
  hence "t = u \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" using s(3) by fastforce
  thus ?A' using s u wellformed_transaction_strand_unlabel_memberD(8)[OF T_wf] by metis
next
  assume ?B
  then obtain s ts' where s:
      "s \<in> set ts'" "receive\<langle>ts'\<rangle> \<in> set (unlabel (transaction_strand T))" "occurs t = s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
    using t stateful_strand_step_mem_substD(2)[
            of ts "unlabel (transaction_strand T)" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
          unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
    by auto

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T \<xi>]

  have T_decl_notin: "x \<notin> fst ` set (transaction_decl T ())" for x
    using transaction_decl_subst_empty_inv[OF \<xi>[unfolded \<xi>_empty]] by simp

  note 0 = s(3) transaction_decl_fresh_renaming_substs_range[OF \<xi> \<sigma> \<alpha>]

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T]
  note T_fresh = admissible_transactionE(14)[OF T]

  have "\<exists>u. s = occurs u"
  proof (cases s)
    case (Var x) 
    hence "(\<exists>c. s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = Fun c []) \<or> (\<exists>y. s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = Var y)"
      using 0(2-5)[of x] \<xi>_empty by (auto simp del: subst_subst_compose)
    thus ?thesis
      using 0(1) by simp
  next
    case (Fun f T)
    hence 1: "f = OccursFact" "length T = 2" "T ! 0 \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = Fun OccursSec []"
              "T ! 1 \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = t"
      using 0(1) by auto
    have "T ! 0 = Fun OccursSec []"
    proof (cases "T ! 0")
      case (Var x) thus ?thesis
        using 0(2-5)[of x] 1(3) T_fresh T_decl_notin
        unfolding list_all_iff by (auto simp del: subst_subst_compose)
    qed (use 1(3) in simp)
    thus ?thesis using Fun 1 0(1) by (auto simp del: subst_subst_compose)
  qed
  then obtain u where u: "s = occurs u" by moura
  hence "t = u \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" using s(3) by fastforce
  thus ?B' using s u wellformed_transaction_strand_unlabel_memberD(1)[OF T_wf] by metis
qed

lemma transaction_decl_subst_proj:
  assumes "transaction_decl_subst \<xi> T"
  shows "transaction_decl_subst \<xi> (transaction_proj n T)"
using assms transaction_proj_decl_eq[of n T]
unfolding transaction_decl_subst_def by presburger

lemma transaction_fresh_subst_proj:
  assumes "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  shows "transaction_fresh_subst \<sigma> (transaction_proj n T) (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n A))"
using assms transaction_proj_fresh_eq[of n T]
      contra_subsetD[OF subterms\<^sub>s\<^sub>e\<^sub>t_mono[OF transaction_proj_trms_subset[of n T]]]
      contra_subsetD[OF subterms\<^sub>s\<^sub>e\<^sub>t_mono[OF trms\<^sub>s\<^sub>s\<^sub>t_proj_subset(1)[of n A]]]
unfolding transaction_fresh_subst_def by metis
  
lemma transaction_renaming_subst_proj:
  assumes "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  shows "transaction_renaming_subst \<alpha> (map (transaction_proj n) P) (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n A))"
proof -
  let ?X = "\<lambda>P A. \<Union>(vars_transaction ` set P) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  define Y where "Y \<equiv> ?X (map (transaction_proj n) P) (proj n A)"
  define Z where "Z \<equiv> ?X P A"

  have "Y \<subseteq> Z"
    using sst_vars_proj_subset(3)[of n A] transaction_proj_vars_subset[of n]
    unfolding Y_def Z_def by fastforce
  hence "insert 0 (snd ` Y) \<subseteq> insert 0 (snd ` Z)" by blast
  moreover have "finite (insert 0 (snd ` Z))" "finite (insert 0 (snd ` Y))"
    unfolding Y_def Z_def by auto
  ultimately have 0: "max_var_set Y \<le> max_var_set Z" using Max_mono by blast

  have "\<exists>n\<ge>max_var_set Z. \<alpha> = var_rename n"
    using assms unfolding transaction_renaming_subst_def Z_def by blast
  hence "\<exists>n\<ge>max_var_set Y. \<alpha> = var_rename n" using 0 le_trans by fast
  thus ?thesis unfolding transaction_renaming_subst_def Y_def by blast
qed

lemma transaction_decl_fresh_renaming_substs_wf_sst:
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes T: "wf'\<^sub>s\<^sub>s\<^sub>t (fst ` set (transaction_decl T ()) \<union> set (transaction_fresh T))
                    (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and \<alpha>: "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "wf'\<^sub>s\<^sub>s\<^sub>t {} (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)))"
proof -
  have 0: "range_vars \<xi> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)) = {}"
          "range_vars \<sigma> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi>) = {}"
          "ground (\<xi> ` (fst ` set (transaction_decl T ())))"
          "ground (\<sigma> ` set (transaction_fresh T))"
          "ground (\<alpha> ` {})"
    using transaction_decl_subst_domain[OF \<xi>]
          transaction_decl_subst_grounds_domain[OF \<xi>]
          transaction_decl_subst_range_vars_empty[OF \<xi>]
          transaction_fresh_subst_range_vars_empty[OF \<sigma>]
          transaction_fresh_subst_domain[OF \<sigma>]
          transaction_fresh_subst_grounds_domain[OF \<sigma>]
    by (simp, simp, simp, simp, simp)

  have 1: "fv\<^sub>s\<^sub>e\<^sub>t (\<xi> ` set (transaction_fresh T)) \<subseteq> set (transaction_fresh T)" (is "?A \<subseteq> ?B")
  proof
    fix x assume x: "x \<in> ?A"
    then obtain y where y: "y \<in> set (transaction_fresh T)" "x \<in> fv (\<xi> y)" by auto
    hence "y \<notin> subst_domain \<xi>"
      using transaction_decl_subst_domain[OF \<xi>]
            transaction_decl_subst_grounds_domain[OF \<xi>]
      by fast
    thus "x \<in> ?B" using x y by auto
  qed

  let ?X = "fst ` set (transaction_decl T ()) \<union> set (transaction_fresh T)"

  have "fv\<^sub>s\<^sub>e\<^sub>t (\<alpha> ` fv\<^sub>s\<^sub>e\<^sub>t (\<sigma> ` fv\<^sub>s\<^sub>e\<^sub>t (\<xi> ` ?X))) = {}" using 0(3-5) 1 by auto
  hence "wf'\<^sub>s\<^sub>s\<^sub>t {} (((unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi>) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>)"
    by (metis wf\<^sub>s\<^sub>s\<^sub>t_subst_apply[OF wf\<^sub>s\<^sub>s\<^sub>t_subst_apply[OF wf\<^sub>s\<^sub>s\<^sub>t_subst_apply[OF T]]])
  thus ?thesis
    using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst unlabel_subst
          labeled_stateful_strand_subst_comp[OF 0(1), of "\<sigma> \<circ>\<^sub>s \<alpha>"]
          labeled_stateful_strand_subst_comp[OF 0(2), of \<alpha>]
          subst_compose_assoc[of \<xi> \<sigma> \<alpha>]
    by metis
qed

lemma admissible_transaction_decl_fresh_renaming_subst_not_occurs:
  fixes \<xi> \<sigma> \<alpha>
  defines "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
  assumes T_adm: "admissible_transaction' T"
    and \<xi>\<sigma>\<alpha>:
      "transaction_decl_subst \<xi> T"
      "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "\<nexists>t. \<theta> x = occurs t"
    and "\<theta> x \<noteq> Fun OccursSec []"
proof -
  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T_adm \<xi>\<sigma>\<alpha>(1)]
  note T_fresh_val = admissible_transactionE(2)[OF T_adm]

  show "\<nexists>t. \<theta> x = occurs t" for x
    using transaction_decl_fresh_renaming_substs_range'(1)[OF \<xi>\<sigma>\<alpha>]
    unfolding \<theta>_def[symmetric] by (cases "x \<in> subst_domain \<theta>") (force,force)

  show "\<theta> x \<noteq> Fun OccursSec []" for x
    using transaction_decl_fresh_renaming_substs_range'(3)[
            OF \<xi>\<sigma>\<alpha> _ \<xi>_empty T_fresh_val, of "\<theta> x"]
    unfolding \<theta>_def[symmetric] by (cases "x \<in> subst_domain \<theta>") auto
qed


subsection \<open>Lemmata: Reachable Constraints\<close>
lemma reachable_constraints_as_transaction_lists:
  fixes f
  defines "f \<equiv> \<lambda>(T,\<xi>,\<sigma>,\<alpha>). dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    and "g \<equiv> concat \<circ> map f"
  assumes A: "A \<in> reachable_constraints P"
  obtains Ts where "A = g Ts"
    and "\<forall>B. prefix B Ts \<longrightarrow> g B \<in> reachable_constraints P"
    and "\<forall>B T \<xi> \<sigma> \<alpha>. prefix (B@[(T,\<xi>,\<sigma>,\<alpha>)]) Ts \<longrightarrow>
                      T \<in> set P \<and> transaction_decl_subst \<xi> T \<and>
                      transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B)) \<and>
                      transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B))"
proof -
  let ?P1 = "\<lambda>A Ts. A = g Ts"
  let ?P2 = "\<lambda>Ts. \<forall>B. prefix B Ts \<longrightarrow> g B \<in> reachable_constraints P"
  let ?P3 = "\<lambda>Ts. \<forall>B T \<xi> \<sigma> \<alpha>. prefix (B@[(T,\<xi>,\<sigma>,\<alpha>)]) Ts \<longrightarrow>
                      T \<in> set P \<and> transaction_decl_subst \<xi> T \<and>
                      transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B)) \<and>
                      transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B))"

  have "\<exists>Ts. ?P1 A Ts \<and> ?P2 Ts \<and> ?P3 Ts" using A
  proof (induction A rule: reachable_constraints.induct)
    case init
    have "?P1 [] []" "?P2 []" "?P3 []" unfolding g_def f_def by simp_all
    thus ?case by blast
  next
    case (step A T \<xi> \<sigma> \<alpha>)
    let ?A' = "A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    obtain Ts where Ts: "?P1 A Ts" "?P2 Ts" "?P3 Ts" using step.IH by blast

    have 1: "?P1 ?A' (Ts@[(T,\<xi>,\<sigma>,\<alpha>)])"
      using Ts(1) unfolding g_def f_def by simp
    
    have 2: "?P2 (Ts@[(T,\<xi>,\<sigma>,\<alpha>)])"
    proof (intro allI impI)
      fix B assume "prefix B (Ts@[(T,\<xi>,\<sigma>,\<alpha>)])"
      hence "prefix B Ts \<or> B = Ts@[(T,\<xi>,\<sigma>,\<alpha>)]" by fastforce
      thus "g B \<in> reachable_constraints P "
        using Ts(1,2) reachable_constraints.step[OF step.hyps]
        unfolding g_def f_def by auto
    qed

    have 3: "?P3 (Ts@[(T,\<xi>,\<sigma>,\<alpha>)])"
      using Ts(1,3) step.hyps(2-5) unfolding g_def f_def by auto 

    show ?case using 1 2 3 by blast
  qed
  thus thesis using that by blast
qed

lemma reachable_constraints_transaction_action_obtain:
  assumes A: "A \<in> reachable_constraints P"
    and a: "a \<in> set A"
  obtains T b B \<alpha> \<sigma> \<xi>
  where "prefix (B@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) A"
    and "T \<in> set P" "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
        "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
    and "b \<in> set (transaction_strand T)" "a = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "fst a = fst b"
proof -
  define f where "f \<equiv> \<lambda>(T,\<xi>,\<sigma>::('fun,'atom,'sets,'lbl) prot_subst,\<alpha>).
                          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  define g where "g \<equiv> concat \<circ> map f"

  obtain Ts where Ts:
      "A = g Ts" "\<forall>B. prefix B Ts \<longrightarrow> g B \<in> reachable_constraints P"
      "\<forall>B T \<xi> \<sigma> \<alpha>. prefix (B@[(T,\<xi>,\<sigma>,\<alpha>)]) Ts \<longrightarrow>
            T \<in> set P \<and> transaction_decl_subst \<xi> T \<and>
            transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B)) \<and>
            transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B))"
    using reachable_constraints_as_transaction_lists[OF A] unfolding g_def f_def by blast

  obtain T \<alpha> \<xi> \<sigma> where T: "(T,\<xi>,\<sigma>,\<alpha>) \<in> set Ts" "a \<in> set (f (T,\<xi>,\<sigma>,\<alpha>))"
    using Ts(1) a unfolding g_def by auto
  
  obtain B where B: "prefix (B@[(T,\<xi>,\<sigma>,\<alpha>)]) Ts"
    using T(1) by (meson prefix_snoc_in_iff) 

  obtain b where b:
      "b \<in> set (transaction_strand T)" "a = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "fst a = fst b"
    using T(2) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_memberD'[of a "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" thesis]
    unfolding f_def by simp

  have 0: "prefix (g B@f (T, \<xi>, \<sigma>, \<alpha>)) A"
    using concat_map_mono_prefix[OF B, of f] unfolding g_def Ts(1) by simp

  have 1: "T \<in> set P" "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B))"
          "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B))"
    using B Ts(3) by (blast,blast,blast,blast)

  show thesis using 0[unfolded f_def] that[OF _ 1 b] by fast
qed

lemma reachable_constraints_unlabel_eq:
  defines "transaction_unlabel_eq \<equiv> \<lambda>T1 T2.
             transaction_decl T1     =          transaction_decl T2 \<and>
             transaction_fresh T1    =          transaction_fresh T2 \<and>
    unlabel (transaction_receive T1) = unlabel (transaction_receive T2) \<and>
    unlabel (transaction_checks T1)  = unlabel (transaction_checks T2) \<and>
    unlabel (transaction_updates T1) = unlabel (transaction_updates T2) \<and>
    unlabel (transaction_send T1)    = unlabel (transaction_send T2)"
  assumes Peq: "list_all2 transaction_unlabel_eq P1 P2"
  shows "unlabel ` reachable_constraints P1 = unlabel ` reachable_constraints P2" (is "?A = ?B")
proof (intro antisym subsetI)
  have "transaction_unlabel_eq T2 T1 = transaction_unlabel_eq T1 T2" for T1 T2
    unfolding transaction_unlabel_eq_def by argo
  hence Peq': "list_all2 transaction_unlabel_eq P2 P1"
    using Peq list_all2_sym by metis

  have 0: "unlabel (transaction_strand T1) = unlabel (transaction_strand T2)"
    when "transaction_unlabel_eq T1 T2" for T1 T2
    using that unfolding transaction_unlabel_eq_def transaction_strand_def by force

  have "vars_transaction T1 = vars_transaction T2" when "transaction_unlabel_eq T1 T2" for T1 T2
    using 0[OF that] by simp
  hence "vars_transaction (P1 ! i) = vars_transaction (P2 ! i)" when "i < length P1" for i
    using that Peq list_all2_conv_all_nth by blast
  moreover have "length P1 = length P2" using Peq unfolding list_all2_iff by argo
  ultimately have 1: "\<Union>(vars_transaction ` set P1) = \<Union>(vars_transaction ` set P2)"
    using in_set_conv_nth[of _ P1] in_set_conv_nth[of _ P2] by fastforce

  have 2:
      "transaction_decl_subst \<xi> T1 \<Longrightarrow> transaction_decl_subst \<xi> T2" (is "?A1 \<Longrightarrow> ?A2")
      "transaction_fresh_subst \<sigma> T1 (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<Longrightarrow> transaction_fresh_subst \<sigma> T2 (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<B>)"
        (is "?B1 \<Longrightarrow> ?B2")
      "transaction_renaming_subst \<alpha> P1 (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<Longrightarrow> transaction_renaming_subst \<alpha> P2 (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<B>)"
        (is "?C1 \<Longrightarrow> ?C2")
      "transaction_renaming_subst \<alpha> P2 (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<Longrightarrow> transaction_renaming_subst \<alpha> P1 (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<B>)"
        (is "?D1 \<Longrightarrow> ?D2")
    when "transaction_unlabel_eq T1 T2" "unlabel \<A> = unlabel \<B>"
    for T1 T2::"('fun,'atom,'sets,'lbl) prot_transaction"
      and \<A> \<B>::"('fun,'atom,'sets,'lbl) prot_strand"
      and \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  proof -
    have *: "transaction_decl T1 = transaction_decl T2"
            "transaction_fresh T1 = transaction_fresh T2"
            "trms_transaction T1 = trms_transaction T2"
      using that unfolding transaction_unlabel_eq_def transaction_strand_def by force+

    show "?A1 \<Longrightarrow> ?A2" using *(1) unfolding transaction_decl_subst_def by argo
    show "?B1 \<Longrightarrow> ?B2" using that(2) *(2,3) unfolding transaction_fresh_subst_def by force
    show "?C1 \<Longrightarrow> ?C2" using that(2) 1 unfolding transaction_renaming_subst_def by metis
    show "?D1 \<Longrightarrow> ?D2" using that(2) 1 unfolding transaction_renaming_subst_def by metis
  qed

  have 3: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T1 \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) =
           unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T2 \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    when "transaction_unlabel_eq T1 T2" for T1 T2 \<theta>
    using 0[OF that] unlabel_subst[of _ \<theta>] dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_cong by metis

  have "\<exists>\<B> \<in> reachable_constraints P2. unlabel \<A> = unlabel \<B>"
    when "\<A> \<in> reachable_constraints P1" for \<A> using that
  proof (induction \<A> rule: reachable_constraints.induct)
    case (step \<A> T \<xi> \<sigma> \<alpha>)
    obtain \<B> where IH: "\<B> \<in> reachable_constraints P2" "unlabel \<A> = unlabel \<B>"
      by (meson step.IH)
    
    obtain T' where T': "T' \<in> set P2" "transaction_unlabel_eq T T'"
      using list_all2_in_set_ex[OF Peq step.hyps(2)] by auto

    show ?case
      using 3[OF T'(2), of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] IH(2) reachable_constraints.step[OF IH(1) T'(1)]
            2[OF T'(2) IH(2)] step.hyps(3-5)
      by (metis unlabel_append[of \<A>] unlabel_append[of \<B>])
  qed (simp add: unlabel_def)
  thus "\<A> \<in> ?A \<Longrightarrow> \<A> \<in> ?B" for \<A> by fast

  have "\<exists>\<B> \<in> reachable_constraints P1. unlabel \<A> = unlabel \<B>"
    when "\<A> \<in> reachable_constraints P2" for \<A> using that
  proof (induction \<A> rule: reachable_constraints.induct)
    case (step \<A> T \<xi> \<sigma> \<alpha>)
    obtain \<B> where IH: "\<B> \<in> reachable_constraints P1" "unlabel \<A> = unlabel \<B>"
      by (meson step.IH)
    
    obtain T' where T': "T' \<in> set P1" "transaction_unlabel_eq T T'"
      using list_all2_in_set_ex[OF Peq' step.hyps(2)] by auto

    show ?case
      using 3[OF T'(2), of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] IH(2) reachable_constraints.step[OF IH(1) T'(1)]
            2[OF T'(2) IH(2)] step.hyps(3-5)
      by (metis unlabel_append[of \<A>] unlabel_append[of \<B>])
  qed (simp add: unlabel_def)
  thus "\<A> \<in> ?B \<Longrightarrow> \<A> \<in> ?A" for \<A> by fast
qed

lemma reachable_constraints_set_eq:
  assumes "set P1 = set P2"
  shows "reachable_constraints P1 = reachable_constraints P2" (is "?A = ?B")
proof (intro antisym subsetI)
  note 0 = assms transaction_renaming_subst_set_eq[OF assms]
  note 1 = reachable_constraints.intros

  show "\<A> \<in> ?A \<Longrightarrow> \<A> \<in> ?B" for \<A>
    by (induct \<A> rule: reachable_constraints.induct) (auto simp add: 0 intro: 1)

  show "\<A> \<in> ?B \<Longrightarrow> \<A> \<in> ?A" for \<A>
    by (induct \<A> rule: reachable_constraints.induct) (auto simp add: 0 intro: 1)
qed

lemma reachable_constraints_set_subst:
  assumes "set P1 = set P2"
    and "Q (reachable_constraints P1)"
  shows "Q (reachable_constraints P2)"
by (rule subst[of _ _ Q, OF reachable_constraints_set_eq[OF assms(1)] assms(2)])

lemma reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s:
  assumes "\<forall>T \<in> set P. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms_transaction T)"
    and "\<A> \<in> reachable_constraints P"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
using assms(2)
proof (induction \<A> rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms_transaction T)"
    using assms(1) step.hyps(2) by blast
  hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    using transaction_decl_fresh_renaming_substs_range_wf_trms[OF step.hyps(3-5)]
    by (metis wf_trms_subst)
  hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    using wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_trms\<^sub>s\<^sub>s\<^sub>t_subst unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] by metis
  hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)))"
    using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq by blast
  thus ?case using step.IH unlabel_append[of \<A>] trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] by auto
qed simp

lemma reachable_constraints_var_types_in_transactions:
  fixes \<A>::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T).
              \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
  shows "\<Gamma>\<^sub>v ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<subseteq> (\<Union>T \<in> set P. \<Gamma>\<^sub>v ` fv_transaction T)" (is "?A \<A>")
    and "\<Gamma>\<^sub>v ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<subseteq> (\<Union>T \<in> set P. \<Gamma>\<^sub>v ` bvars_transaction T)" (is "?B \<A>")
    and "\<Gamma>\<^sub>v ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<subseteq> (\<Union>T \<in> set P. \<Gamma>\<^sub>v ` vars_transaction T)" (is "?C \<A>")
using \<A>
proof (induction \<A> rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  note 2 = transaction_decl_fresh_renaming_substs_wt[OF step.hyps(3-5)]

  have 3: "\<forall>t \<in> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>). fv t = {} \<or> (\<exists>x. t = Var x)"
    using transaction_decl_fresh_renaming_substs_range'(1)[OF step.hyps(3-5)]
    by fastforce

  have "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
       "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
       "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    unfolding T'_def
    by (metis fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq,
        metis bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq,
        metis vars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq)
  hence "\<Gamma> ` Var ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> \<Gamma> ` Var ` fv_transaction T"
        "\<Gamma> ` Var ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = \<Gamma> ` Var ` bvars_transaction T"
        "\<Gamma> ` Var ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> \<Gamma> ` Var ` vars_transaction T"
    using wt_subst_lsst_vars_type_subset[OF 2 3, of "transaction_strand T"]
    by argo+
  hence "\<Gamma>\<^sub>v ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> \<Gamma>\<^sub>v ` fv_transaction T"
        "\<Gamma>\<^sub>v ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = \<Gamma>\<^sub>v ` bvars_transaction T"
        "\<Gamma>\<^sub>v ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> \<Gamma>\<^sub>v ` vars_transaction T"
    by (metis \<Gamma>\<^sub>v_Var_image)+
  hence 4: "\<Gamma>\<^sub>v ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> (\<Union>T \<in> set P. \<Gamma>\<^sub>v ` fv_transaction T)"
           "\<Gamma>\<^sub>v ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> (\<Union>T \<in> set P. \<Gamma>\<^sub>v ` bvars_transaction T)"
           "\<Gamma>\<^sub>v ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> (\<Union>T \<in> set P. \<Gamma>\<^sub>v ` vars_transaction T)"
    using step.hyps(2) by fast+

  have 5: "\<Gamma>\<^sub>v ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> @ T') = (\<Gamma>\<^sub>v ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<union> (\<Gamma>\<^sub>v ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"
          "\<Gamma>\<^sub>v ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> @ T') = (\<Gamma>\<^sub>v ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<union> (\<Gamma>\<^sub>v ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"
          "\<Gamma>\<^sub>v ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> @ T') = (\<Gamma>\<^sub>v ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<union> (\<Gamma>\<^sub>v ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"
    using unlabel_append[of \<A> T']
          fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel T'"]
          bvars\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel T'"]
          vars\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel T'"]
    by auto

  { case 1 thus ?case
      using step.IH(1) 4(1) 5(1)
      unfolding T'_def by (simp del: subst_subst_compose fv\<^sub>s\<^sub>s\<^sub>t_def)
  }

  { case 2 thus ?case
      using step.IH(2) 4(2) 5(2)
      unfolding T'_def by (simp del: subst_subst_compose bvars\<^sub>s\<^sub>s\<^sub>t_def)
  }

  { case 3 thus ?case
      using step.IH(3) 4(3) 5(3)
      unfolding T'_def by (simp del: subst_subst_compose)
  }
qed simp_all

lemma reachable_constraints_no_bvars:
  assumes \<A>: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) = {}"
  shows "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
using assms proof (induction)
  case init
  then show ?case 
    unfolding unlabel_def by auto
next
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  then have "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
    by metis
  moreover
  have "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) = {}"
    using step by (metis bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq)
  ultimately 
  show ?case
    using bvars\<^sub>s\<^sub>s\<^sub>t_append unlabel_append by (metis sup_bot.left_neutral)
qed

lemma reachable_constraints_fv_bvars_disj:
  fixes \<A>::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>S \<in> set P. admissible_transaction' S"
  shows "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
proof -
  let ?X = "\<Union>T \<in> set P. bvars_transaction T"

  note 0 = admissible_transactions_fv_bvars_disj[OF P]

  have 1: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<subseteq> ?X" using \<A>_reach
  proof (induction \<A> rule: reachable_constraints.induct)
    case (step \<A> T \<xi> \<sigma> \<alpha>)
    have "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) = bvars_transaction T"
      using bvars\<^sub>s\<^sub>s\<^sub>t_subst[of "unlabel (transaction_strand T)" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
      by argo
    hence "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<subseteq> ?X"
      using step.hyps(2)
      by blast
    thus ?case
      using step.IH bvars\<^sub>s\<^sub>s\<^sub>t_append
      by auto
  qed (simp add: unlabel_def)

  have 2: "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> ?X = {}" using \<A>_reach
  proof (induction \<A> rule: reachable_constraints.induct)
    case (step \<A> T \<xi> \<sigma> \<alpha>)
    have "x \<noteq> y" when x: "x \<in> ?X" and y: "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" for x y
    proof -
      obtain y' where y': "y' \<in> fv_transaction T" "y \<in> fv ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y')"
        using y unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
        by (metis fv\<^sub>s\<^sub>s\<^sub>t_subst_obtain_var)

      have "y \<notin> \<Union>(vars_transaction ` set P)"
        using transaction_decl_fresh_renaming_substs_range''[OF step.hyps(3-5) y'(2)]
              transaction_renaming_subst_range_notin_vars[OF step.hyps(5), of y']
        by auto
      thus ?thesis using x vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t by fast
    qed
    hence "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<inter> ?X = {}"
      by blast
    thus ?case
      using step.IH
            fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"]
            unlabel_append[of \<A> "transaction_strand T"]
      by force
  qed (simp add: unlabel_def)

  show ?thesis using 0 1 2 by blast
qed

lemma reachable_constraints_vars_TAtom_typed:
  fixes \<A>::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and x: "x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
  shows "\<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
proof -
  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P \<A>_reach)

  have T_adm: "admissible_transaction' T" when "T \<in> set P" for T
    by (meson that Ball_set P)

  have "\<forall>T\<in>set P. \<forall>x\<in>set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    using protocol_transaction_vars_TAtom_typed(3) P by blast
  hence *: "\<Gamma>\<^sub>v ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<subseteq> (\<Union>T\<in>set P. \<Gamma>\<^sub>v ` vars_transaction T)"
    using reachable_constraints_var_types_in_transactions[of \<A> P, OF \<A>_reach] by auto

  have "\<Gamma>\<^sub>v ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<subseteq> TAtom ` insert Value (range Atom)"
  proof -
    have "\<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
      when "T \<in> set P" "x \<in> vars_transaction T" for T x
      using that protocol_transaction_vars_TAtom_typed(1)[of T] P
            admissible_transactionE(5)
      by blast
    hence "(\<Union>T\<in>set P. \<Gamma>\<^sub>v ` vars_transaction T) \<subseteq> TAtom ` insert Value (range Atom)"
      using P by blast
    thus "\<Gamma>\<^sub>v ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<subseteq> TAtom ` insert Value (range Atom)"
      using * by auto
  qed
  thus ?thesis using x by auto
qed

lemma reachable_constraints_vars_not_attack_typed:
  fixes \<A>::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T).
              \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
           "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. \<not>TAtom AttackType \<sqsubseteq> \<Gamma>\<^sub>v x"
    and x: "x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
  shows "\<not>TAtom AttackType \<sqsubseteq> \<Gamma>\<^sub>v x"
using reachable_constraints_var_types_in_transactions(3)[OF \<A>_reach P(1)] P(2) x by fastforce

lemma reachable_constraints_Value_vars_are_fv:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and x: "x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
    and "\<Gamma>\<^sub>v x = TAtom Value"
  shows "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
proof -
  have "\<forall>T\<in>set P. bvars_transaction T = {}"
    using P admissible_transactionE(4) by metis
  hence \<A>_no_bvars: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
    using reachable_constraints_no_bvars[OF \<A>_reach] by metis
  thus ?thesis using x vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"] by blast
qed

lemma reachable_constraints_subterms_subst:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>)) = (subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
proof -
  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P \<A>_reach)

  from \<I> have \<I>': "welltyped_constraint_model \<I> \<A>"
    using welltyped_constraint_model_prefix by auto

  have 1: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>). (\<exists>f. \<I> x = Fun f []) \<or> (\<exists>y. \<I> x = Var y)"
  proof
    fix x
    assume xa: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    have "\<exists>f T. \<I> x = Fun f T"
      using \<I> interpretation_grounds[of \<I> "Var x"]
      unfolding welltyped_constraint_model_def constraint_model_def
      by (cases "\<I> x") auto
    then obtain f T where fT_p: "\<I> x = Fun f T"
      by auto
    hence "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)"
      using \<I>
      unfolding welltyped_constraint_model_def constraint_model_def
      using wf_trm_subst_rangeD
      by metis
    moreover
    have "x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
      using xa var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t[of x "unlabel \<A>"] vars_iff_subtermeq[of x]
      by auto
    hence "\<exists>a. \<Gamma>\<^sub>v x = TAtom a"
      using reachable_constraints_vars_TAtom_typed[OF \<A>_reach P] by blast
    hence "\<exists>a. \<Gamma> (Var x) = TAtom a"
      by simp
    hence "\<exists>a. \<Gamma> (Fun f T) = TAtom a"
      by (metis (no_types, opaque_lifting) \<I>' welltyped_constraint_model_def fT_p wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
    ultimately show "(\<exists>f. \<I> x = Fun f []) \<or> (\<exists>y. \<I> x = Var y)"
      using TAtom_term_cases fT_p by metis
  qed

  have "\<forall>T\<in>set P. bvars_transaction T = {}"
    using assms admissible_transactionE(4) by metis
  then have "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
    using reachable_constraints_no_bvars assms by metis
  then have 2: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> subst_domain \<I> = {}"
    by auto

  show ?thesis
    using subterms_subst_lsst[OF _ 2] 1
    by simp
qed

lemma reachable_constraints_val_funs_private':
  fixes \<A>::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction_terms T"
           "\<forall>T \<in> set P. transaction_decl T () = []"
           "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    and f: "f \<in> \<Union>(funs_term ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "\<not>is_PubConstValue f"
    and "\<not>is_Abs f"
proof -
  have "\<not>is_PubConstValue f \<and> \<not>is_Abs f" using \<A>_reach f
  proof (induction \<A> rule: reachable_constraints.induct)
    case (step \<A> T \<xi> \<sigma> \<alpha>)
    let ?T' = "unlabel (transaction_strand T) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
    let ?T'' = "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

    note \<xi>_empty =
      admissible_transaction_decl_subst_empty'[OF bspec[OF P(2) step.hyps(2)] step.hyps(3)]

    have T: "admissible_transaction_terms T"
      using P(1) step.hyps(2) by metis

    have T_fresh: "\<forall>x \<in> set (transaction_fresh T). fst x = TAtom Value" when "T \<in> set P" for T
      using P that admissible_transactionE(14) unfolding list_all_iff \<Gamma>\<^sub>v_TAtom'' by fast

    show ?thesis using step
    proof (cases "f \<in> \<Union>(funs_term ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)")
      case False
      then obtain t where t: "t \<in> trms\<^sub>s\<^sub>s\<^sub>t ?T'" "f \<in> funs_term t"
        using step.prems trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of ?T'']
              trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?T'')"]
              unlabel_append[of \<A> "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?T''"] unlabel_subst[of "transaction_strand T"]
        by fastforce
      show ?thesis using trms\<^sub>s\<^sub>s\<^sub>t_funs_term_cases[OF t]
      proof
        assume "\<exists>u \<in> trms_transaction T. f \<in> funs_term u"
        thus ?thesis
          using conjunct1[OF conjunct2[OF T[unfolded admissible_transaction_terms_def]]]
          unfolding is_PubConstValue_def by blast
      next
        assume "\<exists>x \<in> fv_transaction T. f \<in> funs_term ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x)"
        then obtain x where "x \<in> fv_transaction T" "f \<in> funs_term ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x)" by moura
        thus ?thesis
          using transaction_decl_fresh_renaming_substs_range'(3)[
                  OF step.hyps(3-5) _ \<xi>_empty T_fresh[OF step.hyps(2), unfolded \<Gamma>\<^sub>v_TAtom''(2)]]
          unfolding is_PubConstValue_def
          by (metis (no_types, lifting) funs_term_Fun_subterm prot_fun.disc(30,48) subst_imgI
                subtermeq_Var_const(2) term.distinct(1) term.inject(2) term.set_cases(1))
      qed
    qed simp
  qed simp
  thus "\<not>is_PubConstValue f" "\<not>is_Abs f" by simp_all
qed

lemma reachable_constraints_val_funs_private:
  fixes \<A>::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and f: "f \<in> \<Union>(funs_term ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "\<not>is_PubConstValue f"
    and "\<not>is_Abs f"
using P reachable_constraints_val_funs_private'[OF \<A>_reach _ _ _ f]
      admissible_transaction_is_wellformed_transaction(4)
      admissible_transactionE(1,14)
unfolding list_all_iff \<Gamma>\<^sub>v_TAtom''
by (blast,fast)

lemma reachable_constraints_occurs_fact_ik_case:
  fixes A::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and occ: "occurs t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  shows "\<exists>n. t = Fun (Val n) []"
using \<A>_reach occ
proof (induction A rule: reachable_constraints.induct)
  case (step A T \<xi> \<sigma> \<alpha>)
  define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  have T_adm: "admissible_transaction' T" using P step.hyps(2) by blast
  hence T: "wellformed_transaction T" "admissible_transaction_occurs_checks T"
    using admissible_transaction_is_wellformed_transaction(1) P_occ step.hyps(2) by (blast,blast)

  have T_fresh: "\<forall>x \<in> set (transaction_fresh T). fst x = TAtom Value"
    using admissible_transactionE(14)[OF T_adm] unfolding list_all_iff by fast

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T_adm step.hyps(3)]

  have \<xi>_dom_empty: "z \<notin> fst ` set (transaction_decl T ())" for z
    using transaction_decl_subst_empty_inv[OF step.hyps(3)[unfolded \<xi>_empty]] by simp

  show ?case
  proof (cases "occurs t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A")
    case False
    hence "occurs t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
      using step.prems unfolding \<theta>_def by simp
    hence "\<exists>ts. occurs t \<in> set ts \<and>
                receive\<langle>ts\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
      unfolding ik\<^sub>s\<^sub>s\<^sub>t_def by force
    hence "\<exists>ts. occurs t \<in> set ts \<and>
                send\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
      using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(1) by blast
    then obtain ts s where s:
        "s \<in> set ts" "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T))" "s \<cdot> \<theta> = occurs t"
      using stateful_strand_step_mem_substD(1)[of _ "unlabel (transaction_strand T)" \<theta>]
            unlabel_subst[of "transaction_strand T" \<theta>]
      by force

    note 0 = transaction_decl_fresh_renaming_substs_range[OF step.hyps(3-5)]

    have 1: "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))"
      using s(2) wellformed_transaction_strand_unlabel_memberD(8)[OF T(1)] by blast

    have 2: "is_Send (send\<langle>ts\<rangle>)"
      unfolding is_Send_def by simp

    have 3: "\<exists>u. s = occurs u"
    proof -
      { fix z
        have "(\<exists>n. \<theta> z = Fun (Val n) []) \<or> (\<exists>y. \<theta> z = Var y)"
          using 0(3,4) T_fresh \<xi>_dom_empty unfolding \<theta>_def by blast
        hence "\<nexists>u. \<theta> z = occurs u" "\<theta> z \<noteq> Fun OccursSec []" by auto
      } note * = this

      obtain u u' where T: "s = Fun OccursFact [u,u']"
        using *(1) s(3) by (cases s) auto
      thus ?thesis using *(2) s(3) by (cases u) auto
    qed

    obtain x where x: "x \<in> set (transaction_fresh T)" "s = occurs (Var x)"
      using 3 s(1) admissible_transaction_occurs_checksE4[OF T(2) 1] by metis
    
    have "t = \<theta> x"
      using s(3) x(2) by auto
    thus ?thesis
      using 0(3)[OF \<xi>_dom_empty x(1)] x(1) T_fresh unfolding \<theta>_def by fast
  qed (simp add: step.IH)
qed simp

lemma reachable_constraints_occurs_fact_send_ex:
  fixes A::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and x: "\<Gamma>\<^sub>v x = TAtom Value" "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  shows "\<exists>ts. occurs (Var x) \<in> set ts \<and> send\<langle>ts\<rangle> \<in> set (unlabel A)"
using \<A>_reach x(2)
proof (induction A rule: reachable_constraints.induct)
  case (step A T \<xi> \<sigma> \<alpha>)
  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF bspec[OF P step.hyps(2)] step.hyps(3)]
  note T = bspec[OF P_occ step.hyps(2)]
  
  show ?case
  proof (cases "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A")
    case True
    show ?thesis
      using step.IH[OF True] unlabel_append[of A]
      by auto
  next
    case False
    then obtain y where y:
        "y \<in> fv_transaction T - set (transaction_fresh T)" "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y = Var x"
      using transaction_decl_fresh_renaming_substs_fv[OF step.hyps(3-5), of x]
            step.prems(1) fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel A"] unlabel_append[of A]
      by auto
    
    have "\<sigma> y = Var y" using y(1) step.hyps(4) unfolding transaction_fresh_subst_def by auto
    hence "\<alpha> y = Var x" using y(2) unfolding subst_compose_def \<xi>_empty by simp
    hence y_val: "fst y = TAtom Value" "\<Gamma>\<^sub>v y = TAtom Value"
      using x(1) \<Gamma>\<^sub>v_TAtom''[of x] \<Gamma>\<^sub>v_TAtom''[of y]
            wt_subst_trm''[OF transaction_renaming_subst_wt[OF step.hyps(5)], of "Var y"]
      by force+

    obtain ts where ts:
        "occurs (Var y) \<in> set ts" "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T))"
      using admissible_transaction_occurs_checksE1[OF T y(1) y_val(2)]
      by (metis list.set_intros(1) unlabel_Cons(1)) 
    hence "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T))" 
      using transaction_strand_subsets(5) by blast
    hence *: "receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>\<rangle> \<in> set (unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      using unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            stateful_strand_step_subst_inI(2)[of _ _ "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] 
      by force

    have "occurs (Var y) \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = occurs (Var x)"
      using y(2) by (auto simp del: subst_subst_compose)
    hence **: "occurs (Var x) \<in> set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" using ts(1) by force

    have "send\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)))"
      using * dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(2) by blast
    thus ?thesis using ** unlabel_append[of A] by force
  qed
qed simp

lemma reachable_constraints_db\<^sub>l\<^sub>s\<^sub>s\<^sub>t_set_args_empty:
  assumes \<A>: "\<A> \<in> reachable_constraints P"
    and PP: "list_all wellformed_transaction P"
    and admissible_transaction_updates:
      "let f = (\<lambda>T. \<forall>x \<in> set (unlabel (transaction_updates T)).
                      is_Update x \<and> is_Var (the_elem_term x) \<and> is_Fun_Set (the_set_term x) \<and>
                      fst (the_Var (the_elem_term x)) = TAtom Value)
      in list_all f P"
    and d: "(t, s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  shows "\<exists>ss. s = Fun (Set ss) []"
  using \<A> d
proof (induction)
  case (step \<A> TT \<xi> \<sigma> \<alpha>)
  let ?TT = "transaction_strand TT \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
  let ?TTu = "unlabel ?TT"
  let ?TTd = "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?TT"
  let ?TTdu = "unlabel ?TTd"

  from step(6) have "(t, s) \<in> set (db'\<^sub>s\<^sub>s\<^sub>t ?TTdu \<I> (db'\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) \<I> []))"
    by (metis db\<^sub>s\<^sub>s\<^sub>t_append db\<^sub>s\<^sub>s\<^sub>t_def step.prems unlabel_append)
  hence "(t, s) \<in> set (db'\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) \<I> []) \<or>
    (\<exists>t' s'. insert\<langle>t',s'\<rangle> \<in> set ?TTdu \<and> t = t' \<cdot> \<I> \<and> s = s' \<cdot> \<I>)"
    using db\<^sub>s\<^sub>s\<^sub>t_in_cases[of t "s" ?TTdu \<I>] by metis 
  thus ?case
  proof
    assume "\<exists>t' s'. insert\<langle>t',s'\<rangle> \<in> set ?TTdu \<and> t = t' \<cdot> \<I> \<and> s = s' \<cdot> \<I>"
    then obtain t' s' where t's'_p: "insert\<langle>t',s'\<rangle> \<in> set ?TTdu" "t = t' \<cdot> \<I>" "s = s' \<cdot> \<I>" by metis
    then obtain lll where "(lll, insert\<langle>t',s'\<rangle>) \<in> set ?TTd" by (meson unlabel_mem_has_label)
    hence "(lll, insert\<langle>t',s'\<rangle>) \<in> set (transaction_strand TT \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(4) by blast
    hence "insert\<langle>t',s'\<rangle> \<in> set ?TTu" by (meson unlabel_in)
    hence "insert\<langle>t',s'\<rangle> \<in> set ((unlabel (transaction_strand TT)) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      by (simp add: subst_lsst_unlabel)
    hence "insert\<langle>t',s'\<rangle> \<in> (\<lambda>x. x \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` set (unlabel (transaction_strand TT))"
      unfolding subst_apply_stateful_strand_def by auto
    then obtain u where
        "u \<in> set (unlabel (transaction_strand TT)) \<and> u \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = insert\<langle>t',s'\<rangle>"
      by auto
    hence "\<exists>t'' s''. insert\<langle>t'',s''\<rangle> \<in> set (unlabel (transaction_strand TT)) \<and>
                   t' = t'' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<and> s' = s'' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      by  (cases u) auto
    then obtain t'' s'' where t''s''_p:
        "insert\<langle>t'',s''\<rangle> \<in> set (unlabel (transaction_strand TT)) \<and>
          t' = t'' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<and> s' = s'' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      by auto
    hence "insert\<langle>t'',s''\<rangle> \<in> set (unlabel (transaction_updates TT))"
      using is_Update_in_transaction_updates[of "insert\<langle>t'',s''\<rangle>" TT]
      using PP step(2) unfolding list_all_iff by auto
    moreover have "\<forall>x\<in>set (unlabel (transaction_updates TT)). is_Fun_Set (the_set_term x)"
      using step(2) admissible_transaction_updates unfolding is_Fun_Set_def list_all_iff by auto
    ultimately have "is_Fun_Set (the_set_term (insert\<langle>t'',s''\<rangle>))" by auto
    moreover have "s' = s'' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" using t''s''_p by blast
    ultimately have "is_Fun_Set (the_set_term (insert\<langle>t',s'\<rangle>))" by (auto simp add: is_Fun_Set_subst)
    hence "is_Fun_Set s" by (simp add: t's'_p(3) is_Fun_Set_subst)
    thus ?case using is_Fun_Set_exi by auto
  qed (auto simp add: step db\<^sub>s\<^sub>s\<^sub>t_def)
qed auto

lemma reachable_constraints_occurs_fact_ik_ground:
  fixes A::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and t: "occurs t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  shows "fv (occurs t) = {}"
proof -
  have 0: "admissible_transaction' T"
    when "T \<in> set P" for T
    using P that unfolding list_all_iff by simp

  note 1 = admissible_transaction_is_wellformed_transaction(1)[OF 0] bspec[OF P_occ]

  have 2: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) =
           (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<union> (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
    when "T \<in> set P" for T \<theta> and A::"('fun,'atom,'sets,'lbl) prot_constr"
    using dual_transaction_ik_is_transaction_send'[OF 1(1)[OF that]] by fastforce

  show ?thesis using \<A>_reach t
  proof (induction A rule: reachable_constraints.induct)
    case (step A T \<xi> \<sigma> \<alpha>)
    note \<xi>_empty = admissible_transaction_decl_subst_empty[OF 0[OF step.hyps(2)] step.hyps(3)]

    from step show ?case
    proof (cases "occurs t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A")
      case False
      hence "occurs t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
        using 2[OF step.hyps(2)] step.prems \<xi>_empty by blast
      then obtain ts where ts:
          "occurs t \<in> set ts" "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
        using wellformed_transaction_send_receive_subst_trm_cases(2)[OF 1(1)[OF step.hyps(2)]]
        by blast
      then obtain ts' s where s:
          "occurs s \<in> set ts'" "send\<langle>ts'\<rangle> \<in> set (unlabel (transaction_send T))" "t = s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
        using transaction_decl_fresh_renaming_substs_occurs_fact_send_receive(1)[
                OF step.hyps(3-5) 0[OF step.hyps(2)] ts(1)]
              transaction_strand_subst_subsets(8)[of T "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
        by blast

      obtain x where x: "x \<in> set (transaction_fresh T)" "s = Var x"
        using admissible_transaction_occurs_checksE4[OF 1(2)[OF step.hyps(2)] s(2,1)] by metis

      have "fv t = {}"
        using transaction_decl_fresh_renaming_substs_range(2)[OF step.hyps(3-5) _ x(1)]
              s(3) x(2) transaction_decl_subst_empty_inv[OF step.hyps(3)[unfolded \<xi>_empty]]
        by (auto simp del: subst_subst_compose)
      thus ?thesis by simp
    qed simp
  qed simp
qed

lemma reachable_constraints_occurs_fact_ik_funs_terms:
  fixes A::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model I A"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
  shows "\<forall>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I). OccursFact \<notin> \<Union>(funs_term ` set (snd (Ana s)))" (is "?A A")
    and "\<forall>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I). OccursSec \<notin> \<Union>(funs_term ` set (snd (Ana s)))" (is "?B A")
    and "Fun OccursSec [] \<notin> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I" (is "?C A")
    and "\<forall>x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. I x \<noteq> Fun OccursSec []" (is "?D A")
proof -
  have T_adm: "admissible_transaction' T" when "T \<in> set P" for T
    using P that unfolding list_all_iff by simp

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  note T_occ = bspec[OF P_occ]

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T_adm]

  have \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" by (metis \<I> welltyped_constraint_model_def)

  have \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
    by (metis \<I> welltyped_constraint_model_def constraint_model_def)

  have \<I>_grounds: "fv (I x) = {}" "\<exists>f T. I x = Fun f T" for x
    using \<I> interpretation_grounds[of I, of "Var x"] empty_fv_exists_fun[of "I x"]
    unfolding welltyped_constraint_model_def constraint_model_def by auto

  have 00: "fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<subseteq> vars_transaction T"
           "fv\<^sub>s\<^sub>e\<^sub>t (subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))) = fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))"
    for T::"('fun,'atom,'sets,'lbl) prot_transaction"
    using fv_trms\<^sub>s\<^sub>s\<^sub>t_subset(1)[of "unlabel (transaction_send T)"] vars_transaction_unfold
          fv_subterms_set[of "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"]
    by blast+

  have 0: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). \<exists>a. \<Gamma> (Var x) = TAtom a"
          "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). \<Gamma> (Var x) \<noteq> TAtom OccursSecType"
          "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))). \<exists>a. \<Gamma> (Var x) = TAtom a"
          "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))). \<Gamma> (Var x) \<noteq> TAtom OccursSecType"
          "\<forall>x \<in> vars_transaction T. \<exists>a. \<Gamma> (Var x) = TAtom a"
          "\<forall>x \<in> vars_transaction T. \<Gamma> (Var x) \<noteq> TAtom OccursSecType"
    when "T \<in> set P" for T
    using admissible_transaction_occurs_fv_types[OF T_adm[OF that]] 00
    by blast+

  note T_fresh_type = admissible_transactionE(2)[OF T_adm]

  have 1: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<cdot>\<^sub>s\<^sub>e\<^sub>t I =
           (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<union> (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> \<cdot>\<^sub>s\<^sub>e\<^sub>t I)"
    when "T \<in> set P" for T \<theta> and A::"('fun,'atom,'sets,'lbl) prot_constr"
    using dual_transaction_ik_is_transaction_send'[OF T_wf[OF that]]
    by fastforce

  have 2: "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> \<cdot>\<^sub>s\<^sub>e\<^sub>t I) =
           subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
    when "T \<in> set P" and \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" for T \<theta>
    using wt_subst_TAtom_subterms_set_subst[OF wt_subst_compose[OF \<theta>(1) \<I>_wt] 0(1)[OF that(1)]]
          wf_trm_subst_rangeD[OF wf_trms_subst_compose[OF \<theta>(2) \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s]]
    by auto

  have 3: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    when "T \<in> set P" "transaction_decl_subst \<xi> T"
         "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
    for \<xi> \<sigma> \<alpha> and T::"('fun,'atom,'sets,'lbl) prot_transaction"
      and A::"('fun,'atom,'sets,'lbl) prot_constr"
    using protocol_transaction_vars_TAtom_typed(3)[of T] P that(1)
          transaction_decl_fresh_renaming_substs_wt[OF that(2-4)]
          transaction_decl_fresh_renaming_substs_range_wf_trms[OF that(2-4)]
          wf_trms_subst_compose
    by simp_all

  have 4: "\<forall>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)).
              OccursFact \<notin> \<Union>(funs_term ` set (snd (Ana s))) \<and>
              OccursSec \<notin> \<Union>(funs_term ` set (snd (Ana s)))"
    when T: "T \<in> set P" for T
  proof
    fix t assume t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))"
    then obtain ts s where s:
        "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))" "s \<in> set ts" "t \<in> subterms s"
      using wellformed_transaction_unlabel_cases(4)[OF T_wf[OF T]]
      by fastforce

    have s_occ: "\<exists>x. s = occurs (Var x)" when "OccursFact \<in> funs_term t \<or> OccursSec \<in> funs_term t"
      using that s(1) subtermeq_imp_funs_term_subset[OF s(3)]
            admissible_transaction_occurs_checksE3[OF T_occ[OF T] _ s(2)]
      by blast

    obtain K T' where K: "Ana t = (K,T')" by moura

    show "OccursFact \<notin> \<Union>(funs_term ` set (snd (Ana t))) \<and>
          OccursSec \<notin> \<Union>(funs_term ` set (snd (Ana t)))"
    proof (rule ccontr)
      assume "\<not>(OccursFact \<notin> \<Union>(funs_term ` set (snd (Ana t))) \<and>
                OccursSec \<notin> \<Union>(funs_term ` set (snd (Ana t))))"
      hence a: "OccursFact \<in> \<Union>(funs_term ` set (snd (Ana t))) \<or>
                OccursSec \<in> \<Union>(funs_term ` set (snd (Ana t)))"
        by simp
      hence "OccursFact \<in> \<Union>(funs_term ` set T') \<or> OccursSec \<in> \<Union>(funs_term ` set T')"
        using K by simp
      hence "OccursFact \<in> funs_term t \<or> OccursSec \<in> funs_term t"
        using Ana_subterm[OF K] funs_term_subterms_eq(1)[of t] by blast
      then obtain x where x: "t \<in> subterms (occurs (Var x))"
        using s(3) s_occ by blast
      thus False using a by fastforce
    qed
  qed

  have 5: "OccursFact \<notin> \<Union>(funs_term ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
          "OccursSec \<notin> \<Union>(funs_term ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      when \<xi>\<sigma>\<alpha>: "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
                "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
      and T: "T \<in> set P"
    for \<xi> \<sigma> \<alpha> and T::"('fun,'atom,'sets,'lbl) prot_transaction"
      and A::"('fun,'atom,'sets,'lbl) prot_constr"
  proof -
    have "OccursFact \<notin> funs_term t" "OccursSec \<notin> funs_term t"
      when "t \<in> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" for t 
      using transaction_decl_fresh_renaming_substs_range'(3)[
              OF \<xi>\<sigma>\<alpha> that \<xi>_empty[OF T \<xi>\<sigma>\<alpha>(1)] T_fresh_type[OF T]]
      by auto
    thus "OccursFact \<notin> \<Union>(funs_term ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
         "OccursSec \<notin> \<Union>(funs_term ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      by blast+
  qed

  have 6: "I x \<noteq> Fun OccursSec []" "\<nexists>t. I x = occurs t" "\<exists>a. \<Gamma> (I x) = TAtom a \<and> a \<noteq> OccursSecType"
    when T: "T \<in> set P"
      and \<xi>\<sigma>\<alpha>: "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
               "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
      and x: "Var x \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
    for x \<xi> \<sigma> \<alpha> and T::"('fun,'atom,'sets,'lbl) prot_transaction"
      and A::"('fun,'atom,'sets,'lbl) prot_constr"
  proof -
    obtain t where t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "t \<cdot> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = Var x"
      using x by moura
    then obtain y where y: "t = Var y" by (cases t) auto

    have "\<exists>a. \<Gamma> t = TAtom a \<and> a \<noteq> OccursSecType"
      using 0(1,2)[OF T] t(1) y
      by force
    thus "\<exists>a. \<Gamma> (I x) = TAtom a \<and> a \<noteq> OccursSecType"
      using wt_subst_trm''[OF 3(1)[OF T \<xi>\<sigma>\<alpha>]] wt_subst_trm''[OF \<I>_wt] t(2) 
      by (metis eval_term.simps(1))
    thus "I x \<noteq> Fun OccursSec []" "\<nexists>t. I x = occurs t"
      by auto
  qed

  have 7: "I x \<noteq> Fun OccursSec []" "\<nexists>t. I x = occurs t" "\<exists>a. \<Gamma> (I x) = TAtom a \<and> a \<noteq> OccursSecType"
    when T: "T \<in> set P"
      and \<xi>\<sigma>\<alpha>: "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
               "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
      and x: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` vars_transaction T)"
    for x \<xi> \<sigma> \<alpha> and T::"('fun,'atom,'sets,'lbl) prot_transaction"
      and A::"('fun,'atom,'sets,'lbl) prot_constr"
  proof -
    obtain y where y: "y \<in> vars_transaction T" "x \<in> fv ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y)"
      using x by auto
    hence y': "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y = Var x"
      using transaction_decl_fresh_renaming_substs_range'(3)[
              OF \<xi>\<sigma>\<alpha> _ \<xi>_empty[OF T \<xi>\<sigma>\<alpha>(1)] T_fresh_type[OF T]]
      by (cases "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<in> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)") force+

    have "\<exists>a. \<Gamma> (Var y) = TAtom a \<and> a \<noteq> OccursSecType"
      using 0(5,6)[OF T] y
      by force
    thus "\<exists>a. \<Gamma> (I x) = TAtom a \<and> a \<noteq> OccursSecType"
      using wt_subst_trm''[OF 3(1)[OF T \<xi>\<sigma>\<alpha>]] wt_subst_trm''[OF \<I>_wt] y'
      by (metis eval_term.simps(1))
    thus "I x \<noteq> Fun OccursSec []" "\<nexists>t. I x = occurs t"
      by auto
  qed

  have 8: "I x \<noteq> Fun OccursSec []" "\<nexists>t. I x = occurs t" "\<exists>a. \<Gamma> (I x) = TAtom a \<and> a \<noteq> OccursSecType"
    when T: "T \<in> set P"
      and \<xi>\<sigma>\<alpha>: "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
               "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
      and x: "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
    for x \<xi> \<sigma> \<alpha> and T::"('fun,'atom,'sets,'lbl) prot_transaction"
      and A::"('fun,'atom,'sets,'lbl) prot_constr"
  proof -
    obtain t where t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))" "t \<cdot> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = Var x"
      using x by moura
    then obtain y where y: "t = Var y" by (cases t) auto

    have "\<exists>a. \<Gamma> t = TAtom a \<and> a \<noteq> OccursSecType"
      using 0(3,4)[OF T] t(1) y
      by force
    thus "\<exists>a. \<Gamma> (I x) = TAtom a \<and> a \<noteq> OccursSecType"
      using wt_subst_trm''[OF 3(1)[OF T \<xi>\<sigma>\<alpha>]] wt_subst_trm''[OF \<I>_wt] t(2) 
      by (metis eval_term.simps(1))
    thus "I x \<noteq> Fun OccursSec []" "\<nexists>t. I x = occurs t"
      by auto
  qed

  have s_fv: "fv s \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` vars_transaction T)"
    when s: "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      and T: "T \<in> set P"
    for s and \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
      and T::"('fun,'atom,'sets,'lbl) prot_transaction"
  proof
    fix x assume "x \<in> fv s"
    hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      using s by auto
    hence *: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      using fv_subterms_set_subst' by fast
    have **: "list_all is_Send (unlabel (transaction_send T))"
      using T_wf[OF T] unfolding wellformed_transaction_def by blast
    have "x \<in> fv\<^sub>s\<^sub>e\<^sub>t ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))"
    proof -
      obtain t where t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "x \<in> fv (t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
        using * by fastforce
      hence "fv t \<subseteq> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
        using fv_trms\<^sub>s\<^sub>s\<^sub>t_subset(1)[of "unlabel (transaction_send T)"]
        by auto
      thus ?thesis using t(2) subst_apply_fv_subset by fast
    qed
    thus "x \<in> fv\<^sub>s\<^sub>e\<^sub>t ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` vars_transaction T)"
      using vars_transaction_unfold[of T] by fastforce
  qed

  show "?A A" using \<A>_reach
  proof (induction A rule: reachable_constraints.induct)
    case (step A T \<xi> \<sigma> \<alpha>)
    have *: "\<forall>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)).
              OccursFact \<notin> \<Union>(funs_term ` set (snd (Ana s)))"
      using 4[OF step.hyps(2)] by blast

    have "\<forall>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot>\<^sub>s\<^sub>e\<^sub>t I.
            OccursFact \<notin> \<Union>(funs_term ` set (snd (Ana s)))"
    proof
      fix t assume t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      then obtain s u where su:
          "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "s \<cdot> I = t"
          "u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))" "u \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = s"
        by force

      obtain Ku Tu where KTu: "Ana u = (Ku,Tu)" by moura
      
      have *: "OccursFact \<notin> \<Union>(funs_term ` set Tu)"
              "OccursFact \<notin> \<Union>(funs_term ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
              "OccursFact \<notin> \<Union>(funs_term ` \<Union>(((set \<circ> snd \<circ> Ana) ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))))"
        using transaction_decl_fresh_renaming_substs_range'(3)[
                OF step.hyps(3-5) _ \<xi>_empty[OF step.hyps(2,3)] T_fresh_type[OF step.hyps(2)]]
              4[OF step.hyps(2)] su(3) KTu
        by (fastforce,fastforce,fastforce)

      have "OccursFact \<notin> \<Union>(funs_term ` set (Tu \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      proof -
        { fix f assume f: "f \<in> \<Union>(funs_term ` set (Tu \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
          then obtain tf where tf: "tf \<in> set Tu" "f \<in> funs_term (tf \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" by moura
          hence "f \<in> funs_term tf \<or> f \<in> \<Union>(funs_term ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
            using funs_term_subst[of tf "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] by force
          hence "f \<noteq> OccursFact" using *(1,2) tf(1) by blast
        } thus ?thesis by metis
      qed
      hence **: "OccursFact \<notin> \<Union>(funs_term ` set (snd (Ana s)))"
      proof (cases u)
        case (Var xu)
        hence "s = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) xu" using su(4) by (metis eval_term.simps(1))
        thus ?thesis using *(3) by fastforce
      qed (use su(4) KTu Ana_subst'[of _ _ Ku Tu "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] in simp)
      
      show "OccursFact \<notin> \<Union>(funs_term ` set (snd (Ana t)))"
      proof (cases s)
        case (Var sx)
        then obtain a where a: "\<Gamma> (I sx) = Var a"
          using su(1) 8(3)[OF step.hyps(2-5), of sx] by fast
        hence "Ana (I sx) = ([],[])" by (metis \<I>_grounds(2) const_type_inv[THEN Ana_const])
        thus ?thesis using Var su(2) by simp
      next
        case (Fun f S)
        hence snd_Ana_t: "snd (Ana t) = snd (Ana s) \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t I"
          using su(2) Ana_subst'[of f S _ "snd (Ana s)" I] by (cases "Ana s") simp_all

        { fix g assume "g \<in> \<Union>(funs_term ` set (snd (Ana t)))"
          hence "g \<in> \<Union>(funs_term ` set (snd (Ana s))) \<or>
                 (\<exists>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set (snd (Ana s))). g \<in> funs_term (I x))"
            using snd_Ana_t funs_term_subst[of _ I] by auto
          hence "g \<noteq> OccursFact"
          proof
            assume "\<exists>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set (snd (Ana s))). g \<in> funs_term (I x)"
            then obtain x where x: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set (snd (Ana s)))" "g \<in> funs_term (I x)" by moura
            have "x \<in> fv s" using x(1) Ana_vars(2)[of s] by (cases "Ana s") auto
            hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` vars_transaction T)"
              using s_fv[OF su(1) step.hyps(2)] by blast
            then obtain a h U where h:
                "I x = Fun h U" "\<Gamma> (I x) = Var a" "a \<noteq> OccursSecType" "arity h = 0"
              using \<I>_grounds(2) 7(3)[OF step.hyps(2-5)] const_type_inv
              by metis
            hence "h \<noteq> OccursFact" by auto
            moreover have "U = []" using h(1,2,4) const_type_inv_wf[of h U a] \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s by fastforce
            ultimately show ?thesis using h(1) x(2) by auto
          qed (use ** in blast)
        } thus ?thesis by blast
      qed
    qed
    thus ?case
      using step.IH step.prems 1[OF step.hyps(2), of A "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            2[OF step.hyps(2) 3[OF step.hyps(2-5)]]
      by auto
  qed simp

  show "?B A" using \<A>_reach
  proof (induction A rule: reachable_constraints.induct)
    case (step A T \<xi> \<sigma> \<alpha>)
    have "\<forall>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot>\<^sub>s\<^sub>e\<^sub>t I.
            OccursSec \<notin> \<Union>(funs_term ` set (snd (Ana s)))"
    proof
      fix t assume t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      then obtain s u where su:
          "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "s \<cdot> I = t"
          "u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))" "u \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = s"
        by force

      obtain Ku Tu where KTu: "Ana u = (Ku,Tu)" by moura
      
      have *: "OccursSec \<notin> \<Union>(funs_term ` set Tu)"
              "OccursSec \<notin> \<Union>(funs_term ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
              "OccursSec \<notin> \<Union>(funs_term ` \<Union>(((set \<circ> snd \<circ> Ana) ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))))"
        using transaction_decl_fresh_renaming_substs_range'(3)[
                OF step.hyps(3-5) _ \<xi>_empty[OF step.hyps(2,3)] T_fresh_type[OF step.hyps(2)]] 
              4[OF step.hyps(2)] su(3) KTu
        by (fastforce,fastforce,fastforce)

      have "OccursSec \<notin> \<Union>(funs_term ` set (Tu \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      proof -
        { fix f assume f: "f \<in> \<Union>(funs_term ` set (Tu \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
          then obtain tf where tf: "tf \<in> set Tu" "f \<in> funs_term (tf \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" by moura
          hence "f \<in> funs_term tf \<or> f \<in> \<Union>(funs_term ` subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
            using funs_term_subst[of tf "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] by force
          hence "f \<noteq> OccursSec" using *(1,2) tf(1) by blast
        } thus ?thesis by metis
      qed
      hence **: "OccursSec \<notin> \<Union>(funs_term ` set (snd (Ana s)))"
      proof (cases u)
        case (Var xu)
        hence "s = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) xu" using su(4) by (metis eval_term.simps(1))
        thus ?thesis using *(3) by fastforce
      qed (use su(4) KTu Ana_subst'[of _ _ Ku Tu "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] in simp)
      
      show "OccursSec \<notin> \<Union>(funs_term ` set (snd (Ana t)))"
      proof (cases s)
        case (Var sx)
        then obtain a where a: "\<Gamma> (I sx) = Var a"
          using su(1) 8(3)[OF step.hyps(2-5), of sx] by fast
        hence "Ana (I sx) = ([],[])" by (metis \<I>_grounds(2) const_type_inv[THEN Ana_const])
        thus ?thesis using Var su(2) by simp
      next
        case (Fun f S)
        hence snd_Ana_t: "snd (Ana t) = snd (Ana s) \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t I"
          using su(2) Ana_subst'[of f S _ "snd (Ana s)" I] by (cases "Ana s") simp_all

        { fix g assume "g \<in> \<Union>(funs_term ` set (snd (Ana t)))"
          hence "g \<in> \<Union>(funs_term ` set (snd (Ana s))) \<or>
                 (\<exists>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set (snd (Ana s))). g \<in> funs_term (I x))"
            using snd_Ana_t funs_term_subst[of _ I] by auto
          hence "g \<noteq> OccursSec"
          proof
            assume "\<exists>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set (snd (Ana s))). g \<in> funs_term (I x)"
            then obtain x where x: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set (snd (Ana s)))" "g \<in> funs_term (I x)" by moura
            have "x \<in> fv s" using x(1) Ana_vars(2)[of s] by (cases "Ana s") auto
            hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` vars_transaction T)"
              using s_fv[OF su(1) step.hyps(2)] by blast
            then obtain a h U where h:
                "I x = Fun h U" "\<Gamma> (I x) = Var a" "a \<noteq> OccursSecType" "arity h = 0"
              using \<I>_grounds(2) 7(3)[OF step.hyps(2-5)] const_type_inv
              by metis
            hence "h \<noteq> OccursSec" by auto
            moreover have "U = []" using h(1,2,4) const_type_inv_wf[of h U a] \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s by fastforce
            ultimately show ?thesis using h(1) x(2) by auto
          qed (use ** in blast)
        } thus ?thesis by blast
      qed
    qed
    thus ?case
      using step.IH step.prems 1[OF step.hyps(2), of A "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            2[OF step.hyps(2) 3[OF step.hyps(2-5)]]
      by auto
  qed simp

  show "?C A" using \<A>_reach
  proof (induction A rule: reachable_constraints.induct)
    case (step A T \<xi> \<sigma> \<alpha>)
    have *: "Fun OccursSec [] \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
      using admissible_transaction_occurs_checksE5[OF T_occ[OF step.hyps(2)]] by blast

    have **: "Fun OccursSec [] \<notin> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      using transaction_decl_fresh_renaming_substs_range'(3)[
              OF step.hyps(3-5) _ \<xi>_empty[OF step.hyps(2,3)] T_fresh_type[OF step.hyps(2)]]
      by auto

    have "Fun OccursSec [] \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
    proof
      assume "Fun OccursSec [] \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      then obtain s where "s \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "s \<cdot> I = Fun OccursSec []"
        by moura
      moreover have "Fun OccursSec [] \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      proof
        assume "Fun OccursSec [] \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
        then obtain u where "u \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "u \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = Fun OccursSec []"
          by moura
        thus False using * ** by (cases u) (force simp del: subst_subst_compose)+
      qed
      ultimately show False using 6[OF step.hyps(2-5)] by (cases s) auto
    qed
    thus ?case using step.IH step.prems 1[OF step.hyps(2), of A "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] by fast
  qed simp

  show "?D A" using \<A>_reach
  proof (induction A rule: reachable_constraints.induct)
    case (step A T \<xi> \<sigma> \<alpha>)
    { fix x assume x: "x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      hence x': "x \<in> vars\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
        by (metis vars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq unlabel_subst)
      hence "x \<in> vars_transaction T \<or> x \<in> fv\<^sub>s\<^sub>e\<^sub>t ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` vars_transaction T)"
        using vars\<^sub>s\<^sub>s\<^sub>t_subst_cases[OF x'] by metis
      moreover have "I x \<noteq> Fun OccursSec []" when "x \<in> vars_transaction T"
        using that 0(5,6)[OF step.hyps(2)] wt_subst_trm''[OF \<I>_wt, of "Var x"]
        by fastforce
      ultimately have "I x \<noteq> Fun OccursSec []"
        using 7(1)[OF step.hyps(2-5), of x]
        by blast
    } thus ?case using step.IH by auto
  qed simp
qed

lemma reachable_constraints_occurs_fact_ik_subst_aux:
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model I A"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and t: "t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "t \<cdot> I = occurs s"
  shows "\<exists>u. t = occurs u"
proof -
  have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
    using \<I> unfolding welltyped_constraint_model_def constraint_model_def by metis
  hence 0: "\<Gamma> t = \<Gamma> (occurs s)"
    using t(2) wt_subst_trm'' by metis

  have 1: "\<Gamma>\<^sub>v ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<subseteq> (\<Union>T \<in> set P. \<Gamma>\<^sub>v ` fv_transaction T)"
          "\<forall>T \<in> set P. \<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    using reachable_constraints_var_types_in_transactions(1)[OF \<A>_reach]
          protocol_transaction_vars_TAtom_typed(2,3) P
    by fast+

  show ?thesis
  proof (cases t)
    case (Var x)
    thus ?thesis
      using 0 1 t(1) var_subterm_ik\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of x "unlabel A"]
      by fastforce
  next
    case (Fun f T)
    hence 2: "f = OccursFact" "length T = Suc (Suc 0)" "T ! 0 \<cdot> I = Fun OccursSec []"
      using t(2) by auto

    have "T ! 0 = Fun OccursSec []"
    proof (cases "T ! 0")
      case (Var y)
      hence "I y = Fun OccursSec []" using Fun 2(3) by simp
      moreover have "Var y \<in> set T" using Var 2(2) length_Suc_conv[of T 1] by auto
      hence "y \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" using Fun t(1) by force
      hence "y \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
        using fv_ik_subset_fv_sst'[of "unlabel A"] vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel A"]
        by blast
      ultimately have False
        using reachable_constraints_occurs_fact_ik_funs_terms(4)[OF \<A>_reach \<I> P P_occ]
        by blast
      thus ?thesis by simp
    qed (use 2(3) in simp)
    moreover have "\<exists>u u'. T = [u,u']"
      using iffD1[OF length_Suc_conv 2(2)] iffD1[OF length_Suc_conv[of _ 0]] length_0_conv by fast
    ultimately show ?thesis using Fun 2(1,2) by force
  qed
qed

lemma reachable_constraints_occurs_fact_ik_subst:
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model I A"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and t: "occurs t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
  shows "occurs t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof -
  have \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
    using \<I> unfolding welltyped_constraint_model_def constraint_model_def by metis

  obtain s where s: "s \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "s \<cdot> I = occurs t"
    using t by auto
  hence u: "\<exists>u. s = occurs u"
    using \<I>_wt reachable_constraints_occurs_fact_ik_subst_aux[OF \<A>_reach \<I> P P_occ]
    by blast
  hence "fv s = {}"
    using reachable_constraints_occurs_fact_ik_ground[OF \<A>_reach P P_occ] s
    by fast
  thus ?thesis
    using s u subst_ground_ident[of s I] 
    by argo
qed

lemma reachable_constraints_occurs_fact_send_in_ik:
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model I A"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and x: "occurs (Var x) \<in> set ts" "send\<langle>ts\<rangle> \<in> set (unlabel A)"
  shows "occurs (I x) \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
using \<A>_reach \<I> x
proof (induction A rule: reachable_constraints.induct)
  case (step A T \<xi> \<sigma> \<alpha>)
  define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"

  have T_adm: "admissible_transaction' T"
    using P step.hyps(2) unfolding list_all_iff by blast

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]
  note T_adm_occ = bspec[OF P_occ]

  have \<I>_is_T_model: "strand_sem_stateful (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) (set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I)) (unlabel T') I"
    using step.prems unlabel_append[of A T'] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel A" I "[]"]
          strand_sem_append_stateful[of "{}" "{}" "unlabel A" "unlabel T'" I]
    by (simp add: T'_def \<theta>_def welltyped_constraint_model_def constraint_model_def db\<^sub>s\<^sub>s\<^sub>t_def)

  show ?case
  proof (cases "send\<langle>ts\<rangle> \<in> set (unlabel A)")
    case False
    hence "send\<langle>ts\<rangle> \<in> set (unlabel T')"
      using step.prems(3) unfolding T'_def \<theta>_def by simp
    hence "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
      using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(2) unfolding T'_def by blast
    then obtain y ts' where y:
        "receive\<langle>ts'\<rangle> \<in> set (unlabel (transaction_receive T))"
        "\<theta> y = Var x" "occurs (Var y) \<in> set ts'"
      using transaction_decl_fresh_renaming_substs_occurs_fact_send_receive(2)[
              OF step.hyps(3-5) T_adm]
            subst_to_var_is_var[of _ \<theta> x] step.prems(2)
      unfolding \<theta>_def by (metis eval_term.simps(1))
    hence "occurs (Var y) \<cdot> \<theta> \<in> set ts' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
          "receive\<langle>ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle> \<in> set (unlabel (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
      using subst_lsst_unlabel_member[of "receive\<langle>ts'\<rangle>" "transaction_receive T" \<theta>]
      by fastforce+
    hence "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> occurs (Var y) \<cdot> \<theta> \<cdot> I"
      using wellformed_transaction_sem_receives[
              OF T_wf, of "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I" "set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I)" \<theta> I "ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>"]
            \<I>_is_T_model
      unfolding T'_def list_all_iff by fastforce
    hence *: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> occurs (\<theta> y \<cdot> I)"
      by auto

    have "occurs (\<theta> y \<cdot> I) \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      using deduct_occurs_in_ik[OF *]
            reachable_constraints_occurs_fact_ik_subst[
              OF step.hyps(1) welltyped_constraint_model_prefix[OF step.prems(1)] P P_occ,
              of "\<theta> y \<cdot> I"]
            reachable_constraints_occurs_fact_ik_funs_terms[
              OF step.hyps(1) welltyped_constraint_model_prefix[OF step.prems(1)] P P_occ]
      by blast
    thus ?thesis using y(2) by simp
  qed (simp add: step.IH[OF welltyped_constraint_model_prefix[OF step.prems(1)]] step.prems(2))
qed simp

lemma reachable_constraints_occurs_fact_deduct_in_ik:
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model I A"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and k: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> occurs k"
  shows "occurs k \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
    and "occurs k \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
using reachable_constraints_occurs_fact_ik_funs_terms(1-3)[OF \<A>_reach \<I> P P_occ]
      reachable_constraints_occurs_fact_ik_subst[OF \<A>_reach \<I> P P_occ]
      deduct_occurs_in_ik[OF k]
by (presburger, presburger)

lemma reachable_constraints_fv_bvars_subset:
  assumes A: "A \<in> reachable_constraints P"
  shows "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<subseteq> (\<Union>T \<in> set P. bvars_transaction T)"
using assms
proof (induction A rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  let ?T' = "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  show ?case
    using step.IH step.hyps(2)
          bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of ?T']
          bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
          bvars\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?T')"]
          unlabel_append[of \<A> "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?T'"]
    by (metis (no_types, lifting) SUP_upper Un_subset_iff)
qed simp

lemma reachable_constraints_fv_disj:
  fixes A::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes A: "A \<in> reachable_constraints P"
  shows "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<inter> (\<Union>T \<in> set P. bvars_transaction T) = {}"
using A
proof (induction A rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  define T' where "T' \<equiv> transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" 
  define X where "X \<equiv> \<Union>T \<in> set P. bvars_transaction T"
  have "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<inter> X = {}"
    using transaction_decl_fresh_renaming_substs_vars_disj(4)[OF step.hyps(3-5)]
          transaction_decl_fresh_renaming_substs_vars_subset(4)[OF step.hyps(3-5,2)]
    unfolding T'_def X_def by blast
  hence "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T') \<inter> X = {}"
    using step.IH[unfolded X_def[symmetric]] fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of T'] by auto
  thus ?case unfolding T'_def X_def by blast
qed simp

(* TODO: this lemma subsumes reachable_constraints_fv_bvars_disj *)
lemma reachable_constraints_fv_bvars_disj':
  fixes A::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes P: "\<forall>T \<in> set P. wellformed_transaction T"
    and A: "A \<in> reachable_constraints P"
  shows "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = {}"
using A
proof (induction A rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  note 0 = transaction_decl_fresh_renaming_substs_vars_disj[OF step.hyps(3-5)]
  note 1 = transaction_decl_fresh_renaming_substs_vars_subset[OF step.hyps(3-5)]

  have 2: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = {}" 
    using 0(7) 1(4)[OF step.hyps(2)] fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq
    unfolding T'_def by (metis (no_types) disjoint_iff_not_equal subset_iff)

  have "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> \<Union>(bvars_transaction ` set P)"
       "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> \<Union>(bvars_transaction ` set P) = {}"
    using reachable_constraints_fv_bvars_subset[OF reachable_constraints.step[OF step.hyps]]
          reachable_constraints_fv_disj[OF reachable_constraints.step[OF step.hyps]]
    unfolding T'_def by auto
  hence 3: "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = {}" by blast
  
  have "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<inter> bvars_transaction T = {}"
    using 0(4)[OF step.hyps(2)] 1(4)[OF step.hyps(2)] by blast
  hence 4: "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = {}"
    by (metis (no_types) T'_def fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq
              unlabel_subst bvars\<^sub>s\<^sub>s\<^sub>t_subst)

  have "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') = {}"
    using 2 3 4 step.IH
    unfolding unlabel_append[of \<A> T']
              fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel T'"]
              bvars\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel T'"]
    by fast
  thus ?case unfolding T'_def by blast
qed simp

lemma reachable_constraints_wf:
  assumes P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
    and A: "A \<in> reachable_constraints P"
  shows "wf\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
proof -
  let ?X = "\<lambda>T. fst ` set (transaction_decl T ()) \<union> set (transaction_fresh T)"

  have "wellformed_transaction T"
    when "T \<in> set P" for T
    using P(1) that by fast+
  hence 0: "wf'\<^sub>s\<^sub>s\<^sub>t (?X T) (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)))"
           "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)) \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)) = {}"
           "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms_transaction T)"
    when T: "T \<in> set P" for T
    unfolding admissible_transaction_terms_def
    by (metis T wellformed_transaction_wf\<^sub>s\<^sub>s\<^sub>t(1),
        metis T wellformed_transaction_wf\<^sub>s\<^sub>s\<^sub>t(2) fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq,
        metis T wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code P(2))

  from A have "wf\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  proof (induction A rule: reachable_constraints.induct)
    case (step A T \<xi> \<sigma> \<alpha>)
    let ?T' = "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

    have IH: "wf'\<^sub>s\<^sub>s\<^sub>t {} (unlabel A)" "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = {}" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
      using step.IH by metis+

    have 1: "wf'\<^sub>s\<^sub>s\<^sub>t {} (unlabel (A@?T'))"
      using transaction_decl_fresh_renaming_substs_wf_sst[OF 0(1)[OF step.hyps(2)] step.hyps(3-5)]
            wf\<^sub>s\<^sub>s\<^sub>t_vars_mono[of "{}"] wf\<^sub>s\<^sub>s\<^sub>t_append[OF IH(1)]
      by simp

    have 2: "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@?T') \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@?T') = {}"
      using reachable_constraints_fv_bvars_disj'[OF P(1)]
            reachable_constraints.step[OF step.hyps]
      by blast

    have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?T')"
      using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq unlabel_subst
            wf_trms_subst[
              OF transaction_decl_fresh_renaming_substs_range_wf_trms[OF step.hyps(3-5)],
              THEN wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_trms\<^sub>s\<^sub>s\<^sub>t_subst,
              OF 0(3)[OF step.hyps(2)]]
      by metis
    hence 3: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@?T'))"
      using IH(3) by auto

    show ?case using 1 2 3 by force
  qed simp
  thus "wf\<^sub>s\<^sub>s\<^sub>t (unlabel A)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" by metis+
qed

lemma reachable_constraints_no_Ana_attack:
  assumes \<A>: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. wellformed_transaction T"
           "\<forall>T \<in> set P. admissible_transaction_terms T"
           "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T).
              \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    and t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "attack\<langle>n\<rangle> \<notin> set (snd (Ana t))"
proof -
  have T_adm_term: "admissible_transaction_terms T" when "T \<in> set P" for T
    using P that by blast

  have T_wf: "wellformed_transaction T" when "T \<in> set P" for T
    using P that by blast

  have T_fresh: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    when "T \<in> set P" for T
    using P(3) that by fast

  show ?thesis
  using \<A> t
  proof (induction \<A> rule: reachable_constraints.induct)
    case (step A T \<xi> \<sigma> \<alpha>) thus ?case
    proof (cases "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)")
      case False
      hence "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)))"
        using step.prems by simp
      hence "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
        using dual_transaction_ik_is_transaction_send'[OF T_wf[OF step.hyps(2)]]
        by metis
      hence "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
        using transaction_decl_fresh_renaming_substs_trms[
                OF step.hyps(3-5), of "transaction_send T"]
              wellformed_transaction_unlabel_cases(4)[OF T_wf[OF step.hyps(2)]]
        by fastforce
      then obtain s where s: "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))" "t = s \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
        by moura
      hence s': "attack\<langle>n\<rangle> \<notin> set (snd (Ana s))"
        using admissible_transaction_no_Ana_Attack[OF T_adm_term[OF step.hyps(2)]]
              trms_transaction_unfold[of T]
        by blast

      note * = transaction_decl_fresh_renaming_substs_range'(1-3)[OF step.hyps(3-5)]
               transaction_decl_fresh_renaming_substs_range_no_attack_const[
                 OF step.hyps(3-5) T_fresh[OF step.hyps(2)]]

      show ?thesis
      proof
        assume n: "attack\<langle>n\<rangle> \<in> set (snd (Ana t))"
        thus False
        proof (cases s)
          case (Var x)
          hence "(\<exists>c. t = Fun c []) \<or> (\<exists>y. t = Var y)"
            using *(1)[of t] n s(2) by (force simp del: subst_subst_compose)
          thus ?thesis using n Ana_subterm' by fastforce
        next
          case (Fun f S)
          hence "attack\<langle>n\<rangle> \<in> set (snd (Ana s)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
            using Ana_subst'[of f S _ "snd (Ana s)" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] s(2) s' n
            by (cases "Ana s") auto
          hence "attack\<langle>n\<rangle> \<in> set (snd (Ana s)) \<or> attack\<langle>n\<rangle> \<in> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
            using const_mem_subst_cases' by fast
          thus ?thesis using *(4) s' by fast
        qed
      qed
    qed simp
  qed simp
qed

lemma reachable_constraints_receive_attack_if_attack:
  assumes \<A>: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. wellformed_transaction T"
           "\<forall>T \<in> set P. admissible_transaction_terms T"
           "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T).
              \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
           "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. \<not>TAtom AttackType \<sqsubseteq> \<Gamma>\<^sub>v x"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and l: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> attack\<langle>l\<rangle>"
  shows "attack\<langle>l\<rangle> \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    and "receive\<langle>[attack\<langle>l\<rangle>]\<rangle> \<in> set (unlabel \<A>)"
    and "\<forall>T \<in> set P. \<forall>s \<in> set (transaction_strand T).
              is_Send (snd s) \<and> length (the_msgs (snd s)) = 1 \<and>
              is_Fun_Attack (hd (the_msgs (snd s)))
              \<longrightarrow> the_Attack_label (the_Fun (hd (the_msgs (snd s)))) = fst s
         \<Longrightarrow> (l,receive\<langle>[attack\<langle>l\<rangle>]\<rangle>) \<in> set \<A>" (is "?Q \<Longrightarrow> (l,receive\<langle>[attack\<langle>l\<rangle>]\<rangle>) \<in> set \<A>")
proof -
  have \<I>': "constr_sem_stateful \<I> (unlabel \<A>)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
           "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    using \<I> unfolding welltyped_constraint_model_def constraint_model_def by metis+

  have 0: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
    when \<A>: "\<A> \<in> reachable_constraints P" for \<A>
    using reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s[OF _ \<A>] admissible_transaction_terms_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(2)
          ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset[of "unlabel \<A>"] wf_trms_subst[OF \<I>'(3)]
    by fast

  have 1: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>). \<not>TAtom AttackType \<sqsubseteq> \<Gamma>\<^sub>v x"
    when \<A>: "\<A> \<in> reachable_constraints P" for \<A>
    using reachable_constraints_vars_not_attack_typed[OF \<A> P(3,4)]
          fv_ik_subset_vars_sst'[of "unlabel \<A>"]
    by fast

  have 2: "attack\<langle>l\<rangle> \<notin> set (snd (Ana t)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" when t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" for t
  proof
    assume "attack\<langle>l\<rangle> \<in> set (snd (Ana t)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    then obtain s where s: "s \<in> set (snd (Ana t))" "s \<cdot> \<I> = attack\<langle>l\<rangle>" by moura

    obtain x where x: "s = Var x"
      by (cases s) (use s reachable_constraints_no_Ana_attack[OF \<A> P(1-3) t] in auto)

    have "x \<in> fv t" using x Ana_subterm'[OF s(1)] vars_iff_subtermeq by force
    hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" using t fv_subterms by fastforce
    hence "\<Gamma>\<^sub>v x \<noteq> TAtom AttackType" using 1[OF \<A>] by fastforce
    thus False using s(2) x wt_subst_trm''[OF \<I>'(4), of "Var x"] by fastforce
  qed

  have 3: "attack\<langle>l\<rangle> \<notin> set (snd (Ana t))" when t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)" for t
  proof
    assume "attack\<langle>l\<rangle> \<in> set (snd (Ana t))"
    then obtain s where s:
        "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<I> ` fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))" "attack\<langle>l\<rangle> \<in> set (snd (Ana s))"
      using Ana_subst_subterms_cases[OF t] 2 by fast
    then obtain x where x: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" "s \<sqsubseteq> \<I> x" by moura
    hence "\<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
      using var_is_subterm[of x] subterms_subst_subset'[of \<I> "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"]
      by force
    hence *: "wf\<^sub>t\<^sub>r\<^sub>m (\<I> x)" "wf\<^sub>t\<^sub>r\<^sub>m s"
      using wf_trms_subterms[OF 0[OF \<A>]] wf_trm_subtermeq[OF _ x(2)]
      by auto

    show False
      using term.order_trans[
              OF subtermeq_imp_subtermtypeeq[OF *(2) Ana_subterm'[OF s(2)]]
                 subtermeq_imp_subtermtypeeq[OF *(1) x(2)]]
            1[OF \<A>] x(1) wt_subst_trm''[OF \<I>'(4), of "Var x"]
      by force
  qed

  have 4: "t = attack\<langle>n\<rangle>"
    when t: "t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = attack\<langle>n\<rangle>"
      and hyps: "transaction_decl_subst \<xi> T"
                "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
                "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      and T: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    for t n
      and T::"('fun, 'atom, 'sets, 'lbl) prot_transaction"
      and \<xi> \<sigma> \<alpha>::"('fun, 'atom, 'sets, 'lbl) prot_subst"
      and \<A>::"('fun, 'atom, 'sets, 'lbl) prot_strand"
  proof (cases t)
    case (Var x)
    hence "attack\<langle>n\<rangle> \<in> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      by (metis (no_types, lifting) t eval_term.simps(1) subst_imgI term.distinct(1))  
    thus ?thesis
      using transaction_decl_fresh_renaming_substs_range_no_attack_const[OF hyps T]
      by blast
  qed (use t in simp)

  have 5: "\<exists>ts'. ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta> \<and> (l,send\<langle>ts'\<rangle>) \<in> set (transaction_strand T)"
    when ts: "(l,receive\<langle>ts\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    for l ts \<theta> and T::"('fun, 'atom, 'sets, 'lbl) prot_transaction"
    using subst_lsst_memD(2)[OF ts[unfolded dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(1)[symmetric]]]
    by auto

  have 6: "l' = l" when "(l',receive\<langle>[attack\<langle>l\<rangle>]\<rangle>) \<in> set \<A>" and Q: "?Q" for l'
    using \<A> that(1)
  proof (induction \<A> rule: reachable_constraints.induct)
    case (step \<A> T \<xi> \<sigma> \<alpha>) show ?case
    proof (cases "(l',receive\<langle>[attack\<langle>l\<rangle>]\<rangle>) \<in> set \<A>")
      case False
      hence *: "(l',receive\<langle>[attack\<langle>l\<rangle>]\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
        using step.prems by simp
      have "(l',send\<langle>[attack\<langle>l\<rangle>]\<rangle>) \<in> set (transaction_strand T)"
        using 4[OF _ step.hyps(3-5)] P(3) step.hyps(2) 5[OF *] by force
      thus ?thesis using Q step.hyps(2) unfolding is_Fun_Attack_def by fastforce
    qed (use step.IH in simp)
  qed simp

  have 7: "\<exists>t. ts = [t] \<and> t = attack\<langle>l\<rangle>"
    when ts: "receive\<langle>ts\<rangle> \<in> set (unlabel \<A>)" "attack\<langle>l\<rangle> \<in> set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" for ts
    using \<A> ts(1)
  proof (induction \<A> rule: reachable_constraints.induct)
    case (step \<A> T \<xi> \<sigma> \<alpha>)
    obtain t where t: "t \<in> set ts" "attack\<langle>l\<rangle> = t \<cdot> \<I>" using ts(2) by blast
    hence t_in_ik: "t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> @ dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      using step.prems(1) in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of t] by blast

    have t_attack_eq: "t = attack\<langle>l\<rangle>"
    proof (cases t)
      case (Var x) 
      hence "TAtom AttackType \<notin> subterms (\<Gamma> t)"
        using t_in_ik 1[OF reachable_constraints.step[OF step.hyps]] by fastforce
      thus ?thesis using t(2) wt_subst_trm''[OF \<I>'(4), of t] by force
    qed (use t(2) in simp)

    show ?case
    proof (cases "receive\<langle>ts\<rangle> \<in> set (unlabel \<A>)")
      case False
      then obtain l' where l':
          "(l', receive\<langle>ts\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
        using step.prems(1) unfolding unlabel_def by force
      then obtain ts' where ts':
          "ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "(l', send\<langle>ts'\<rangle>) \<in> set (transaction_strand T)"
        using 5 by meson
      then obtain t' where t': "t' \<in> set ts'" "t' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = attack\<langle>l\<rangle>"
        using t(1) t_attack_eq by force

      note * = t'(1) 4[OF t'(2) step.hyps(3-5)]

      have "send\<langle>ts'\<rangle> \<in> set (unlabel (transaction_strand T))"
        using ts'(2) step.hyps(2) P(2) unfolding unlabel_def by force
      hence "length ts' = 1"
        using step.hyps(2) P(2,3) * unfolding admissible_transaction_terms_def by fastforce
      hence "ts' = [attack\<langle>l\<rangle>]" using * P(3) step.hyps(2) by (cases ts') auto
      thus ?thesis by (simp add: ts'(1))
    qed (use step.IH in simp)
  qed simp

  show "attack\<langle>l\<rangle> \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    using private_const_deduct[OF _ l] 3 by simp
  then obtain ts where ts: "receive\<langle>ts\<rangle> \<in> set (unlabel \<A>)" "attack\<langle>l\<rangle> \<in> set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    using in_ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t_iff[of _ \<A>] unfolding unlabel_def by force
  then obtain t where "ts = [t]" "t = attack\<langle>l\<rangle>"
    using 7 by blast
  thus "receive\<langle>[attack\<langle>l\<rangle>]\<rangle> \<in> set (unlabel \<A>)"
    using ts(1) by blast
  hence "\<exists>l'. (l', receive\<langle>[attack\<langle>l\<rangle>]\<rangle>) \<in> set \<A>"
    unfolding unlabel_def by fastforce
  thus "(l,receive\<langle>[attack\<langle>l\<rangle>]\<rangle>) \<in> set \<A>" when ?Q
    using that 6 by fast
qed

lemma reachable_constraints_receive_attack_if_attack':
  assumes \<A>: "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and n: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> attack\<langle>n\<rangle>"
  shows "attack\<langle>n\<rangle> \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    and "receive\<langle>[attack\<langle>n\<rangle>]\<rangle> \<in> set (unlabel \<A>)"
proof -
  have P': "\<forall>T \<in> set P. wellformed_transaction T"
           "\<forall>T \<in> set P. admissible_transaction_terms T"
           "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
           "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. \<not>TAtom AttackType \<sqsubseteq> \<Gamma>\<^sub>v x"
    using admissible_transaction_is_wellformed_transaction(1,4)[OF bspec[OF P]]
          admissible_transactionE(2,15)[OF bspec[OF P]]
    by (blast, blast, blast, blast)

  show "attack\<langle>n\<rangle> \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "receive\<langle>[attack\<langle>n\<rangle>]\<rangle> \<in> set (unlabel \<A>)"
    using reachable_constraints_receive_attack_if_attack(1,2)[OF \<A> P'(1,2) _ P'(4) \<I> n] P'(3)
    by (metis, metis)
qed

lemma constraint_model_Value_term_is_Val:
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model I A"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and x: "\<Gamma>\<^sub>v x = TAtom Value" "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  shows "\<exists>n. I x = Fun (Val n) []"
using reachable_constraints_occurs_fact_send_ex[OF \<A>_reach P P_occ x]
      reachable_constraints_occurs_fact_send_in_ik[OF \<A>_reach \<I> P P_occ]
      reachable_constraints_occurs_fact_ik_case[OF \<A>_reach P P_occ]
by fast

lemma constraint_model_Value_term_is_Val':
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model I A"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and x: "(TAtom Value, m) \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  shows "\<exists>n. I (TAtom Value, m) = Fun (Val n) []"
using constraint_model_Value_term_is_Val[OF \<A>_reach \<I> P P_occ _ x] by simp

(* We use this lemma to show that fresh constants first occur in \<I>(\<A>) at the point where they were generated *)
lemma constraint_model_Value_var_in_constr_prefix:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
  shows "\<forall>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow> (\<exists>B. prefix B \<A> \<and> x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<and> \<I> x \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
    (is "\<forall>x \<in> ?X \<A>. ?R x \<longrightarrow> ?Q x \<A>")
using \<A>_reach \<I>
proof (induction \<A> rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  let ?P = "\<lambda>\<A>. \<forall>x \<in> ?X \<A>. ?R x \<longrightarrow> ?Q x \<A>"

  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  have IH: "?P \<A>" using step welltyped_constraint_model_prefix by fast

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF bspec[OF P step.hyps(2)] step.hyps(3)]

  have T_adm: "admissible_transaction' T" by (metis P step.hyps(2))

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  have \<I>_is_T_model: "strand_sem_stateful (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) (set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)) (unlabel T') \<I>"
    using step.prems unlabel_append[of \<A> T'] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>" \<I> "[]"]
          strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" "unlabel T'" \<I>]
    by (simp add: T'_def welltyped_constraint_model_def constraint_model_def db\<^sub>s\<^sub>s\<^sub>t_def)

  have \<I>_interp: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
    by (metis \<I> welltyped_constraint_model_def constraint_model_def,
        metis \<I> welltyped_constraint_model_def,
        metis \<I> welltyped_constraint_model_def constraint_model_def)

  have 1: "?Q x \<A>" when x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'" "\<Gamma>\<^sub>v x = TAtom Value" for x
  proof -
    obtain n where n: "\<I> x = Fun n []" "is_Val n" "\<not>public n"
      using constraint_model_Value_term_is_Val[
              OF reachable_constraints.step[OF step.hyps] step.prems P P_occ x(2)]
            x(1) fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel T'"] unlabel_append[of \<A> T']
      unfolding T'_def by moura

    have "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      using x(1) fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq unfolding T'_def by fastforce
    then obtain y where y: "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)" "x \<in> fv ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y)"
      using fv\<^sub>s\<^sub>s\<^sub>t_subst_obtain_var[of x "unlabel (transaction_strand T)" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
      by auto

    have y_x: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y = Var x" and y_not_fresh: "y \<notin> set (transaction_fresh T)"
      using y(2) transaction_decl_fresh_renaming_substs_range[OF step.hyps(3-5), of y]
      by (force, fastforce)

    have "\<Gamma> ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y) = TAtom Value" using x(2) y_x by simp
    moreover have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      by (rule transaction_decl_fresh_renaming_substs_wt[OF step.hyps(3-5)])
    ultimately have y_val: "\<Gamma>\<^sub>v y = TAtom Value"
      by (metis wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def \<Gamma>.simps(1))

    have "Fun n [] = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>" using n y_x by simp
    hence y_n: "Fun n [] = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>) y"
      by (metis subst_subst_compose[of "Var y" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" \<I>] eval_term.simps(1))

    have \<A>_ik_\<I>_vals: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>). \<exists>f. \<I> x = Fun f []"
    proof -
      have "\<exists>a. \<Gamma> (\<I> x) = Var a" when "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" for x
        using that reachable_constraints_vars_TAtom_typed[OF step.hyps(1) P, of x]
              vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"] wt_subst_trm''[OF \<I>_wt, of "Var x"]
        by force
      hence "\<exists>f. \<I> x = Fun f []" when "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" for x
        using that wf_trm_subst[OF \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s, of "Var x"] wf_trm_Var[of x] const_type_inv_wf
              empty_fv_exists_fun[OF interpretation_grounds[OF \<I>_interp], of "Var x"] 
        by (metis eval_term.simps(1)[of _ x \<I>])
      thus ?thesis
        using fv_ik_subset_fv_sst'[of "unlabel \<A>"] vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"]
        by blast
    qed
    hence \<A>_subterms_subst_cong: "subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) = subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      by (metis ik\<^sub>s\<^sub>s\<^sub>t_subst[of "unlabel \<A>" \<I>] unlabel_subst[of \<A> \<I>] subterms_subst_lsst_ik[of \<A> \<I>])

    have x_nin_\<A>: "x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
    proof -
      have "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
        using x(1) fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq unfolding T'_def by fast
      hence "x \<in> fv\<^sub>s\<^sub>s\<^sub>t ((unlabel (transaction_strand T) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>)"
        using transaction_fresh_subst_grounds_domain[OF step.hyps(4)] step.hyps(4)
              labeled_stateful_strand_subst_comp[of \<sigma> "transaction_strand T" \<alpha>]
              unlabel_subst[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>" \<alpha>]
              unlabel_subst[of "transaction_strand T" \<sigma>]
        by (simp add: \<xi>_empty transaction_fresh_subst_def range_vars_alt_def)
      then obtain y where "\<alpha> y = Var x"
        using transaction_renaming_subst_var_obtain(1)[OF step.hyps(5)] by blast
      thus ?thesis
        using transaction_renaming_subst_range_notin_vars[OF step.hyps(5), of y]
              vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"]
        by auto
    qed

    from admissible_transaction_fv_in_receives_or_selects[OF T_adm y(1) y_not_fresh]
    have n_cases: "Fun n [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<or> (\<exists>z \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<Gamma>\<^sub>v z = TAtom Value \<and> \<I> z = Fun n [])"
    proof
      assume y_in: "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
      then obtain ts where ts:
          "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T))" "y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set ts)"
        using admissible_transaction_strand_step_cases(1)[OF T_adm]
        by force
      hence ts_deduct: "list_all (\<lambda>t. ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I>) ts"
        using wellformed_transaction_sem_receives[
                OF T_wf, of "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" \<I> "ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
              \<I>_is_T_model
              subst_lsst_unlabel_member[of "receive\<langle>ts\<rangle>" "transaction_receive T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
        unfolding T'_def list_all_iff by force

      obtain ty where ty: "ty \<in> set ts" "y \<in> fv ty" using ts(2) by fastforce
      
      have "Fun n [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<or> (\<exists>z \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>). \<Gamma>\<^sub>v z = TAtom Value \<and> \<I> z = Fun n [])"
      proof -
        have "Fun n [] \<sqsubseteq> ty \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I>"
          using imageI[of "Var y" "subterms ty" "\<lambda>x. x \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>"]
                var_is_subterm[OF ty(2)] subterms_subst_subset[of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>" ty]
                subst_subst_compose[of ty "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" \<I>] y_n
          by (auto simp del: subst_subst_compose)
        hence "Fun n [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
          using ty(1) private_fun_deduct_in_ik[of _ _ n "[]"] n(2,3) ts_deduct
          unfolding is_Val_def is_Abs_def list_all_iff by fast
        hence "Fun n [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<or> (\<exists>z \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>). \<I> z = Fun n [])"
          using const_subterm_subst_cases[of n _ \<I>] \<A>_ik_\<I>_vals by fastforce
        thus ?thesis
          using \<I>_wt n(2) unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def is_Val_def is_Abs_def by force
      qed
      thus ?thesis
        using fv_ik_subset_fv_sst' ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset[of "unlabel \<A>"] \<A>_subterms_subst_cong
        by fast
    next
      assume y_in: "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<and>
                    (\<exists>t s. select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_checks T)) \<and> y \<in> fv t \<union> fv s)"
      then obtain s where s: "select\<langle>Var y,Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))"
        using admissible_transaction_strand_step_cases(2)[OF T_adm] by force
      hence "select\<langle>(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y, Fun (Set s) []\<rangle> \<in>
              set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
        using subst_lsst_unlabel_member
        by fastforce
      hence n_in_db: "(Fun n [], Fun (Set s) []) \<in> set (db'\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) \<I> [])"
        using wellformed_transaction_sem_pos_checks(1)[
                OF T_wf, of "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" \<I>
                               assign "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y" "Fun (Set s) []"]
              \<I>_is_T_model n y_x
        unfolding T'_def db\<^sub>s\<^sub>s\<^sub>t_def
        by fastforce

      obtain tn sn where tsn: "insert\<langle>tn,sn\<rangle> \<in> set (unlabel \<A>)" "Fun n [] = tn \<cdot> \<I>"
        using db\<^sub>s\<^sub>s\<^sub>t_in_cases[OF n_in_db] by force

      have "Fun n [] = tn \<or> (\<exists>z. \<Gamma>\<^sub>v z = TAtom Value \<and> tn = Var z)"
        using \<I>_wt tsn(2) n(2) unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def is_Val_def is_Abs_def by (cases tn) auto
      moreover have "tn \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" "fv tn \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
        using tsn(1) in_subterms_Union by force+
      ultimately show ?thesis using tsn(2) by auto
    qed

    from n_cases show ?thesis
    proof
      assume "\<exists>z \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<Gamma>\<^sub>v z = TAtom Value \<and> \<I> z = Fun n []"
      then obtain B where B: "prefix B \<A>" "Fun n [] \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
        by (metis IH n(1))
      thus ?thesis
        using n x_nin_\<A> trms\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset(1)[of B]
        by (metis (no_types, opaque_lifting) self_append_conv subset_iff subterms\<^sub>s\<^sub>e\<^sub>t_mono prefix_def)
    qed (use n x_nin_\<A> in fastforce)
  qed

  have "?P (\<A>@T')"
  proof (intro ballI impI)
    fix x assume x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T')" "\<Gamma>\<^sub>v x = TAtom Value"
    show "?Q x (\<A>@T')"
    proof (cases "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>")
      case False
      hence "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'" using x(1) unlabel_append[of \<A>] fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] by simp
      then obtain B where B: "prefix B \<A>" "x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B" "\<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
        using x(2) 1 by moura
      thus ?thesis using prefix_prefix by fast
    qed (use x(2) IH prefix_prefix in fast)
  qed
  thus ?case unfolding T'_def by blast
qed simp

lemma constraint_model_Val_const_in_constr_prefix:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and P: "\<forall>T \<in> set P. wellformed_transaction T"
           "\<forall>T \<in> set P. admissible_transaction_terms T"
    and n: "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
  shows "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
proof -
  have *: "wf\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
          "constr_sem_stateful \<I> (unlabel \<A>)"
          "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
          "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
          "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    using reachable_constraints_wf(1)[OF P(1) _ \<A>_reach]
          admissible_transaction_terms_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s \<I> P(2) n
    unfolding welltyped_constraint_model_def constraint_model_def wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code by fast+

  show ?thesis
    using constraint_model_priv_const_in_constr_prefix[OF * _ _ n]
    by simp
qed

lemma constraint_model_Val_const_in_constr_prefix':
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and n: "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
  shows "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
using constraint_model_Val_const_in_constr_prefix[OF \<A>_reach \<I> _ _ n]
      P admissible_transaction_is_wellformed_transaction(1,4)
by fast

lemma constraint_model_Value_in_constr_prefix_fresh_action':
  fixes P::"('fun, 'atom, 'sets, 'lbl) prot_transaction list"
  assumes A: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction_terms T"
           "\<forall>T \<in> set P. transaction_decl T () = []"
           "\<forall>T \<in> set P. bvars_transaction T = {}"
    and n: "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  obtains B T \<xi> \<sigma> \<alpha> where "prefix (B@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) A"
    and "B \<in> reachable_constraints P" "T \<in> set P" "transaction_decl_subst \<xi> T"
        "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)" "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
    and "Fun (Val n) [] \<in> subst_range \<sigma>"
proof -
  define f where "f \<equiv>
    \<lambda>(T::('fun, 'atom, 'sets, 'lbl) prot_transaction,
      \<xi>::('fun, 'atom, 'sets, 'lbl) prot_subst,
      \<sigma>::('fun, 'atom, 'sets, 'lbl) prot_subst,
      \<alpha>::('fun, 'atom, 'sets, 'lbl) prot_subst).
        dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  define g where "g \<equiv> concat \<circ> map f"

  obtain Ts where Ts:
      "A = g Ts" "\<forall>B. prefix B Ts \<longrightarrow> g B \<in> reachable_constraints P"
      "\<forall>B T \<xi> \<sigma> \<alpha>. prefix (B@[(T,\<xi>,\<sigma>,\<alpha>)]) Ts \<longrightarrow>
                        T \<in> set P \<and> transaction_decl_subst \<xi> T \<and>
                        transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B)) \<and>
                        transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B))"
    using reachable_constraints_as_transaction_lists[OF A] unfolding g_def f_def by blast

  obtain T \<xi> \<sigma> \<alpha> where T:
      "(T, \<xi>, \<sigma>, \<alpha>) \<in> set Ts" "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    using n trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq unlabel_subst
    unfolding Ts(1) g_def f_def unlabel_def trms\<^sub>s\<^sub>s\<^sub>t_def
    by fastforce
  
  obtain B where B:
      "prefix (B@[(T, \<xi>, \<sigma>, \<alpha>)]) Ts" "g B \<in> reachable_constraints P" "T \<in> set P"
      "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B))"
      "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (g B))"
  proof -
    obtain B where "\<exists>C. B@(T, \<xi>, \<sigma>, \<alpha>)#C = Ts" by (metis T(1) split_list)
    thus ?thesis using Ts(2-) that[of B] by auto
  qed

  note T_adm_terms = bspec[OF P(1) B(3)]
  note T_decl_empty = bspec[OF P(2) B(3)]
  note T_no_bvars = bspec[OF P(3) B(3)]
  note \<xi>_empty = admissible_transaction_decl_subst_empty'[OF T_decl_empty B(4)]

  have "trms\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = trms_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
    using trms\<^sub>s\<^sub>s\<^sub>t_subst[of _ "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] T_no_bvars by blast
  hence "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
    by (metis T(2) unlabel_subst)
  hence "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    using admissible_transaction_terms_no_Value_consts(1)[OF T_adm_terms]
          const_subterms_subst_cases'[of "Val n" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "trms_transaction T"]
    by blast
  then obtain tn where tn: "tn \<in> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" "Fun (Val n) [] \<sqsubseteq> tn" "is_Fun tn"
    by fastforce

  have "Fun (Val n) [] \<in> subst_range \<sigma>"
    using tn(1-) transaction_decl_fresh_renaming_substs_range'(2,4)[OF B(4-6) tn(1) \<xi>_empty]
    by fastforce
  moreover have "prefix (g B@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) A"
    using Ts(1) B(1) unfolding g_def f_def prefix_def by fastforce
  ultimately show thesis using that B(2-) by blast
qed

lemma constraint_model_Value_in_constr_prefix_fresh_action:
  fixes P::"('fun, 'atom, 'sets, 'lbl) prot_transaction list"
  assumes A: "A \<in> reachable_constraints P"
    and P_adm: "\<forall>T \<in> set P. admissible_transaction' T"
    and n: "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  obtains B T \<xi> \<sigma> \<alpha> where "prefix (B@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) A"
    and "B \<in> reachable_constraints P" "T \<in> set P" "transaction_decl_subst \<xi> T"
        "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)" "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
    and "Fun (Val n) [] \<in> subst_range \<sigma>"
proof -
  have P: "\<forall>T \<in> set P. admissible_transaction_terms T"
          "\<forall>T \<in> set P. transaction_decl T () = []"
          "\<forall>T \<in> set P. bvars_transaction T = {}"
  using P_adm admissible_transactionE(1) admissible_transaction_no_bvars(2)
        admissible_transaction_is_wellformed_transaction(4)
  by (blast,blast,blast)

  show ?thesis using that constraint_model_Value_in_constr_prefix_fresh_action'[OF A P n] by blast
qed

lemma reachable_constraints_occurs_fact_ik_case':
  fixes A::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and val: "Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  shows "occurs (Fun (Val n) []) \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof -
  obtain B T \<xi> \<sigma> \<alpha> where B:
      "prefix (B@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) A"
      "B \<in> reachable_constraints P"
      "T \<in> set P"
      "transaction_decl_subst \<xi> T"
      "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      "Fun (Val n) [] \<in> subst_range \<sigma>"
    using constraint_model_Value_in_constr_prefix_fresh_action[OF \<A>_reach P val]
    by blast

  define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  have T_adm: "admissible_transaction' T" using P B(3) by blast
  hence T_wf: "wellformed_transaction T" "admissible_transaction_occurs_checks T"
    using admissible_transaction_is_wellformed_transaction(1) bspec[OF P_occ B(3)] by (blast,blast)

  obtain x where x: "x \<in> set (transaction_fresh T)" "\<theta> x = Fun (Val n) []"
    using transaction_fresh_subst_domain[OF B(5)] B(7)
          admissible_transaction_decl_subst_empty[OF T_adm B(4)]
    by (force simp add: subst_compose \<theta>_def)

  obtain ts where ts: "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))" "occurs (Var x) \<in> set ts"
    using admissible_transaction_occurs_checksE2[OF T_wf(2) x(1)]
    by (metis (mono_tags, lifting) list.set_intros(1) unlabel_Cons(1))

  have "occurs (Var x) \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
    using ts by force
  hence "occurs (Var x) \<cdot> \<theta> \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    using dual_transaction_ik_is_transaction_send'[OF T_wf(1), of \<theta>] by fast
  hence "occurs (Fun (Val n) []) \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    using x(2) by simp
  thus ?thesis
    using B(1)[unfolded \<theta>_def[symmetric]]
          unlabel_append[of B "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"]
          ik\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel B" "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"]
    unfolding prefix_def by force
qed

lemma reachable_constraints_occurs_fact_ik_case'':
  fixes A::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "A \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> A"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and val: "Fun (Val n) [] \<sqsubseteq> t" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t"
  shows "occurs (Fun (Val n) []) \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof -
  obtain f ts where t: "t = Fun f ts" using val(1) by (cases t) simp_all

  show ?thesis
    using private_fun_deduct_in_ik[OF val(2,1)[unfolded t]]
          constraint_model_Val_const_in_constr_prefix'[OF \<A>_reach \<I> P, of n]
          reachable_constraints_occurs_fact_ik_case'[OF \<A>_reach P P_occ, of n]
    by fastforce
qed

lemma admissible_transaction_occurs_checks_prop:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and f: "f \<in> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
  shows "\<not>is_PubConstValue f"
    and "\<not>is_Abs f"
proof -
  obtain x where x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" "f \<in> funs_term (\<I> x)" using f by moura
  obtain T where T: "Fun f T \<sqsubseteq> \<I> x" using funs_term_Fun_subterm[OF x(2)] by moura

  have \<I>_interp: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
    by (metis \<I> welltyped_constraint_model_def constraint_model_def,
        metis \<I> welltyped_constraint_model_def,
        metis \<I> welltyped_constraint_model_def constraint_model_def)

  note 0 = x(1) reachable_constraints_vars_TAtom_typed[OF \<A>_reach P, of x] 
           vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"]

  have 1: "\<Gamma> (Var x) = \<Gamma> (\<I> x)" using wt_subst_trm''[OF \<I>_wt, of "Var x"] by simp
  hence "\<exists>a. \<Gamma> (\<I> x) = Var a" using 0 by force
  hence "\<exists>f. \<I> x = Fun f []"
    using x(1) wf_trm_subst[OF \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s, of "Var x"] wf_trm_Var[of x] const_type_inv_wf
          empty_fv_exists_fun[OF interpretation_grounds[OF \<I>_interp], of "Var x"] 
    by (metis eval_term.simps(1)[of _ x \<I>])
  hence 2: "\<I> x = Fun f []" using x(2) by force

  have 3: "\<Gamma>\<^sub>v x \<noteq> TAtom AbsValue" using 0 by force

  have "\<not>is_PubConstValue f \<and> \<not>is_Abs f"
  proof (cases "\<Gamma>\<^sub>v x = TAtom Value")
    case True
    then obtain B where B: "prefix B \<A>" "x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B" "\<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      using constraint_model_Value_var_in_constr_prefix[OF \<A>_reach \<I> P P_occ] x(1)
      by fast
  
    have "\<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      using B(1,3) trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel B"] unlabel_append[of B]
      unfolding prefix_def by auto
    hence "f \<in> \<Union>(funs_term ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      using x(2) funs_term_subterms_eq(2)[of "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"] by blast
    thus ?thesis
      using reachable_constraints_val_funs_private[OF \<A>_reach P]
      by blast+
  next
    case False thus ?thesis using x 1 2 3 unfolding is_PubConstValue_def by (cases f) auto
  qed
  thus "\<not>is_PubConstValue f" "\<not>is_Abs f" by metis+
qed

lemma admissible_transaction_occurs_checks_prop':
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and f: "f \<in> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
  shows "\<nexists>n. f = PubConst Value n"
    and "\<nexists>n. f = Abs n"
using admissible_transaction_occurs_checks_prop[OF \<A>_reach \<I> P P_occ f]
unfolding is_PubConstValue_def by auto

lemma transaction_var_becomes_Val:
  assumes \<A>_reach: "\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and \<alpha>: "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and P_occ: "\<forall>T \<in> set P. admissible_transaction_occurs_checks T"
    and T: "T \<in> set P"
    and x: "x \<in> fv_transaction T" "fst x = TAtom Value"
  shows "\<exists>n. Fun (Val n) [] = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I>"
proof -
  obtain m where m: "x = (TAtom Value, m)" by (metis x(2) eq_fst_iff)

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF bspec[OF P T] \<xi>]

  have x_not_bvar: "x \<notin> bvars_transaction T" "fv ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x) \<inter> bvars_transaction T = {}"
    using x(1) admissible_transactions_fv_bvars_disj[OF P] T
          transaction_decl_fresh_renaming_substs_vars_disj(2)[OF \<xi> \<sigma> \<alpha>, of x]
          vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
    by (blast, blast)

  have \<sigma>x_type: "\<Gamma> (\<sigma> x) = TAtom Value"
    using \<sigma> x \<Gamma>\<^sub>v_TAtom''(2)[of x] wt_subst_trm''[of \<sigma> "Var x"]
    unfolding transaction_fresh_subst_def by simp

  show ?thesis
  proof (cases "x \<in> subst_domain \<sigma>")
    case True
    then obtain c where c: "\<sigma> x = Fun c []" "\<not>public c" "arity c = 0"
      using \<sigma> unfolding transaction_fresh_subst_def by fastforce
    then obtain n where n: "c = Val n" using \<sigma>x_type by (cases c) (auto split: option.splits)
    show ?thesis using c n subst_compose[of \<sigma> \<alpha> x] \<xi>_empty by simp
  next
    case False
    hence "\<sigma> x = Var x" by auto
    then obtain n where n: "(\<sigma> \<circ>\<^sub>s \<alpha>) x = Var (TAtom Value, n)"
      using m transaction_renaming_subst_is_renaming(1)[OF \<alpha>] subst_compose[of \<sigma> \<alpha> x]
      by force
    hence "(TAtom Value, n) \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      using x_not_bvar fv\<^sub>s\<^sub>s\<^sub>t_subst_fv_subset[OF x(1), of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] \<xi>_empty
      by force
    hence "\<exists>n'. \<I> (TAtom Value, n) = Fun (Val n') []"
      using constraint_model_Value_term_is_Val'[OF \<A>_reach \<I> P P_occ, of n] x
            fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] unlabel_append[of \<A>]
      by fastforce
    thus ?thesis using n \<xi>_empty by simp
  qed
qed

lemma reachable_constraints_SMP_subset:
  assumes \<A>: "\<A> \<in> reachable_constraints P"
  shows "SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<subseteq> SMP (\<Union>T \<in> set P. trms_transaction T)" (is "?A \<A>")
    and "SMP (pair`setops\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)) \<subseteq> SMP (\<Union>T\<in>set P. pair`setops_transaction T)" (is "?B \<A>")
proof -
  have "?A \<A> \<and> ?B \<A>" using \<A>
  proof (induction \<A> rule: reachable_constraints.induct)
    case (step A T \<xi> \<sigma> \<alpha>)
    define T' where "T' \<equiv> transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
    define M where "M \<equiv> \<Union>T \<in> set P. trms_transaction T"
    define N where "N \<equiv> \<Union>T \<in> set P. pair ` setops_transaction T"
  
    let ?P = "\<lambda>t. \<exists>s \<delta>. s \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = s \<cdot> \<delta>"
    let ?Q = "\<lambda>t. \<exists>s \<delta>. s \<in> N \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = s \<cdot> \<delta>"
  
    have IH: "SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<subseteq> SMP M" "SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)) \<subseteq> SMP N"
      using step.IH by (metis M_def, metis N_def)
  
    note \<xi>\<sigma>\<alpha>_wt = transaction_decl_fresh_renaming_substs_wt[OF step.hyps(3-5)]
    note \<xi>\<sigma>\<alpha>_wf = transaction_decl_fresh_renaming_substs_range_wf_trms[OF step.hyps(3-5)]

    have 0: "SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')) = SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<union> SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"
            "SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'))) =
              SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)) \<union> SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel T'))"
      using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of T']
            setops\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of T']
            trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel A" "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"]
            setops\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel A" "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"]
            unlabel_append[of A "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'"]
            image_Un[of pair "setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)" "setops\<^sub>s\<^sub>s\<^sub>t (unlabel T')"]
            SMP_union[of "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'"]
            SMP_union[of "pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)" "pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel T')"]
      by argo+
  
    have 1: "SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T') \<subseteq> SMP M"
    proof (intro SMP_subset_I ballI)
      fix t show "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<Longrightarrow> ?P t"
        using trms\<^sub>s\<^sub>s\<^sub>t_wt_subst_ex[OF \<xi>\<sigma>\<alpha>_wt \<xi>\<sigma>\<alpha>_wf, of t "unlabel (transaction_strand T)"]
              unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] step.hyps(2)
        unfolding T'_def M_def by auto
    qed
  
    have 2: "SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel T')) \<subseteq> SMP N"
    proof (intro SMP_subset_I ballI)
      fix t show "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel T') \<Longrightarrow> ?Q t"
        using setops\<^sub>s\<^sub>s\<^sub>t_wt_subst_ex[OF \<xi>\<sigma>\<alpha>_wt \<xi>\<sigma>\<alpha>_wf, of t "unlabel (transaction_strand T)"]
              unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] step.hyps(2)
        unfolding T'_def N_def by auto
    qed
  
    have "SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')) \<subseteq> SMP M"
         "SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'))) \<subseteq> SMP N"
      using 0 1 2 IH by blast+
    thus ?case unfolding T'_def M_def N_def by blast
  qed (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  thus "?A \<A>" "?B \<A>" by metis+
qed

lemma reachable_constraints_no_Pair_fun':
  assumes A: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
           "\<forall>T \<in> set P. transaction_decl T () = []"
           "\<forall>T \<in> set P. admissible_transaction_terms T"
           "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
  shows "Pair \<notin> \<Union>(funs_term ` SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
using A
proof (induction A rule: reachable_constraints.induct)
  case (step A T \<xi> \<sigma> \<alpha>)
  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  note T_fresh_type = bspec[OF P(1) step.hyps(2)]

  note \<xi>_empty =
    admissible_transaction_decl_subst_empty'[OF bspec[OF P(2) step.hyps(2)] step.hyps(3)]

  note T_adm_terms = bspec[OF P(3) step.hyps(2)]

  note \<xi>\<sigma>\<alpha>_wt = transaction_decl_fresh_renaming_substs_wt[OF step.hyps(3-5)]
  note \<xi>\<sigma>\<alpha>_wf = transaction_decl_fresh_renaming_substs_range_wf_trms[OF step.hyps(3-5)]

  have 0: "SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@T')) = SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<union> SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"
    using SMP_union[of "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'"]
          unlabel_append[of A T'] trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel A" "unlabel T'"]
    by simp

  have 1: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"
    using reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s[OF _ reachable_constraints.step[OF step.hyps]]
          admissible_transaction_terms_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(3)
          trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel A"] unlabel_append[of A]
    unfolding T'_def by force

  have 2: "Pair \<notin> \<Union>(funs_term ` (subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)))"
    using transaction_decl_fresh_renaming_substs_range'(3)[
            OF step.hyps(3-5) _ \<xi>_empty T_fresh_type]
    by force

  have "Pair \<notin> \<Union>(funs_term ` (trms_transaction T))"
    using T_adm_terms unfolding admissible_transaction_terms_def by blast
  hence "Pair \<notin> funs_term t"
    when t: "t \<in> trms\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" for t
    using 2 trms\<^sub>s\<^sub>s\<^sub>t_funs_term_cases[OF t]
    by force
  hence 3: "Pair \<notin> funs_term t" when t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'" for t
    using t unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
          trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
    unfolding T'_def by metis

  have "\<exists>a. \<Gamma>\<^sub>v x = TAtom a" when "x \<in> vars_transaction T" for x
    using that protocol_transaction_vars_TAtom_typed(1) bspec[OF P(4) step.hyps(2)]
    by fast
  hence "\<exists>a. \<Gamma>\<^sub>v x = TAtom a" when "x \<in> vars\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" for x
    using wt_subst_fv\<^sub>s\<^sub>e\<^sub>t_termtype_subterm[OF _ \<xi>\<sigma>\<alpha>_wt \<xi>\<sigma>\<alpha>_wf, of x "vars_transaction T"]
          vars\<^sub>s\<^sub>s\<^sub>t_subst_cases[OF that]
    by fastforce
  hence "\<exists>a. \<Gamma>\<^sub>v x = TAtom a" when "x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'" for x
    using that unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
          vars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
    unfolding T'_def
    by simp
  hence "\<exists>a. \<Gamma>\<^sub>v x = TAtom a" when "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')" for x
    using that fv_trms\<^sub>s\<^sub>s\<^sub>t_subset(1) by fast
  hence "Pair \<notin> funs_term (\<Gamma> (Var x))" when "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')" for x
    using that by fastforce
  moreover have "Pair \<in> funs_term s"
    when s: "Ana s = (K, M)" "Pair \<in> \<Union>(funs_term ` set K)"
    for s::"('fun,'atom,'sets,'lbl) prot_term" and K M
  proof (cases s)
    case (Fun f S) thus ?thesis using s Ana_Fu_keys_not_pairs[of _ S K M] by (cases f) force+
  qed (use s in simp)
  ultimately have "Pair \<notin> funs_term t" when t: "t \<in> SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')" for t
    using t 3 SMP_funs_term[OF t _ _ 1, of Pair] funs_term_type_iff by fastforce
  thus ?case using 0 step.IH(1) unfolding T'_def by blast
qed simp

lemma reachable_constraints_no_Pair_fun:
  assumes A: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
  shows "Pair \<notin> \<Union>(funs_term ` SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
using reachable_constraints_no_Pair_fun'[OF A]
      P admissible_transactionE(1,2,3)
      admissible_transaction_is_wellformed_transaction(4)
by blast

lemma reachable_constraints_setops_form:
  assumes A: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and t: "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
  shows "\<exists>c s. t = pair (c, Fun (Set s) []) \<and> \<Gamma> c = TAtom Value"
using A t
proof (induction A rule: reachable_constraints.induct)
  case (step A T \<xi> \<sigma> \<alpha>) 

  have T_adm: "admissible_transaction' T" when "T \<in> set P" for T
    using P that unfolding list_all_iff by simp

  note T_adm' = admissible_transaction_is_wellformed_transaction(2,3)[OF T_adm]
  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  note \<xi>\<sigma>\<alpha>_wt = transaction_decl_fresh_renaming_substs_wt[OF step.hyps(3-5)]
  note \<xi>\<sigma>\<alpha>_wf = transaction_decl_fresh_renaming_substs_range_wf_trms[OF step.hyps(3-5)]
  
  show ?case using step.IH
  proof (cases "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)")
    case False
    hence "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      using step.prems setops\<^sub>s\<^sub>s\<^sub>t_append unlabel_append
            setops\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
            unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
      by fastforce
    then obtain t' \<delta> where t':
        "t' \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T))"
        "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "t = t' \<cdot> \<delta>"
      using setops\<^sub>s\<^sub>s\<^sub>t_wt_subst_ex[OF \<xi>\<sigma>\<alpha>_wt \<xi>\<sigma>\<alpha>_wf] by blast
    then obtain s s' where s: "t' = pair (s,s')"
      using setops\<^sub>s\<^sub>s\<^sub>t_are_pairs by fastforce
    moreover have "InSet ac s s' = InSet Assign s s' \<or> InSet ac s s' = InSet Check s s'" for ac
      by (cases ac) simp_all
    ultimately have "\<exists>n. s = Var (Var Value, n)" "\<exists>u. s' = Fun (Set u) []"
      using t'(1) setops\<^sub>s\<^sub>s\<^sub>t_member_iff[of s s' "unlabel (transaction_strand T)"]
            pair_in_pair_image_iff[of s s']
            transaction_inserts_are_Value_vars[
              OF T_wf[OF step.hyps(2)] T_adm'(2)[OF step.hyps(2)], of s s']
            transaction_deletes_are_Value_vars[
              OF T_wf[OF step.hyps(2)] T_adm'(2)[OF step.hyps(2)], of s s']
            transaction_selects_are_Value_vars[
              OF T_wf[OF step.hyps(2)] T_adm'(1)[OF step.hyps(2)], of s s']
            transaction_inset_checks_are_Value_vars[
              OF T_adm[OF step.hyps(2)], of s s']
            transaction_notinset_checks_are_Value_vars[
              OF T_adm[OF step.hyps(2)], of _ _ _ s s']
      by metis+
    then obtain ss n where ss: "t = pair (\<delta> (Var Value, n), Fun (Set ss) [])"
      using t'(4) s unfolding pair_def by force

    have "\<Gamma> (\<delta> (Var Value, n)) = TAtom Value" "wf\<^sub>t\<^sub>r\<^sub>m (\<delta> (Var Value, n))"
      using t'(2) wt_subst_trm''[OF t'(2), of "Var (Var Value, n)"] apply simp
      using t'(3) by (cases "(Var Value, n) \<in> subst_domain \<delta>") auto
    thus ?thesis using ss by blast
  qed simp
qed (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma reachable_constraints_insert_delete_form:
  assumes A: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and t: "insert\<langle>t,s\<rangle> \<in> set (unlabel A) \<or> delete\<langle>t,s\<rangle> \<in> set (unlabel A)" (is "?Q t s A")
  shows "\<exists>k. s = Fun (Set k) []" (is ?A)
    and "\<Gamma> t = TAtom Value" (is ?B)
    and "(\<exists>x. t = Var x) \<or> (\<exists>n. t = Fun (Val n) [])" (is ?C)
proof -
  have 0: "pair (t,s) \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)" using t unfolding setops\<^sub>s\<^sub>s\<^sub>t_def by force

  show 1: ?A ?B using reachable_constraints_setops_form[OF A P 0] by (fast,fast)

  show ?C using A t
  proof (induction A rule: reachable_constraints.induct)
    case (step \<A> T \<xi> \<sigma> \<alpha>)
    let ?T' = "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

    note T_adm = bspec[OF P step.hyps(2)]
    note T_wf = admissible_transaction_is_wellformed_transaction(1,3)[OF T_adm]

    have "?Q t s \<A> \<or> ?Q t s ?T'"
      using step.prems dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(4,5)[of t s ?T']
      unfolding unlabel_append by auto
    thus ?case
    proof
      assume "?Q t s ?T'"
      then obtain u v where u: "?Q u v (transaction_strand T)" "t = u \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
        by (metis (no_types, lifting) stateful_strand_step_mem_substD(4,5) unlabel_subst)

      obtain x where x: "u = Var x"
        using u(1) transaction_inserts_are_Value_vars(1)[OF T_wf, of u v]
              transaction_deletes_are_Value_vars(1)[OF T_wf, of u v]
        by fastforce

      show ?case
        using u(2) x
              transaction_decl_fresh_renaming_substs_range'(3)[
                OF step.hyps(3,4,5) _
                   admissible_transaction_decl_subst_empty[OF T_adm step.hyps(3)]
                   admissible_transactionE(2)[OF T_adm],
                of t]
        by (cases "t \<in> subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)")
           (blast, metis eval_term.simps(1) subst_imgI)
    qed (use step.IH in fastforce)
  qed simp
qed

lemma reachable_constraints_setops_type:
  fixes t::"('fun,'atom,'sets,'lbl) prot_term"
  assumes A: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
    and t: "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
  shows "\<Gamma> t = TComp Pair [TAtom Value, TAtom SetType]"
proof -
  obtain s c where s: "t = pair (c, Fun (Set s) [])" "\<Gamma> c = TAtom Value"
    using reachable_constraints_setops_form[OF A P t] by moura
  hence "(Fun (Set s) []::('fun,'atom,'sets,'lbl) prot_term) \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
    using t setops\<^sub>s\<^sub>s\<^sub>t_member_iff[of c "Fun (Set s) []" "unlabel A"]
    by force
  hence "wf\<^sub>t\<^sub>r\<^sub>m (Fun (Set s) []::('fun,'atom,'sets,'lbl) prot_term)"
    using reachable_constraints_wf(2) P A admissible_transaction_is_wellformed_transaction(1,4)
    unfolding admissible_transaction_terms_def by blast
  hence "arity (Set s) = 0" unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by simp
  thus ?thesis using s unfolding pair_def by fastforce
qed

lemma reachable_constraints_setops_same_type_if_unifiable:
  assumes A: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
  shows "\<forall>s \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A). \<forall>t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A).
          (\<exists>\<delta>. Unifier \<delta> s t) \<longrightarrow> \<Gamma> s = \<Gamma> t"
    (is "?P A")
using reachable_constraints_setops_type[OF A P] by simp

lemma reachable_constraints_setops_unifiable_if_wt_instance_unifiable:
  assumes A: "A \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction' T"
  shows "\<forall>s \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A). \<forall>t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A).
          (\<exists>\<sigma> \<theta> \<rho>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>) \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>) \<and>
                   Unifier \<rho> (s \<cdot> \<sigma>) (t \<cdot> \<theta>))
          \<longrightarrow> (\<exists>\<delta>. Unifier \<delta> s t)"
proof (intro ballI impI)
  fix s t assume st: "s \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)" "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)" and
    "\<exists>\<sigma> \<theta> \<rho>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>) \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>) \<and>
             Unifier \<rho> (s \<cdot> \<sigma>) (t \<cdot> \<theta>)"
  then obtain \<sigma> \<theta> \<rho> where \<sigma>:
      "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
      "Unifier \<rho> (s \<cdot> \<sigma>) (t \<cdot> \<theta>)"
    by moura

  obtain fs ft cs ct where c:
      "s = pair (cs, Fun (Set fs) [])" "t = pair (ct, Fun (Set ft) [])"
      "\<Gamma> cs = TAtom Value" "\<Gamma> ct = TAtom Value" 
    using reachable_constraints_setops_form[OF A P st(1)]
          reachable_constraints_setops_form[OF A P st(2)]
    by moura

  have "cs \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" "ct \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
    using c(1,2) setops_subterm_trms[OF st(1), of cs] setops_subterm_trms[OF st(2), of ct]
          Fun_param_is_subterm[of cs "args s"] Fun_param_is_subterm[of ct "args t"]
    unfolding pair_def by simp_all
  moreover have
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
    using P admissible_transaction_is_wellformed_transaction(1,4)
    unfolding admissible_transaction_terms_def by fast+
  ultimately have *: "wf\<^sub>t\<^sub>r\<^sub>m cs" "wf\<^sub>t\<^sub>r\<^sub>m ct"
    using reachable_constraints_wf(2)[OF _ _ A] wf_trms_subterms by blast+

  have "(\<exists>x. cs = Var x) \<or> (\<exists>c d. cs = Fun c [])"
    using const_type_inv_wf c(3) *(1) by (cases cs) auto
  moreover have "(\<exists>x. ct = Var x) \<or> (\<exists>c d. ct = Fun c [])"
    using const_type_inv_wf c(4) *(2) by (cases ct) auto
  ultimately show "\<exists>\<delta>. Unifier \<delta> s t"
    using reachable_constraints_setops_form[OF A P] reachable_constraints_setops_type[OF A P] st \<sigma> c
    unfolding pair_def by auto
qed

lemma reachable_constraints_tfr:
  assumes M:
      "M \<equiv> \<Union>T \<in> set P. trms_transaction T"
      "has_all_wt_instances_of \<Gamma> M N"
      "finite N"
      "tfr\<^sub>s\<^sub>e\<^sub>t N"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
      "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    and \<A>: "\<A> \<in> reachable_constraints P"
  shows "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
using \<A>
proof (induction \<A> rule: reachable_constraints.induct)
  case (step A T \<xi> \<sigma> \<alpha>)
  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  have P': "\<forall>T \<in> set P. admissible_transaction' T" using P(1) admissible_transactionE'(1) by blast

  have AT'_reach: "A@T' \<in> reachable_constraints P"
    using reachable_constraints.step[OF step.hyps] unfolding T'_def by metis

  note T_adm = bspec[OF P(1) step.hyps(2)]
  note T_adm' = bspec[OF P'(1) step.hyps(2)]

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T_adm' step.hyps(3)]

  note \<xi>\<sigma>\<alpha>_wt = transaction_decl_fresh_renaming_substs_wt[OF step.hyps(3-5)]
  note \<xi>\<sigma>\<alpha>_wf = transaction_decl_fresh_renaming_substs_range_wf_trms[OF step.hyps(3-5)]

  have \<xi>\<sigma>\<alpha>_bvars_disj: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<inter> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = {}"
    using transaction_decl_fresh_renaming_substs_vars_disj(4)[OF step.hyps(3,4,5,2)] \<xi>_empty
    by simp

  have wf_trms_M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
    using admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P'(1) unfolding M(1) by blast

  have "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@T'))"
    using reachable_constraints_SMP_subset(1)[OF AT'_reach]
          tfr_subset(3)[OF M(4), of "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@T')"]
          SMP_SMP_subset[of M N] SMP_I'[OF wf_trms_M M(5,2)]
    unfolding M(1) by blast
  moreover have "\<forall>p. Ana (pair p) = ([],[])" unfolding pair_def by auto
  ultimately have 1: "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@T') \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (A@T')))"
    using tfr_setops_if_tfr_trms[of "unlabel (A@T')"]
          reachable_constraints_no_Pair_fun[OF AT'_reach P']
          reachable_constraints_setops_same_type_if_unifiable[OF AT'_reach P']
          reachable_constraints_setops_unifiable_if_wt_instance_unifiable[OF AT'_reach P']
    by blast

  have "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    using step.hyps(2) P(2) tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p
    unfolding comp_tfr\<^sub>s\<^sub>s\<^sub>t_def tfr\<^sub>s\<^sub>s\<^sub>t_def by fastforce
  hence "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel T')"
    using tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_all_wt_subst_apply[OF _ \<xi>\<sigma>\<alpha>_wt \<xi>\<sigma>\<alpha>_wf \<xi>\<sigma>\<alpha>_bvars_disj]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
          unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
    unfolding T'_def by argo
  hence 2: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (A@T'))"
    using step.IH unlabel_append
    unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by auto

  have "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel (A@T'))" using 1 2 by (metis tfr\<^sub>s\<^sub>s\<^sub>t_def)
  thus ?case by (metis T'_def)
qed simp

lemma reachable_constraints_tfr':
  assumes M:
      "M \<equiv> \<Union>T \<in> set P. trms_transaction T \<union> pair' Pair ` setops_transaction T"
      "has_all_wt_instances_of \<Gamma> M N"
      "finite N"
      "tfr\<^sub>s\<^sub>e\<^sub>t N"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and P:
      "\<forall>T \<in> set P. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
      "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    and \<A>: "\<A> \<in> reachable_constraints P"
  shows "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
using \<A>
proof (induction \<A> rule: reachable_constraints.induct)
  case (step A T \<xi> \<sigma> \<alpha>)
  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  have AT'_reach: "A@T' \<in> reachable_constraints P"
    using reachable_constraints.step[OF step.hyps] unfolding T'_def by metis

  note \<xi>\<sigma>\<alpha>_wt = transaction_decl_fresh_renaming_substs_wt[OF step.hyps(3-5)]
  note \<xi>\<sigma>\<alpha>_wf = transaction_decl_fresh_renaming_substs_range_wf_trms[OF step.hyps(3-5)]

  have \<xi>\<sigma>\<alpha>_bvars_disj: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<inter> range_vars (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = {}"
    by (rule transaction_decl_fresh_renaming_substs_vars_disj(4)[OF step.hyps(3,4,5,2)])

  have wf_trms_M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
    using P(1) setops\<^sub>s\<^sub>s\<^sub>t_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s(2) unfolding M(1) pair_code wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric] by fast

  have "SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@T')) \<subseteq> SMP M" "SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (A@T'))) \<subseteq> SMP M"
    using reachable_constraints_SMP_subset[OF AT'_reach]
          SMP_mono[of "\<Union>T \<in> set P. trms_transaction T" M]
          SMP_mono[of "\<Union>T \<in> set P. pair ` setops_transaction T" M]
    unfolding M(1) pair_code[symmetric] by blast+
  hence 1: "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@T') \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (A@T')))"
    using tfr_subset(3)[OF M(4), of "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@T') \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (A@T'))"]
          SMP_union[of "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@T')" "pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (A@T'))"]
          SMP_SMP_subset[of M N] SMP_I'[OF wf_trms_M M(5,2)]
    by blast

  have "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    using step.hyps(2) P(2) tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p
    unfolding comp_tfr\<^sub>s\<^sub>s\<^sub>t_def tfr\<^sub>s\<^sub>s\<^sub>t_def by fastforce
  hence "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel T')"
    using tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_all_wt_subst_apply[OF _ \<xi>\<sigma>\<alpha>_wt \<xi>\<sigma>\<alpha>_wf \<xi>\<sigma>\<alpha>_bvars_disj]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
          unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
    unfolding T'_def by argo
  hence 2: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (A@T'))"
    using step.IH unlabel_append
    unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by auto

  have "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel (A@T'))" using 1 2 by (metis tfr\<^sub>s\<^sub>s\<^sub>t_def)
  thus ?case by (metis T'_def)
qed simp

lemma reachable_constraints_typing_cond\<^sub>s\<^sub>s\<^sub>t:
  assumes M:
      "M \<equiv> \<Union>T \<in> set P. trms_transaction T \<union> pair' Pair ` setops_transaction T"
      "has_all_wt_instances_of \<Gamma> M N"
      "finite N"
      "tfr\<^sub>s\<^sub>e\<^sub>t N"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
      "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    and \<A>: "\<A> \<in> reachable_constraints P"
  shows "typing_cond\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
using reachable_constraints_wf[OF P(1,2) \<A>] reachable_constraints_tfr'[OF M P(2,3) \<A>]
unfolding typing_cond\<^sub>s\<^sub>s\<^sub>t_def by blast

context
begin
private lemma reachable_constraints_typing_result_aux:
  assumes 0: "wf\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)" "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "wf\<^sub>s\<^sub>s\<^sub>t (unlabel (\<A>@[(l,send\<langle>[attack\<langle>n\<rangle>]\<rangle>)]))" "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel (\<A>@[(l,send\<langle>[attack\<langle>n\<rangle>]\<rangle>)]))"
        "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@[(l,send\<langle>[attack\<langle>n\<rangle>]\<rangle>)]))"
proof -
  let ?n = "[(l,send\<langle>[attack\<langle>n\<rangle>]\<rangle>)]"
  let ?A = "\<A>@?n"

  show "wf\<^sub>s\<^sub>s\<^sub>t (unlabel ?A)"
    using 0(1) wf\<^sub>s\<^sub>s\<^sub>t_append_suffix'[of "{}" "unlabel \<A>" "unlabel ?n"] unlabel_append[of \<A> ?n]
    by simp

  show "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?A)"
    using 0(3) trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel ?n"] unlabel_append[of \<A> ?n]
    by fastforce

  have "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?n \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ?n). \<exists>c. t = Fun c []"
       "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?n \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ?n). Ana t = ([],[])"
    by (simp_all add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  hence "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) \<union>
                (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?n \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ?n)))"
    using 0(2) tfr_consts_mono unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by blast
  hence "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@?n) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (\<A>@?n)))"
    using unlabel_append[of \<A> ?n] trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel ?n"]
          setops\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel ?n"]
    by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  thus "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel ?A)"
    using 0(2) unlabel_append[of ?A ?n]
    unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by auto
qed

lemma reachable_constraints_typing_result:
  fixes P
  assumes M:
      "has_all_wt_instances_of \<Gamma> (\<Union>T \<in> set P. trms_transaction T) N"
      "finite N"
      "tfr\<^sub>s\<^sub>e\<^sub>t N"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
      "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    and A: "\<A> \<in> reachable_constraints P"
    and \<I>: "constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
  shows "\<exists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
proof -
  have I:
      "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
      "constr_sem_stateful \<I> (unlabel (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)]))"
    using \<I> unfolding constraint_model_def by metis+

  note 0 = admissible_transaction_is_wellformed_transaction(1,4)[OF admissible_transactionE'(1)]

  have 1: "\<forall>T \<in> set P. wellformed_transaction T"
    using P(1) 0(1) by blast
  
  have 2: "\<forall>T \<in> set P. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
    using P(1) 0(2) unfolding admissible_transaction_terms_def by blast
  
  have 3: "wf\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)" "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    using reachable_constraints_tfr[OF _ M P A] reachable_constraints_wf[OF 1(1) 2 A] by metis+

  show ?thesis
    using stateful_typing_result[OF reachable_constraints_typing_result_aux[OF 3] I(1,3)]
    by (metis welltyped_constraint_model_def constraint_model_def)
qed

lemma reachable_constraints_typing_result':
  fixes P
  assumes M:
      "M \<equiv> \<Union>T \<in> set P. trms_transaction T \<union> pair' Pair ` setops_transaction T"
      "has_all_wt_instances_of \<Gamma> M N"
      "finite N"
      "tfr\<^sub>s\<^sub>e\<^sub>t N"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
      "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    and A: "\<A> \<in> reachable_constraints P"
    and \<I>: "constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
  shows "\<exists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
proof -
  have I:
      "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
      "constr_sem_stateful \<I> (unlabel (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)]))"
    using \<I> unfolding constraint_model_def by metis+

  have 0: "wf\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)" "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    using reachable_constraints_tfr'[OF M P(2-3) A]
          reachable_constraints_wf[OF P(1,2) A]
    by metis+

  show ?thesis
    using stateful_typing_result[OF reachable_constraints_typing_result_aux[OF 0] I(1,3)]
    by (metis welltyped_constraint_model_def constraint_model_def)
qed
end

lemma reachable_constraints_transaction_proj:
  assumes "\<A> \<in> reachable_constraints P"
  shows "proj n \<A> \<in> reachable_constraints (map (transaction_proj n) P)"
using assms
proof (induction \<A> rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>) show ?case
    using step.hyps(2) reachable_constraints.step[OF
            step.IH _ transaction_decl_subst_proj[OF step.hyps(3)]
            transaction_fresh_subst_proj[OF step.hyps(4)]
            transaction_renaming_subst_proj[OF step.hyps(5)]]
    by (simp add: proj_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t proj_subst transaction_strand_proj)
qed (simp add: reachable_constraints.init)

context
begin
private lemma reachable_constraints_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_aux:
  fixes P
  defines "Ts \<equiv> concat (map transaction_strand P)"
  assumes A: "A \<in> reachable_constraints P"
  shows "\<forall>b \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A). \<exists>a \<in> set Ts. \<exists>\<delta>. b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<and>
      wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and>
      (\<forall>t \<in> subst_range \<delta>. (\<exists>x. t = Var x) \<or> (\<exists>c. t = Fun c []))"
    (is "\<forall>b \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A). \<exists>a \<in> set Ts. ?P b a")
using A
proof (induction A rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  define Q where "Q \<equiv> ?P"
  define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  let ?R = "\<lambda>A Ts. \<forall>b \<in> set A. \<exists>a \<in> set Ts. Q b a"

  have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
       "\<forall>t \<in> subst_range \<theta>. (\<exists>x. t = Var x) \<or> (\<exists>c. t = Fun c [])"
    using transaction_decl_fresh_renaming_substs_wt[OF step.hyps(3-5)]
          transaction_decl_fresh_renaming_substs_range_wf_trms[OF step.hyps(3-5)]
          transaction_decl_fresh_renaming_substs_range'(1)[OF step.hyps(3-5)]
    unfolding \<theta>_def by (metis,metis,fastforce)
  hence "?R (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) (transaction_strand T)"
    using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_self_inverse[of "transaction_strand T"]
    by (auto simp add: Q_def subst_apply_labeled_stateful_strand_def)
  hence "?R (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) (transaction_strand T)"
    by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst)
  hence "?R (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) Ts"
    using step.hyps(2) unfolding Ts_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by fastforce
  thus ?case using step.IH unfolding Q_def \<theta>_def by auto
qed simp

lemma reachable_constraints_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t:
  fixes P
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "Ts \<equiv> concat (map transaction_strand P)"
  assumes P_pc: "comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> Pair Ts M S"
    and A: "A \<in> reachable_constraints P"
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t A ((f S) - {m. intruder_synth {} m})"
using par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_if_comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t'[OF P_pc, of "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A", THEN par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t]
      reachable_constraints_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_aux[OF A, unfolded Ts_def[symmetric]]
unfolding f_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_self_inverse by fast
end

lemma reachable_constraints_par_comp_constr:
  fixes P f S
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "Ts \<equiv> concat (map transaction_strand P)"
    and "Sec \<equiv> f S - {m. intruder_synth {} m}"
    and "M \<equiv> \<Union>T \<in> set P. trms_transaction T \<union> pair' Pair ` setops_transaction T"
  assumes M:
      "has_all_wt_instances_of \<Gamma> M N"
      "finite N"
      "tfr\<^sub>s\<^sub>e\<^sub>t N"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
      "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
      "comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> Pair Ts M_fun S"   
    and \<A>: "\<A> \<in> reachable_constraints P"
    and \<I>: "constraint_model \<I> \<A>"
  shows "\<exists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> \<A> \<and>
              ((\<forall>n. welltyped_constraint_model \<I>\<^sub>\<tau> (proj n \<A>)) \<or>
               (\<exists>\<A>' l t. prefix \<A>' \<A> \<and> suffix [(l, receive\<langle>t\<rangle>)] \<A>' \<and> strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>))"
proof -
  have \<I>': "constr_sem_stateful \<I> (unlabel \<A>)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    using \<I> unfolding constraint_model_def by blast+

  show ?thesis
    using reachable_constraints_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t[OF P(4)[unfolded Ts_def] \<A>]
          reachable_constraints_typing_cond\<^sub>s\<^sub>s\<^sub>t[OF M_def M P(1-3) \<A>]
          par_comp_constr_stateful[OF _ _ \<I>', of Sec]
    unfolding f_def Sec_def welltyped_constraint_model_def constraint_model_def by blast
qed

lemma reachable_constraints_component_leaks_if_composed_leaks:
  fixes Sec Q
  defines "leaks \<equiv> \<lambda>\<A>. \<exists>\<I>\<^sub>\<tau> \<A>'.
    Q \<I>\<^sub>\<tau> \<and> prefix \<A>' \<A> \<and> (\<exists>l' t. suffix [(l', receive\<langle>t\<rangle>)] \<A>') \<and> strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>"
  assumes Sec: "\<forall>s \<in> Sec. \<not>{} \<turnstile>\<^sub>c s" "ground Sec"
    and composed_leaks: "\<exists>\<A> \<in> reachable_constraints Ps. leaks \<A>"
  shows "\<exists>l. \<exists>\<A> \<in> reachable_constraints (map (transaction_proj l) Ps). leaks \<A>"
proof -
  from composed_leaks obtain \<A> \<I>\<^sub>\<tau> \<A>' s n where
      \<A>: "\<A> \<in> reachable_constraints Ps" and
      \<A>': "prefix \<A>' \<A>" "constr_sem_stateful \<I>\<^sub>\<tau> (proj_unl n \<A>'@[send\<langle>[s]\<rangle>])" and
      \<I>\<^sub>\<tau>: "Q \<I>\<^sub>\<tau>" and
      s: "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>"
    unfolding leaks_def strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by fast

  have "\<not>{} \<turnstile>\<^sub>c s" "s \<cdot> \<I>\<^sub>\<tau> = s" using s Sec by auto
  then obtain B k' u where
      "constr_sem_stateful \<I>\<^sub>\<tau> (proj_unl n B@[send\<langle>[s]\<rangle>])"
      "prefix (proj n B) (proj n \<A>)" "suffix [(k', receive\<langle>u\<rangle>)] (proj n B)"
      "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n B) \<I>\<^sub>\<tau>"
    using constr_sem_stateful_proj_priv_term_prefix_obtain[OF \<A>' s]
    unfolding welltyped_constraint_model_def constraint_model_def by metis
  thus ?thesis
    using \<I>\<^sub>\<tau> reachable_constraints_transaction_proj[OF \<A>, of n] proj_idem[of n B]
    unfolding leaks_def strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def
    by metis
qed

lemma reachable_constraints_preserves_labels:
  assumes \<A>: "\<A> \<in> reachable_constraints P"
  shows "\<forall>a \<in> set \<A>. \<exists>T \<in> set P. \<exists>b \<in> set (transaction_strand T). fst b = fst a"
    (is "\<forall>a \<in> set \<A>. \<exists>T \<in> set P. ?P T a")
using \<A>
proof (induction \<A> rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  have "\<forall>a \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)). ?P T a"
  proof
    fix a assume a: "a \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    then obtain b where b: "b \<in> set (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" "a = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p b"
      unfolding dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto
    then obtain c where c: "c \<in> set (transaction_strand T)" "b = c \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      unfolding subst_apply_labeled_stateful_strand_def by auto

    have "?P T c" using c(1) by blast
    hence "?P T b" using c(2) by (simp add: subst_lsstp_fst_eq)
    thus "?P T a" using b(2) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_fst_eq[of b] by presburger
  qed
  thus ?case using step.IH step.hyps(2) by (metis Un_iff set_append)
qed simp

lemma reachable_constraints_preserves_labels':
  assumes P: "\<forall>T \<in> set P. \<forall>a \<in> set (transaction_strand T). has_LabelN l a \<or> has_LabelS a"
    and \<A>: "\<A> \<in> reachable_constraints P"
  shows "\<forall>a \<in> set \<A>. has_LabelN l a \<or> has_LabelS a"
using reachable_constraints_preserves_labels[OF \<A>] P by fastforce

lemma reachable_constraints_transaction_proj_proj_eq:
  assumes \<A>: "\<A> \<in> reachable_constraints (map (transaction_proj l) P)"
  shows "proj l \<A> = \<A>"
    and "prefix \<A>' \<A> \<Longrightarrow> proj l \<A>' = \<A>'"
using \<A>
proof (induction \<A> rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  let ?T = "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  note A = reachable_constraints.step[OF step.hyps]

  have P: "\<forall>T \<in> set (map (transaction_proj l) P).
            \<forall>a \<in> set (transaction_strand T). has_LabelN l a \<or> has_LabelS a"
    using transaction_proj_labels[of l] unfolding list_all_iff by auto

  note * = reachable_constraints_preserves_labels'[OF P A]

  have **: "\<forall>a \<in> set \<A>'. has_LabelN l a \<or> has_LabelS a"
    when "\<forall>a \<in> set B. has_LabelN l a \<or> has_LabelS a" "prefix \<A>' B" for B
    using that assms unfolding prefix_def by auto

  note *** = proj_ident[unfolded list_all_iff]

  { case 1 thus ?case using *[THEN ***] by blast }
  { case 2 thus ?case using *[THEN **, THEN ***] by blast }
qed (simp_all add: reachable_constraints.init)

lemma reachable_constraints_transaction_proj_star_proj:
  assumes \<A>: "\<A> \<in> reachable_constraints (map (transaction_proj l) P)"
    and k_neq_l: "k \<noteq> l"
  shows "proj k \<A> \<in> reachable_constraints (map transaction_star_proj P)"
using \<A>
proof (induction \<A> rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  have "map (transaction_proj k) (map (transaction_proj l) P) = map transaction_star_proj P"
    using transaction_star_proj_negates_transaction_proj(2)[OF k_neq_l]
    by fastforce
  thus ?case
    using reachable_constraints_transaction_proj[OF reachable_constraints.step[OF step.hyps], of k]
    by argo
qed (simp add: reachable_constraints.init)

lemma reachable_constraints_aligned_prefix_ex:
  fixes P
  defines "f \<equiv> \<lambda>T.
    list_all is_Receive (unlabel (transaction_receive T)) \<and>
    list_all is_Check_or_Assignment (unlabel (transaction_checks T)) \<and>
    list_all is_Update (unlabel (transaction_updates T)) \<and>
    list_all is_Send (unlabel (transaction_send T))"
  assumes P: "list_all f P" "list_all ((list_all (Not \<circ> has_LabelS)) \<circ> tl \<circ> transaction_send) P"
    and s: "\<not>{} \<turnstile>\<^sub>c s" "fv s = {}"
    and A: "A \<in> reachable_constraints P" "prefix B A"
    and B: "\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] B"
           "constr_sem_stateful \<I> (unlabel B@[send\<langle>[s]\<rangle>])"
  shows "\<exists>C \<in> reachable_constraints P.
          prefix C A \<and> (\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] C) \<and>
          declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<I> = declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t C \<I> \<and>
          constr_sem_stateful \<I> (unlabel C@[send\<langle>[s]\<rangle>])"
using A
proof (induction A rule: reachable_constraints.induct)
  case (step A T \<xi> \<sigma> \<alpha>)
  define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  let ?T = "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  note AT_reach = reachable_constraints.step[OF step.hyps]

  obtain lb tsb B' where B': "B = B'@[(lb, receive\<langle>tsb\<rangle>)]" using B(1) unfolding suffix_def by blast

  define decl_ik where "decl_ik \<equiv> \<lambda>S::('fun,'atom,'sets,'lbl) prot_strand.
    \<Union>{set ts |ts. \<langle>\<star>, receive\<langle>ts\<rangle>\<rangle> \<in> set S} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"

  have decl_ik_append: "decl_ik (M@N) = decl_ik M \<union> decl_ik N" for M N
    unfolding decl_ik_def by fastforce

  have "\<langle>\<star>, receive\<langle>ts\<rangle>\<rangle> \<notin> set N"
    when "\<star> \<notin> fst ` set N" for ts and N::"('fun, 'atom, 'sets, 'lbl) prot_strand"
    using that by force
  hence decl_ik_star: "decl_ik M = decl_ik (M@N)" when "\<star> \<notin> fst ` set N" for M N
    using that unfolding decl_ik_def by simp 

  have decl_decl_ik: "declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<I> = {t. decl_ik S \<turnstile> t}" for S
    unfolding declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t_alt_def decl_ik_def by blast

  have "f T" using P(1) step.hyps(2) by (simp add: list_all_iff)
  hence "list_all is_Send (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
        "list_all is_Check_or_Assignment (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
        "list_all is_Update (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
        "list_all is_Receive (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
    using subst_sst_list_all(2)[of "unlabel (transaction_receive T)" \<theta>]
          subst_sst_list_all(11)[of "unlabel (transaction_checks T)" \<theta>]
          subst_sst_list_all(10)[of "unlabel (transaction_updates T)" \<theta>]
          subst_sst_list_all(1)[of "unlabel (transaction_send T)" \<theta>]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all(1)[of "transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>"]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all(11)[of "transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>"]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all(10)[of "transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>"]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all(2)[of "transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>"]
    unfolding f_def by (metis unlabel_subst[of _ \<theta>])+
  hence "\<not>list_ex is_Receive (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
        "\<not>list_ex is_Receive (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
        "\<not>list_ex is_Receive (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
        "list_all is_Receive (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
    unfolding list_ex_iff list_all_iff by blast+
  then obtain TA TB where T:
      "?T = TA@TB" "\<not>list_ex is_Receive (unlabel TA)" "list_all is_Receive (unlabel TB)"
      "TB = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
    using transaction_dual_subst_unfold[of T \<theta>] unfolding \<theta>_def by fastforce

  have 0: "prefix B (A@TA@TB)" using step.prems B' T by argo

  have 1: "prefix B A" when "prefix B (A@TA)"
    using that T(2) B' prefix_prefix_inv
    unfolding list_ex_iff unlabel_def by fastforce
  
  have 2: "\<star> \<notin> fst ` set TB2" when "TB = TB1@(l,x)#TB2" for TB1 l x TB2
  proof -
    have "k \<noteq> \<star>" when "k \<in> set (map fst (tl (transaction_send T)))" for k
      using that P(2) step.hyps(2) unfolding list_all_iff by auto
    hence "k \<noteq> \<star>" when "k \<in> set (map fst (tl TB))" for k
      using that subst_lsst_map_fst_eq[of "tl (transaction_send T)" \<theta>]
            dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_map_fst_eq[of "tl (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"]
      unfolding T(4) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_tl subst_lsst_tl by simp
    moreover have "set TB2 \<subseteq> set (tl TB)"
      using that
      by (metis (no_types, lifting) append_eq_append_conv2 order.eq_iff list.sel(3) self_append_conv
                set_mono_suffix suffix_appendI suffix_tl tl_append2)
    ultimately show ?thesis by auto
  qed

  have 3: "declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t TB \<I> = declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t (TB1@[(l,x)]) \<I>"
    when "TB = TB1@(l,x)#TB2" for TB1 l x TB2
    using decl_ik_star[OF 2[OF that], of "TB1@[(l,x)]"] unfolding that decl_decl_ik by simp

  show ?case
  proof (cases "prefix B A")
    case False
    hence 4: "\<not>prefix B (A@TA)" using 1 by blast

    have 5: "\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] (A@?T)"
    proof -
      have "(lb, receive\<langle>tsb\<rangle>) \<in> set TB"
        using 0 4 prefix_prefix_inv[OF _ suffixI[OF B'], of "A@TA" TB] by (metis append_assoc)
      hence "receive\<langle>tsb\<rangle> \<in> set (unlabel TB)"
        unfolding unlabel_def by force
      hence "\<exists>ts. suffix [receive\<langle>ts\<rangle>] (unlabel TB)"
        using T(3) unfolding list_all_iff is_Receive_def suffix_def
        by (metis in_set_conv_decomp list.distinct(1) list.set_cases rev_exhaust)
      then obtain TB' ts where "unlabel TB = TB'@[receive\<langle>ts\<rangle>]" unfolding suffix_def by blast
      then obtain TB'' x where "TB = TB''@[x]" "snd x = receive\<langle>ts\<rangle>"
        by (metis (no_types, opaque_lifting) append1_eq_conv list.distinct(1) rev_exhaust
              rotate1.simps(2) rotate1_is_Nil_conv unlabel_Cons(2) unlabel_append unlabel_nil)
      then obtain l where "suffix [(l, receive\<langle>ts\<rangle>)] TB"
        by (metis surj_pair prod.sel(2) suffix_def)
      thus ?thesis
        using T(4) transaction_dual_subst_unfold[of T \<theta>]
              suffix_append[of "[(l, receive\<langle>ts\<rangle>)]"]
        unfolding \<theta>_def by metis
    qed

    obtain TB1 where TB:
        "B = A@TA@TB1@[(lb, receive\<langle>tsb\<rangle>)]" "prefix (TB1@[(lb, receive\<langle>tsb\<rangle>)]) TB"
      using 0 4 B' prefix_snoc_obtain[of B' "(lb, receive\<langle>tsb\<rangle>)" "A@TA" TB thesis]
      by (metis append_assoc)
    then obtain TB2 where TB2: "TB = TB1@(lb, receive\<langle>tsb\<rangle>)#TB2"
      unfolding prefix_def by fastforce
    hence TB2': "list_all is_Receive (unlabel TB2)"
      using T(3) unfolding list_all_iff is_Receive_def proj_def unlabel_def by auto

    have 6: "constr_sem_stateful \<I> (unlabel B)" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s \<cdot> \<I>"
      using B(2) strand_sem_append_stateful[of "{}" "{}" "unlabel B" "[send\<langle>[s]\<rangle>]" \<I>]
      by auto

    have "constr_sem_stateful \<I> (unlabel (A@TA@TB1@[(lb, receive\<langle>tsb\<rangle>)]))"
      using 6(1) TB(1) by blast
    hence "constr_sem_stateful \<I> (unlabel (A@?T))"
      using T(1) TB2 strand_sem_receive_prepend_stateful[
              of "{}" "{}" "unlabel (A@TA@TB1@[(lb, receive\<langle>tsb\<rangle>)])" \<I>,
              OF _ TB2']
      by auto
    moreover have "set (unlabel B) \<subseteq> set (unlabel (A@?T))"
      using step.prems(1) unfolding prefix_def by force
    hence "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@?T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s \<cdot> \<I>"
      using ideduct_mono[OF 6(2)] subst_all_mono[of _ _ \<I>]
            ik\<^sub>s\<^sub>s\<^sub>t_set_subset[of "unlabel B" "unlabel (A@?T)"]
      by meson
    ultimately have 7: "constr_sem_stateful \<I> (unlabel (A@?T)@[send\<langle>[s]\<rangle>])"
      using strand_sem_append_stateful[of "{}" "{}" "unlabel (A@?T)" "[send\<langle>[s]\<rangle>]" \<I>]
      by auto

    have "declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<I> = declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@?T) \<I>"
    proof -
      have "declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t TB \<I> = declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t (TB1@[(lb, receive\<langle>tsb\<rangle>)]) \<I>"
        using 3[of _ lb "receive\<langle>tsb\<rangle>"] TB(2) unfolding prefix_def by auto
      hence "(decl_ik TB \<turnstile> t) \<longleftrightarrow> decl_ik (TB1@[(lb,receive\<langle>tsb\<rangle>)]) \<turnstile> t" for t
        unfolding TB(1) T(1) decl_decl_ik by blast
      hence "(decl_ik (A@TA@TB) \<turnstile> t) \<longleftrightarrow> decl_ik (A@TA@TB1@[(lb,receive\<langle>tsb\<rangle>)]) \<turnstile> t" for t
        using ideduct_mono_eq[of "decl_ik TB" "decl_ik (TB1@[(lb,receive\<langle>tsb\<rangle>)])" "decl_ik (A@TA)"]
        by (metis decl_ik_append[of "A@TA"] Un_commute[of _ "decl_ik (A@TA)"] append_assoc)
      thus ?thesis unfolding TB(1) T(1) decl_decl_ik by blast
    qed
    thus ?thesis using step.prems AT_reach B(1) 5 7 by force
  qed (use step.IH prefix_append in blast)
qed (use B(1) suffix_def in simp)

lemma reachable_constraints_secure_if_filter_secure_case:
  fixes f l n
    and P::"('fun,'atom,'sets,'lbl) prot_transaction list"
  defines "has_attack \<equiv> \<lambda>P.
      \<exists>\<A> \<in> reachable_constraints P. \<exists>\<I>. constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
    and "f \<equiv> \<lambda>T. list_ex (\<lambda>a. is_Update (snd a) \<or> is_Send (snd a)) (transaction_strand T)"
    and "g \<equiv> \<lambda>T. transaction_fresh T = [] \<longrightarrow> f T"
  assumes att: "has_attack P"
  shows "has_attack (filter g P)"
proof -
  let ?attack = "\<lambda>A I. constraint_model I (A@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"

  define constr' where "constr' \<equiv>
    \<lambda>(T::('fun,'atom,'sets,'lbl) prot_transaction,\<xi>::('fun,'atom,'sets,'lbl) prot_subst,
      \<sigma>::('fun,'atom,'sets,'lbl) prot_subst,\<alpha>::('fun,'atom,'sets,'lbl) prot_subst).
      dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  define constr where "constr \<equiv> \<lambda>Ts. concat (map constr' Ts)"

  define h where "h \<equiv>
    \<lambda>(T::('fun,'atom,'sets,'lbl) prot_transaction,_::('fun,'atom,'sets,'lbl) prot_subst,
      _::('fun,'atom,'sets,'lbl) prot_subst,_::('fun,'atom,'sets,'lbl) prot_subst).
      g T"

  obtain A I where A: "A \<in> reachable_constraints P" "?attack A I"
    using att unfolding has_attack_def by blast

  obtain Ts where Ts:
      "A = constr Ts"
      "\<forall>B. prefix B Ts \<longrightarrow> constr B \<in> reachable_constraints P"
      "\<forall>B T \<xi> \<sigma> \<alpha>. prefix (B@[(T,\<xi>,\<sigma>,\<alpha>)]) Ts \<longrightarrow>
          T \<in> set P \<and> transaction_decl_subst \<xi> T \<and>
          transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr B)) \<and>
          transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr B))"
    using reachable_constraints_as_transaction_lists[OF A(1)] constr_def constr'_def by auto

  define B where "B \<equiv> constr (filter h Ts)"

  have Ts': "T \<in> set P" when "(T,\<xi>,\<sigma>,\<alpha>) \<in> set Ts" for T \<xi> \<sigma> \<alpha>
    using that Ts(3) by (meson prefix_snoc_in_iff) 

  have constr_Cons: "constr (p#Ts) = constr' p@constr Ts" for p Ts unfolding constr_def by simp

  have constr_snoc: "constr (Ts@[p]) = constr Ts@constr' p" for p Ts unfolding constr_def by simp

  have 0: "?attack B I" when A_att: "?attack A I"
  proof -
    have not_f_T_case: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr' p) = {}" "\<And>D. dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (constr' p)) I D = D"
      when not_f_T: "\<not>(f T)" and p: "p = (T,\<xi>,\<sigma>,\<alpha>)" for p T \<xi> \<sigma> \<alpha>
    proof -
      have constr_p: "constr' p = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
        unfolding p constr'_def by fast

      have "\<not>is_Receive a" when a: "(l,a) \<in> set (constr' p)" for l a
      proof
        assume "is_Receive a"
        then obtain ts where ts: "a = receive\<langle>ts\<rangle>" by (cases a) auto
        then obtain ts' where ts':
          "(l,send\<langle>ts'\<rangle>) \<in> set (transaction_strand T)" "ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
          using a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(1)[of l ts] subst_lsst_memD(2)[of l _ "transaction_strand T"]
          unfolding constr_p by blast
        thus False using not_f_T unfolding f_def list_ex_iff by fastforce
      qed
      thus "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr' p) = {}" using in_ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t_iff by fastforce

      have "\<not>is_Update a" when a: "(l,a) \<in> set (constr' p)" for l a
      proof
        assume "is_Update a"
        then obtain t s where ts: "a = insert\<langle>t,s\<rangle> \<or> a = delete\<langle>t,s\<rangle>" by (cases a) auto
        then obtain t' s' where ts':
          "(l,insert\<langle>t',s'\<rangle>) \<in> set (transaction_strand T) \<or>
               (l,delete\<langle>t',s'\<rangle>) \<in> set (transaction_strand T)"
          "t = t' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "s = s' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
          using a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(4,5)[of l]
            subst_lsst_memD(4,5)[of l _ _ "transaction_strand T"]
          unfolding constr_p by blast
        thus False using not_f_T unfolding f_def list_ex_iff by fastforce
      qed
      thus "\<And>D. dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (constr' p)) I D = D"
        using dbupd\<^sub>s\<^sub>s\<^sub>t_no_upd[of "unlabel (constr' p)" I] by (meson unlabel_mem_has_label) 
    qed

    have *: "strand_sem_stateful M D (unlabel B) I"
      when "strand_sem_stateful M D (unlabel A) I" for M D
      using that Ts' unfolding Ts(1) B_def
    proof (induction Ts arbitrary: M D)
      case (Cons p Ts)
      obtain T \<xi> \<sigma> \<alpha> where p: "p = (T,\<xi>,\<sigma>,\<alpha>)" by (cases p) simp
      have T_in: "T \<in> set P" using Cons.prems(2) unfolding p by fastforce

      let ?M' = "M \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr' p) \<cdot>\<^sub>s\<^sub>e\<^sub>t I)"
      let ?D' = "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (constr' p)) I D"

      have p_sem: "strand_sem_stateful M D (unlabel (constr' p)) I"
        and IH: "strand_sem_stateful ?M' ?D' (unlabel (constr (filter h Ts))) I"
        using Cons.IH[of ?M' ?D'] Cons.prems
              strand_sem_append_stateful[of M D "unlabel (constr' p)" "unlabel (constr Ts)" I]
        unfolding constr_Cons unlabel_append by fastforce+

      show ?case
      proof (cases "T \<in> set (filter g P)")
        case True
        hence h_p: "filter h (p#Ts) = p#filter h Ts" unfolding h_def p by simp
        show ?thesis
          using p_sem IH strand_sem_append_stateful[of M D "unlabel (constr' p)" _ I]
          unfolding h_p constr_Cons unlabel_append by blast
      next
        case False
        hence not_f: "\<not>(f T)"
          and not_h: "\<not>(h p)"
          using T_in unfolding g_def h_def p by auto

        show ?thesis
          using not_h not_f_T_case[OF not_f p] IH
          unfolding constr_Cons unlabel_append by auto
      qed
    qed simp

    have **: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
    proof
      show "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<subseteq> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
        unfolding Ts(1) B_def constr_def by (induct Ts) (auto simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)

      show "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<subseteq> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B" using Ts' unfolding Ts(1) B_def
      proof (induction Ts)
        case (Cons p Ts)
        obtain T \<xi> \<sigma> \<alpha> where p: "p = (T,\<xi>,\<sigma>,\<alpha>)" by (cases p) simp
        have T_in: "T \<in> set P" using Cons.prems unfolding p by fastforce

        have IH: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr Ts) \<subseteq> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr (filter h Ts))"
          using Cons.IH Cons.prems by auto

        show ?case
        proof (cases "T \<in> set (filter g P)")
          case True
          hence h_p: "filter h (p#Ts) = p#filter h Ts" unfolding h_def p by simp
          show ?thesis
            using IH unfolding h_p constr_Cons unlabel_append ik\<^sub>s\<^sub>s\<^sub>t_append by blast
        next
          case False
          hence not_f: "\<not>(f T)"
            and not_h: "\<not>(h p)"
            using T_in unfolding g_def h_def p by auto

          show ?thesis
            using not_h not_f_T_case[OF not_f p] IH
            unfolding constr_Cons unlabel_append by auto
        qed
      qed simp
    qed

    show ?thesis
      using A_att *[of "{}" "{}"] ** strand_sem_stateful_if_sends_deduct
            strand_sem_append_stateful[of "{}" "{}" _ "unlabel [(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)]" I]
      unfolding constraint_model_def unlabel_append by force
  qed

  have 1: "B \<in> reachable_constraints (filter g P)"
    using A(1) Ts(2,3) unfolding Ts(1) B_def
  proof (induction Ts rule: List.rev_induct)
    case (snoc p Ts)
    obtain T \<xi> \<sigma> \<alpha> where p: "p = (T,\<xi>,\<sigma>,\<alpha>)" by (cases p) simp

    have constr_p: "constr' p = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      unfolding constr'_def p by fastforce

    have T_in: "T \<in> set P"
      and \<xi>: "transaction_decl_subst \<xi> T"
      and \<sigma>: "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr Ts))"
      and \<alpha>: "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr Ts))"
      using snoc.prems(3) unfolding p by fast+

    have "transaction_fresh_subst s t bb"
      when "transaction_fresh_subst s t aa" "bb \<subseteq> aa"
      for s t bb aa using that unfolding transaction_fresh_subst_def by fast
          
    have "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr (filter h Ts)) \<subseteq> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr Ts)"
      unfolding constr_def unlabel_def by fastforce
    hence \<sigma>': "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr (filter h Ts)))"
      using \<sigma> unfolding transaction_fresh_subst_def by fast

    have "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr (filter h Ts)) \<subseteq> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr Ts)"
      unfolding constr_def unlabel_def vars\<^sub>s\<^sub>s\<^sub>t_def by auto
    hence \<alpha>': "transaction_renaming_subst \<alpha> (filter g P) (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (constr (filter h Ts)))"
      using \<alpha> unfolding transaction_renaming_subst_def by auto

    have IH: "constr (filter h Ts) \<in> reachable_constraints (filter g P)"
      using snoc.prems snoc.IH by simp

    show ?case
    proof (cases "h p")
      case True
      hence h_p: "filter h (Ts@[p]) = filter h Ts@[p]" by fastforce
      have T_in': "T \<in> set (filter g P)" using T_in True unfolding h_def p by fastforce
      show ?thesis
        using IH reachable_constraints.step[OF IH T_in' \<xi> \<sigma>' \<alpha>']
        unfolding h_p constr_snoc constr_p by fast
    next
      case False thus ?thesis using IH by fastforce
    qed
  qed (simp add: constr_def)

  show ?thesis using 0 1 A(2) unfolding has_attack_def by blast
qed

lemma reachable_constraints_fv_Value_typed:
  assumes P: "\<forall>T \<in> set P. admissible_transaction' T"
    and A: "\<A> \<in> reachable_constraints P"
    and x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
  shows "\<Gamma>\<^sub>v x = TAtom Value"
proof -
  obtain T where T: "T \<in> set P" "\<Gamma>\<^sub>v x \<in> \<Gamma>\<^sub>v ` fv_transaction T"
    using x P(1) reachable_constraints_var_types_in_transactions(1)[OF A(1)]
          admissible_transactionE(2) 
    by blast

  show ?thesis
    using T(2) admissible_transactionE(3)[OF bspec[OF P(1) T(1)]]
          vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
    by force
qed

lemma reachable_constraints_fv_Value_const_cases:
  assumes P: "\<forall>T \<in> set P. admissible_transaction' T"
    and A: "\<A> \<in> reachable_constraints P"
    and I: "welltyped_constraint_model \<I> \<A>"
    and x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
  shows "(\<exists>n. \<I> x = Fun (Val n) []) \<or> (\<exists>n. \<I> x = Fun (PubConst Value n) [])"
proof -
  have x': "\<Gamma> (\<I> x) = TAtom Value" "fv (\<I> x) = {}" "wf\<^sub>t\<^sub>r\<^sub>m (\<I> x)"
    using reachable_constraints_fv_Value_typed[OF P A x] I wt_subst_trm''[of \<I> "Var x"]
    unfolding welltyped_constraint_model_def constraint_model_def by auto

  obtain f where f: "arity f = 0" "\<I> x = Fun f []"
    using TAtom_term_cases[OF x'(3,1)] x' const_type_inv_wf[of _ _ Value] by (cases "\<I> x") force+

  show ?thesis
  proof (cases f)
    case (Fu g) thus ?thesis by (metis f(2) x'(1) \<Gamma>_Fu_simps(4)[of g "[]"])
  qed (use f x'(1) in auto)
qed

lemma reachable_constraints_receive_attack_if_attack'':
  assumes P: "\<forall>T \<in> set P. admissible_transaction' T"
    and A: "\<A> \<in> reachable_constraints P"
    and wt_attack: "welltyped_constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
  shows "receive\<langle>[attack\<langle>n\<rangle>]\<rangle> \<in> set (unlabel \<A>)"
proof -
  have I: "welltyped_constraint_model \<I> \<A>"
    using welltyped_constraint_model_prefix wt_attack by blast

  show ?thesis
    using wt_attack strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" "[send\<langle>[attack\<langle>n\<rangle>]\<rangle>]" \<I>]
          reachable_constraints_receive_attack_if_attack'(2)[OF A(1) P I]
    unfolding welltyped_constraint_model_def constraint_model_def by simp
qed

context
begin

private lemma reachable_constraints_initial_value_transaction_aux:
  fixes P::"('fun,'atom,'sets,'lbl) prot" and N::"nat set"
  assumes P: "\<forall>T \<in> set P. admissible_transaction' T"
    and A: "A \<in> reachable_constraints P"
    and P':
      "\<forall>T \<in> set P. \<forall>(l,a) \<in> set (transaction_strand T). \<forall>t.
        a \<noteq> select\<langle>t,\<langle>k\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t in \<langle>k\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t not in \<langle>k\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> delete\<langle>t,\<langle>k\<rangle>\<^sub>s\<rangle>"
    shows "(l,\<langle>ac: t \<in> s\<rangle>) \<in> set A \<Longrightarrow> (\<exists>u. s = \<langle>u\<rangle>\<^sub>s \<and> u \<noteq> k)" (is "?A A \<Longrightarrow> ?Q A")
      and "(l,\<langle>t not in s\<rangle>) \<in> set A \<Longrightarrow> (\<exists>u. s = \<langle>u\<rangle>\<^sub>s \<and> u \<noteq> k)" (is "?B A \<Longrightarrow> ?Q A")
      and "(l,delete\<langle>t,s\<rangle>) \<in> set A \<Longrightarrow> (\<exists>u. s = \<langle>u\<rangle>\<^sub>s \<and> u \<noteq> k)" (is "?C A \<Longrightarrow> ?Q A")
proof -
  have "(?A A \<longrightarrow> ?Q A) \<and> (?B A \<longrightarrow> ?Q A) \<and> (?C A \<longrightarrow> ?Q A)" (is "?D A") using A
  proof (induction A rule: reachable_constraints.induct)
    case (step \<A> T \<xi> \<sigma> \<alpha>)
    define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
    let ?T' = "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"

    note T_adm = bspec[OF P step.hyps(2)]
    note T_wf = admissible_transaction_is_wellformed_transaction[OF T_adm]
    note T_P' = bspec[OF P' step.hyps(2)]

    have 0: "?Q ?T'" when A: "?A ?T'"
    proof -
      obtain t' s' where t:
          "(l, \<langle>ac: t' \<in> s'\<rangle>) \<in> set (transaction_strand T)" "t = t' \<cdot> \<theta>" "s = s' \<cdot> \<theta>"
        using A dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(6) subst_lsst_memD(6) by blast
      obtain u where u: "s' = \<langle>u\<rangle>\<^sub>s"
        using transaction_selects_are_Value_vars[OF T_wf(1,2), of t' s']
              transaction_inset_checks_are_Value_vars[OF T_adm, of t' s']
              unlabel_in[OF t(1)]
        by (cases ac) auto
      show ?thesis using T_P' t(1,3) unfolding u by (cases ac) auto
    qed

    have 1: "?Q ?T'" when B: "?B ?T'"
    proof -
      obtain t' s' where t:
          "(l, \<langle>t' not in s'\<rangle>) \<in> set (transaction_strand T)" "t = t' \<cdot> \<theta>" "s = s' \<cdot> \<theta>"
        using B dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(7) subst_lsst_memD(9) by blast
      obtain u where u: "s' = \<langle>u\<rangle>\<^sub>s"
        using transaction_notinset_checks_are_Value_vars(2)[OF T_adm unlabel_in[OF t(1)]]
        by fastforce
      show ?thesis using T_P' t(1,3) unfolding u by auto
    qed

    have 2: "?Q ?T'" when C: "?C ?T'"
    proof -
      obtain t' s' where t:
          "(l, delete\<langle>t', s'\<rangle>) \<in> set (transaction_strand T)" "t = t' \<cdot> \<theta>" "s = s' \<cdot> \<theta>"
        using C dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(5) subst_lsst_memD(5) by blast
      obtain u where u: "s' = \<langle>u\<rangle>\<^sub>s"
        using transaction_deletes_are_Value_vars(2)[OF T_wf(1,3) unlabel_in[OF t(1)]] by blast
      show ?thesis using T_P' t(1,3) unfolding u by auto
    qed

    show ?case using 0 1 2 step.IH unfolding \<theta>_def by auto
  qed simp
  thus "?A A \<Longrightarrow> ?Q A" "?B A \<Longrightarrow> ?Q A" "?C A \<Longrightarrow> ?Q A" by fast+
qed

lemma reachable_constraints_initial_value_transaction:
  fixes P::"('fun,'atom,'sets,'lbl) prot" and N::"nat set" and k A T_upds
  defines "checks_not_k \<equiv> \<lambda>B.
            T_upds \<noteq> [] \<longrightarrow> (
             (\<forall>l t s. (l,\<langle>t in s\<rangle>) \<in> set (A@B) \<longrightarrow> (\<exists>u. s = \<langle>u\<rangle>\<^sub>s \<and> u \<noteq> k)) \<and>
             (\<forall>l t s. (l,\<langle>t not in s\<rangle>) \<in> set (A@B) \<longrightarrow> (\<exists>u. s = \<langle>u\<rangle>\<^sub>s \<and> u \<noteq> k)) \<and>
             (\<forall>l t s. (l,delete\<langle>t,s\<rangle>) \<in> set (A@B) \<longrightarrow> (\<exists>u. s = \<langle>u\<rangle>\<^sub>s \<and> u \<noteq> k)))"
  assumes P: "\<forall>T \<in> set P. admissible_transaction' T"
    and A: "A \<in> reachable_constraints P"
    and N: "finite N" "\<forall>n \<in> N. \<not>(Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
    and T:
      "T \<in> set P" "Var x \<in> set T_ts" "\<Gamma>\<^sub>v x = TAtom Value" "fv\<^sub>s\<^sub>e\<^sub>t (set T_ts) = {x}"
      "\<forall>n. \<not>(Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set T_ts)"
      "T = Transaction (\<lambda>(). []) [x] [] [] T_upds [(l1,send\<langle>T_ts\<rangle>)]"
      "T_upds = [] \<or>
       (T_upds = [(l2,insert\<langle>Var x, \<langle>k\<rangle>\<^sub>s\<rangle>)] \<and>
        (\<forall>T \<in> set P. \<forall>(l,a) \<in> set (transaction_strand T). \<forall>t.
          a \<noteq> select\<langle>t,\<langle>k\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t in \<langle>k\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> \<langle>t not in \<langle>k\<rangle>\<^sub>s\<rangle> \<and> a \<noteq> delete\<langle>t,\<langle>k\<rangle>\<^sub>s\<rangle>))"
  shows "\<exists>B. A@B \<in> reachable_constraints P \<and> B \<in> reachable_constraints P \<and> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t B = {} \<and>
             (T_upds = [] \<longrightarrow> list_all is_Receive (unlabel B)) \<and> 
             (T_upds \<noteq> [] \<longrightarrow> list_all (\<lambda>a. is_Insert a \<or> is_Receive a) (unlabel B)) \<and>
             (\<forall>n. Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<longrightarrow> Fun (Val n) [] \<notin> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B) \<and>
             (\<forall>n. Fun (Val n) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<longrightarrow> Fun (Val n) [] \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B) \<and>
             N = {n. Fun (Val n) [] \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B} \<and>
             checks_not_k B \<and>
             (\<forall>l a. (l,a) \<in> set B \<and> is_Insert a \<longrightarrow>
                      (l = l2 \<and> (\<exists>n. a = insert\<langle>Fun (Val n) [],\<langle>k\<rangle>\<^sub>s\<rangle>)))"
    (is "\<exists>B. A@B \<in> ?reach P \<and> B \<in> ?reach P \<and> ?Q1 B \<and> ?Q2 B \<and> ?Q3 B \<and> ?Q4 B \<and> ?Q5 B \<and> ?Q6 N B \<and>
             checks_not_k B \<and> ?Q7 B")
using N
proof (induction N rule: finite_induct)
  case empty
  define B where "B \<equiv> []::('fun,'atom,'sets,'lbl) prot_constr"

  have 0: "A@B \<in> ?reach P" "B \<in> ?reach P"
    using A unfolding B_def by auto

  have 1: "?Q1 B" "?Q2 B" "?Q3 B" "?Q4 B" "?Q6 {} B"
    unfolding B_def by auto
  
  have 2: "checks_not_k B"
    using reachable_constraints_initial_value_transaction_aux[OF P 0(1)] T(7)
    unfolding checks_not_k_def by presburger

  have 3: "?Q5 B" "?Q7 B"
    unfolding B_def by simp_all

  show ?case using 0 1 2 3 by blast
next
  case (insert n N)
  obtain B where B:
      "A@B \<in> reachable_constraints P" "B \<in> reachable_constraints P"
      "?Q1 B" "?Q2 B" "?Q3 B" "?Q4 B" "?Q5 B" "?Q6 N B" "checks_not_k B" "?Q7 B"
    using insert.IH insert.prems by blast

  define \<xi> where "\<xi> \<equiv> Var::('fun,'atom,'sets,'lbl) prot_subst"

  define \<sigma> where "\<sigma> \<equiv> Var(x := Fun (Val n) [])::('fun,'atom,'sets,'lbl) prot_subst"

  have \<sigma>: "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B))"
  proof (unfold transaction_fresh_subst_def; intro conjI)
    have "subst_range \<sigma> = {Fun (Val n) []}" unfolding \<sigma>_def by simp
    moreover have "Fun (Val n) [] \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B))"
      using insert.prems insert.hyps(2) B(7,8) ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset[of "unlabel B"]
      unfolding unlabel_append trms\<^sub>s\<^sub>s\<^sub>t_append by blast
    ultimately show "\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B))" by fastforce
  next
    show "subst_domain \<sigma> = set (transaction_fresh T)" using T(6) unfolding \<sigma>_def by auto
  next
    show "\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms_transaction T)"
      using T(5,7) unfolding \<sigma>_def T(6) by fastforce
  qed (force simp add: T(3) \<sigma>_def wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)+
  hence \<sigma>': "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
    unfolding transaction_fresh_subst_def by fastforce

  have \<xi>: "transaction_decl_subst \<xi> T"
    using T(6) unfolding \<xi>_def transaction_decl_subst_def by fastforce

  obtain \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst" where \<alpha>:
      "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B))"
    unfolding transaction_renaming_subst_def by blast
  hence \<alpha>': "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
    unfolding transaction_renaming_subst_def by auto

  define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  define C where "C \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"

  have \<theta>x: "\<theta> x = Fun (Val n) []" unfolding \<theta>_def \<xi>_def \<sigma>_def subst_compose by force

  have "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = []" "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = []"
    using T(6) unfolding \<theta>_def \<xi>_def \<sigma>_def by auto
  moreover have
      "(T_upds = [] \<and> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = []) \<or>
       (T_upds \<noteq> [] \<and> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = [(l2,insert\<langle>\<theta> x, \<langle>k\<rangle>\<^sub>s\<rangle>)])"
    using subst_lsst_cons[of "(l2,insert\<langle>Var x,\<langle>k\<rangle>\<^sub>s\<rangle>)" "[]" \<theta>] T(6,7) unfolding dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst by auto
  hence "(T_upds = [] \<and> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = []) \<or>
         (T_upds \<noteq> [] \<and> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = [(l2,insert\<langle>Fun (Val n) [],\<langle>k\<rangle>\<^sub>s\<rangle>)])"
    unfolding \<theta>_def \<xi>_def \<sigma>_def by (auto simp: subst_compose)
  moreover have "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = [(l1, receive\<langle>T_ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>)]"
    using subst_lsst_cons[of "(l1, receive\<langle>T_ts\<rangle>)" "[]" \<theta>] T(6) unfolding dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst by auto
  hence "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = [(l1, receive\<langle>T_ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>)]"
    by auto
  ultimately have C:
      "(T_upds = [] \<and> C = [(l1, receive\<langle>T_ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>)]) \<or>
       (T_upds \<noteq> [] \<and> C = [(l2, insert\<langle>Fun (Val n) [],\<langle>k\<rangle>\<^sub>s\<rangle>), (l1, receive\<langle>T_ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>)])"
    unfolding C_def transaction_dual_subst_unfold by force

  have C': "Fun (Val n) [] \<in> set (T_ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>)" "Fun (Val n) [] \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t C"
    using T(2) in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of _ "unlabel C"] C
    unfolding \<theta>_def \<xi>_def \<sigma>_def by (force, force)

  have "fv (t \<cdot> \<theta>) = {}" when t: "t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set T_ts" for t
  proof -
    have  "fv t \<subseteq> {x}" using t T(4) fv_subset_subterms by blast
    hence "fv (t \<cdot> \<xi> \<circ>\<^sub>s \<sigma>) = {}" unfolding \<xi>_def \<sigma>_def by (induct t) auto
    thus ?thesis unfolding \<theta>_def by (metis subst_ground_ident_compose(2))
  qed
  hence 1: "ground (set (T_ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>))" by auto

  have 2: "m = n" when m: "Fun (Val m) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t C" for m
  proof -
    have "Fun (Val m) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set (T_ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>)"
      using m C in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of _ "unlabel C"] by fastforce
    hence *: "Fun (Val m) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set T_ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>" by simp
    show ?thesis using const_subterms_subst_cases[OF *] T(4,5) \<theta>x by fastforce
  qed

  have C_trms: "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t C \<subseteq> {Fun (Val n) [],\<langle>k\<rangle>\<^sub>s} \<union> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t C"
    using C in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of _ "unlabel C"] by fastforce

  have 3: "m = n" when m: "Fun (Val m) [] \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t C" for m
    using m 2[of m] C_trms by fastforce

  have Q1: "?Q1 (B@C)" using B(3) C 1 by auto
  have Q2: "?Q2 (B@C)" using B(4) C by force
  have Q3: "?Q3 (B@C)" using B(5) C by force
  have Q4: "?Q4 (B@C)" using B(6) insert.prems C 2 unfolding unlabel_append ik\<^sub>s\<^sub>s\<^sub>t_append by blast
  have Q5: "?Q5 (B@C)" using B(7) C' 3 unfolding unlabel_append ik\<^sub>s\<^sub>s\<^sub>t_append trms\<^sub>s\<^sub>s\<^sub>t_append by blast
  have Q6: "?Q6 (insert n N) (B@C)" using B(8) C' 2 unfolding unlabel_append ik\<^sub>s\<^sub>s\<^sub>t_append by blast
  have Q7: "?Q7 (B@C)" using B(10) C by fastforce
  have Q8: "checks_not_k (B@C)" using B(9) C unfolding checks_not_k_def by force

  have "B@C \<in> reachable_constraints P" "A@B@C \<in> reachable_constraints P"
    using reachable_constraints.step[OF B(1) T(1) \<xi> \<sigma> \<alpha>]
          reachable_constraints.step[OF B(2) T(1) \<xi> \<sigma>' \<alpha>']
    unfolding \<theta>_def[symmetric] C_def[symmetric] by simp_all
  thus ?case using Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 by blast
qed

end


subsection \<open>Equivalence Between the Symbolic Protocol Model and a Ground Protocol Model\<close>

context
begin

subsubsection \<open>Intermediate Step: Equivalence to a Ground Protocol Model with Renaming\<close>

private definition "consts_of X = {t. t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t X \<and> (\<exists>c. t = Fun c [])}"

private fun mk_symb where
  "mk_symb (\<xi>, \<sigma>, I, T, \<alpha>) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t((transaction_strand T) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

private fun T_symb :: " _ \<Rightarrow> ('fun,'atom,'sets,'lbl) prot_constr" where
  "T_symb w = concat (map mk_symb w)"


private definition "narrow \<sigma> S = (\<lambda>x. if x \<in> S then \<sigma> x else Var x)"

private fun mk_inv\<alpha>I where
  "mk_inv\<alpha>I n (\<xi>, \<sigma>, I, T) =
    narrow ((var_rename_inv n) \<circ>\<^sub>s I) (fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s var_rename n))"

private fun inv\<alpha>I where
  "inv\<alpha>I ns w = foldl (\<circ>\<^sub>s) Var (map2 mk_inv\<alpha>I ns w)"

private fun mk_I where
  "mk_I (\<xi>, \<sigma>, I, T, \<alpha>) = narrow I (fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"

private fun comb_I where
  "comb_I w = fold (\<circ>\<^sub>s) (map mk_I w) (\<lambda>x. Fun OccursSec [])"

private abbreviation "ground_term t \<equiv> ground {t}"

private lemma ground_term_def2: "ground_term t \<longleftrightarrow> (fv t = {})"
  by auto

private definition "ground_strand s \<equiv> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t s = {}"

private fun ground_step :: "(_, _) stateful_strand_step \<Rightarrow> bool" where
  "ground_step s \<longleftrightarrow> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p s = {}"

private fun ground_lstep :: "_ strand_label \<times> (_, _) stateful_strand_step \<Rightarrow> bool" where
  "ground_lstep (l,s) \<longleftrightarrow> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p s = {}"


private inductive_set ground_protocol_states_aux::
  "('fun,'atom,'sets,'lbl) prot \<Rightarrow>
   (('fun,'atom,'sets,'lbl) prot_terms \<times>
    (('fun,'atom,'sets,'lbl) prot_term \<times> ('fun,'atom,'sets,'lbl) prot_term) set
    \<times> _ set \<times> _ set \<times> _ list) set"
  for P::"('fun,'atom,'sets,'lbl) prot"
where
  init:
  "({},{},{},{},[]) \<in> ground_protocol_states_aux P"
| step:
  "\<lbrakk>(IK,DB,trms,vars,w) \<in> ground_protocol_states_aux P;
    T \<in> set P;
    transaction_decl_subst \<xi> T;
    transaction_fresh_subst \<sigma> T trms;
    transaction_renaming_subst \<alpha> P vars;
    A = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>);
    strand_sem_stateful IK DB (unlabel A) I;
    interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I;
    wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)
   \<rbrakk> \<Longrightarrow> (IK \<union> ((ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I), dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB,
          trms \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A, vars \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A,
          w@[(\<xi>, \<sigma>, I, T, \<alpha>)]) \<in> ground_protocol_states_aux P"

private lemma T_symb_append':
  " T_symb (w@w') = T_symb w @ T_symb w'"
proof (induction w arbitrary: w')
  case Nil
  then show ?case
    by auto
next
  case (Cons a w)
  then show ?case
    by auto
qed

private lemma T_symb_append:
  "T_symb (w@[(\<xi>, \<sigma>, I, T, \<alpha>)]) = T_symb w @ dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t((transaction_strand T) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
using T_symb_append'[of w "[(\<xi>, \<sigma>, I, T,\<alpha>)]"] by auto

private lemma ground_step_subst:
  assumes "ground_step a"
  shows "a = a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>"
using assms 
proof (induction a)
  case (NegChecks Y F F')
  then have FY: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set Y = {}"
    unfolding ground_step.simps
    unfolding fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p.simps by auto
  {  
    have "\<forall>t s. (t,s) \<in> set F \<longrightarrow> t \<cdot> (rm_vars (set Y) \<sigma>) = t"
    proof (rule, rule, rule)
      fix t s 
      assume "(t, s) \<in> set F"
      then show "t \<cdot> rm_vars (set Y) \<sigma> = t"
        using FY by fastforce                      
    qed
    moreover
    have "\<forall>t s. (t,s) \<in> set F \<longrightarrow> s \<cdot> (rm_vars (set Y) \<sigma>) = s"
    proof (rule, rule, rule)
      fix t s 
      assume "(t, s) \<in> set F"
      then show "s \<cdot> rm_vars (set Y) \<sigma> = s"
        using FY by fastforce                      
    qed
    ultimately
    have "\<forall>f \<in> set F. f \<cdot>\<^sub>p (rm_vars (set Y) \<sigma>) = f"
      by auto
    then have "F = F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set Y) \<sigma>"
      by (metis (no_types, lifting) map_idI split_cong subst_apply_pairs_def)
  }
  moreover
  from NegChecks have F'Y: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' - set Y = {}"
    unfolding ground_step.simps
    unfolding fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p.simps by auto
  {  
    have "\<forall>t s. (t,s) \<in> set F' \<longrightarrow> t \<cdot> (rm_vars (set Y) \<sigma>) = t"
    proof (rule, rule, rule)
      fix t s 
      assume "(t, s) \<in> set F'"
      then show "t \<cdot> rm_vars (set Y) \<sigma> = t"
        using F'Y by fastforce                      
    qed
    moreover
    have "\<forall>t s. (t,s) \<in> set F' \<longrightarrow> s \<cdot> (rm_vars (set Y) \<sigma>) = s"
    proof (rule, rule, rule)
      fix t s 
      assume "(t, s) \<in> set F'"
      then show "s \<cdot> rm_vars (set Y) \<sigma> = s"
        using F'Y by fastforce                      
    qed
    ultimately
    have "\<forall>f \<in> set F'. f \<cdot>\<^sub>p (rm_vars (set Y) \<sigma>) = f"
      by auto
    then have "F' = F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set Y) \<sigma>"
      by (simp add: map_idI subst_apply_pairs_def)
  }
  ultimately
  show ?case 
    by simp
qed (auto simp add: map_idI subst_ground_ident)

private lemma ground_lstep_subst:
  assumes "ground_lstep a"
  shows "a = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>"
using assms by (cases a) (auto simp add: ground_step_subst)

private lemma subst_apply_term_rm_vars_swap:
  assumes "\<forall>x\<in>fv t - set X. I x = I' x"
  shows "t \<cdot> rm_vars (set X) I = t \<cdot> rm_vars (set X) I'"
using assms by (induction t) auto

private lemma subst_apply_pairs_rm_vars_swap:
  assumes "\<forall>x\<in>\<Union> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r ` set ps) - set X. I x = I' x"
  shows "ps \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) I = ps \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) I'"
proof -
  have "\<forall>p \<in> set ps. p \<cdot>\<^sub>p rm_vars (set X) I = p  \<cdot>\<^sub>p rm_vars (set X) I'"
  proof
    fix p
    assume "p \<in> set ps"
    obtain t s where "p = (t,s)"
      by (cases p) auto
    have "\<forall>x\<in>fv t - set X. I x = I' x"
      by (metis DiffD1 DiffD2 DiffI \<open>p = (t, s)\<close> \<open>p \<in> set ps\<close> assms fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.elims fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_inI(4))
    then have "t \<cdot> rm_vars (set X) I = t \<cdot> rm_vars (set X) I'"
      using subst_apply_term_rm_vars_swap by blast
    have "\<forall>x\<in>fv s - set X. I x = I' x"
      by (metis DiffD1 DiffD2 DiffI \<open>p = (t, s)\<close> \<open>p \<in> set ps\<close> assms fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.elims fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_inI(5))
    then have "s \<cdot> rm_vars (set X) I = s \<cdot> rm_vars (set X) I'"
      using subst_apply_term_rm_vars_swap by blast
    show "p \<cdot>\<^sub>p rm_vars (set X) I = p \<cdot>\<^sub>p rm_vars (set X) I'"
      using \<open>p = (t, s)\<close> \<open>s \<cdot> rm_vars (set X) I = s \<cdot> rm_vars (set X) I'\<close>
            \<open>t \<cdot> rm_vars (set X) I = t \<cdot> rm_vars (set X) I'\<close>
      by fastforce
  qed
  then show ?thesis
    unfolding subst_apply_pairs_def by auto
qed

private lemma subst_apply_stateful_strand_step_swap:
  assumes "\<forall>x\<in>fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p T. I x = I' x"
  shows "T \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p I = T  \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p I'"
  using assms
proof (induction T)
  case (Send ts)
  then show ?case
    using term_subst_eq by fastforce
next
  case (NegChecks X F G)
  then have "\<forall>x \<in> \<Union>(fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r ` set F) \<union> \<Union>(fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r ` set G) - set X. I x = I' x"
    by auto
  then show ?case
    using subst_apply_pairs_rm_vars_swap[of F]
          subst_apply_pairs_rm_vars_swap[of G]
    by auto
qed (simp_all add: term_subst_eq_conv)

private lemma subst_apply_labeled_stateful_strand_step_swap:
  assumes "\<forall>x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd T). I x = I' x"
  shows "T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p I = T  \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p I'"
using assms subst_apply_stateful_strand_step_swap
by (metis prod.exhaust_sel subst_apply_labeled_stateful_strand_step.simps) 

private lemma subst_apply_labeled_stateful_strand_swap:
  assumes "\<forall>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T. I x = I' x"
  shows "T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I = T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I'"
  using assms
proof (induction T)
  case Nil
  then show ?case
    by auto
next
  case (Cons a T)
  then show ?case
    using subst_apply_labeled_stateful_strand_step_swap
    by (metis UnCI fv\<^sub>s\<^sub>s\<^sub>t_Cons subst_lsst_cons unlabel_Cons(2))
qed

private lemma transaction_renaming_subst_not_in_fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t:
  fixes \<xi> \<sigma> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
    and A::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  assumes "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  shows "x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
proof -
  have 0: "x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<alpha>)"
    when x: "x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      and \<alpha>: "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
    for x
      and A::"('fun,'atom,'sets,'lbl) prot_constr"
      and \<xi> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst" 
  proof -
    have "x \<notin> range_vars \<alpha>"
      using x \<alpha> transaction_renaming_subst_vars_disj(6) by blast
    moreover
    have "subst_domain \<alpha> = UNIV"
      using \<alpha> transaction_renaming_subst_is_renaming(4) by blast
    ultimately
    show ?thesis
      using subst_fv_dom_img_subset[of _ \<alpha>] fv\<^sub>s\<^sub>s\<^sub>t_subst_obtain_var subst_compose unlabel_subst
      by (metis (no_types, opaque_lifting) subset_iff top_greatest)
  qed

  have 1: "x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<alpha>)"
    when x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      and \<alpha>: "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
    for x
      and A::"('fun,'atom,'sets,'lbl) prot_constr"
      and \<xi> \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
    using \<alpha> x 0 by (metis Un_iff vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t)

  show ?thesis using 1 assms by metis
qed

private lemma wf_comb_I_Nil: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (comb_I []))"
  by auto

private lemma comb_I_append:
  "comb_I (w @ [(\<xi>, \<sigma>, I, T, \<alpha>)]) = (mk_I (\<xi>, \<sigma>, I, T, \<alpha>) \<circ>\<^sub>s (comb_I w))"
by auto

private lemma reachable_constraints_if_ground_protocol_states_aux:
  assumes "(IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P"
  shows "T_symb w \<in> reachable_constraints P
         \<and> constr_sem_stateful (comb_I w) (unlabel (T_symb w))
         \<and> IK = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((T_symb w) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t (comb_I w))
         \<and> DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel ((T_symb w))) (comb_I w) {}
         \<and> trms = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)
         \<and> vars = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)
         \<and> interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (comb_I w)
         \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (comb_I w))"
  using assms
proof (induction rule: ground_protocol_states_aux.induct)
  case init
  show ?case
    using wf_comb_I_Nil by auto
next
  case (step IK DB trms vars w T \<xi> \<sigma> \<alpha> A I)
  then have step': "T_symb w \<in> reachable_constraints P"
    "strand_sem_stateful {} {} (unlabel (T_symb w)) (comb_I w)"
    "IK = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w)"
    "DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w) {}"
    "trms = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)"
    "vars = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)"
    "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (comb_I w)"
    "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (comb_I w))"
    by auto

  define w' where "w' = w @ [(\<xi>, \<sigma>, I, T, \<alpha>)]"

  have interps_w: "\<forall>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w). (comb_I w) x = (comb_I w') x"
  proof 
    fix x
    assume "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)"
    then have "x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      using step(5) transaction_renaming_subst_not_in_fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t unfolding step'(6) by blast
    then have "mk_I (\<xi>, \<sigma>, I, T, \<alpha>) x = Var x"
      unfolding mk_I.simps narrow_def by metis
    then have "comb_I w x = (mk_I (\<xi>, \<sigma>, I, T, \<alpha>) \<circ>\<^sub>s (comb_I (w))) x"
      by (simp add: subst_compose)
    then show "comb_I w x = comb_I w' x"
      unfolding w'_def by auto
  qed

  have interps_T: "\<forall>x \<in> fv\<^sub>s\<^sub>s\<^sub>t (unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>))). I x = (comb_I w') x"
  proof 
    fix x
    assume "x \<in> fv\<^sub>s\<^sub>s\<^sub>t (unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>)))"
    then have a: "x \<in> (fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      by (metis fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq mk_symb.simps)
    have "(comb_I w') x = (mk_I (\<xi>, \<sigma>, I, T, \<alpha>) \<circ>\<^sub>s (comb_I (w))) x"
      unfolding w'_def by auto
    also
    have "... = ((mk_I (\<xi>, \<sigma>, I, T, \<alpha>)) x) \<cdot> comb_I w"
      unfolding subst_compose by auto
    also
    have "... = (narrow I (fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) x) \<cdot> comb_I w"
      using a by auto
    also
    have "... = (I x) \<cdot> comb_I w"
      by (metis a narrow_def)
    also
    have "... = I x"
      by (metis UNIV_I ground_subst_range_empty_fv step.hyps(8) subst_compose
                subst_ground_ident_compose(1))
    finally
    show "I x = (comb_I w') x"
      by auto
  qed

  have "T_symb w' \<in> reachable_constraints P"
  proof -
    have "T_symb w \<in> reachable_constraints P"
      using step'(1) .
    moreover
    have "T \<in> set P"
      using step(2) by auto
    moreover
    have "transaction_decl_subst \<xi> T"
      using step(3) by auto
    moreover
    have "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w))"
      using step(4) step'(5) by auto
    moreover
    have "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w))"
      using step(5) step'(6) by auto
    ultimately
    have "(T_symb w) @ mk_symb (\<xi>, \<sigma>, I, T, \<alpha>) \<in> reachable_constraints P"
      using reachable_constraints.step[of "T_symb w" P T \<xi> \<sigma> \<alpha>] by auto
    then show "T_symb w' \<in> reachable_constraints P"
      unfolding w'_def by auto
  qed
  moreover
  have "strand_sem_stateful {} {} (unlabel (T_symb w')) (comb_I w')"
  proof -
    have "strand_sem_stateful {} {} (unlabel (T_symb w)) (comb_I w')"
    proof -
      have "strand_sem_stateful {} {} (unlabel (T_symb w)) (comb_I w)"
        using step'(2) by auto
      then show "strand_sem_stateful {} {} (unlabel (T_symb w)) (comb_I w')"
        using interps_w strand_sem_model_swap by blast
    qed
    moreover
    have "strand_sem_stateful
            (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<cdot>\<^sub>s\<^sub>e\<^sub>t comb_I w')
            (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w') {})
            (unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>)))
            (comb_I w')"
    proof -
      have "A = (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>))"
        unfolding step(6) by auto
      moreover
      have "strand_sem_stateful
              (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w))
              (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w) {})
              (unlabel A)
              I"
        using step'(3) step'(4) step.hyps(7) by force
      moreover
      {
        have "\<forall>x\<in>fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)). comb_I w x = comb_I w' x"
          using interps_w by (metis fv_ik\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t)
        then have "\<forall>x\<in>fv t. comb_I w x = comb_I w' x" when t: "t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)" for t
          using t by auto
        then have "t \<cdot> comb_I w' = t \<cdot> comb_I w" when t: "t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)" for t
          using t term_subst_eq[of t "comb_I w'" "comb_I w"] by metis
        then have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<cdot>\<^sub>s\<^sub>e\<^sub>t comb_I w' = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<cdot>\<^sub>s\<^sub>e\<^sub>t comb_I w"
          by auto
        also
        have "... = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w)"
          by (metis ik\<^sub>s\<^sub>s\<^sub>t_subst unlabel_subst)
        finally
        have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<cdot>\<^sub>s\<^sub>e\<^sub>t comb_I w' = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w)"
          by auto
      }
      moreover
      {
        have "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w) {} =
              dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w') {}"
          by (metis db\<^sub>s\<^sub>s\<^sub>t_subst_swap[OF interps_w] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t empty_set)
      }
      ultimately
      have "strand_sem_stateful
              (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<cdot>\<^sub>s\<^sub>e\<^sub>t comb_I w')
              (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w') {})
              (unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>)))
              I"
        by force
      then show "strand_sem_stateful
                  (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<cdot>\<^sub>s\<^sub>e\<^sub>t comb_I w')
                  (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w') {})
                  (unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>)))
                  (comb_I w')"
        using interps_T strand_sem_model_swap[of "unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>))" I "comb_I w'"]
        by force 
    qed
    ultimately
    show "strand_sem_stateful {} {} (unlabel (T_symb w')) (comb_I w')"
      using strand_sem_append_stateful[
              of "{}" "{}" "unlabel (T_symb w)" "unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>))" "(comb_I w')"]
      unfolding w'_def by auto
  qed
  moreover
  have "IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w' \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w')"
  proof -
    have AI: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      by (metis ik\<^sub>s\<^sub>s\<^sub>t_subst unlabel_subst)

    have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w' \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w') = 
           ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w') \<union> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb [(\<xi>, \<sigma>, I, T, \<alpha>)] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w')"
      unfolding w'_def by (simp add: subst_lsst_append)
    also 
    have "... = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w') \<union> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb [(\<xi>, \<sigma>, I, T, \<alpha>)] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)"
      by (metis T_symb_append T_symb_append' interps_T mk_symb.simps self_append_conv2
                subst_apply_labeled_stateful_strand_swap)
    also
    have "... = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w) \<union> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb [(\<xi>, \<sigma>, I, T, \<alpha>)] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)"
      by (metis interps_w subst_apply_labeled_stateful_strand_swap)
    also 
    have "... = IK \<union> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)"
      using step'(3) step.hyps(6) by auto
    also
    have "... = IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A  \<cdot>\<^sub>s\<^sub>e\<^sub>t I)"
      unfolding AI by auto
    finally
    show "IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w' \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w')"
      using step'(3) step(6) T_symb.simps mk_symb.simps by auto
  qed
  moreover
  have "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w')) (comb_I w') {}"
  proof -
    have "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB =
          dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w) {})"
      using step'(4) by auto
    moreover
    have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))) I
                        (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w) {})"
      using step(6) by auto
    moreover
    have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>))) I
                        (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w) {})"
      by auto
    moreover
    have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>))) (comb_I w')
                        (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w) {})"
      by (metis (no_types, lifting) db\<^sub>s\<^sub>s\<^sub>t_subst_swap[OF interps_T] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t empty_set)
    moreover
    have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>))) (comb_I w')
                        (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w') {})"
      by (metis (no_types, lifting) db\<^sub>s\<^sub>s\<^sub>t_subst_swap[OF interps_w] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t empty_set)
    moreover
    have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w) @ unlabel (mk_symb (\<xi>, \<sigma>, I, T, \<alpha>))) (comb_I w') {}"
      using dbupd\<^sub>s\<^sub>s\<^sub>t_append by metis
    moreover
    have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel ((T_symb w) @ mk_symb (\<xi>, \<sigma>, I, T, \<alpha>))) (comb_I w') {}"
      by auto
    moreover
    have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w')) (comb_I w') {}"
      unfolding w'_def by auto
    ultimately
    show "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w')) (comb_I w') {}"
      by auto
  qed
  moreover
  have "trms \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w')"
  proof -
    have "trms \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      using step'(5) by auto
    moreover
    have "... = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      using step(6) by auto
    moreover 
    have "... = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb [(\<xi>, \<sigma>, I, T, \<alpha>)])"
      by auto
    moreover
    have "... = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w @ T_symb [(\<xi>, \<sigma>, I, T, \<alpha>)])"
      by auto
    moreover
    have "... = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w')"
      unfolding w'_def by auto
    ultimately
    show "trms \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w')"
      by auto
  qed
  moreover
  have "vars \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w')"
  proof -
    have "vars \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      using step'(6) by fastforce
    moreover
    have "... = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
      using step(6) by auto
    moreover 
    have "... = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb [(\<xi>, \<sigma>, I, T, \<alpha>)])"
      by auto
    moreover
    have "... = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w @ T_symb [(\<xi>, \<sigma>, I, T, \<alpha>)])"
      by auto
    moreover
    have "... = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w')"
      unfolding w'_def by auto
    ultimately
    show "vars \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w')"
      using step(6) by auto
  qed
  moreover
  have interp_comb_I_w': "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (comb_I w')"
    using interpretation_comp(1) step'(7) unfolding w'_def by auto
  moreover
  have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (comb_I w'))"
  proof 
    fix t
    assume "t \<in> subst_range (comb_I w')"
    then have "\<exists>x. x \<in> subst_domain (comb_I w') \<and> t = comb_I w' x"
      by auto
    then obtain x where "x \<in> subst_domain (comb_I w')" "t = comb_I w' x"
      by auto
    then show "wf\<^sub>t\<^sub>r\<^sub>m t"
      by (metis (no_types, lifting) w'_def interp_comb_I_w' comb_I_append ground_subst_dom_iff_img
                  mk_I.simps narrow_def step'(8) step.hyps(8) step.hyps(9) subst_compose_def
                  wf_trm_Var wf_trm_subst)
  qed
  ultimately
  show ?case
    unfolding w'_def by auto
qed

private lemma ground_protocol_states_aux_if_reachable_constraints:
  assumes "A \<in> reachable_constraints P"
  assumes "constr_sem_stateful I (unlabel A)"
  assumes "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
  shows "\<exists>w. (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I, dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I {}, trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A, vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A, w)
              \<in> ground_protocol_states_aux P"
using assms
proof (induction rule: reachable_constraints.induct)
  case init
  then show ?case
    using ground_protocol_states_aux.init by auto 
next
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  have "\<exists>w. (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t I, dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) I {}, trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>, vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>, w)
              \<in> ground_protocol_states_aux P"
    by (metis local.step(6,7,8,9) step.IH strand_sem_append_stateful unlabel_append)
  then obtain w where w_p:
      "(ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t I, dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) I {}, trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>, vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>, w)
        \<in> ground_protocol_states_aux P"
    by auto

  define w' where "w' = w@[(\<xi>, \<sigma>, I, T, \<alpha>)]"
  define \<A>' where "\<A>' = \<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  let ?T = "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"

  have "T \<in> set P"
    using step.hyps(2) .
  moreover
  have "transaction_decl_subst \<xi> T"
    using step.hyps(3) .
  moreover
  have "transaction_fresh_subst \<sigma> T (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    using step.hyps(4) .
  moreover
  have "transaction_renaming_subst \<alpha> P (vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    using step.hyps(5) .
  moreover
  have "strand_sem_stateful (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t I) (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) I {}) ?T I"
    using step(7) strand_sem_append_stateful[of "{}"  "{}" "unlabel \<A>" ?T I]
    by auto
  moreover
  have "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
    using assms(3) .
  moreover
  have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
    using step.prems(3) by fastforce
  ultimately
  have "((ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<union> (ik\<^sub>s\<^sub>s\<^sub>t ?T \<cdot>\<^sub>s\<^sub>e\<^sub>t I),
         dbupd\<^sub>s\<^sub>s\<^sub>t ?T I (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) I {}),
         trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<union> trms\<^sub>s\<^sub>s\<^sub>t ?T,
         vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<union> vars\<^sub>s\<^sub>s\<^sub>t ?T,
         w@[(\<xi>, \<sigma>, I, T, \<alpha>)])
      \<in> ground_protocol_states_aux P"
    using ground_protocol_states_aux.step[
            OF w_p,
            of T \<xi> \<sigma> \<alpha> "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" I]
    by metis
  moreover
  have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<cdot>\<^sub>s\<^sub>e\<^sub>t I = (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<union> (ik\<^sub>s\<^sub>s\<^sub>t ?T \<cdot>\<^sub>s\<^sub>e\<^sub>t I)"
    unfolding \<A>'_def by auto
  moreover
  have "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>') I {} = dbupd\<^sub>s\<^sub>s\<^sub>t ?T I (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) I {})"
    unfolding \<A>'_def by (simp add: dbupd\<^sub>s\<^sub>s\<^sub>t_append) 
  moreover
  have "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<union> trms\<^sub>s\<^sub>s\<^sub>t ?T"
    unfolding \<A>'_def by auto
  moreover
  have "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<union> vars\<^sub>s\<^sub>s\<^sub>t ?T"
    unfolding \<A>'_def by auto
  ultimately
  have "(ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<cdot>\<^sub>s\<^sub>e\<^sub>t I, dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>') I {}, trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>', vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>', w')
          \<in> ground_protocol_states_aux P"
    using w'_def by auto
  then show ?case 
    unfolding \<A>'_def w'_def by auto
qed

private lemma protocol_model_equivalence_aux1:
  "{(IK, DB) | IK DB. \<exists>w trms vars. (IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P} = 
   {(ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I), dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I {}) | A I.
      A \<in> reachable_constraints P \<and> strand_sem_stateful {} {} (unlabel A) I \<and>
      interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)}"
proof (rule; rule; rule)
  fix IK DB
  assume "(IK, DB) \<in>
            {(IK, DB) | IK DB. \<exists>w trms vars. (IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P}"
  then have "\<exists>w trms vars. (IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P"
    by auto
  then obtain w trms vars where "(IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P"
    by auto
  then have reachable:
      "T_symb w \<in> reachable_constraints P"
      "strand_sem_stateful {} {} (unlabel (T_symb w)) (comb_I w)"
      "IK = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t comb_I w)"
      "DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w) {}"
      "trms = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)"
      "vars = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)" 
      "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (comb_I w)"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (comb_I w))"
    using reachable_constraints_if_ground_protocol_states_aux[of IK DB trms vars w P] by auto
  then have
      "IK = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t (comb_I w))"
      "DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel (T_symb w)) (comb_I w) {}"
      "T_symb w \<in> reachable_constraints P"
      "strand_sem_stateful {} {} (unlabel (T_symb w)) (comb_I w)"
      "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (comb_I w) \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (comb_I w))"
    by auto
  then show "\<exists>A I. (IK, DB) = (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I), dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I {}) \<and>
                   A \<in> reachable_constraints P \<and> strand_sem_stateful {} {} (unlabel A) I \<and>
                   interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
    by blast
next
  fix IK DB
  assume "(IK, DB) \<in>
            {(ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I), dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I {}) | A I.
              A \<in> reachable_constraints P \<and> strand_sem_stateful {} {} (unlabel A) I \<and>
              interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)}"
  then obtain A I where A_I_p:
     "IK = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)"
     "DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I {}"
     "A \<in> reachable_constraints P"
     "strand_sem_stateful {} {} (unlabel A) I"
     "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
     "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" 
    by auto
  then have "\<exists>w. (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I, dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I {}, trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A, vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A, w)
                  \<in> ground_protocol_states_aux P"
    using ground_protocol_states_aux_if_reachable_constraints[of A P I] by auto
  then have "\<exists>w. (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I, DB, trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A, vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A, w) \<in> ground_protocol_states_aux P"
    using A_I_p by blast
  then have "\<exists>w. (ik\<^sub>s\<^sub>s\<^sub>t (unlabel A \<cdot>\<^sub>s\<^sub>s\<^sub>t I), DB, trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A, vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A, w) \<in> ground_protocol_states_aux P"
    by (simp add: ik\<^sub>s\<^sub>s\<^sub>t_subst)
  then have "(\<exists>w trms vars. (IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P)"
    by (metis (no_types) A_I_p(1) unlabel_subst)
  then show "\<exists>IK' DB'. (IK, DB) = (IK', DB') \<and>
                       (\<exists>w trms vars. (IK', DB', trms, vars, w) \<in> ground_protocol_states_aux P)"
    by auto
qed

subsubsection \<open>The Protocol Model Equivalence Proof\<close>

private lemma subst_ground_term_ident:
  assumes "ground_term t"
  shows "t \<cdot> I = t"
using assms by (simp add: subst_ground_ident)

private lemma subst_comp_rm_vars_eq:
  fixes \<delta> :: "('fun,'atom,'sets,'lbl) prot_subst"
  fixes \<alpha> :: "('fun,'atom,'sets,'lbl) prot_subst"
  fixes I :: "('fun,'atom,'sets,'lbl) prot_subst"
  assumes "subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)"
  shows "(\<delta> \<circ>\<^sub>s \<alpha>) = (\<delta> \<circ>\<^sub>s (rm_vars (set X) \<alpha>))"
proof (rule ext)
  fix x
  show "(\<delta> \<circ>\<^sub>s \<alpha>) x = (\<delta> \<circ>\<^sub>s rm_vars (set X) \<alpha>) x"
  proof (cases "x \<in> set X")
    case True
    have gt: "ground_term (\<delta> x)"
      using True assms by auto

    have "(\<delta> \<circ>\<^sub>s \<alpha>) x = (\<delta> x) \<cdot> \<alpha>"
      using subst_compose by metis
    also
    have "... = \<delta> x"
      using gt subst_ground_term_ident by blast
    also
    have "... = (\<delta> x) \<cdot> (rm_vars (set X) \<alpha>)"
      using gt subst_ground_term_ident by fastforce 
    also
    have "... = (\<delta> \<circ>\<^sub>s (rm_vars (set X) \<alpha>)) x"
      using subst_compose by metis
    ultimately
    show ?thesis
      by auto
  next
    case False
    have delta_x: "\<delta> x = Var x"
      using False assms by blast
    have "(rm_vars (set X) \<alpha>) x = \<alpha> x"
      using False by auto

    have "(\<delta> \<circ>\<^sub>s \<alpha>) x = (\<delta> x) \<cdot> \<alpha>"
      using subst_compose by metis
    also
    have "... = (Var x) \<cdot> \<alpha>"
      using delta_x by presburger
    also
    have "... = (Var x) \<cdot> (rm_vars (set X) \<alpha>)"
      using False by force
    also
    have "... = (\<delta> x) \<cdot> (rm_vars (set X) \<alpha>)"
      using delta_x by presburger
    also
    have "... = (\<delta> \<circ>\<^sub>s (rm_vars (set X) \<alpha>)) x"
      using subst_compose by metis
    finally
    show ?thesis 
      by auto
  qed
qed

private lemma subst_comp_rm_vars_commute:
  assumes "\<forall>x\<in>set X. \<forall>y. \<alpha> y \<noteq> Var x"
  assumes "subst_range \<alpha> \<subseteq> range Var"
  assumes "subst_domain \<delta> = set X"
  assumes "ground (subst_range \<delta>)"
  shows "(\<delta> \<circ>\<^sub>s (rm_vars (set X) \<alpha>)) = (rm_vars (set X) \<alpha> \<circ>\<^sub>s \<delta>)"
proof (rule ext)
  fix x
  show "(\<delta> \<circ>\<^sub>s rm_vars (set X) \<alpha>) x = (rm_vars (set X) \<alpha> \<circ>\<^sub>s \<delta>) x"
  proof (cases "x \<in> set X")
    case True
    then have gt: "ground_term (\<delta> x)"
      using True assms(3,4) by auto

    have "(\<delta> \<circ>\<^sub>s (rm_vars (set X) \<alpha>)) x = \<delta> x \<cdot> rm_vars (set X) \<alpha>"
      by (simp add: subst_compose)
    also
    have "... = \<delta> x"
      using gt by auto
    also
    have "... = ((rm_vars (set X) \<alpha>) x) \<cdot> \<delta>"
      by (simp add: True)
    also
    have "... = (rm_vars (set X) \<alpha> \<circ>\<^sub>s \<delta>) x"
      by (simp add: subst_compose)
    finally 
    show ?thesis .
  next
    case False
    have \<delta>_x: "\<delta> x = Var x"
      using False assms(3) by blast
    obtain y where y_p: "\<alpha> x = Var y"
      by (meson assms(2) image_iff subsetD subst_imgI)
    then have "y \<notin> set X"
      using assms(1) by blast
    then show ?thesis
      using assms(3,4) subst_domI False \<delta>_x y_p
      by (metis (mono_tags, lifting) subst_comp_notin_dom_eq subst_compose)
  qed
qed

private lemma negchecks_model_substitution_lemma_1:
  fixes \<alpha> :: "('fun,'atom,'sets,'lbl) prot_subst"
  fixes I :: "('fun,'atom,'sets,'lbl) prot_subst"
  assumes "negchecks_model (\<alpha> \<circ>\<^sub>s I) DB X F F'"
  assumes "subst_range \<alpha> \<subseteq> range Var"
  assumes "\<forall>x\<in>set X. \<forall>y. \<alpha> y \<noteq> Var x"
  shows  "negchecks_model I DB X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>) (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>)"
  unfolding negchecks_model_def
proof (rule, rule)
  fix \<delta> :: "('fun,'atom,'sets,'lbl) prot_subst"
  assume a: "subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)"

  have "(\<exists>(t, s)\<in>set F. t \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I)) \<or>
          (\<exists>(t, s)\<in>set F'. (t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<notin> DB)"
    using a assms(1) unfolding negchecks_model_def by auto
  then show "(\<exists>(t, s)\<in>set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>). t \<cdot> \<delta> \<circ>\<^sub>s I \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s I) \<or> 
               (\<exists>(t, s)\<in>set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>). (t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s I \<notin> DB)"
  proof
    assume "\<exists>(t, s)\<in>set F. t \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I)"
    then obtain t s where t_s_p: "(t, s)\<in>set F" "t \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I)"
      by auto
    from this(2) have "t \<cdot> \<delta> \<circ>\<^sub>s ((rm_vars (set X) \<alpha>) \<circ>\<^sub>s I) \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s ((rm_vars (set X) \<alpha>) \<circ>\<^sub>s I)"
      using assms(3) a using subst_comp_rm_vars_eq[of \<delta> X \<alpha>] subst_compose_assoc
      by (metis (no_types, lifting)) 
    then have "t \<cdot> (rm_vars (set X) \<alpha>) \<circ>\<^sub>s  ( \<delta> \<circ>\<^sub>s I) \<noteq> s \<cdot> (rm_vars (set X) \<alpha>) \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s I)"
      using subst_comp_rm_vars_commute[of X \<alpha> \<delta>, OF assms(3) assms(2)] a
      by (metis (no_types, lifting) subst_compose_assoc[symmetric])
    then have "t \<cdot> (rm_vars (set X) \<alpha>) \<cdot> ( \<delta> \<circ>\<^sub>s I) \<noteq> s \<cdot> (rm_vars (set X) \<alpha>) \<cdot> (\<delta> \<circ>\<^sub>s I)"
      by auto
    moreover
    have "(t \<cdot> rm_vars (set X) \<alpha>, s \<cdot> rm_vars (set X) \<alpha>) \<in> set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>)"
      using subst_apply_pairs_pset_subst t_s_p(1) by fastforce
    ultimately
    have "\<exists>(t, s)\<in>set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>). t \<cdot> \<delta> \<circ>\<^sub>s I \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s I"
      by auto
    then show ?thesis
      by auto
  next
    assume "\<exists>(t, s)\<in>set F'. (t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<notin> DB"
    then obtain t s where t_s_p: "(t, s) \<in> set F'" "(t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<notin> DB"
      by auto
    from this(2) have "(t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s (rm_vars (set X) \<alpha> \<circ>\<^sub>s I) \<notin> DB"
      using assms(3) a subst_comp_rm_vars_eq[OF a]
      by (metis (no_types, lifting) case_prod_conv subst_subst_compose)
    then have "(t, s) \<cdot>\<^sub>p rm_vars (set X) \<alpha> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s I) \<notin> DB"
      using a subst_comp_rm_vars_commute[of X \<alpha> \<delta>, OF assms(3) assms(2)]
      by (metis (no_types, lifting) case_prod_conv subst_compose_assoc) 
    then have "(t \<cdot> rm_vars (set X) \<alpha>, s \<cdot> rm_vars (set X) \<alpha>) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s I \<notin> DB"
      by auto
    moreover
    have "(t \<cdot> rm_vars (set X) \<alpha>, s \<cdot> rm_vars (set X) \<alpha>) \<in> set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>)"
      using t_s_p(1) subst_apply_pairs_pset_subst by fastforce
    ultimately
    have "(\<exists>(t, s) \<in> set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>). (t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s I \<notin> DB)"
      by auto
    then show ?thesis
      by auto
  qed
qed

private lemma negchecks_model_substitution_lemma_2:
  fixes \<alpha> :: "('fun,'atom,'sets,'lbl) prot_subst"
  fixes I :: "('fun,'atom,'sets,'lbl) prot_subst"
  assumes "negchecks_model I DB X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>) (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>)"
  assumes "subst_range \<alpha> \<subseteq> range Var"
  assumes "\<forall>x\<in>set X. \<forall>y. \<alpha> y \<noteq> Var x"
  shows "negchecks_model (\<alpha> \<circ>\<^sub>s I) DB X F F'"
  unfolding negchecks_model_def
proof (rule, rule)
  fix \<delta> :: "('fun,'atom,'sets,'lbl) prot_subst"
  assume a: "subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)"

  have "(\<exists>(t, s)\<in>set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>). t \<cdot> \<delta> \<circ>\<^sub>s  I \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s (I)) \<or>
          (\<exists>(t, s)\<in>set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>). (t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s I \<notin> DB)"
    using a assms(1)unfolding negchecks_model_def by auto
  then show "(\<exists>(t, s)\<in>set F. t \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I)) \<or>
               (\<exists>(t, s)\<in>set F'. (t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<notin> DB)"
  proof
    assume "\<exists>(t, s)\<in>set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>). t \<cdot> \<delta> \<circ>\<^sub>s  I \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s (I)"
    then obtain t s where t_s_p: "(t, s) \<in> set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>)" "t \<cdot> \<delta> \<circ>\<^sub>s I \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s I"
      by auto
    then have "\<exists>t' s'. t = t' \<cdot> rm_vars (set X) \<alpha> \<and> s = s' \<cdot> rm_vars (set X) \<alpha> \<and> (t',s') \<in> set F"
      unfolding subst_apply_pairs_def by auto
    then obtain t' s' where t'_s'_p: 
      "t = t' \<cdot> rm_vars (set X) \<alpha>" 
      "s = s' \<cdot> rm_vars (set X) \<alpha>" 
      "(t',s') \<in> set F"
      by auto
    then have "t' \<cdot> rm_vars (set X) \<alpha> \<cdot> \<delta> \<circ>\<^sub>s I \<noteq> s' \<cdot> rm_vars (set X) \<alpha> \<cdot> \<delta> \<circ>\<^sub>s I"
      using t_s_p by auto
    then have "t' \<cdot>  \<delta> \<cdot> rm_vars (set X) \<alpha> \<circ>\<^sub>s I \<noteq> s' \<cdot> \<delta> \<cdot> rm_vars (set X) \<alpha>  \<circ>\<^sub>s I"
      using a subst_comp_rm_vars_commute[OF assms(3,2)] by (metis (no_types, lifting) subst_subst)
    then have "t' \<cdot>  \<delta> \<cdot> \<alpha> \<circ>\<^sub>s I \<noteq> s' \<cdot> \<delta> \<cdot> \<alpha>  \<circ>\<^sub>s I"
      using subst_comp_rm_vars_eq[OF a] by (metis (no_types, lifting) subst_subst)
    moreover
    from t_s_p(1) have "(t', s') \<in> set F"
      using subst_apply_pairs_pset_subst t'_s'_p by fastforce
    ultimately
    have "\<exists>(t, s)\<in>set F. t \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I)"
      by auto
    then show ?thesis
      by auto
  next
    assume "\<exists>(t, s)\<in>set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>). (t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s I \<notin> DB"
    then obtain t s where t_s_p: 
      "(t, s) \<in> set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>)" 
      "(t \<cdot> \<delta> \<circ>\<^sub>s I, s \<cdot> \<delta> \<circ>\<^sub>s I) \<notin> DB"
      by auto
    then have "\<exists>t' s'. t = t' \<cdot> rm_vars (set X) \<alpha> \<and> s = s' \<cdot> rm_vars (set X) \<alpha> \<and> (t',s') \<in> set F'"
      unfolding subst_apply_pairs_def by auto
    then obtain t' s' where t'_s'_p: 
      "t = t' \<cdot> rm_vars (set X) \<alpha>" 
      "s = s' \<cdot> rm_vars (set X) \<alpha>" 
      "(t',s') \<in> set F'"
      by auto
    then have "(t' \<cdot> rm_vars (set X) \<alpha> \<cdot> \<delta> \<circ>\<^sub>s I, s' \<cdot> rm_vars (set X) \<alpha> \<cdot> \<delta> \<circ>\<^sub>s I) \<notin> DB"
      using t_s_p by auto
    then have "(t' \<cdot>  \<delta> \<cdot> rm_vars (set X) \<alpha> \<circ>\<^sub>s I, s' \<cdot> \<delta> \<cdot> rm_vars (set X) \<alpha>  \<circ>\<^sub>s I) \<notin> DB"
      using a subst_comp_rm_vars_commute[OF assms(3,2)]
      by (metis (no_types, lifting) subst_subst)
    then have "(t' \<cdot>  \<delta> \<cdot> \<alpha> \<circ>\<^sub>s I , s' \<cdot> \<delta> \<cdot> \<alpha>  \<circ>\<^sub>s I) \<notin> DB"
      using subst_comp_rm_vars_eq[OF a] by (metis (no_types, lifting) subst_subst)
    moreover
    from t_s_p(1) have "(t', s') \<in> set F'"
      using subst_apply_pairs_pset_subst t'_s'_p by fastforce
    ultimately
    have "\<exists>(t, s)\<in>set F'. (t, s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s (\<alpha> \<circ>\<^sub>s I) \<notin> DB"
      by auto
    then show ?thesis
      by auto
  qed
qed

private lemma negchecks_model_substitution_lemma:
  fixes \<alpha> :: "('fun,'atom,'sets,'lbl) prot_subst"
  fixes I :: "('fun,'atom,'sets,'lbl) prot_subst"
  assumes "subst_range \<alpha> \<subseteq> range Var"
  assumes "\<forall>x\<in>set X. \<forall>y. \<alpha> y \<noteq> Var x"
  shows "negchecks_model (\<alpha> \<circ>\<^sub>s I) DB X F F' \<longleftrightarrow>
           negchecks_model I DB X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>) (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>)"
using assms negchecks_model_substitution_lemma_1[of \<alpha> I DB X F F'] 
      negchecks_model_substitution_lemma_2[of I DB X F \<alpha> F'] assms
by auto

private lemma strand_sem_stateful_substitution_lemma:
  fixes \<alpha> :: "('fun,'atom,'sets,'lbl) prot_subst"
  fixes I :: "('fun,'atom,'sets,'lbl) prot_subst"
  assumes "subst_range \<alpha> \<subseteq> range Var"
  assumes "\<forall>x \<in> bvars\<^sub>s\<^sub>s\<^sub>t T. \<forall>y. \<alpha> y \<noteq> Var x"
  shows "strand_sem_stateful IK DB (T \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>) I = strand_sem_stateful IK DB T (\<alpha> \<circ>\<^sub>s I)"
using assms
proof (induction T arbitrary: IK DB)
  case Nil
  then show ?case by auto
next
  case (Cons a T)
  then show ?case
  proof (induction a)
    case (Receive ts)
    have "((\<lambda>x. x \<cdot> \<alpha> \<cdot> I) ` (set ts)) \<union> IK = ((\<lambda>t. t \<cdot> \<alpha>) ` set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<union> IK"
      by blast
    then show ?case
      using Receive by (force simp add: subst_sst_cons)
  next
    case (NegChecks X F F')

    have bounds: "\<forall>x\<in>bvars\<^sub>s\<^sub>s\<^sub>t T. \<forall>y. \<alpha> y \<noteq> Var x"
      using NegChecks by auto

    have "\<forall>x\<in>bvars\<^sub>s\<^sub>s\<^sub>t ([\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>]). \<forall>y. \<alpha> y \<noteq> Var x"
      using NegChecks by auto
    then have bounds2: "\<forall>x\<in>set X. \<forall>y. \<alpha> y \<noteq> Var x"
      by simp

    have "negchecks_model I DB X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>) (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>) \<longleftrightarrow>
            negchecks_model (\<alpha> \<circ>\<^sub>s I) DB X F F'"
      using NegChecks.prems(2) bounds2 negchecks_model_substitution_lemma by blast
    moreover
    have "strand_sem_stateful IK DB (T \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>) I \<longleftrightarrow> strand_sem_stateful IK DB T (\<alpha> \<circ>\<^sub>s I)"
      using Cons NegChecks(2) bounds by blast
    ultimately
    show ?case
      by (simp add: subst_sst_cons)
  qed (force simp add: subst_sst_cons)+
qed

private lemma ground_subst_rm_vars_subst_compose_dist:
  assumes "ground (subst_range \<xi>\<sigma>)"
  shows "(rm_vars (set X) (\<xi>\<sigma> \<circ>\<^sub>s \<alpha>)) = (rm_vars (set X) \<xi>\<sigma> \<circ>\<^sub>s rm_vars (set X) \<alpha>)"
proof (rule ext)
  fix x
  show "rm_vars (set X) (\<xi>\<sigma> \<circ>\<^sub>s \<alpha>) x = (rm_vars (set X) \<xi>\<sigma> \<circ>\<^sub>s rm_vars (set X) \<alpha>) x"
  proof (cases "x \<in> set X")
    case True
    then show ?thesis
      by (simp add: subst_compose)
  next
    case False
    note False_outer = False
    show ?thesis
    proof (cases "x \<in> subst_domain \<xi>\<sigma>")
      case True
      then show ?thesis
        by (metis (mono_tags, lifting) False assms ground_subst_range_empty_fv 
              subst_ground_ident_compose(1))
    next
      case False
      have "\<xi>\<sigma> x = Var x"
        using False by blast
      then show ?thesis 
        using False_outer by (simp add: subst_compose)
    qed
  qed
qed

private lemma stateful_strand_ground_subst_comp:
  assumes "ground (subst_range \<xi>\<sigma>)"
  shows "T \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi>\<sigma> \<circ>\<^sub>s \<alpha> = (T \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi>\<sigma>) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>"
using assms by (meson disjoint_iff ground_subst_no_var stateful_strand_subst_comp)

private lemma labelled_stateful_strand_ground_subst_comp:
  assumes "ground (subst_range \<xi>\<sigma>)"
  shows "T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi>\<sigma> \<circ>\<^sub>s \<alpha> = (T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi>\<sigma>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>"
using assms by (metis Int_empty_left ground_range_vars labeled_stateful_strand_subst_comp)

private lemma transaction_fresh_subst_ground_subst_range:
  assumes "transaction_fresh_subst \<sigma> T trms"
  shows "ground (subst_range \<sigma>)"
using assms by (metis range_vars_alt_def transaction_fresh_subst_range_vars_empty)

private lemma transaction_decl_subst_ground_subst_range:
  assumes "transaction_decl_subst \<xi> T"
  shows "ground (subst_range \<xi>)"
proof -
  have \<xi>_ground: "\<forall>x \<in> subst_domain \<xi>. ground_term (\<xi> x)"
    using assms transaction_decl_subst_domain transaction_decl_subst_grounds_domain by force
  show ?thesis
  proof (rule ccontr)
    assume "fv\<^sub>s\<^sub>e\<^sub>t (subst_range \<xi>) \<noteq> {}"
    then have "\<exists>x \<in> subst_domain \<xi>. fv (\<xi> x) \<noteq> {}"
      by auto
    then obtain x where x_p: "x \<in> subst_domain \<xi> \<and> fv (\<xi> x) \<noteq> {}"
      by meson
    moreover 
    have "ground_term (\<xi> x)"
      using \<xi>_ground x_p by auto
    ultimately
    show "False"
      by auto
  qed
qed

private lemma fresh_transaction_decl_subst_ground_subst_range:
  assumes "transaction_fresh_subst \<sigma> T trms"
  assumes "transaction_decl_subst \<xi> T"
  shows "ground (subst_range (\<xi> \<circ>\<^sub>s \<sigma>))"
proof -
  have "ground (subst_range \<xi>)"
    using assms transaction_decl_subst_ground_subst_range by blast
  moreover
  have "ground (subst_range \<sigma>)"
    using assms
    using transaction_fresh_subst_ground_subst_range by blast 
  ultimately
  show "ground (subst_range (\<xi> \<circ>\<^sub>s \<sigma>))"
    by (metis (no_types, opaque_lifting) Diff_iff all_not_in_conv empty_iff empty_subsetI 
          range_vars_alt_def range_vars_subst_compose_subset subset_antisym sup_bot.right_neutral)
qed

private lemma strand_sem_stateful_substitution_lemma':
  assumes "transaction_renaming_subst \<alpha> P vars"
  assumes "transaction_fresh_subst \<sigma> T trms"
  assumes "transaction_decl_subst \<xi> T"
  assumes "finite vars"
  assumes "T \<in> set P"
  shows "strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))) I
    \<longleftrightarrow> strand_sem_stateful IK DB (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma>))) (\<alpha> \<circ>\<^sub>s I)"
proof -
  have \<alpha>_Var: "subst_range \<alpha> \<subseteq> range Var"
    using assms(1) transaction_renaming_subst_is_renaming(5) by blast
  have "(\<forall>x\<in>vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T). \<forall>y. \<alpha> y \<noteq> Var x)"
    using assms(4,2) transaction_renaming_subst_vars_transaction_neq assms(1) assms(5) by blast 
  then have "(\<forall>x\<in>bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T). \<forall>y. \<alpha> y \<noteq> Var x)"
    by (metis UnCI vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t)
  then have T_Vars: "(\<forall>x\<in>bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma>)). \<forall>y. \<alpha> y \<noteq> Var x)"
    by (metis bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq)

  have ground_\<xi>_\<sigma>: "ground (subst_range (\<xi> \<circ>\<^sub>s \<sigma>))"
    using fresh_transaction_decl_subst_ground_subst_range
    using assms(2) assms(3) by blast
 
  from assms(1) ground_\<xi>_\<sigma> have 
    "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) =
    unlabel ((dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>)"
    using stateful_strand_ground_subst_comp[of _ "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"]
    by (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst unlabel_subst) 
  then show ?thesis
    using strand_sem_stateful_substitution_lemma \<alpha>_Var T_Vars
    by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst subst_lsst_unlabel)
qed

inductive_set ground_protocol_states::
  "('fun,'atom,'sets,'lbl) prot \<Rightarrow>
   (('fun,'atom,'sets,'lbl) prot_terms \<times>
    (('fun,'atom,'sets,'lbl) prot_term \<times> ('fun,'atom,'sets,'lbl) prot_term) set
    \<times>
   _ set
   ) set" (* TODO: write up the type nicer *)
  for P::"('fun,'atom,'sets,'lbl) prot"
where
  init:
  "({},{},{}) \<in> ground_protocol_states P"
| step:
  "\<lbrakk>(IK,DB,consts) \<in> ground_protocol_states P;
    T \<in> set P;
    transaction_decl_subst \<xi> T;
    transaction_fresh_subst \<sigma> T consts;
    A = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma>);
    strand_sem_stateful IK DB (unlabel A) I;
    interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I;
    wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)
   \<rbrakk> \<Longrightarrow> (IK \<union> ((ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I), dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB,
          consts \<union> {t. t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<and> (\<exists>c. t = Fun c [])}) \<in> ground_protocol_states P"


private lemma transaction_fresh_subst_consts_of_iff:
  "transaction_fresh_subst \<sigma> T (consts_of trms) \<longleftrightarrow> transaction_fresh_subst \<sigma> T trms"
proof (cases "transaction_fresh_subst \<sigma> T (consts_of trms) \<or> transaction_fresh_subst \<sigma> T trms")
  case True
  then have "\<forall>t \<in> subst_range \<sigma>. \<exists>c. t = Fun c []"
    unfolding transaction_fresh_subst_def by auto
  have "(\<forall>t \<in> subst_range \<sigma>. t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (consts_of trms) \<longleftrightarrow> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t trms)"
  proof 
    fix t
    assume "t \<in> subst_range \<sigma>"
    then obtain c where c_p: "t = Fun c []"
      using \<open>\<forall>t\<in>subst_range \<sigma>. \<exists>c. t = Fun c []\<close> by blast
    have "Fun c [] \<in> subterms\<^sub>s\<^sub>e\<^sub>t (consts_of trms) \<longleftrightarrow> Fun c [] \<in> subterms\<^sub>s\<^sub>e\<^sub>t trms"
      unfolding consts_of_def by auto
    then show "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (consts_of trms) \<longleftrightarrow> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t trms"
      using c_p by auto
  qed
  then show ?thesis
    using transaction_fresh_subst_def by force
next
  case False
  then show ?thesis by auto
qed

private lemma transaction_renaming_subst_inv:
  assumes "transaction_renaming_subst \<alpha> P X "
  shows "\<exists>\<alpha>inv. \<alpha> \<circ>\<^sub>s \<alpha>inv = Var \<and>  wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<alpha>inv)"
using var_rename_inv_comp transaction_renaming_subst_def assms subst_apply_term_empty subst_term_eqI
by (metis var_rename_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_range(2))  

private lemma consts_of_union_distr: 
  "consts_of (trms1 \<union> trms2) = consts_of trms1 \<union> consts_of trms2"
unfolding consts_of_def by auto

private lemma ground_protocol_states_aux_finite_vars:
  assumes "(IK,DB,trms,vars,w) \<in> ground_protocol_states_aux P"
  shows "finite vars"
using assms by (induction rule: ground_protocol_states_aux.induct) auto

private lemma dbupd\<^sub>s\<^sub>s\<^sub>t_substitution_lemma:
  "dbupd\<^sub>s\<^sub>s\<^sub>t T (\<alpha> \<circ>\<^sub>s I) DB = dbupd\<^sub>s\<^sub>s\<^sub>t (T \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>) I DB"
proof (induction T arbitrary: DB)
  case Nil
  then show ?case
    by auto 
next
  case (Cons a T)
  then show ?case
    by (induction a) (simp_all add: subst_apply_stateful_strand_def)
qed

private lemma subst_Var_const_subterm_subst:
  assumes "subst_range \<alpha> \<subseteq> range Var"
  shows "Fun c [] \<sqsubseteq> t \<longleftrightarrow> Fun c [] \<sqsubseteq> t \<cdot> \<alpha>"
  using assms
proof (induction t)
  case (Var x)
  then show ?case
    by (metis is_Var_def subtermeq_Var_const(1) term.discI(2) var_renaming_is_Fun_iff)
next
  case (Fun f ts)
  then show ?case
    by auto
qed

private lemma subst_Var_consts_of:
  assumes "subst_range \<alpha> \<subseteq> range Var"
  shows "consts_of T = consts_of (T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<alpha>)"
proof (rule antisym; rule subsetI)
  fix x
  assume "x \<in> consts_of T"
  then obtain t c where t_c_p: "t \<in> T \<and> x \<sqsubseteq> t \<and> x = Fun c []"
    unfolding consts_of_def by auto
  moreover
  have "x \<sqsubseteq> t \<cdot> \<alpha>"
    using t_c_p by (meson assms subst_Var_const_subterm_subst)
  ultimately
  show "x \<in> consts_of (T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<alpha>)"
    unfolding consts_of_def by auto 
next
  fix x
  assume "x \<in> consts_of (T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<alpha>)"
  then obtain t c where t_c_p: "t \<in> T \<and> x \<sqsubseteq> t \<cdot> \<alpha> \<and> x = Fun c []"
    unfolding consts_of_def by auto
  moreover
  have "x \<sqsubseteq> t"
    using t_c_p by (meson assms subst_Var_const_subterm_subst)
  ultimately
  show "x \<in> consts_of T"
    unfolding consts_of_def by auto
qed

private lemma fst_set_subst_apply_set:
  "fst ` set F \<cdot>\<^sub>s\<^sub>e\<^sub>t \<alpha> = fst ` (set F \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<alpha>)"
by (induction F) auto

private lemma snd_set_subst_apply_set:
  "snd ` set F \<cdot>\<^sub>s\<^sub>e\<^sub>t \<alpha> = snd ` (set F \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<alpha>)"
by (induction F) auto

private lemma trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_fst_snd: 
  "trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F = fst ` set F \<union> snd ` set F"
by (auto simp add: rev_image_eqI)

private lemma consts_of_trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_range_Var:
  assumes "subst_range \<alpha> \<subseteq> range Var"
  shows "consts_of (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) = consts_of (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<alpha>))"
  using assms
proof (induction a)
  case (NegChecks X F F')
  have \<alpha>_subs_rng_Var: "subst_range (rm_vars (set X) \<alpha>) \<subseteq> range Var"
    using assms by auto

  have "consts_of (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) = consts_of (fst ` set F \<union> snd ` set F)"
    using trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_fst_snd by metis
  also
  have "... = consts_of (fst ` set F) \<union> consts_of (snd ` set F)"
    using consts_of_union_distr by blast
  also
  have "... = consts_of ((fst ` set F) \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<alpha>) \<union>
                consts_of ((snd ` set F) \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<alpha>)"
    using \<alpha>_subs_rng_Var subst_Var_consts_of[of "rm_vars (set X) \<alpha>" "fst ` set F"] 
            subst_Var_consts_of[of "rm_vars (set X) \<alpha>" "snd ` set F"] 
    by auto
  also
  have "... = consts_of (((fst ` set F) \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<alpha>) \<union>
                ((snd ` set F) \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<alpha>))"
    using consts_of_union_distr by auto
  also
  have "... = consts_of (fst ` set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>) \<union>
                snd ` set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>))"
    unfolding subst_apply_pairs_def fst_set_subst_apply_set snd_set_subst_apply_set by simp 
  also
  have "... = consts_of (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>))"
    using trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_fst_snd[of "F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>"] 
    by metis
  finally 
  have 1: "consts_of (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) = consts_of (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>))"
    by auto

  have "consts_of (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F') = consts_of (fst ` set F' \<union> snd ` set F')"
    using trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_fst_snd by metis
  also
  have "... = consts_of (fst ` set F') \<union> consts_of (snd ` set F')"
    using consts_of_union_distr by blast
  also
  have "... = consts_of ((fst ` set F') \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<alpha>) \<union>
                consts_of ((snd ` set F') \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<alpha>)"
    using subst_Var_consts_of[of "rm_vars (set X) \<alpha>" "fst ` set F'"] \<alpha>_subs_rng_Var
            subst_Var_consts_of[of "rm_vars (set X) \<alpha>" "snd ` set F'"]
    by auto
  also
  have "... = consts_of ((fst ` set F' \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<alpha>) \<union>
                (snd ` set F' \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<alpha>))"
    using consts_of_union_distr by auto
  also
  have "... = consts_of (fst ` set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>) \<union> 
                snd ` set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>))"
    unfolding subst_apply_pairs_def fst_set_subst_apply_set snd_set_subst_apply_set by simp 
  also
  have "... = consts_of (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>))"
    using trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_fst_snd[of "F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>"] 
    by metis
  finally have 2: "consts_of (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F') = consts_of (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<alpha>))"
    by auto

  show ?case 
    using 1 2 by (simp add: consts_of_union_distr)
qed (use subst_Var_consts_of[of _ "{_, _}", OF assms] subst_Var_consts_of[OF assms] in auto)

private lemma consts_of_trms\<^sub>s\<^sub>s\<^sub>t_range_Var:
  assumes "subst_range \<alpha> \<subseteq> range Var"
  shows "consts_of (trms\<^sub>s\<^sub>s\<^sub>t T) = consts_of (trms\<^sub>s\<^sub>s\<^sub>t (T \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>))"
proof (induction T)
  case Nil
  then show ?case by auto
next
  case (Cons a T)
  have "consts_of (trms\<^sub>s\<^sub>s\<^sub>t (a # T)) = consts_of (trms\<^sub>s\<^sub>s\<^sub>t [a] \<union> trms\<^sub>s\<^sub>s\<^sub>t T)"
    by simp
  also
  have "... = consts_of (trms\<^sub>s\<^sub>s\<^sub>t [a]) \<union> consts_of (trms\<^sub>s\<^sub>s\<^sub>t T)"
    using consts_of_union_distr by simp
  also 
  have "... = consts_of (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) \<union> consts_of (trms\<^sub>s\<^sub>s\<^sub>t T)"
    by simp
  also
  have "... = consts_of (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<alpha>)) \<union> consts_of (trms\<^sub>s\<^sub>s\<^sub>t T)"
    using consts_of_trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_range_Var[OF assms] by simp
  also 
  have "... = consts_of (trms\<^sub>s\<^sub>s\<^sub>t ([a] \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>)) \<union> consts_of (trms\<^sub>s\<^sub>s\<^sub>t T)"
    by (simp add: subst_apply_stateful_strand_def)
  also
  have "... = consts_of (trms\<^sub>s\<^sub>s\<^sub>t ([a] \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>)) \<union> consts_of (trms\<^sub>s\<^sub>s\<^sub>t (T \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>))"
    using local.Cons by simp
  also
  have "... = consts_of (trms\<^sub>s\<^sub>s\<^sub>t (a # T \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>))"
    by (simp add: consts_of_union_distr subst_sst_cons)
  finally
  show ?case
    by simp
qed

private lemma consts_of_trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t_range_Var:
  assumes "subst_range \<alpha> \<subseteq> range Var"
  shows "consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T) = consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>))"
using consts_of_trms\<^sub>s\<^sub>s\<^sub>t_range_Var[of \<alpha> "unlabel T"]
by (metis assms unlabel_subst)

private lemma transaction_renaming_subst_range:
  assumes "transaction_renaming_subst \<alpha> P vars"
  shows "subst_range \<alpha> \<subseteq> range Var"
using assms unfolding transaction_renaming_subst_def var_rename_def by auto

private lemma protocol_models_equiv3':
  assumes "(IK,DB,trms,vars,w) \<in> ground_protocol_states_aux P"
  shows "(IK,DB, consts_of trms) \<in> ground_protocol_states P"
  using assms 
proof (induction rule: ground_protocol_states_aux.induct)
  case init
  then show ?case
    using ground_protocol_states.init unfolding consts_of_def by force
next
  case (step IK DB trms vars w T \<xi> \<sigma> \<alpha> A I)

  have fin_vars: "finite vars"
    using ground_protocol_states_aux_finite_vars step by auto

  have ground_\<xi>\<sigma>: "ground (subst_range (\<xi> \<circ>\<^sub>s \<sigma>))"
    using fresh_transaction_decl_subst_ground_subst_range using step.hyps(3) step.hyps(4) by blast

  have \<alpha>_Var: "subst_range \<alpha> \<subseteq> range Var"
    using step(5) transaction_renaming_subst_range by metis

  define I' where "I' = \<alpha> \<circ>\<^sub>s I"
  define A' where "A' = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma>)"

  have "(IK, DB, consts_of trms) \<in> ground_protocol_states P"
    using step by force
  moreover
  have T_in_P: "T \<in> set P"
     using step by force
  moreover
  have "transaction_decl_subst \<xi> T"
     using step by force
  moreover
  have "transaction_fresh_subst \<sigma> T (consts_of trms)"
     using step transaction_fresh_subst_consts_of_iff by force
  moreover
  have "A' = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma>)"
    using A'_def .
  moreover
  have "strand_sem_stateful IK DB (unlabel A') I'"
    using step(7) step(4) step(5) step(3) T_in_P fin_vars unfolding A'_def I'_def step(6)
    using strand_sem_stateful_substitution_lemma'
    by auto
  moreover
  have "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I'"
    using step(8) unfolding I'_def
    by (meson interpretation_comp(1)) 
  moreover
  have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I')"
   using step(9) unfolding I'_def
   using step.hyps(5) transaction_renaming_subst_range_wf_trms wf_trms_subst_compose by blast 
  ultimately
  have "(IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A' \<cdot>\<^sub>s\<^sub>e\<^sub>t I'), dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A') I' DB, 
           consts_of trms \<union> consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A')) \<in> ground_protocol_states P"
    using ground_protocol_states.step[of IK DB "consts_of trms" P T \<xi> \<sigma> A' I']
    unfolding consts_of_def by blast
  moreover
  have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A' \<cdot>\<^sub>s\<^sub>e\<^sub>t I' = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
  proof - 
    have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A' \<cdot>\<^sub>s\<^sub>e\<^sub>t I' = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<alpha> \<circ>\<^sub>s I"
      unfolding A'_def I'_def step(6) by auto
    also
    have "... = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((A' \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)"
      unfolding unlabel_subst[symmetric] ik\<^sub>s\<^sub>s\<^sub>t_subst by auto
    also
    have "... = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)"
      unfolding A'_def step(6)
      using labelled_stateful_strand_ground_subst_comp[of _ "transaction_strand T", OF ground_\<xi>\<sigma>]
      by (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst)
    also
    have "... = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      by (metis ik\<^sub>s\<^sub>s\<^sub>t_subst unlabel_subst)
    finally 
    show "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A' \<cdot>\<^sub>s\<^sub>e\<^sub>t I' = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      by auto
  qed
  moreover
  have "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A') I' DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB"
  proof -
    have "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A') I' DB = 
            dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A') (\<alpha> \<circ>\<^sub>s I) DB"
      unfolding A'_def I'_def step(6) using step by auto
    also
    have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A' \<cdot>\<^sub>s\<^sub>s\<^sub>t \<alpha>) I DB"
      using dbupd\<^sub>s\<^sub>s\<^sub>t_substitution_lemma by metis
    also
    have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB"
      unfolding A'_def step(6)
      using stateful_strand_ground_subst_comp[of _ "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"] 
        ground_\<xi>\<sigma> by (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_unlabel)
    finally
    show "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A') I' DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB"
      by auto
  qed
  moreover
  have "consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A') = consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
    by (metis (no_types, lifting) A'_def \<alpha>_Var consts_of_trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t_range_Var ground_\<xi>\<sigma> 
         labelled_stateful_strand_ground_subst_comp step.hyps(6) trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq)
  ultimately
  show ?case
    using consts_of_union_distr by metis
qed

private lemma protocol_models_equiv4':
  assumes "(IK, DB, csts) \<in> ground_protocol_states P"
  shows "\<exists>trms w vars. (IK,DB,trms,vars,w) \<in> ground_protocol_states_aux P 
                  \<and> csts = consts_of trms
                  \<and> vars = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)"
  using assms 
proof (induction rule: ground_protocol_states.induct)
  case init
  have "({}, {}, {}, {}, []) \<in> ground_protocol_states_aux P"
    using ground_protocol_states_aux.init by blast
  moreover
  have "{} = consts_of {}"
    unfolding consts_of_def by auto
  moreover
  have "{} = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb [])"
    by auto
  ultimately
  show ?case
    by metis
next
  case (step IK DB "consts" T \<xi> \<sigma> A I)
  then obtain trms w vars where trms_w_vars_p:
    "(IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P"
    "consts = consts_of trms"
    "vars = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w)"
    by auto

  have "\<exists>\<alpha>. transaction_renaming_subst \<alpha> P vars"
    unfolding transaction_renaming_subst_def by blast

  then obtain \<alpha> :: "('fun,'atom,'sets,'lbl) prot_subst"
    where \<alpha>_p: "transaction_renaming_subst \<alpha> P vars"
    by blast
  then obtain \<alpha>inv where \<alpha>inv_p: "\<alpha> \<circ>\<^sub>s \<alpha>inv = Var \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<alpha>inv)"
    using transaction_renaming_subst_inv[of \<alpha> P vars] by auto

  define A' where "A' = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  define I' where "I' = \<alpha>inv \<circ>\<^sub>s I"
  define trms' where "trms' = trms \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A'"
  define vars' where "vars' = vars \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A'"
  define w' where "w' = w @ [(\<xi>, \<sigma>, I', T, \<alpha>)]"
  define IK' where "IK' = IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I)"
  define DB' where "DB' = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB"

  have P_state: "(IK', DB' , trms', vars', w') \<in> ground_protocol_states_aux P"
  proof -
    have 1: "(IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P"
      using \<open>(IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P\<close> by blast
    moreover
    have "T \<in> set P"
      using step(2) .
    moreover
    have "transaction_decl_subst \<xi> T"
      using step(3) .
    moreover
    have fresh_\<sigma>: "transaction_fresh_subst \<sigma> T trms"
      using step(4) trms_w_vars_p(2)
      using transaction_fresh_subst_consts_of_iff by auto
    moreover
    have "transaction_renaming_subst \<alpha> P vars"
      using \<alpha>_p .
    moreover
    have "A' = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      unfolding A'_def by auto
    moreover
    have "strand_sem_stateful IK DB (unlabel A') I'"
    proof -
      have fin_vars: "finite vars"
        using 1 ground_protocol_states_aux_finite_vars by blast
      show "strand_sem_stateful IK DB (unlabel A') I'"
        using step(6) strand_sem_stateful_substitution_lemma'[OF \<alpha>_p fresh_\<sigma> step(3) fin_vars]
          step(2) unfolding A'_def step(5)
        by (metis (no_types, lifting) I'_def \<alpha>inv_p subst_compose_assoc var_comp(2))
    qed
    moreover
    have "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I'"
      using step(7) by (simp add: I'_def interpretation_substI subst_compose)
    moreover
    have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I')"
      using I'_def \<alpha>inv_p step.hyps(8) wf_trms_subst_compose by blast
    moreover
    have "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A') I' DB"
    proof -
      have "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I DB = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) (\<alpha> \<circ>\<^sub>s \<alpha>inv \<circ>\<^sub>s I) DB"
        by (simp add: \<alpha>inv_p)
      also
      have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A') (\<alpha>inv \<circ>\<^sub>s I) DB"
        unfolding A'_def step(5)
        by (metis (no_types, lifting) dbupd\<^sub>s\<^sub>s\<^sub>t_substitution_lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_unlabel 
             subst_compose_assoc)
      also
      have "... = dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A') I' DB"
        unfolding A'_def I'_def by auto
      finally
      show ?thesis
        by auto
    qed
    moreover
    have "IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) = IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A' \<cdot>\<^sub>s\<^sub>e\<^sub>t I')"
    proof -
      have "IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) = IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<alpha>  \<circ>\<^sub>s \<alpha>inv) \<circ>\<^sub>s I)"
        using \<alpha>inv_p by auto
      also
      have "... = IK \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A' \<cdot>\<^sub>s\<^sub>e\<^sub>t I')"
        unfolding A'_def step(5) unlabel_subst[symmetric] ik\<^sub>s\<^sub>s\<^sub>t_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst I'_def by auto
      finally
      show ?thesis
        by auto
    qed
    ultimately
    show "(IK', DB' , trms', vars', w') \<in> ground_protocol_states_aux P"
      using ground_protocol_states_aux.step[of IK DB trms vars w P T \<xi> \<sigma> \<alpha> A' I']
      unfolding trms'_def vars'_def w'_def IK'_def DB'_def by auto
  qed
  moreover
  have "consts \<union> consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = consts_of trms'"
  proof -
    have \<alpha>_Var: "subst_range \<alpha> \<subseteq> range Var"
      using \<alpha>_p transaction_renaming_subst_range by blast

    have ground_\<xi>\<sigma>: "ground (subst_range (\<xi> \<circ>\<^sub>s \<sigma>))"
      using fresh_transaction_decl_subst_ground_subst_range using step.hyps(3) step.hyps(4) by blast

    have "consts \<union> consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = (consts_of trms) \<union> consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
      using trms_w_vars_p(2) by blast
    also
    have "... = (consts_of trms) \<union> consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>))"
      using consts_of_trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t_range_Var[of \<alpha>, OF \<alpha>_Var, of A] by auto
    also
    have "... = (consts_of trms) \<union> consts_of (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A')"
      using step(5) A'_def ground_\<xi>\<sigma>
      using labelled_stateful_strand_ground_subst_comp[of _ "(dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"]
      by (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst)
    also
    have "... = consts_of (trms \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A')"
      using consts_of_union_distr by blast
    also
    have "... = consts_of trms'"
      unfolding trms'_def by auto
    finally
    show "?thesis"
      by auto
  qed
  moreover
  have "vars' = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T_symb w')"
    using P_state reachable_constraints_if_ground_protocol_states_aux by auto
  ultimately
  show ?case
    unfolding DB'_def IK'_def consts_of_def[symmetric] by metis
qed

private lemma protocol_model_equivalence_aux2:
  "{(IK, DB) | IK DB. \<exists>csts. (IK, DB, csts) \<in> ground_protocol_states P} = 
   {(IK, DB) | IK DB. \<exists>w trms vars. (IK, DB, trms, vars, w) \<in> ground_protocol_states_aux P}"
using protocol_models_equiv4' protocol_models_equiv3' by meson

theorem protocol_model_equivalence:
  "{(IK, DB) | IK DB. \<exists>csts. (IK, DB, csts) \<in> ground_protocol_states P} = 
   {(ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I), dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I {}) | A I.
      A \<in> reachable_constraints P \<and> strand_sem_stateful {} {} (unlabel A) I \<and>
      interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)}"
using protocol_model_equivalence_aux2 protocol_model_equivalence_aux1 by auto

end

end

end
