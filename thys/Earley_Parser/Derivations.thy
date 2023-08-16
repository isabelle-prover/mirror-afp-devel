theory Derivations
  imports
    CFG
begin

section \<open>Adjusted content from AFP/LocalLexing\<close>

type_synonym 'a derivation = "(nat \<times> 'a rule) list"

lemma is_word_empty: "is_word \<G> []" by (auto simp add: is_word_def)

lemma derives1_implies_derives[simp]:
  "derives1 \<G> a b \<Longrightarrow> derives \<G> a b"
  by (auto simp add: derives_def derivations_def derivations1_def)

lemma derives_trans:
  "derives \<G> a b \<Longrightarrow> derives \<G> b c \<Longrightarrow> derives \<G> a c"
  by (auto simp add: derives_def derivations_def)

lemma derives1_eq_derivations1:
  "derives1 \<G> x y = ((x, y) \<in> derivations1 \<G>)"
  by (simp add: derivations1_def)

lemma derives_induct[consumes 1, case_names Base Step]:
  assumes derives: "derives \<G> a b"
  assumes Pa: "P a"
  assumes induct: "\<And>y z. derives \<G> a y \<Longrightarrow> derives1 \<G> y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
proof -
  note rtrancl_lemma = rtrancl_induct[where a = a and b = b and r = "derivations1 \<G>" and P=P]
  from derives Pa induct rtrancl_lemma show "P b"
    by (metis derives_def derivations_def derives1_eq_derivations1)
qed

definition Derives1 :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a rule \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "Derives1 \<G> u i r v \<equiv> \<exists> x y N \<alpha>. 
    u = x @ [N] @ y \<and>
    v = x @ \<alpha> @ y \<and>
    (N, \<alpha>) \<in> set (\<RR> \<G>) \<and> r = (N, \<alpha>) \<and> i = length x"  

lemma Derives1_split:
  "Derives1 \<G> u i r v \<Longrightarrow> \<exists> x y. u = x @ [fst r] @ y \<and> v = x @ (snd r) @ y \<and> length x = i"
  by (metis Derives1_def fst_conv snd_conv)

lemma Derives1_implies_derives1: "Derives1 \<G> u i r v \<Longrightarrow> derives1 \<G> u v"
  by (auto simp add: Derives1_def derives1_def)

lemma derives1_implies_Derives1: "derives1 \<G> u v \<Longrightarrow> \<exists> i r. Derives1 \<G> u i r v"
  by (auto simp add: Derives1_def derives1_def)

fun Derivation :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a derivation \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "Derivation _ a [] b = (a = b)"
| "Derivation \<G> a (d#D) b = (\<exists> x. Derives1 \<G> a (fst d) (snd d) x \<and> Derivation \<G> x D b)"

lemma Derivation_implies_derives: "Derivation \<G> a D b \<Longrightarrow> derives \<G> a b"
proof (induct D arbitrary: a b)
  case Nil thus ?case 
    by (simp add: derives_def derivations_def)
next
  case (Cons d D)
  note ihyps = this
  from ihyps have "\<exists> x. Derives1 \<G> a (fst d) (snd d) x \<and> Derivation \<G> x D b" by auto
  then obtain x where "Derives1 \<G> a (fst d) (snd d) x" and xb: "Derivation \<G> x D b" by blast
  with Derives1_implies_derives1 have d1: "derives \<G> a x" by fastforce
  from ihyps xb have d2:"derives \<G> x b" by simp
  show "derives \<G> a b" by (rule derives_trans[OF d1 d2])
qed 

lemma Derivation_Derives1: "Derivation \<G> a S y \<Longrightarrow> Derives1 \<G> y i r z \<Longrightarrow> Derivation \<G> a (S@[(i,r)]) z"
proof (induct S arbitrary: a y z i r)
  case Nil thus ?case by simp
next
  case (Cons s S) thus ?case 
    by (metis Derivation.simps(2) append_Cons) 
qed

lemma derives_implies_Derivation: "derives \<G> a b \<Longrightarrow> \<exists> D. Derivation \<G> a D b"
proof (induct rule: derives_induct)
  case Base
  show ?case by (rule exI[where x="[]"], simp)
next
  case (Step y z)
  note ihyps = this
  from ihyps obtain D where ay: "Derivation \<G> a D y" by blast
  from ihyps derives1_implies_Derives1 obtain i r where yz: "Derives1 \<G> y i r z" by blast
  from Derivation_Derives1[OF ay yz] show ?case by auto
qed

lemma rule_nonterminal_type[simp]: "wf_\<G> \<G> \<Longrightarrow> (N, \<alpha>) \<in> set (\<RR> \<G>) \<Longrightarrow> is_nonterminal \<G> N"
  by (auto simp add: is_nonterminal_def wf_\<G>_defs)

lemma Derives1_rule [elim]: "Derives1 \<G> a i r b \<Longrightarrow> r \<in> set (\<RR> \<G>)"
  using Derives1_def by metis

lemma is_terminal_nonterminal: "wf_\<G> \<G> \<Longrightarrow> is_terminal \<G> x \<Longrightarrow> is_nonterminal \<G> x \<Longrightarrow> False"
  by (auto simp: wf_\<G>_defs disjoint_iff is_nonterminal_def is_terminal_def)

lemma is_word_is_terminal: "i < length u \<Longrightarrow> is_word \<G> u \<Longrightarrow> is_terminal \<G> (u ! i)"
  using is_word_def by force

lemma Derivation_append: "Derivation \<G> a (D@E) c = (\<exists> b. Derivation \<G> a D b \<and> Derivation \<G> b E c)"
  by (induct D arbitrary: a c E) auto

lemma Derivation_implies_append: 
  "Derivation \<G> a D b \<Longrightarrow> Derivation \<G> b E c \<Longrightarrow> Derivation \<G> a (D@E) c"
  using Derivation_append by blast


section \<open>Additional derivation lemmas\<close>

lemma Derives1_prepend:
  assumes "Derives1 \<G> u i r v"
  shows "Derives1 \<G> (w@u) (i + length w) r (w@v)"
proof -
  obtain x y N \<alpha> where *:
    "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
    "(N, \<alpha>) \<in> set (\<RR> \<G>)" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by (smt (verit))
  hence "w@u = w @ x @ [N] @ y" "w@v = w @ x @ \<alpha> @ y"
    by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="w@x"])
    apply (rule_tac exI[where x="y"])
    by simp
qed

lemma Derivation_prepend:
  "Derivation \<G> b D b' \<Longrightarrow> Derivation \<G> (a@b) (map (\<lambda>(i, r). (i + length a, r)) D) (a@b')"
  using Derives1_prepend by (induction D arbitrary: b b') (auto, fast)

lemma Derives1_append:
  assumes "Derives1 \<G> u i r v"
  shows "Derives1 \<G> (u@w) i r (v@w)"
proof -
  obtain x y N \<alpha> where *: 
    "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
    "(N, \<alpha>) \<in> set (\<RR> \<G>)" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by (smt (verit))
  hence "u@w = x @ [N] @ y @ w" "v@w = x @ \<alpha> @ y @ w"
    by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="x"])
    apply (rule_tac exI[where x="y@w"])
    by blast
qed

lemma Derivation_append':
  "Derivation \<G> a D a' \<Longrightarrow> Derivation \<G> (a@b) D (a'@b)"
  using Derives1_append by (induction D arbitrary: a a') (auto, fast)

lemma Derivation_append_rewrite:
  assumes "Derivation \<G> a D (b @ c @ d) " "Derivation \<G> c E c'"
  shows "\<exists>F. Derivation \<G> a F (b @ c' @ d)"
  using assms Derivation_append' Derivation_prepend Derivation_implies_append by fast

lemma derives1_if_valid_rule:
  "(N, \<alpha>) \<in> set (\<RR> \<G>) \<Longrightarrow> derives1 \<G> [N] \<alpha>"
  unfolding derives1_def
  apply (rule_tac exI[where x="[]"])
  apply (rule_tac exI[where x="[]"])
  by simp

lemma derives_if_valid_rule:
  "(N, \<alpha>) \<in> set (\<RR> \<G>) \<Longrightarrow> derives \<G> [N] \<alpha>"
  using derives1_if_valid_rule by fastforce

lemma Derivation_from_empty:
  "Derivation \<G> [] D a \<Longrightarrow> a = []"
  by (cases D) (auto simp: Derives1_def)

lemma Derivation_concat_split:
  "Derivation \<G> (a@b) D c \<Longrightarrow> \<exists>E F a' b'. Derivation \<G> a E a' \<and> Derivation \<G> b F b' \<and>
     c = a' @ b' \<and> length E \<le> length D \<and> length F \<le> length D"
proof (induction D arbitrary: a b)
  case Nil
  thus ?case
    by (metis Derivation.simps(1) order_refl)
next
  case (Cons d D)
  then obtain ab where *: "Derives1 \<G> (a@b) (fst d) (snd d) ab" "Derivation \<G> ab D c"
    by auto
  then obtain x y N \<alpha> where #:
    "a@b = x @ [N] @ y" "ab = x @ \<alpha> @ y" "(N,\<alpha>) \<in> set (\<RR> \<G>)" "snd d = (N,\<alpha>)" "fst d = length x"
    using * unfolding Derives1_def by blast
  show ?case
  proof (cases "length a \<le> length x")
    case True
    hence ab_def: 
      "a = take (length a) x" 
      "b = drop (length a) x @ [N] @ y"
      "ab = take (length a) x @ drop (length a) x @ \<alpha> @ y"
      using #(1,2) True by (metis append_eq_append_conv_if)+
    then obtain E F a' b' where IH:
      "Derivation \<G> (take (length a) x) E a'"
      "Derivation \<G> (drop (length a) x @ \<alpha> @ y) F b'"
      "c = a' @ b'"
      "length E \<le> length D"
      "length F \<le> length D"
      using Cons *(2) by blast
    have "Derives1 \<G> b (fst d - length a) (snd d) (drop (length a) x @ \<alpha> @ y)"
      unfolding Derives1_def using *(1) #(3-5) ab_def(2) by (metis length_drop)
    hence "Derivation \<G> b ((fst d - length a, snd d) # F) b'"
      using IH(2) by force
    moreover have "Derivation \<G> a E a'"
      using IH(1) ab_def(1) by fastforce
    ultimately show ?thesis
      using IH(3-5) by fastforce
  next
    case False
    hence a_def: "a = x @ [N] @ take (length a - length x - 1) y"
      using #(1) append_eq_conv_conj[of a b "x @ [N] @ y"] take_all_iff take_append
      by (metis append_Cons append_Nil diff_is_0_eq le_cases take_Cons')
    hence b_def: "b = drop (length a - length x - 1) y"
      using #(1) by (metis List.append.assoc append_take_drop_id same_append_eq)
    have "ab = x @ \<alpha> @ take (length a - length x - 1) y @ drop (length a - length x - 1) y"
      using #(2) by force
    then obtain E F a' b' where IH:
      "Derivation \<G> (x @ \<alpha> @ take (length a - length x - 1) y) E a'"
      "Derivation \<G> (drop (length a - length x - 1) y) F b'"
      "c = a' @ b'"
      "length E \<le> length D"
      "length F \<le> length D"
      using Cons.IH[of "x @ \<alpha> @ take (length a - length x - 1) y" "drop (length a - length x - 1) y"] *(2) by auto
    have "Derives1 \<G> a (fst d) (snd d) (x @ \<alpha> @ take (length a - length x - 1) y)"
      unfolding Derives1_def using #(3-5) a_def by blast
    hence "Derivation \<G> a ((fst d, snd d) # E) a'"
      using IH(1) by fastforce
    moreover have "Derivation \<G> b F b'"
      using b_def IH(2) by blast
    ultimately show ?thesis
      using IH(3-5) by fastforce
  qed
qed

lemma Derivation_\<SS>1:
  assumes "Derivation \<G> [\<SS> \<G>] D \<omega>" "is_word \<G> \<omega>" "wf_\<G> \<G>"
  shows "\<exists>\<alpha> E. Derivation \<G> \<alpha> E \<omega> \<and> (\<SS> \<G>,\<alpha>) \<in> set (\<RR> \<G>)"
proof (cases D)
  case Nil
  thus ?thesis
    using assms is_nonterminal_startsymbol is_terminal_nonterminal by (metis Derivation.simps(1) is_word_def list.set_intros(1))
next
  case (Cons d D)
  then obtain \<alpha> where "Derives1 \<G> [\<SS> \<G>] (fst d) (snd d) \<alpha>" "Derivation \<G> \<alpha> D \<omega>"
    using assms by auto
  hence "(\<SS> \<G>, \<alpha>) \<in> set (\<RR> \<G>)"
    unfolding Derives1_def
    by (metis List.append.right_neutral List.list.discI append_eq_Cons_conv append_is_Nil_conv nth_Cons_0 self_append_conv2)
  thus ?thesis
    using \<open>Derivation \<G> \<alpha> D \<omega>\<close> by auto
qed

end