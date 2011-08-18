(*  Title:       Coinductive natural numbers
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Coinductive natural numbers *}

theory Coinductive_Nat imports
  "~~/src/HOL/Library/Extended_Nat"
begin

text {*
  Coinductive natural numbers are isomorphic to natural numbers with infinity:
  View Nat\_Infinity @{typ "enat"} as codatatype
  with constructors @{term "0 :: enat"} and @{term "eSuc"}.
*}

lemmas eSuc_plus = iadd_Suc

lemmas plus_enat_eq_0_conv = iadd_is_0

coinductive_set enat_set :: "enat set"
where "0 \<in> enat_set"
  | "n \<in> enat_set \<Longrightarrow> (eSuc n) \<in> enat_set"

lemma enat_set_eq_UNIV [simp]: "enat_set = UNIV"
proof
  show "enat_set \<subseteq> UNIV" by blast
  show "UNIV \<subseteq> enat_set"
  proof
    fix x :: enat
    assume "x \<in> UNIV"
    thus "x \<in> enat_set"
    proof coinduct
      case (enat_set x)
      show ?case
      proof(cases "x = 0")
        case True thus ?thesis by simp
      next
        case False
        then obtain n where "x = eSuc n"
          by(cases x)(fastsimp simp add: eSuc_def zero_enat_def gr0_conv_Suc
                               split: enat.splits)+
        thus ?thesis by auto
      qed
    qed
  qed
qed

subsection {* Case operator *}

lemma enat_coexhaust:
  obtains (0) "n = 0"
     | (eSuc) n' where "n = eSuc n'"
proof -
  have "n \<in> enat_set" by auto
  thus thesis by cases (erule that)+
qed

definition enat_cocase :: "'a \<Rightarrow> (enat \<Rightarrow> 'a) \<Rightarrow> enat \<Rightarrow> 'a"
where [nitpick_simp]:
  "enat_cocase z s n = 
   (case n of enat n' \<Rightarrow> (case n' of 0 \<Rightarrow> z | Suc n'' \<Rightarrow> s (enat n'')) | \<infinity> \<Rightarrow> s \<infinity>)"

lemma enat_cocase_0 [simp]:
  "enat_cocase z s 0 = z"
by(simp add: enat_cocase_def zero_enat_def)

lemma enat_cocase_eSuc [simp]:
  "enat_cocase z s (eSuc n) = s n"
by(simp add: enat_cocase_def eSuc_def split: enat.splits)

lemma neq_zero_conv_eSuc:
  "n \<noteq> 0 \<longleftrightarrow> (\<exists>n'. n = eSuc n')"
by(cases n rule: enat_coexhaust) simp_all

syntax
  eSuc :: logic
translations
  "case p of 0 \<Rightarrow> a | eSuc n \<Rightarrow> b" \<rightleftharpoons> "CONST enat_cocase a (\<lambda>n. b) p"

lemma enat_cocase_cert:
  assumes "CASE \<equiv> enat_cocase c d"
  shows "(CASE 0 \<equiv> c) &&& (CASE (eSuc n) \<equiv> d n)"
  using assms by simp_all

lemma enat_cosplit_asm: 
  "P (enat_cocase c d n) = (\<not> (n = 0 \<and> \<not> P c \<or> (\<exists>m. n = eSuc m \<and> \<not> P (d m))))"
by(cases n rule: enat_coexhaust) simp_all

lemma enat_cosplit:
  "P (enat_cocase c d n) = ((n = 0 \<longrightarrow> P c) \<and> (\<forall>m. n = eSuc m \<longrightarrow> P (d m)))"
by(cases n rule: enat_coexhaust) simp_all

subsection {* Corecursion for @{typ enat} *}

definition enat_corec :: "'a \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> enat"
where [code del]:
  "enat_corec a f = 
  (if \<exists>n. ((map_comp f) ^^ n) f a = None
   then enat (LEAST n. ((map_comp f) ^^ n) f a = None) 
   else \<infinity>)"

lemma funpow_Suc_tail_rec: 
  "(f ^^ (Suc n)) a = (f ^^ n) (f a)"
by(induct n) simp_all

lemma funpow_map_comp_lem:
  "map_comp f g a = g a'
  \<Longrightarrow> ((map_comp f) ^^ (Suc n)) g a = ((map_comp f) ^^ n) g a'"
proof(induct n arbitrary: a a' g)
  case 0 thus ?case by simp
next
  case (Suc n)
  hence "(f \<circ>\<^sub>m (f \<circ>\<^sub>m g)) a = (f \<circ>\<^sub>m g) a'"
    by(simp add: map_comp_def)
  hence "((op \<circ>\<^sub>m f) ^^ (Suc n)) (f \<circ>\<^sub>m g) a = ((op \<circ>\<^sub>m f) ^^ n) (f \<circ>\<^sub>m g) a'" 
    by(rule Suc)
  thus ?case by(simp only: funpow_Suc_tail_rec)
qed

lemma enat_corec [code, nitpick_simp]:
  "enat_corec a f = (case f a of None \<Rightarrow> 0 | Some a \<Rightarrow> eSuc (enat_corec a f))"
proof(cases "\<exists>n. ((map_comp f) ^^ n) f a = None")
  case True
  let ?m = "LEAST n. ((map_comp f) ^^ n) f a = None"
  from True obtain n where n: "((map_comp f) ^^ n) f a = None" ..
  hence fpl: "((map_comp f) ^^ ?m) f a = None" by(rule LeastI)
  show ?thesis
  proof(cases "f a")
    case None
    hence "((map_comp f) ^^ 0) f a = None" by simp
    hence "enat_corec a f = enat ?m"
      unfolding enat_corec_def by(auto simp del: funpow.simps)
    also have "?m = 0"
      by(rule Least_equality, simp_all add: None)
    finally show ?thesis using None by(simp add: zero_enat_def)
  next
    case (Some a')
    from n have "enat_corec a f = enat ?m" unfolding enat_corec_def by auto
    also from n have "?m = Suc (LEAST n. ((map_comp f) ^^ (Suc n)) f a = None)"
      by(rule Least_Suc)(simp add: Some)
    also from Some have "(f \<circ>\<^sub>m f) a = f a'" by(simp add: map_comp_def)
    hence Suc_n_a_n_a': "!!n. ((op \<circ>\<^sub>m f) ^^ (Suc n)) f a = ((op \<circ>\<^sub>m f) ^^ n) f a'"
      by(rule funpow_map_comp_lem)
    hence "Suc (LEAST n. ((map_comp f) ^^ (Suc n)) f a = None) =
      Suc (LEAST n. ((map_comp f) ^^ n) f a' = None)" by simp
    also note eSuc_enat[symmetric]
    also from Some n have "n \<noteq> 0" by -(rule notI, simp)
    then obtain n' where n': "n = Suc n'" by(auto simp add: gr0_conv_Suc)
    with Suc_n_a_n_a'[of n'] n have "((map_comp f) ^^ n') f a' = None"
      by(simp only:)
    hence "enat (LEAST n. ((op \<circ>\<^sub>m f) ^^ n) f a' = None) = enat_corec a' f"
      unfolding enat_corec_def by auto
    finally show ?thesis using Some by simp
  qed
next
  case False
  hence fp: "!!n. (map_comp f ^^ n) f a \<noteq> None" by auto
  from False have "enat_corec a f = \<infinity>" unfolding enat_corec_def by auto
  moreover from fp[of 0] obtain a' where Some: "f a = Some a'" by auto
  moreover
  { fix n
    have "(f \<circ>\<^sub>m f) a = f a'" using Some by(simp add: map_comp_def)
    hence "(op \<circ>\<^sub>m f ^^ (Suc n)) f a = (op \<circ>\<^sub>m f ^^ n) f a'"
      by(rule funpow_map_comp_lem)
    with fp[of "Suc n"] have "(map_comp f ^^ n) f a' \<noteq> None" by simp }
  hence "enat_corec a' f = \<infinity>" by(simp add: enat_corec_def)
  ultimately show ?thesis by simp
qed

subsection {* Less as greatest fixpoint *}

coinductive_set Le_enat :: "(enat \<times> enat) set"
where
  Le_enat_zero: "(0, n) \<in> Le_enat"
| Le_enat_add: "\<lbrakk> (m, n) \<in> Le_enat; k \<noteq> 0 \<rbrakk> \<Longrightarrow> (eSuc m, n + k) \<in> Le_enat"

lemma ile_into_Le_enat:
  "m \<le> n \<Longrightarrow> (m, n) \<in> Le_enat"
proof -
  assume "m \<le> n" 
  hence "(m, n) \<in> {(m, n)|m n. m \<le> n}" by simp
  thus ?thesis
  proof coinduct
    case (Le_enat m n)
    hence "m \<le> n" by simp
    show ?case
    proof(cases "m = 0")
      case True
      hence ?Le_enat_zero by simp
      thus ?thesis ..
    next
      case False
      with `m \<le> n` obtain m' n' where "m = eSuc m'" "n = n' + 1" "m' \<le> n'"
        by(cases m rule: enat_coexhaust, simp)
          (cases n rule: enat_coexhaust, auto simp add: eSuc_plus_1[symmetric])
      hence ?Le_enat_add by fastsimp
      thus ?thesis ..
    qed
  qed
qed

lemma Le_enat_imp_ile_enat_k:
  "(m, n) \<in> Le_enat \<Longrightarrow> n < enat l \<Longrightarrow> m < enat l"
proof(induct l arbitrary: m n)
  case 0
  thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc l)
  from `(m, n) \<in> Le_enat` show ?case
  proof cases
    case Le_enat_zero
    with `n < enat (Suc l)` show ?thesis by auto
  next
    case (Le_enat_add M N K)
    from `n = N + K` `n < enat (Suc l)` `K \<noteq> 0`
    have "N < enat l" by(cases N)(cases K, auto simp add: zero_enat_def)
    with `(M, N) \<in> Le_enat` have "M < enat l" by(rule Suc)
    with `m = eSuc M` show ?thesis by(simp add: eSuc_enat[symmetric])
  qed
qed

lemma enat_less_imp_le:
  assumes k: "!!k. n < enat k \<Longrightarrow> m < enat k"
  shows "m \<le> n"
proof(cases n)
  case (enat n')
  with k[of "Suc n'"] show ?thesis by(cases m) simp_all
qed simp

lemma Le_enat_imp_ile:
  "(m, n) \<in> Le_enat \<Longrightarrow> m \<le> n"
by(rule enat_less_imp_le)(erule Le_enat_imp_ile_enat_k)

lemma Le_enat_eq_ile:
  "(m, n) \<in> Le_enat \<longleftrightarrow> m \<le> n"
by(blast intro: Le_enat_imp_ile ile_into_Le_enat)

lemma enat_leI [consumes 1, case_names Leenat, case_conclusion Leenat zero eSuc]:
  assumes major: "(m, n) \<in> X"
  and step:
    "\<And>m n. (m, n) \<in> X 
     \<Longrightarrow> m = 0 \<or> (\<exists>m' n' k. m = eSuc m' \<and> n = n' + enat k \<and> k \<noteq> 0 \<and>
                           ((m', n') \<in> X \<or> m' = n'))"
  shows "m \<le> n"
apply(rule Le_enat.coinduct[unfolded Le_enat_eq_ile, where X="\<lambda>m n. (m, n) \<in> X"])
apply(fastsimp simp add: zero_enat_def dest: step intro: major)+
done

subsection {* Equality as greatest fixpoint *}

lemma enat_equalityI [consumes 1, case_names Eqenat,
                                  case_conclusion Eqenat zero eSuc]:
  assumes major: "(m, n) \<in> X"
  and step:
    "\<And>m n. (m, n) \<in> X
     \<Longrightarrow> m = 0 \<and> n = 0 \<or> (\<exists>m' n'. m = eSuc m' \<and> n = eSuc n' \<and> ((m', n') \<in> X \<or> m' = n'))"
  shows "m = n"
proof(rule antisym)
  from major show "m \<le> n"
    by(coinduct rule: enat_leI)
      (drule step, auto simp add: eSuc_plus_1 enat_1[symmetric])

  from major have "(n, m) \<in> {(n, m). (m, n) \<in> X}"
    by simp
  thus "n \<le> m"
  proof(coinduct rule: enat_leI)
    case (Leenat n m)
    hence "(m, n) \<in> X" by simp
    from step[OF this] show ?case
      by(auto simp add: eSuc_plus_1 enat_1[symmetric])
  qed
qed

lemma enat_equality_funI [consumes 1, case_names zero eSuc,
                                      case_conclusion eSuc Eqzero EqeSuc]:
  assumes fun_0: "f 0 = g 0"
  and fun_eSuc: "!!n. f (eSuc n) = 0 \<and> g (eSuc n) = 0 \<or>
                    (\<exists>n1 n2. f (eSuc n) = eSuc n1 \<and> g (eSuc n) = eSuc n2 \<and>
                             ((\<exists>m. n1 = f m \<and> n2 = g m) \<or> n1 = n2))"
  shows "f n = g n"
proof -
  have "(f n, g n) \<in> {(f n, g n)|n. True}" by auto
  thus ?thesis
  proof(coinduct rule: enat_equalityI)
    case (Eqenat n1 n2)
    then obtain n where n: "n1 = f n" "n2 = g n" by auto
    show ?case
    proof(cases n rule: enat_coexhaust)
      case 0 with fun_0 have "f n = g n" by simp
      thus ?thesis using n by(cases "g n" rule: enat_coexhaust) simp_all
    next
      case (eSuc n')
      with n fun_eSuc[of n'] show ?thesis by simp
    qed
  qed
qed

subsection {* Uniqueness of corecursion *}

lemma enat_corec_unique:
  assumes h: "!!x. h x = (case f x of None \<Rightarrow> 0 | Some x' \<Rightarrow> eSuc (h x'))"
  shows "h x = enat_corec x f"
proof -
  have "(h x, enat_corec x f) \<in> {(h x, enat_corec x f)|x. True}" by blast
  thus ?thesis
  proof(coinduct rule: enat_equalityI)
    case (Eqenat n m)
    then obtain x where x: "n = h x" "m = enat_corec x f" by auto
    with h[of x] enat_corec[of x f]
    show ?case by(clarsimp split: option.split) blast
  qed
qed

lemma eSuc_minus_eSuc [simp]: "eSuc n - eSuc m = n - m"
by(simp add: eSuc_def split: enat.split)

lemma eSuc_minus_1 [simp]: "eSuc n - 1 = n"
by(simp add: one_enat_def eSuc_enat[symmetric] zero_enat_def[symmetric])

subsection {* Misc. *}

lemma enat_add_mono [simp]:
  "enat x + y < enat x + z \<longleftrightarrow> y < z"
by(cases y)(case_tac [!] z, simp_all)

lemma enat_add1_eq [simp]: "enat x + y = enat x + z \<longleftrightarrow> y = z"
by (metis enat_add_mono add_commute neq_iff)

lemma enat_add2_eq [simp]: "y + enat x = z + enat x \<longleftrightarrow> y = z"
by (metis enat_add1_eq add_commute)

lemma enat_less_enat_plusI: "x < y \<Longrightarrow> enat x < enat y + z"
by(cases z) simp_all

lemma enat_less_enat_plusI2:
  "enat y < z \<Longrightarrow> enat (x + y) < enat x + z"
by (metis enat_add_mono plus_enat_simps(1))

lemma min_enat1_conv_enat: "\<And>a b. min (enat a) b = enat (case b of enat b' \<Rightarrow> min a b' | \<infinity> \<Rightarrow> a)"
  and min_enat2_conv_enat: "\<And>a b. min a (enat b) = enat (case a of enat a' \<Rightarrow> min a' b | \<infinity> \<Rightarrow> b)"
by(simp_all split: enat.split)

end