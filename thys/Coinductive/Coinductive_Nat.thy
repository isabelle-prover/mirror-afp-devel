(*  Title:       Coinductive natural numbers
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Coinductive natural numbers *}

theory Coinductive_Nat imports
  "~~/src/HOL/Library/Extended_Nat"
begin

lemmas eSuc_plus = iadd_Suc

lemmas plus_enat_eq_0_conv = iadd_is_0

lemma enat_add_sub_same:
  fixes a b :: enat shows "a \<noteq> \<infinity> \<Longrightarrow> a + b - a = b"
by(cases b) auto

lemma enat_the_enat: "n \<noteq> \<infinity> \<Longrightarrow> enat (the_enat n) = n"
by auto

lemma enat_min_eq_0_iff:
  fixes a b :: enat
  shows "min a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
by(auto simp add: min_def)

lemma enat_le_plus_same: "x \<le> (x :: enat) + y" "x \<le> y + x"
by(auto simp add: less_eq_enat_def plus_enat_def split: enat.split)

lemma the_enat_0 [simp]: "the_enat 0 = 0"
by(simp add: zero_enat_def)

lemma the_enat_eSuc: "n \<noteq> \<infinity> \<Longrightarrow> the_enat (eSuc n) = Suc (the_enat n)"
by(cases n)(simp_all add: eSuc_enat)

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
          by(cases x)(fastforce simp add: eSuc_def zero_enat_def gr0_conv_Suc
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

locale co begin

wrap_free_constructors (no_code) ["0::enat", eSuc] enat_case [=] [[], [epred]] [[epred: "0::enat"]]
  apply (erule enat_coexhaust, assumption)
 apply (rule eSuc_inject)
by (rule zero_ne_eSuc)

end

lemma enat_cocase_0 [simp]: "co.enat_case z s 0 = z"
by (rule co.enat.case(1))

lemma enat_cocase_eSuc [simp]: "co.enat_case z s (eSuc n) = s n"
by (rule co.enat.case(2))

lemma neq_zero_conv_eSuc: "n \<noteq> 0 \<longleftrightarrow> (\<exists>n'. n = eSuc n')"
by(cases n rule: enat_coexhaust) simp_all

lemma enat_cocase_cert:
  assumes "CASE \<equiv> co.enat_case c d"
  shows "(CASE 0 \<equiv> c) &&& (CASE (eSuc n) \<equiv> d n)"
  using assms by simp_all

lemma enat_cosplit_asm:
  "P (co.enat_case c d n) = (\<not> (n = 0 \<and> \<not> P c \<or> (\<exists>m. n = eSuc m \<and> \<not> P (d m))))"
by (rule co.enat.split_asm)

lemma enat_cosplit:
  "P (co.enat_case c d n) = ((n = 0 \<longrightarrow> P c) \<and> (\<forall>m. n = eSuc m \<longrightarrow> P (d m)))"
by (rule co.enat.split)

abbreviation epred :: "enat => enat" where "epred \<equiv> co.epred"

lemma epred_0 [simp]: "epred 0 = 0" by(rule co.enat.sel(1))
lemma epred_eSuc [simp]: "epred (eSuc n) = n" by(rule co.enat.sel(2))
declare co.enat.collapse[simp]
lemma epred_conv_minus: "epred n = n - 1"
by(cases n rule: co.enat.exhaust)(simp_all)

subsection {* Corecursion for @{typ enat} *}

lemma enat_case_numeral [simp]: "enat_case f i (numeral v) = (let n = numeral v in f n)"
by(simp add: numeral_eq_enat)

lemma enat_case_0 [simp]: "enat_case f i 0 = f 0"
by(simp add: zero_enat_def)

lemma [simp]:
  shows max_eSuc_eSuc: "max (eSuc n) (eSuc m) = eSuc (max n m)"
  and min_eSuc_eSuc: "min (eSuc n) (eSuc m) = eSuc (min n m)"
by(simp_all add: eSuc_def split: enat.split)


definition epred_numeral :: "num \<Rightarrow> enat"
where [code del]: "epred_numeral = enat \<circ> pred_numeral"

lemma numeral_eq_eSuc: "numeral k = eSuc (epred_numeral k)"
by(simp add: numeral_eq_Suc eSuc_def epred_numeral_def numeral_eq_enat)

lemma epred_numeral_simps [simp]:
  "epred_numeral num.One = 0"
  "epred_numeral (num.Bit0 k) = numeral (Num.BitM k)"
  "epred_numeral (num.Bit1 k) = numeral (num.Bit0 k)"
by(simp_all add: epred_numeral_def enat_numeral zero_enat_def)

lemma [simp]:
  shows eq_numeral_eSuc: "numeral k = eSuc n \<longleftrightarrow> epred_numeral k = n"
  and Suc_eq_numeral: "eSuc n = numeral k \<longleftrightarrow> n = epred_numeral k"
  and less_numeral_Suc: "numeral k < eSuc n \<longleftrightarrow> epred_numeral k < n"
  and less_eSuc_numeral: "eSuc n < numeral k \<longleftrightarrow> n < epred_numeral k"
  and le_numeral_eSuc: "numeral k \<le> eSuc n \<longleftrightarrow> epred_numeral k \<le> n"
  and le_eSuc_numeral: "eSuc n \<le> numeral k \<longleftrightarrow> n \<le> epred_numeral k"
  and diff_eSuc_numeral: "eSuc n - numeral k = n - epred_numeral k"
  and diff_numeral_eSuc: "numeral k - eSuc n = epred_numeral k - n"
  and max_eSuc_numeral: "max (eSuc n) (numeral k) = eSuc (max n (epred_numeral k))"
  and max_numeral_eSuc: "max (numeral k) (eSuc n) = eSuc (max (epred_numeral k) n)"
  and min_eSuc_numeral: "min (eSuc n) (numeral k) = eSuc (min n (epred_numeral k))"
  and min_numeral_eSuc: "min (numeral k) (eSuc n) = eSuc (min (epred_numeral k) n)"
by(simp_all add: numeral_eq_eSuc)

lemma enat_cocase_numeral [simp]:
  "co.enat_case a f (numeral v) = (let pv = epred_numeral v in f pv)"
by(simp add: numeral_eq_eSuc)

lemma enat_cocase_add_eq_if [simp]:
  "co.enat_case a f ((numeral v) + n) = (let pv = epred_numeral v in f (pv + n))"
by(simp add: numeral_eq_eSuc iadd_Suc)


lemma [simp]:
  shows epred_1: "epred 1 = 0"
  and epred_numeral: "epred (numeral i) = epred_numeral i"
  and epred_Infty: "epred \<infinity> = \<infinity>"
  and epred_enat: "epred (enat m) = enat (m - 1)"
by(simp_all add: epred_conv_minus one_enat_def zero_enat_def eSuc_def epred_numeral_def numeral_eq_enat split: enat.split)

lemmas epred_simps = epred_0 epred_1 epred_numeral epred_eSuc epred_Infty epred_enat

lemma epred_iadd1: "a \<noteq> 0 \<Longrightarrow> epred (a + b) = epred a + b"
apply(cases a b rule: enat.exhaust[case_product enat.exhaust])
apply(simp_all add: epred_conv_minus eSuc_def one_enat_def zero_enat_def split: enat.splits)
done

lemma epred_min [simp]: "epred (min a b) = min (epred a) (epred b)"
by(cases a b rule: enat_coexhaust[case_product enat_coexhaust]) simp_all

lemma epred_le_epredI: "n \<le> m \<Longrightarrow> epred n \<le> epred m"
by(cases m n rule: enat_coexhaust[case_product enat_coexhaust]) simp_all

lemma epred_minus_epred [simp]:
  "m \<noteq> 0 \<Longrightarrow> epred n - epred m = n - m"
by(cases n m rule: enat_coexhaust[case_product enat_coexhaust])(simp_all add: epred_conv_minus)

lemma eSuc_epred: "n \<noteq> 0 \<Longrightarrow> eSuc (epred n) = n"
by(cases n rule: enat_coexhaust) simp_all

lemma epred_inject: "\<lbrakk> x \<noteq> 0; y \<noteq> 0 \<rbrakk> \<Longrightarrow> epred x = epred y \<longleftrightarrow> x = y"
by(cases x y rule: enat.exhaust[case_product enat.exhaust])(auto simp add: zero_enat_def)



definition enat_unfold :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> enat"
where "enat_unfold stop next a =
  (if \<exists>n. stop ((next ^^ n) a)
   then enat (LEAST n. stop ((next ^^ n) a))
   else \<infinity>)"

lemma enat_unfold [code, nitpick_simp]:
  "enat_unfold stop next a =
  (if stop a then 0 else eSuc (enat_unfold stop next (next a)))"
  (is "?lhs = ?rhs")
proof(cases "\<exists>n. stop ((next ^^ n) a)")
  case True
  let ?P = "\<lambda>n. stop ((next ^^ n) a)"
  let ?m = "Least ?P"
  from True obtain n where n: "?P n" ..
  hence "?P ?m" by(rule LeastI)
  show ?thesis
  proof(cases "stop a")
    case True
    thus ?thesis
      by(auto simp add: enat_unfold_def zero_enat_def intro: Least_equality exI[where x=0])
  next
    case False
    with n obtain n' where n': "n = Suc n'" by(cases n) auto
    from n have "?lhs = enat ?m" by(auto simp add: enat_unfold_def)
    also from n have "?m = Suc (LEAST n. ?P (Suc n))"
      by(rule Least_Suc)(simp add: False)
    finally show ?thesis using False n n'
      by(auto simp add: eSuc_enat[symmetric] funpow_swap1 enat_unfold_def)
  qed
qed(auto simp add: enat_unfold_def funpow_swap1 elim: allE[where x=0] allE[where x="Suc n" for n])

lemma enat_unfold_stop [simp]: "stop a \<Longrightarrow> enat_unfold stop next a = 0"
by(simp add: enat_unfold)

lemma enat_unfold_next: "\<not> stop a \<Longrightarrow> enat_unfold stop next a = eSuc (enat_unfold stop next (next a))"
by(simp add: enat_unfold)

lemma enat_unfold_eq_0 [simp]:
  "enat_unfold stop next a = 0 \<longleftrightarrow> stop a"
by(simp add: enat_unfold)

lemma epred_enat_unfold [simp]:
  "epred (enat_unfold stop next a) = (if stop a then 0 else enat_unfold stop next (next a))"
by(simp add: enat_unfold_next)


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
      hence ?Le_enat_add by fastforce
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
                           ((m', n') \<in> X \<or> m' \<le> n'))"
  shows "m \<le> n"
apply(rule Le_enat.coinduct[unfolded Le_enat_eq_ile, where X="\<lambda>x y. (x, y) \<in> X"])
apply(fastforce simp add: zero_enat_def dest: step intro: major)+
done

lemma enat_le_coinduct[consumes 1, case_names le, case_conclusion le 0 eSuc]:
  assumes P: "P m n"
  and step:
    "\<And>m n. P m n 
     \<Longrightarrow> (n = 0 \<longrightarrow> m = 0) \<and>
         (m \<noteq> 0 \<longrightarrow> n \<noteq> 0 \<longrightarrow> (\<exists>k n'. P (epred m) n' \<and> epred n = n' + k) \<or> epred m \<le> epred n)"
  shows "m \<le> n"
proof -
  from P have "(m, n) \<in> {(m, n). P m n}" by simp
  thus ?thesis
  proof(coinduct rule: enat_leI)
    case (Leenat m n)
    hence "P m n" by simp
    show ?case
    proof(cases m rule: enat_coexhaust)
      case 0 
      thus ?thesis by simp
    next
      case (eSuc m')
      with step[OF `P m n`]
      have "n \<noteq> 0" and disj: "(\<exists>k n'. P m' n' \<and> epred n = n' + k) \<or> m' \<le> epred n" by auto
      from `n \<noteq> 0` obtain n' where n': "n = eSuc n'"
        by(cases n rule: enat_coexhaust) auto
      from disj show ?thesis
      proof
        assume "m' \<le> epred n"
        with eSuc n' show ?thesis 
          by(auto 4 3 intro: exI[where x="Suc 0"] simp add: eSuc_enat[symmetric] iadd_Suc_right zero_enat_def[symmetric])
      next
        assume "\<exists>k n'. P m' n' \<and> epred n = n' + k"
        then obtain k n'' where n'': "epred n = n'' + k" and k: "P m' n''" by blast
        show ?thesis using eSuc k n' n''
          by(cases k)(auto 4 3 simp add: iadd_Suc_right[symmetric] eSuc_enat intro: exI[where x=\<infinity>])
      qed
    qed
  qed
qed

subsection {* Equality as greatest fixpoint *}

lemma enat_equalityI [consumes 1, case_names Eq_enat,
                                  case_conclusion Eq_enat zero eSuc]:
  assumes major: "(m, n) \<in> X"
  and step:
    "\<And>m n. (m, n) \<in> X
     \<Longrightarrow> m = 0 \<and> n = 0 \<or> (\<exists>m' n'. m = eSuc m' \<and> n = eSuc n' \<and> ((m', n') \<in> X \<or> m' = n'))"
  shows "m = n"
proof(rule antisym)
  from major show "m \<le> n"
    by(coinduct rule: enat_leI)
      (drule step, auto simp add: eSuc_plus_1 enat_1[symmetric])

  from major have "(n, m) \<in> {(n, m). (m, n) \<in> X}" by simp
  thus "n \<le> m"
  proof(coinduct rule: enat_leI)
    case (Leenat n m)
    hence "(m, n) \<in> X" by simp
    from step[OF this] show ?case
      by(auto simp add: eSuc_plus_1 enat_1[symmetric])
  qed
qed

lemma enat_coinduct [consumes 1, case_names Eq_enat, case_conclusion Eq_enat zero eSuc]:
  assumes major: "P m n"
  and step: "\<And>m n. P m n 
    \<Longrightarrow> (m = 0 \<longleftrightarrow> n = 0) \<and>
       (m \<noteq> 0 \<longrightarrow> n \<noteq> 0 \<longrightarrow> P (epred m) (epred n) \<or> epred m = epred n)"
  shows "m = n"
proof -
  from major have "(m, n) \<in> {(m, n). P m n}" by simp
  thus ?thesis
  proof(coinduct rule: enat_equalityI)
    case (Eq_enat m n)
    hence "P m n" by simp
    from step[OF this] show ?case
      by(cases m n rule: enat_coexhaust[case_product enat_coexhaust]) auto
  qed
qed

lemma enat_coinduct2 [consumes 1, case_names zero eSuc]:
  "\<lbrakk> P m n; \<And>m n. P m n \<Longrightarrow> m = 0 \<longleftrightarrow> n = 0; 
     \<And>m n. \<lbrakk> P m n; m \<noteq> 0; n \<noteq> 0 \<rbrakk> \<Longrightarrow> P (epred m) (epred n) \<or> epred m = epred n \<rbrakk>
  \<Longrightarrow> m = n"
by(erule enat_coinduct) blast

subsection {* Uniqueness of corecursion *}

lemma enat_unfold_unique:
  assumes h: "!!x. h x = (if stop x then 0 else eSuc (h (next x)))"
  shows "h x = enat_unfold stop next x"
by(coinduction arbitrary: x rule: enat_coinduct)(subst (1 3) h, auto)

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
