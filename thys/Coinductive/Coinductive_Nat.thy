(*  Title:       Coinductive natural numbers
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Coinductive natural numbers *}

theory Coinductive_Nat imports
  Nat_Infinity
begin

text {*
  Coinductive natural numbers are isomorphic to natural numbers with infinity:
  View Nat\_Infinity @{typ "inat"} as codatatype
  with constructors @{term "0 :: inat"} and @{term "iSuc"}.
*}

lemma iSuc_plus: "iSuc n + m = iSuc (n + m)"
by (metis add_assoc add_commute plus_1_iSuc(2))

lemma plus_inat_eq_0_conv:
  fixes n :: inat 
  shows "n + m = 0 \<longleftrightarrow> n = 0 \<and> m = 0"
by(cases n, cases m)(simp_all add: zero_inat_def)

coinductive_set inat :: "inat \<Rightarrow> bool"
where "0 \<in> inat"
  | "n \<in> inat \<Longrightarrow> (iSuc n) \<in> inat"

lemma inat_eq_UNIV [simp]: "inat = UNIV"
proof
  show "inat \<subseteq> UNIV" by blast
  show "UNIV \<subseteq> inat"
  proof
    fix x :: inat
    assume "x \<in> UNIV"
    thus "x \<in> inat"
    proof coinduct
      case (inat x)
      show ?case
      proof(cases "x = 0")
	case True thus ?thesis by simp
      next
	case False
	then obtain n where "x = iSuc n"
	  by(cases x)(fastsimp simp add: iSuc_def zero_inat_def gr0_conv_Suc
                               split: inat.splits)+
	thus ?thesis by auto
      qed
    qed
  qed
qed

subsection {* Case operator *}

lemma inat_coexhaust:
  obtains (0) "n = 0"
     | (iSuc) n' where "n = iSuc n'"
proof -
  have "n \<in> inat" by auto
  thus thesis by cases (erule that)+
qed

definition inat_cocase :: "'a \<Rightarrow> (inat \<Rightarrow> 'a) \<Rightarrow> inat \<Rightarrow> 'a"
where [nitpick_simp]:
  "inat_cocase z s n = 
   (case n of Fin n' \<Rightarrow> (case n' of 0 \<Rightarrow> z | Suc n'' \<Rightarrow> s (Fin n'')) | Infty \<Rightarrow> s Infty)"

lemma inat_cocase_0 [simp]:
  "inat_cocase z s 0 = z"
by(simp add: inat_cocase_def zero_inat_def)

lemma inat_cocase_iSuc [simp]:
  "inat_cocase z s (iSuc n) = s n"
by(simp add: inat_cocase_def iSuc_def split: inat.splits)

lemma neq_zero_conv_iSuc:
  "n \<noteq> 0 \<longleftrightarrow> (\<exists>n'. n = iSuc n')"
by(cases n rule: inat_coexhaust) simp_all

syntax
  iSuc :: logic
translations
  "case p of 0 \<Rightarrow> a | iSuc n \<Rightarrow> b" \<rightleftharpoons> "CONST inat_cocase a (\<lambda>n. b) p"

lemma inat_cocase_cert:
  assumes "CASE \<equiv> inat_cocase c d"
  shows "(CASE 0 \<equiv> c) &&& (CASE (iSuc n) \<equiv> d n)"
  using assms by simp_all

lemma inat_cosplit_asm: 
  "P (inat_cocase c d n) = (\<not> (n = 0 \<and> \<not> P c \<or> (\<exists>m. n = iSuc m \<and> \<not> P (d m))))"
by(cases n rule: inat_coexhaust) simp_all

lemma inat_cosplit:
  "P (inat_cocase c d n) = ((n = 0 \<longrightarrow> P c) \<and> (\<forall>m. n = iSuc m \<longrightarrow> P (d m)))"
by(cases n rule: inat_coexhaust) simp_all

subsection {* Corecursion for @{typ inat} *}

definition inat_corec :: "'a \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> inat"
where [code del]:
  "inat_corec a f = 
  (if \<exists>n. ((map_comp f) ^^ n) f a = None
   then Fin (LEAST n. ((map_comp f) ^^ n) f a = None) 
   else Infty)"

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

lemma inat_corec [code, nitpick_simp]:
  "inat_corec a f = (case f a of None \<Rightarrow> 0 | Some a \<Rightarrow> iSuc (inat_corec a f))"
proof(cases "\<exists>n. ((map_comp f) ^^ n) f a = None")
  case True
  let ?m = "LEAST n. ((map_comp f) ^^ n) f a = None"
  from True obtain n where n: "((map_comp f) ^^ n) f a = None" ..
  hence fpl: "((map_comp f) ^^ ?m) f a = None" by(rule LeastI)
  show ?thesis
  proof(cases "f a")
    case None
    hence "((map_comp f) ^^ 0) f a = None" by simp
    hence "inat_corec a f = Fin ?m"
      unfolding inat_corec_def by(auto simp del: funpow.simps)
    also have "?m = 0"
      by(rule Least_equality, simp_all add: None)
    finally show ?thesis using None by(simp add: zero_inat_def)
  next
    case (Some a')
    from n have "inat_corec a f = Fin ?m" unfolding inat_corec_def by auto
    also from n have "?m = Suc (LEAST n. ((map_comp f) ^^ (Suc n)) f a = None)"
      by(rule Least_Suc)(simp add: Some)
    also from Some have "(f \<circ>\<^sub>m f) a = f a'" by(simp add: map_comp_def)
    hence Suc_n_a_n_a': "!!n. ((op \<circ>\<^sub>m f) ^^ (Suc n)) f a = ((op \<circ>\<^sub>m f) ^^ n) f a'"
      by(rule funpow_map_comp_lem)
    hence "Suc (LEAST n. ((map_comp f) ^^ (Suc n)) f a = None) =
      Suc (LEAST n. ((map_comp f) ^^ n) f a' = None)" by simp
    also note iSuc_Fin[symmetric]
    also from Some n have "n \<noteq> 0" by -(rule notI, simp)
    then obtain n' where n': "n = Suc n'" by(auto simp add: gr0_conv_Suc)
    with Suc_n_a_n_a'[of n'] n have "((map_comp f) ^^ n') f a' = None"
      by(simp only:)
    hence "Fin (LEAST n. ((op \<circ>\<^sub>m f) ^^ n) f a' = None) = inat_corec a' f"
      unfolding inat_corec_def by auto
    finally show ?thesis using Some by simp
  qed
next
  case False
  hence fp: "!!n. (map_comp f ^^ n) f a \<noteq> None" by auto
  from False have "inat_corec a f = Infty" unfolding inat_corec_def by auto
  moreover from fp[of 0] obtain a' where Some: "f a = Some a'" by auto
  moreover
  { fix n
    have "(f \<circ>\<^sub>m f) a = f a'" using Some by(simp add: map_comp_def)
    hence "(op \<circ>\<^sub>m f ^^ (Suc n)) f a = (op \<circ>\<^sub>m f ^^ n) f a'"
      by(rule funpow_map_comp_lem)
    with fp[of "Suc n"] have "(map_comp f ^^ n) f a' \<noteq> None" by simp }
  hence "inat_corec a' f = Infty" by(simp add: inat_corec_def)
  ultimately show ?thesis by simp
qed

subsection {* Less as greatest fixpoint *}

coinductive_set Le_inat :: "(inat \<times> inat) set"
where
  Le_inat_zero: "(0, n) \<in> Le_inat"
| Le_inat_add: "\<lbrakk> (m, n) \<in> Le_inat; k \<noteq> 0 \<rbrakk> \<Longrightarrow> (iSuc m, n + k) \<in> Le_inat"

lemma ile_into_Le_inat:
  "m \<le> n \<Longrightarrow> (m, n) \<in> Le_inat"
proof -
  assume "m \<le> n" 
  hence "(m, n) \<in> {(m, n)|m n. m \<le> n}" by simp
  thus ?thesis
  proof coinduct
    case (Le_inat m n)
    hence "m \<le> n" by simp
    show ?case
    proof(cases "m = 0")
      case True
      hence ?Le_inat_zero by simp
      thus ?thesis ..
    next
      case False
      with `m \<le> n` obtain m' n' where "m = iSuc m'" "n = n' + 1" "m' \<le> n'"
	by(cases m rule: inat_coexhaust, simp)
          (cases n rule: inat_coexhaust, auto simp add: iSuc_plus_1[symmetric])
      hence ?Le_inat_add by fastsimp
      thus ?thesis ..
    qed
  qed
qed

lemma Le_inat_imp_ile_Fin_k:
  "(m, n) \<in> Le_inat \<Longrightarrow> n < Fin l \<Longrightarrow> m < Fin l"
proof(induct l arbitrary: m n)
  case 0
  thus ?case by(simp add: zero_inat_def[symmetric])
next
  case (Suc l)
  from `(m, n) \<in> Le_inat` show ?case
  proof cases
    case Le_inat_zero
    with `n < Fin (Suc l)` show ?thesis by auto
  next
    case (Le_inat_add M N K)
    from `n = N + K` `n < Fin (Suc l)` `K \<noteq> 0`
    have "N < Fin l" by(cases N)(cases K, auto simp add: zero_inat_def)
    with `(M, N) \<in> Le_inat` have "M < Fin l" by(rule Suc)
    with `m = iSuc M` show ?thesis by(simp add: iSuc_Fin[symmetric])
  qed
qed

lemma inat_less_imp_le:
  assumes k: "!!k. n < Fin k \<Longrightarrow> m < Fin k"
  shows "m \<le> n"
proof(cases n)
  case (Fin n')
  with k[of "Suc n'"] show ?thesis by(cases m) simp_all
qed simp

lemma Le_inat_imp_ile:
  "(m, n) \<in> Le_inat \<Longrightarrow> m \<le> n"
by(rule inat_less_imp_le)(erule Le_inat_imp_ile_Fin_k)

lemma Le_inat_eq_ile:
  "(m, n) \<in> Le_inat \<longleftrightarrow> m \<le> n"
by(blast intro: Le_inat_imp_ile ile_into_Le_inat)

lemma inat_leI [consumes 1, case_names Leinat, case_conclusion Leinat zero iSuc]:
  assumes major [simplified mem_def]: "(m, n) \<in> X"
  and step [simplified mem_def]:
    "\<And>m n. (m, n) \<in> X 
     \<Longrightarrow> m = 0 \<or> (\<exists>m' n' k. m = iSuc m' \<and> n = n' + Fin k \<and> k \<noteq> 0 \<and>
                           ((m', n') \<in> X \<or> m' = n'))"
  shows "m \<le> n"
apply(rule Le_inat.coinduct[unfolded Le_inat_eq_ile, where X="curry X"])
apply(fastsimp simp add: mem_def zero_inat_def dest: step intro: major)+
done

subsection {* Equality as greatest fixpoint *}

lemma inat_equalityI [consumes 1, case_names Eqinat,
                                  case_conclusion Eqinat zero iSuc]:
  assumes major: "(m, n) \<in> X"
  and step:
    "\<And>m n. (m, n) \<in> X
     \<Longrightarrow> m = 0 \<and> n = 0 \<or> (\<exists>m' n'. m = iSuc m' \<and> n = iSuc n' \<and> ((m', n') \<in> X \<or> m' = n'))"
  shows "m = n"
proof(rule antisym)
  from major show "m \<le> n"
    by(coinduct rule: inat_leI)
      (drule step, auto simp add: iSuc_plus_1 Fin_1[symmetric])

  from major have "(n, m) \<in> (\<lambda>(n, m). (m, n) \<in> X)"
    by(simp add: mem_def)
  thus "n \<le> m"
  proof(coinduct rule: inat_leI)
    case (Leinat n m)
    hence "(m, n) \<in> X" by(simp add: mem_def)
    from step[OF this] show ?case
      by(auto simp add: mem_def iSuc_plus_1 Fin_1[symmetric])
  qed
qed

lemma inat_equality_funI [consumes 1, case_names zero iSuc,
                                      case_conclusion iSuc Eqzero EqiSuc]:
  assumes fun_0: "f 0 = g 0"
  and fun_iSuc: "!!n. f (iSuc n) = 0 \<and> g (iSuc n) = 0 \<or>
                    (\<exists>n1 n2. f (iSuc n) = iSuc n1 \<and> g (iSuc n) = iSuc n2 \<and>
                             ((\<exists>m. n1 = f m \<and> n2 = g m) \<or> n1 = n2))"
  shows "f n = g n"
proof -
  have "(f n, g n) \<in> {(f n, g n)|n. True}" by auto
  thus ?thesis
  proof(coinduct rule: inat_equalityI)
    case (Eqinat n1 n2)
    then obtain n where n: "n1 = f n" "n2 = g n" by auto
    show ?case
    proof(cases n rule: inat_coexhaust)
      case 0 with fun_0 have "f n = g n" by simp
      thus ?thesis using n by(cases "g n" rule: inat_coexhaust) simp_all
    next
      case (iSuc n')
      with n fun_iSuc[of n'] show ?thesis by simp
    qed
  qed
qed

subsection {* Uniqueness of corecursion *}

lemma inat_corec_unique:
  assumes h: "!!x. h x = (case f x of None \<Rightarrow> 0 | Some x' \<Rightarrow> iSuc (h x'))"
  shows "h x = inat_corec x f"
proof -
  have "(h x, inat_corec x f) \<in> {(h x, inat_corec x f)|x. True}" by blast
  thus ?thesis
  proof(coinduct rule: inat_equalityI)
    case (Eqinat n m)
    then obtain x where x: "n = h x" "m = inat_corec x f" by auto
    with h[of x] inat_corec[of x f]
    show ?case by(clarsimp split: option.split) blast
  qed
qed

subsection {* minus for @{typ inat} *}

instantiation inat :: minus begin

definition
  "minus n m = (case n of Fin n \<Rightarrow> (case m of Fin m \<Rightarrow> Fin (n - m) | \<infinity> \<Rightarrow> 0) 
                            | \<infinity> \<Rightarrow> \<infinity>)"

instance ..

end

lemma minus_inat_simps [simp]:
  "Fin n - Fin m = Fin (n - m)"
  "Fin n - \<infinity> = 0"
  "0 - n' = 0"
  "\<infinity> - n' = \<infinity>"
  "n' - 0 = n'"
by(simp_all add: minus_inat_def zero_inat_def split: inat.split)

lemma iSuc_minus_iSuc [simp]: "iSuc n - iSuc m = n - m"
by(simp add: iSuc_def split: inat.split)

lemma iSuc_minus_1 [simp]: "iSuc n - 1 = n"
by(simp add: one_inat_def iSuc_Fin[symmetric] zero_inat_def[symmetric])

subsection {* Misc. *}

lemma Fin_add_mono [simp]:
  "Fin x + y < Fin x + z \<longleftrightarrow> y < z"
by(cases y)(case_tac [!] z, simp_all)

lemma Fin_add1_eq [simp]: "Fin x + y = Fin x + z \<longleftrightarrow> y = z"
by (metis Fin_add_mono add_commute neq_iff)

lemma Fin_add2_eq [simp]: "y + Fin x = z + Fin x \<longleftrightarrow> y = z"
by (metis Fin_add1_eq add_commute)

primrec the_Fin :: "inat \<Rightarrow> nat"
where "the_Fin (Fin n) = n"

lemma Fin_less_Fin_plusI: "x < y \<Longrightarrow> Fin x < Fin y + z"
by(cases z) simp_all

lemma Fin_less_Fin_plusI2:
  "Fin y < z \<Longrightarrow> Fin (x + y) < Fin x + z"
by (metis Fin_add_mono nat_add_commute plus_inat_simps(1))

lemma min_Fin1_conv_Fin: "\<And>a b. min (Fin a) b = Fin (case b of Fin b' \<Rightarrow> min a b' | \<infinity> \<Rightarrow> a)"
  and min_Fin2_conv_Fin: "\<And>a b. min a (Fin b) = Fin (case a of Fin a' \<Rightarrow> min a' b | \<infinity> \<Rightarrow> b)"
by(simp_all split: inat.split)

end