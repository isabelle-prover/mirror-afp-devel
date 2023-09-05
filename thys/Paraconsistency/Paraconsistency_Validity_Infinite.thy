(* Anders Schlichtkrull, DTU Compute, Denmark *)

theory Paraconsistency_Validity_Infinite imports Paraconsistency
  abbrevs
    "Truth" = "\<^bold>\<top>"
    and
    "Falsity" = "\<^bold>\<bottom>"
    and
    "Neg'" = "\<^bold>\<not>"
    and
    "Con'" = "\<^bold>\<and>"
    and
    "Eql" = "\<^bold>\<Leftrightarrow>"
    and
    "Eql'" = "\<^bold>\<leftrightarrow>"
    and
    "Dis'" = "\<^bold>\<or>"
    and
    "Imp" = "\<^bold>\<Rightarrow>"
    and
    "Imp'" = "\<^bold>\<rightarrow>"
    and
    "Box" = "\<^bold>\<box>"
    and
    "Neg" = "\<^bold>\<rightharpoondown>\<^bold>\<rightharpoondown>"
    and
    "Con" = "\<^bold>\<and>\<^bold>\<and>"
    and
    "Dis" = "\<^bold>\<or>\<^bold>\<or>"
    and
    "Cla" = "\<^bold>\<Delta>"
    and
    "Nab" = "\<^bold>\<nabla>"
    and
    "CON" = "[\<^bold>\<and>\<^bold>\<and>]"
    and
    "DIS" = "[\<^bold>\<or>\<^bold>\<or>]"
    and
    "NAB" = "[\<^bold>\<nabla>]"
    and
    "ExiEql" = "[\<^bold>\<exists>\<^bold>=]"
begin

text
\<open>
The details about the definitions, lemmas and theorems are described in an article in the
Post-proceedings of the 24th International Conference on Types for Proofs and Programs (TYPES 2018).
\<close>

section \<open>Notation\<close>

notation Pro ("\<langle>_\<rangle>" [39] 39)
notation Truth ("\<^bold>\<top>")
notation Neg' ("\<^bold>\<not> _" [40] 40)
notation Con' (infixr "\<^bold>\<and>" 35)
notation Eql (infixr "\<^bold>\<Leftrightarrow>" 25)
notation Eql' (infixr "\<^bold>\<leftrightarrow>" 25)
notation Falsity ("\<^bold>\<bottom>")
notation Dis' (infixr "\<^bold>\<or>" 30) 
notation Imp (infixr "\<^bold>\<Rightarrow>" 25) 
notation Imp' (infixr "\<^bold>\<rightarrow>" 25)
notation Box ("\<^bold>\<box> _" [40] 40) 
notation Neg ("\<^bold>\<rightharpoondown>\<^bold>\<rightharpoondown> _" [40] 40)
notation Con (infixr "\<^bold>\<and>\<^bold>\<and>" 35) 
notation Dis (infixr "\<^bold>\<or>\<^bold>\<or>" 30)
notation Cla ("\<^bold>\<Delta> _" [40] 40) 
notation Nab ("\<^bold>\<nabla> _" [40] 40)
abbreviation DetTrue :: tv ("\<bullet>") where "\<bullet> \<equiv> Det True"
abbreviation DetFalse :: tv ("\<circ>") where "\<circ> \<equiv> Det False"
notation Indet ("\<lfloor>_\<rfloor>" [39] 39)

text 
\<open>
Strategy: We define a formula that is valid in the sets {0..<1}, {0..<2}, ..., {0..<n-1} but is
not valid in the set {0..<n}
\<close>

section \<open>Injections From Sets to Sets\<close>

text 
\<open>
We define the notion of an injection from a set X to a set Y 
\<close>

definition inj_from_to :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "inj_from_to f X Y \<equiv> inj_on f X \<and> f ` X \<subseteq> Y"

lemma bij_betw_inj_from_to: "bij_betw f X Y \<Longrightarrow> inj_from_to f X Y"
  unfolding bij_betw_def inj_from_to_def by simp

text 
\<open>
Special lemma for finite cardinality only
\<close>

lemma inj_from_to_if_card:
  assumes "card X \<le> card Y"
  assumes "finite X"
  shows "\<exists>f. inj_from_to f X Y"
  unfolding inj_from_to_def
  by (metis assms card_image card_le_inj card_subset_eq obtain_subset_with_card_n order_refl)

section \<open>Extension of Paraconsistency Theory\<close>

text 
\<open>
The Paraconsistency theory is extended with abbreviation \<open>is_det\<close> and a number of lemmas that are 
or generalizations of previous lemmas
\<close>

abbreviation is_det :: "tv \<Rightarrow> bool" where "is_det tv \<equiv> \<not> is_indet tv"

theorem valid_iff_valid_in:
  assumes "card U \<ge> card (props p)"
  shows "valid p \<longleftrightarrow> valid_in U p"
  using assms valid_in_valid valid_valid_in by blast

text 
\<open>
Generalization of \<open>change_tv_injection\<close>
\<close>

lemma change_tv_injection_on:
  assumes "inj_on f U"
  shows "inj_on (change_tv f) (domain U)"
proof
  fix x y
  assume "x \<in> domain U" "y \<in> domain U" "change_tv f x = change_tv f y"
  then show "x = y"
    unfolding domain_def using assms inj_onD by (cases x; cases y) auto
qed

text 
\<open>
Similar to \<open>change_tv_injection_on\<close>
\<close>

lemma change_tv_injection_from_to:
  assumes "inj_from_to f U W"
  shows "inj_from_to (change_tv f) (domain U) (domain W)"
  unfolding inj_from_to_def
proof
  show "inj_on (change_tv f) (domain U)"
    using assms change_tv_injection_on unfolding inj_from_to_def by blast
next
  show "change_tv f ` domain U \<subseteq> domain W"
  proof
    fix x
    assume "x \<in> change_tv f ` domain U"
    then show "x \<in> domain W"
      unfolding domain_def image_def
      using assms inj_from_to_def[of f U W]
      by (cases x) auto
  qed
qed

text 
\<open>
Similar to \<open>eval_change_inj_on\<close>
\<close>

lemma change_tv_surj_on:
  assumes "f ` U = W"
  shows "(change_tv f) ` (domain U) = (domain W)"
proof
  show "change_tv f ` domain U \<subseteq> domain W"
  proof
    fix x
    assume "x \<in> change_tv f ` domain U"
    then show "x \<in> domain W"
    proof
      fix x'
      assume "x = change_tv f x'" "x' \<in> domain U"
      then show "x \<in> domain W"
        unfolding domain_def using assms by fastforce
    qed
  qed
next
  show "domain W \<subseteq> change_tv f ` domain U"
  proof
    fix x
    assume "x \<in> domain W"
    then show "x \<in> change_tv f ` domain U"
      unfolding domain_def using assms image_iff by fastforce
  qed
qed

text 
\<open>
Similar to \<open>eval_change_inj_on\<close>
\<close>

lemma change_tv_bij_betw:
  assumes "bij_betw f U W"
  shows "bij_betw (change_tv f) (domain U) (domain W)"
  using assms change_tv_injection_on change_tv_surj_on unfolding bij_betw_def by simp

text 
\<open>
Generalization of \<open>eval_change\<close>
\<close>

lemma eval_change_inj_on:
  assumes "inj_on f U"
  assumes "range i \<subseteq> domain U"
  shows "eval (change_int f i) p = change_tv f (eval i p)"
proof (induct p)
  fix p
  assume "eval (change_int f i) p = change_tv f (eval i p)"
  then have "eval_neg (eval (change_int f i) p) = eval_neg (change_tv f (eval i p))"
    by simp
  then have "eval_neg (eval (change_int f i) p) = change_tv f (eval_neg (eval i p))"
    by (cases "eval i p") (simp_all add: case_bool_if)
  then show "eval (change_int f i) (\<^bold>\<not> p) = change_tv f (eval i (\<^bold>\<not> p))"
    by simp
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  show "eval (change_int f i) (p1 \<^bold>\<and> p2) = change_tv f (eval i (p1 \<^bold>\<and> p2))"
    using assms ih1 ih2 change_tv.simps(1) change_tv_injection_on eval.simps(2) eval.simps(4)
      inj_onD ranges by metis
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  have "Det (eval (change_int f i) p1 = eval (change_int f i) p2) =
      Det (change_tv f (eval i p1) = change_tv f (eval i p2))"
    using ih1 ih2 by simp
  also have "... = Det ((eval i p1) = (eval i p2))"
  proof -
    have "inj_on (change_tv f) (domain U)"
      using assms(1) change_tv_injection_on by simp
    then show ?thesis
      using assms(2) ranges by (simp add: inj_on_eq_iff)
  qed
  also have "... = change_tv f (Det (eval i p1 = eval i p2))"
    by simp
  finally show "eval (change_int f i) (p1 \<^bold>\<Leftrightarrow> p2) = change_tv f (eval i (p1 \<^bold>\<Leftrightarrow> p2))"
    by simp
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  show "eval (change_int f i) (p1 \<^bold>\<leftrightarrow> p2) = change_tv f (eval i (p1 \<^bold>\<leftrightarrow> p2))"
    using assms ih1 ih2 inj_on_eq_iff change_tv.simps(1) change_tv_injection_on eval_equality
      eval_negation ranges by smt
qed (simp_all add: change_int_def)

section \<open>Logics of Equal Cardinality Are Equal\<close>

text 
\<open>
We prove that validity in a set depends only on the cardinality of the set
\<close>

lemma inj_from_to_valid_in:
  assumes "inj_from_to f W U"
  assumes "valid_in U p"
  shows "valid_in W p"
  unfolding valid_in_def proof (rule, rule)
  fix i :: "char list \<Rightarrow> tv"
  assume a: "range i \<subseteq> domain W"
  from assms have valid_p: "\<forall>i. range i \<subseteq> domain U \<longrightarrow> eval i p = \<bullet>"
    unfolding valid_in_def by simp
  have "range (change_int f i) \<subseteq> domain U"
  proof
    fix x
    assume "x \<in> range (change_int f i)"
    then obtain xa where xa: "change_int f i xa = x"
      by blast
    have "inj_from_to (change_tv f) (domain W) (domain U)"
      using change_tv_injection_from_to assms by simp
    then have "(change_tv f) (i xa) \<in> domain U"
      using a by (metis inj_from_to_def image_eqI range_eqI subsetCE)
    then show "x \<in> domain U"
      using xa change_int_def by simp
  qed
  then have "eval (change_int f i) p = \<bullet>"
    using valid_p by simp
  then have "eval (change_int f i) p = \<bullet>"
    by simp
  then have "change_tv f (eval i p) = \<bullet>"
    using a assms(1) eval_change_inj_on unfolding inj_from_to_def by metis
  then show "eval i p = \<bullet>"
    using change_tv.elims tv.distinct(1) by fast
qed

corollary
  assumes "inj_from_to f U W"
  assumes "inj_from_to g W U"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using assms inj_from_to_valid_in by fast

lemma bij_betw_valid_in:
  assumes "bij_betw f U W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using assms inj_from_to_valid_in bij_betw_inv bij_betw_inj_from_to by metis

theorem eql_finite_eql_card_valid_in:
  assumes "finite U \<longleftrightarrow> finite W"
  assumes "card U = card W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
proof (cases "finite U")
  case True
  then show ?thesis
    using assms bij_betw_iff_card bij_betw_valid_in by metis
next
  case False
  then have "(\<exists>f :: nat \<Rightarrow> nat. bij_betw f U UNIV) \<and> (\<exists>g :: nat \<Rightarrow> nat. bij_betw g W UNIV)"
    using assms Schroeder_Bernstein infinite_iff_countable_subset inj_Suc top_greatest by metis
  with bij_betw_valid_in show ?thesis
    by metis
qed

corollary
  assumes "U \<noteq> {}"
  assumes "W \<noteq> {}"
  assumes "card U = card W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using assms eql_finite_eql_card_valid_in card_gt_0_iff by metis

theorem finite_eql_card_valid_in:
  assumes "finite U"
  assumes "finite W"
  assumes "card U = card W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using eql_finite_eql_card_valid_in by (simp add: assms)

theorem infinite_valid_in:
  assumes "infinite U"
  assumes "infinite W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using eql_finite_eql_card_valid_in by (simp add: assms)

section \<open>Conversions Between Nats and Strings\<close>

definition nat_of_digit :: "char \<Rightarrow> nat" where
  "nat_of_digit c =
   (if c = (CHR ''1'') then 1 else if c = (CHR ''2'') then 2 else if c = (CHR ''3'') then 3 else
    if c = (CHR ''4'') then 4 else if c = (CHR ''5'') then 5 else if c = (CHR ''6'') then 6 else
    if c = (CHR ''7'') then 7 else if c = (CHR ''8'') then 8 else if c = (CHR ''9'') then 9 else 0)"

proposition "range nat_of_digit = {0..<10}"
proof
  show "range nat_of_digit \<subseteq> {0..<10}"
    unfolding nat_of_digit_def by auto
next
  show "{0..<10} \<subseteq> range nat_of_digit"
  proof
    fix x :: nat
    assume a: "x \<in> {0..<10}"
    show "x \<in> range nat_of_digit"
    proof (cases "x = 0")
      case True
      then show ?thesis
        unfolding nat_of_digit_def by auto
    next
      case False
      with a show ?thesis
        unfolding nat_of_digit_def by auto
    qed
  qed
qed

lemma nat_of_digit_of_nat[simp]: "n < 10 \<Longrightarrow> nat_of_digit (digit_of_nat n) = n"
  unfolding digit_of_nat_def nat_of_digit_def
  by simp presburger

function nat_of_string :: "string \<Rightarrow> nat"
  where
    "nat_of_string n = (if length n \<le> 1 then nat_of_digit (last n) else
      (nat_of_string (butlast n)) * 10 + (nat_of_digit (last n)))"
  by simp_all
termination
  by (relation "measure length") simp_all

lemma nat_of_string_step:
  "nat_of_string (string_of_nat (m div 10)) * 10 + m mod 10 = nat_of_string (string_of_nat m)"
  by simp

lemma nat_of_string_of_nat: "nat_of_string (string_of_nat n) = n"
proof (induct rule: string_of_nat.induct)
  case (1 m)
  then show ?case
  proof (cases "m < 10")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "nat_of_string (string_of_nat (m div 10)) = m div 10"
      using 1 by simp
    then have "nat_of_string (string_of_nat (m div 10)) * 10 = (m div 10) * 10"
      by simp
    then have "nat_of_string (string_of_nat (m div 10)) * 10 + (m mod 10) =
        (m div 10) * 10 + (m mod 10)"
      by simp
    also have "... = m"
      by simp
    finally show ?thesis
      using nat_of_string_step by simp
  qed
qed

lemma "inj string_of_nat"
  using inj_on_inverseI nat_of_string_of_nat by metis

section \<open>Derived Formula Constructors\<close>

definition PRO :: "id list \<Rightarrow> fm list" where
  "PRO ids \<equiv> map Pro ids"

definition Pro_nat :: "nat \<Rightarrow> fm" ("\<langle>_\<rangle>\<^sub>1" [40] 40) where
  "\<langle>n\<rangle>\<^sub>1 \<equiv> \<langle>string_of_nat n\<rangle>"

definition PRO_nat :: "nat list \<Rightarrow> fm list" ("\<langle>_\<rangle>\<^sub>1\<^sub>2\<^sub>3" [40] 40) where
  "\<langle>ns\<rangle>\<^sub>1\<^sub>2\<^sub>3 \<equiv> map Pro_nat ns"

definition CON :: "fm list \<Rightarrow> fm" ("[\<^bold>\<and>\<^bold>\<and>] _" [40] 40) where
  "[\<^bold>\<and>\<^bold>\<and>] ps \<equiv> foldr Con ps \<^bold>\<top>"

definition DIS :: "fm list \<Rightarrow> fm" ("[\<^bold>\<or>\<^bold>\<or>] _" [40] 40) where
  "[\<^bold>\<or>\<^bold>\<or>] ps \<equiv> foldr Dis ps \<^bold>\<bottom>"

definition NAB :: "fm list \<Rightarrow> fm" ("[\<^bold>\<nabla>] _" [40] 40) where
  "[\<^bold>\<nabla>] ps \<equiv> [\<^bold>\<and>\<^bold>\<and>] (map Nab ps)"

definition off_diagonal_product :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set" where
  "off_diagonal_product xs ys \<equiv> {(x,y). (x,y) \<in> (xs \<times> ys) \<and> x \<noteq> y }"

definition List_off_diagonal_product :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list" where
  "List_off_diagonal_product xs ys \<equiv> filter (\<lambda>(x,y). not_equal x y) (List.product xs ys)"

definition ExiEql :: "fm list \<Rightarrow> fm" ("[\<^bold>\<exists>\<^bold>=] _" [40] 40) where
  "[\<^bold>\<exists>\<^bold>=] ps \<equiv> [\<^bold>\<or>\<^bold>\<or>] (map (\<lambda>(x,y). x \<^bold>\<Leftrightarrow> y) (List_off_diagonal_product ps ps))"

lemma cla_false_Imp:
  assumes "eval i a = \<bullet>"
  assumes "eval i b = \<circ>"
  shows "eval i (a \<^bold>\<Rightarrow> b) = \<circ>"
  using assms by simp

lemma eval_CON:
  "eval i ([\<^bold>\<and>\<^bold>\<and>] ps) = Det (\<forall>p \<in> set ps. eval i p = \<bullet>)"
  unfolding CON_def
  by (induct ps) simp_all

lemma eval_DIS:
  "eval i ([\<^bold>\<or>\<^bold>\<or>] ps) = Det (\<exists>p \<in> set ps. eval i p = \<bullet>)"
  unfolding DIS_def
proof (induct ps)
  case Nil
  then show ?case
    by simp
next
  case Cons
  with eval.simps eval_negation foldr.simps list.set_intros o_apply set_ConsD show ?case by smt
qed

lemma eval_Nab: "eval i (\<^bold>\<nabla> p) = Det (is_indet (eval i p))"
proof (induct p)
  case (Pro x)
  then show ?case
    using string_tv.cases tv.simps(5) tv.simps(6) eval_negation
      eval.simps(2) eval.simps(4) eval.simps(5) by smt
next
  case (Neg' p)
  then show ?case
    using eval_negation by fastforce
next
  case (Eql' p1 p2)
  then show ?case
    using string_tv.cases tv.simps(5) tv.simps(6) eval_negation
      eval.simps(2) eval.simps(4) eval.simps(5) by smt
qed auto

lemma eval_NAB:
  "eval i ([\<^bold>\<nabla>] ps) = Det (\<forall>p \<in> set ps. is_indet (eval i p))"
proof (cases "\<forall>p\<in>set ps. is_indet (eval i p)")
  case True
  then have "eval i ([\<^bold>\<nabla>] ps) = \<bullet>"
    unfolding NAB_def using eval_CON by fastforce
  then show ?thesis
    using True by simp
next
  case False
  then have "\<not> (\<forall>p\<in>set ps. eval i (\<^bold>\<nabla> p) = \<bullet>)"
    using eval_Nab by simp
  then have "\<not> (\<forall>p\<in>set (map Nab ps). eval i p = \<bullet>)"
    by simp
  then have "eval i ([\<^bold>\<nabla>] ps) = \<circ>"
    unfolding NAB_def using eval_CON[of i "(map Nab ps)"] by simp
  then show ?thesis
    using False by simp
qed

lemma eval_ExiEql:
  "eval i ([\<^bold>\<exists>\<^bold>=] ps) =
    Det (\<exists>(p1, p2)\<in>(off_diagonal_product (set ps) (set ps)). eval i p1 = eval i p2)"
  using eval_DIS[of i "(map (\<lambda>(x, y). x \<^bold>\<Leftrightarrow> y) (List_off_diagonal_product ps ps))"]
  unfolding off_diagonal_product_def ExiEql_def List_off_diagonal_product_def
  by auto

section \<open>Pigeon Hole Formula\<close>

definition pigeonhole_fm :: "nat \<Rightarrow> fm" where
  "pigeonhole_fm n \<equiv> [\<^bold>\<nabla>] \<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3 \<^bold>\<Rightarrow> [\<^bold>\<exists>\<^bold>=] \<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3"

definition interp_of_id :: "nat \<Rightarrow> id \<Rightarrow> tv" where
  "interp_of_id maxi i \<equiv> if (nat_of_string i) < maxi then \<lfloor>nat_of_string i\<rfloor>  else \<bullet>"

lemma interp_of_id_pigeonhole_fm_False: "eval (interp_of_id n) (pigeonhole_fm n) = \<circ>"
proof -
  have all_indet: "\<forall>p \<in> set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3). is_indet (eval (interp_of_id n) p)"
  proof
    fix p
    assume a: "p \<in> set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)"
    show "is_indet (eval (interp_of_id n) p)"
    proof -
      from a have "p \<in> Pro_nat ` {..<n}"
        unfolding PRO_nat_def using atLeast_upt set_map by metis
      then have "\<exists>m<n. p = (\<langle>m\<rangle>\<^sub>1)"
        unfolding Pro_nat_def by fast
      then show ?thesis                
        unfolding interp_of_id_def Pro_nat_def using nat_of_string_of_nat by fastforce
    qed
  qed
  then have "eval (interp_of_id n) ([\<^bold>\<nabla>] (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) = \<bullet>"
    using eval_NAB by simp
  moreover
  have "\<forall>a b. a \<in> set (map (\<lambda>n. \<langle>n\<rangle>\<^sub>1) [0..<n]) \<longrightarrow>
         b \<in> set (map (\<lambda>n. \<langle>n\<rangle>\<^sub>1) [0..<n]) \<longrightarrow> a \<noteq> b \<longrightarrow>
         eval (interp_of_id n) a = eval (interp_of_id n) b \<longrightarrow> False"
    using all_indet in_set_conv_nth length_map nat_of_string_of_nat nth_map tv.inject tv.simps(5)
      eval.simps(1)
    unfolding interp_of_id_def PRO_def PRO_nat_def Pro_nat_def
    by smt
  then have "\<forall>(p1, p2)\<in>off_diagonal_product (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)).
               eval (interp_of_id n) p1 \<noteq> eval (interp_of_id n) p2"
    unfolding off_diagonal_product_def PRO_nat_def Pro_nat_def by blast
  then have "\<not> (\<exists>(p1, p2)\<in>off_diagonal_product (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)).
              eval (interp_of_id n) p1 = eval (interp_of_id n) p2)"
    by blast
  then have "eval (interp_of_id n) ([\<^bold>\<exists>\<^bold>=] (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) = \<circ>"
    using eval_ExiEql[of "interp_of_id n" "\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3"] by simp
  ultimately
  show ?thesis
    unfolding pigeonhole_fm_def using cla_false_Imp[of "interp_of_id n"] by blast
qed

lemma range_interp_of_id: "range (interp_of_id n) \<subseteq> domain {0..<n}"
  unfolding interp_of_id_def domain_def by (simp add: image_subset_iff)

theorem not_valid_in_n_pigeonhole_fm: "\<not> (valid_in {0..<n} (pigeonhole_fm n))"
  unfolding valid_in_def using interp_of_id_pigeonhole_fm_False[of n] range_interp_of_id[of n]
  by fastforce

theorem not_valid_pigeonhole_fm: "\<not> (valid (pigeonhole_fm n))"
  unfolding valid_def using interp_of_id_pigeonhole_fm_False[of n]
  by fastforce

lemma cla_imp_I:
  assumes "is_det (eval i a)"
  assumes "is_det (eval i b)"
  assumes "eval i a = \<bullet> \<Longrightarrow> eval i b = \<bullet>"
  shows "eval i (a \<^bold>\<Rightarrow> b) = \<bullet>"
proof -
  have "is_det tv = (case tv of Det _ \<Rightarrow> True | \<lfloor>_\<rfloor> \<Rightarrow> False)" for tv
    by (metis (full_types) tv.exhaust tv.simps(5) tv.simps(6))
  then show ?thesis
    using assms
    by (metis (full_types) eval.simps(4) eval.simps(5) tv.exhaust tv.simps(6))
qed

lemma is_det_NAB: "is_det (eval i ([\<^bold>\<nabla>] ps))"
  unfolding eval_NAB by auto

lemma is_det_ExiEql: "is_det (eval i ([\<^bold>\<exists>\<^bold>=] ps))"
  using eval_ExiEql by auto

lemma pigeonhole_nat:
  assumes "finite n"
  assumes "finite m"
  assumes "card n > card m"
  assumes "f ` n \<subseteq> m"
  shows "\<exists>x\<in>n. \<exists>y\<in>n. x \<noteq> y \<and> f x = f y"
  using assms not_le inj_on_iff_card_le unfolding inj_on_def
  by metis

lemma pigeonhole_nat_set:
  assumes "f ` {0..<n} \<subseteq> {0..<m}"
  assumes "m < (n :: nat)"
  shows "\<exists>j1\<in>{0..<n}. \<exists>j2\<in>{0..<n}. j1 \<noteq> j2 \<and> f j1 = f j2"
  using assms pigeonhole_nat[of "({0..<n})" "{0..<m}" f]
  by simp

lemma inj_Pro_nat: "(\<langle>p1\<rangle>\<^sub>1) = (\<langle>p2\<rangle>\<^sub>1) \<Longrightarrow> p1 = p2"
  unfolding Pro_nat_def using fm.inject(1) nat_of_string_of_nat
  by metis

lemma eval_true_in_lt_n_pigeonhole_fm:
  assumes "m < n"
  assumes "range i \<subseteq> domain {0..<m}"
  shows "eval i (pigeonhole_fm n) = \<bullet>"
proof -
  {
    assume "eval i ([\<^bold>\<nabla>] (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) = \<bullet>"
    then have "\<forall>p \<in> set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3). is_indet (eval i p)"
      using eval_NAB by auto
    then have *: "\<forall>j<n. is_indet (eval i (\<langle>j\<rangle>\<^sub>1))"
      unfolding PRO_nat_def by auto
    have **: "\<forall>j<n. \<exists>k<m. eval i (\<langle>j\<rangle>\<^sub>1) = (\<lfloor>k\<rfloor>)"
    proof -
      have "\<forall>j<n. is_indet (eval i (\<langle>j\<rangle>\<^sub>1)) \<Longrightarrow> j < n \<Longrightarrow> \<exists>k<m. eval i (\<langle>j\<rangle>\<^sub>1) = (\<lfloor>k\<rfloor>)" for j
      proof (rule_tac x="get_indet (i (string_of_nat j))" in exI)
        show "\<forall>j<n. is_indet (eval i (\<langle>j\<rangle>\<^sub>1)) \<Longrightarrow> j < n \<Longrightarrow> get_indet (i (string_of_nat j)) < m \<and>
               eval i (\<langle>j\<rangle>\<^sub>1) = (\<lfloor>get_indet (i (string_of_nat j))\<rfloor>)"
        proof (induct "i (string_of_nat j)")
          case (Det x)
          then show ?case
            unfolding Pro_nat_def using eval.simps(1) tv.simps(5) by metis
        next
          case (Indet x)
          then show ?case
          proof (subgoal_tac "x<m")
            show "(\<lfloor>x\<rfloor>) = i (string_of_nat j) \<Longrightarrow> \<forall>j<n. is_indet (eval i (\<langle>j\<rangle>\<^sub>1)) \<Longrightarrow> j < n \<Longrightarrow>
                   x < m \<Longrightarrow> get_indet (i (string_of_nat j)) < m \<and>
                   eval i (\<langle>j\<rangle>\<^sub>1) = (\<lfloor>get_indet (i (string_of_nat j))\<rfloor>)"
              unfolding Pro_nat_def using eval.simps(1) tv.simps(6) by metis
          next
            show "(\<lfloor>x\<rfloor>) = i (string_of_nat j) \<Longrightarrow> \<forall>j<n. is_indet (eval i (\<langle>j\<rangle>\<^sub>1)) \<Longrightarrow> j < n \<Longrightarrow> x < m"
              using assms(2) atLeast0LessThan unfolding domain_def by fast
          qed
        qed
      qed
      then show ?thesis
        using * by simp
    qed
    then have "\<forall>j<n. \<exists>k<m. get_indet (eval i (\<langle>j\<rangle>\<^sub>1)) = k"
      by fastforce
    then have "(\<lambda>j. get_indet (eval i (\<langle>j\<rangle>\<^sub>1))) ` {0..<n} \<subseteq> {0..<m}"
      by fastforce
    then have "\<exists>j1 \<in> {0..<n}. \<exists>j2 \<in> {0..<n}. j1 \<noteq> j2 \<and> get_indet (eval i (\<langle>j1\<rangle>\<^sub>1)) =
                get_indet (eval i (\<langle>j2\<rangle>\<^sub>1))"
      using assms(1) pigeonhole_nat_set by simp
    then have "\<exists>j1 < n. \<exists>j2 < n. j1 \<noteq> j2 \<and> get_indet (eval i (\<langle>j1\<rangle>\<^sub>1)) =
                get_indet (eval i (\<langle>j2\<rangle>\<^sub>1))"
      using atLeastLessThan_iff by blast
    then have "\<exists>j1 < n. \<exists>j2 < n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)"
      using ** tv.simps(6) by metis
    then have "\<exists>(p1, p2)\<in>off_diagonal_product (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)).
                 eval i p1 = eval i p2"
    proof (rule_tac P="\<lambda>j1. j1<n \<and> (\<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) =
                        eval i (\<langle>j2\<rangle>\<^sub>1))" in exE)
      show "\<exists>j1<n. \<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
              \<exists>x<n. \<exists>j2<n. x \<noteq> j2 \<and> eval i (\<langle>x\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)"
        by simp
    next
      show "\<exists>j1<n. \<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
              j1 < n \<and> (\<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)) \<Longrightarrow>
              \<exists>(p1, p2)\<in>off_diagonal_product (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)).
              eval i p1 = eval i p2" for j1
      proof (rule_tac P="\<lambda>j2. j2<n \<and> j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)" in exE)
        show "\<exists>j1<n. \<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
                j1 < n \<and> (\<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)) \<Longrightarrow>
                \<exists>x<n. j1 \<noteq> x \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>x\<rangle>\<^sub>1)"
          by simp
      next
        show "\<exists>j1<n. \<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
                j1 < n \<and> (\<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)) \<Longrightarrow>
                j2 < n \<and> j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
                \<exists>(p1, p2)\<in>off_diagonal_product (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)).
                eval i p1 = eval i p2" for j2
          unfolding off_diagonal_product_def PRO_nat_def using inj_Pro_nat
          by (rule_tac x="(\<langle>j1\<rangle>\<^sub>1, \<langle>j2\<rangle>\<^sub>1)" in bexI) auto
      qed
    qed
    then have "eval i ([\<^bold>\<exists>\<^bold>=] (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) = \<bullet>"
      using eval_ExiEql by simp
  }
  then show ?thesis
    unfolding pigeonhole_fm_def using cla_imp_I is_det_ExiEql is_det_NAB by simp
qed

theorem valid_in_lt_n_pigeonhole_fm:
  assumes "m<n"
  shows "valid_in {0..<m} (pigeonhole_fm n)"
  using assms
  unfolding valid_in_def
  using interp_of_id_pigeonhole_fm_False[of n]
  using range_interp_of_id[of n]
  using eval_true_in_lt_n_pigeonhole_fm
  by simp

theorem not_valid_in_pigeonhole_fm_card:
  assumes "finite U"
  shows "\<not> valid_in U (pigeonhole_fm (card U))"
  using assms ex_bij_betw_nat_finite not_valid_in_n_pigeonhole_fm bij_betw_valid_in by metis

theorem not_valid_in_pigeonhole_fm_lt_card:
  assumes "finite (U::nat set)"
  assumes "inj_from_to f U W"
  shows "\<not> valid_in W (pigeonhole_fm (card U))"
proof -
  have "\<not> valid_in U (pigeonhole_fm (card U))"
    using not_valid_in_pigeonhole_fm_card assms by simp
  then show ?thesis
    using assms inj_from_to_valid_in by metis
qed

theorem valid_in_pigeonhole_fm_n_gt_card:
  assumes "finite U"
  assumes "card U < n"
  shows "valid_in U (pigeonhole_fm n)"
  using assms ex_bij_betw_finite_nat bij_betw_valid_in valid_in_lt_n_pigeonhole_fm by metis

section \<open>Validity Is the Intersection of the Finite Logics\<close>

lemma "valid p \<longleftrightarrow> (\<forall>U. finite U \<longrightarrow> valid_in U p)"
proof
  assume "valid p"
  then show "\<forall>U. finite U \<longrightarrow> valid_in U p"
    using transfer by blast
next
  assume "\<forall>U. finite U \<longrightarrow> valid_in U p"
  then have "valid_in {1..card (props p)} p"
    by simp
  then show "valid p"
    using reduce by simp
qed

section \<open>Logics of Different Cardinalities Are Different\<close>

lemma finite_card_lt_valid_in_not_valid_in:
  assumes "finite U"
  assumes "card U < card W"
  shows "valid_in U \<noteq> valid_in W"
proof -
  have finite_W: "finite W"
    using assms(2) card.infinite by fastforce
  have "valid_in U (pigeonhole_fm (card W))"
    using valid_in_pigeonhole_fm_n_gt_card assms by simp
  moreover
  have "\<not> valid_in W (pigeonhole_fm (card W))"
    using not_valid_in_pigeonhole_fm_card assms finite_W by simp
  ultimately show ?thesis
    by fastforce
qed

lemma valid_in_UNIV_p_valid: "valid_in UNIV p = valid p"
  using universal_domain valid_def valid_in_def by simp

theorem infinite_valid_in_valid:
  assumes "infinite U"
  shows "valid_in U p \<longleftrightarrow> valid p"
  using assms infinite_valid_in[of U UNIV p] valid_in_UNIV_p_valid by simp

lemma finite_not_finite_valid_in_not_valid_in:
  assumes "finite U \<noteq> finite W"
  shows "valid_in U \<noteq> valid_in W"
proof -
  {
    fix U W :: "nat set"
    assume inf: "infinite U"
    assume fin: "finite W"
    then have valid_in_W_pigeonhole_fm: "valid_in W (pigeonhole_fm (Suc (card W)))"
      using valid_in_pigeonhole_fm_n_gt_card[of W] by simp
    have "\<not> valid (pigeonhole_fm (Suc (card W)))"
      using not_valid_pigeonhole_fm by simp
    then have "\<not> valid_in U (pigeonhole_fm (Suc (card W)))"
      using inf fin infinite_valid_in_valid by simp
    then have "valid_in U \<noteq> valid_in W"
      using valid_in_W_pigeonhole_fm by fastforce
  }
  then show ?thesis
    using assms by metis
qed

lemma card_not_card_valid_in_not_valid_in:
  assumes "card U \<noteq> card W"
  shows "valid_in U \<noteq> valid_in W"
  using assms
proof -
  {
    fix U W :: "nat set"
    assume a: "card U < card W"
    then have "finite W"
      using card.infinite gr_implies_not0 by blast
    then have valid_in_W_pigeonhole_fm: "valid_in W (pigeonhole_fm (Suc (card W)))"
      using valid_in_pigeonhole_fm_n_gt_card[of W] by simp
    have "valid_in U \<noteq> valid_in W"
    proof (cases "finite U")
      case True
      then show ?thesis
        using a finite_card_lt_valid_in_not_valid_in by simp
    next
      case False
      have "\<not> valid (pigeonhole_fm (Suc (card W)))"
        using not_valid_pigeonhole_fm by simp
      then have "\<not> valid_in U (pigeonhole_fm (Suc (card W)))"
        using False infinite_valid_in_valid by simp
      then show ?thesis
        using valid_in_W_pigeonhole_fm by fastforce
    qed
  }
  then show ?thesis
    using assms neqE by metis
qed

section \<open>Finite Logics Are Different from Infinite Logics\<close>

theorem extend: "valid \<noteq> valid_in U" if "finite U"
  using that not_valid_pigeonhole_fm valid_in_pigeonhole_fm_n_gt_card by fastforce

corollary "\<not> (\<exists>n. \<forall>p. valid p \<longleftrightarrow> valid_in {0..n} p)"
  using extend by fast

corollary "\<forall>n. \<exists>p. \<not> (valid p \<longleftrightarrow> valid_in {0..n} p)"
  using extend by fast

corollary "\<not> (\<forall>p. valid p \<longleftrightarrow> valid_in {0..n} p)"
  using extend by fast

corollary "valid \<noteq> valid_in {0..n}"
  using extend by simp

proposition "valid = valid_in {0..}"
  unfolding valid_def valid_in_def
  using universal_domain
  by simp

corollary "valid = valid_in {n..}"
  using infinite_valid_in[of UNIV "{n..}"] universal_domain
  unfolding valid_def valid_in_def
  by (simp add: infinite_Ici)

corollary "\<not> (\<exists>n m. \<forall>p. valid p \<longleftrightarrow> valid_in {m..n} p)"
  using extend by fast

end \<comment> \<open>\<open>Paraconsistency_Validity_Infinite\<close> file\<close>
