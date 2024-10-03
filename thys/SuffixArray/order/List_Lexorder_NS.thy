theory List_Lexorder_NS
  imports 
      "../util/Sorting_Util" 
      "../util/List_Slice" 
      "../order/List_Permutation_Util" 

begin


section \<open>General Non-standard Lexicographical Comparison\<close>

text \<open> This section is based on the @{const lexord} classical lexicographical definition
       in the the List library but accounts for a variant of lexicographic order defined below 
       that we rely on for verifying sais.
       The main difference is that this ordering preferences the original string over its prefix.
       For example, "aaa" is less than "aa", which in turn is less than "a".\<close>

definition nslexord :: "('a \<times> 'a) set \<Rightarrow> ('a list \<times> 'a list) set" where
"nslexord r = {(x,y). (\<exists>a v. x = y @ a # v) \<or>
                      (\<exists>u a b v w. (a, b) \<in> r \<and> x = u @ a # v \<and> y = u @ b # w)}"

definition nslexordp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"nslexordp cmp xs ys \<longleftrightarrow>
  (\<exists>b c as bs cs. xs = as @ b # bs \<and> ys = as @ c # cs \<and> cmp b c) \<or>
  (\<exists>c cs. xs = ys @ c # cs)"

lemma nslexord_eq_nslexordp:
  "(xs, ys) \<in> nslexord {(x, y). cmp x y} \<longleftrightarrow> nslexordp cmp xs ys"
  "(xs, ys) \<in> nslexord r \<longleftrightarrow> nslexordp (\<lambda>x y. (x, y) \<in> r) xs ys"
  by (clarsimp simp: nslexord_def nslexordp_def; blast)+

definition nslexordeqp ::  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"nslexordeqp cmp xs ys \<longleftrightarrow> nslexordp cmp xs ys \<or> (xs = ys)"

subsection \<open>Intro and Elimination\<close>

lemma nslexordpI1:
  "\<exists>b c as bs cs. xs = as @ b # bs \<and> ys = as @ c # cs \<and> cmp b c \<Longrightarrow> nslexordp cmp xs ys"
  by (simp add: nslexordp_def)

lemma nslexordpI2:
  "\<exists>c cs. xs = ys @ c # cs \<Longrightarrow> nslexordp cmp xs ys"
  by (simp add: nslexordp_def)

lemma nslexordpE:
  "nslexordp cmp xs ys \<Longrightarrow>
   (\<exists>b c as bs cs. xs = as @ b # bs \<and> ys = as @ c # cs \<and> cmp b c) \<or>
   (\<exists>c cs. xs = ys @ c # cs)"
  by (simp add: nslexordp_def)

lemma nslexordp_imp_eq:
  "nslexordp cmp xs ys \<Longrightarrow> nslexordeqp cmp xs ys"
  by (simp add: nslexordeqp_def)

lemma nslexordeqp_imp_eq_or_less:
  "nslexordeqp cmp xs ys \<Longrightarrow> xs = ys \<or> nslexordp cmp xs ys"
  using nslexordeqp_def by auto

subsection "Simplification"

lemma nslexord_Nil_left[simp]: "([], y) \<notin> nslexord r"
  by (unfold nslexord_def, induct y, auto)

lemma nslexord_Nil_right[simp]: "(y, []) \<in> nslexord r = (\<exists>a x. y = a # x)"
  by (unfold nslexord_def, induct y, auto)

lemma nslexord_cons_cons[simp]:
  "(a # x, b # y) \<in> nslexord r \<longleftrightarrow> (a, b) \<in> r \<or> (a = b \<and> (x, y) \<in> nslexord r)"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp add: nslexord_def)
    apply (metis hd_append list.sel(1) list.sel(3) tl_append2)
    done
qed (auto simp add: nslexord_def; (blast | meson Cons_eq_appendI))

lemma nslexordp_cons_cons[simp]:
  "nslexordp r (a # x) (b # y)  \<longleftrightarrow> r a b \<or> (a = b \<and> nslexordp r x y)"
  by (metis mem_Collect_eq nslexord_cons_cons nslexord_eq_nslexordp(1) prod.simps(2))

lemmas nslexord_simps = nslexord_Nil_left nslexord_Nil_right nslexord_cons_cons

lemma nslexord_same_pref_iff:
  "(xs @ ys, xs @ zs) \<in> nslexord r \<longleftrightarrow> (\<exists>x \<in> set xs. (x, x) \<in> r) \<or> (ys, zs) \<in> nslexord r"
  by(induction xs) auto

lemma nslexord_same_pref_if_irrefl[simp]:
  "irrefl r \<Longrightarrow> (xs @ ys, xs @ zs) \<in> nslexord r \<longleftrightarrow> (ys, zs) \<in> nslexord r"
  by (simp add: irrefl_def nslexord_same_pref_iff)

lemma nslexord_append_leftI:
  "\<exists>b z. y = b # z \<Longrightarrow> (x @ y, x) \<in> nslexord r"
  by (simp add: nslexordpI2 nslexord_eq_nslexordp(2))

lemma nslexord_append_left_rightI:
  "(a ,b) \<in> r \<Longrightarrow> (u @ a # x, u @ b # y) \<in> nslexord r"
  by (simp add: nslexord_same_pref_iff)

lemma nslexord_append_rightI:
  "(u, v) \<in> nslexord r \<Longrightarrow> (x @ u, x @ v) \<in> nslexord r"
  by (simp add: nslexord_same_pref_iff)

lemma nslexord_append_rightD:
  "\<lbrakk>(x @ u, x @ v) \<in> nslexord r; (\<forall>a. (a,a) \<notin> r) \<rbrakk> \<Longrightarrow> (u,v) \<in> nslexord r"
  by (simp add: nslexord_same_pref_iff)

\<comment> \<open>nslexord is extension of partial ordering List.lex\<close>
lemma nslexord_lex:
  "(x,y) \<in> lex r = ((x,y) \<in> nslexord r \<and> length x = length y)"
proof (induction x arbitrary: y)
  case (Cons a x y) then show ?case
    by (cases y) (force+)
qed auto

subsection \<open>Recursive version\<close>

fun nslexordrec ::  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"nslexordrec P [] _ = False" |
"nslexordrec P _ [] = True" |
"nslexordrec P (x#xs) (y#ys) = (if P x y then True else if x = y then nslexordrec P xs ys else False)"

lemma nslexordp_eq_nslexordrec:
  "nslexordp cmp xs ys \<longleftrightarrow> nslexordrec cmp xs ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case
    by (simp add: nslexordp_def)
next
  case (Cons a xs)
  note IH = this

  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis
      by (simp add: nslexordp_def)
  next
    case (Cons b zs)
    note P = IH[of zs]
    have "cmp a b \<Longrightarrow> ?thesis"
      by (simp add: Cons)
    moreover
    have "\<lbrakk>\<not>cmp a b; a = b\<rbrakk> \<Longrightarrow> ?thesis"
      by (simp add: P Cons)
    moreover
    have "\<lbrakk>\<not>cmp a b; a \<noteq> b\<rbrakk> \<Longrightarrow> ?thesis"
      by (simp add: local.Cons)
    ultimately show ?thesis
      by blast
  qed
qed

lemmas nslexordp_induct = nslexordrec.induct

subsection "Properties"

text \<open>Useful properties for proving things about relations,
      such as what type of order is satisfied\<close>

lemma nslexord_total_on:
  assumes "total_on A R"
  shows "total_on {xs. set xs \<subseteq> A} (nslexord R)"
proof (intro total_onI)
  fix x y
  assume "x \<in> {xs. set xs \<subseteq> A}" "y \<in> {xs. set xs \<subseteq> A}" "x \<noteq> y"
  hence  "set x \<subseteq> A" "set y \<subseteq> A" "x \<noteq> y"
    by blast+
  then show "(x, y) \<in> nslexord R \<or> (y, x) \<in> nslexord R"
  proof (induct x arbitrary: y)
    case Nil
    then show ?case
      by (metis list.exhaust nslexord_Nil_right)
  next
    case (Cons a x)
    note IH = this
    then show ?case
    proof (cases y)
      case Nil
      then show ?thesis
        by auto
    next
      case (Cons b z)
      then show ?thesis
        by (metis Cons.hyps IH(2-4) assms list.set_intros(1,2) nslexord_cons_cons subset_code(1)
                  total_on_def)
    qed
  qed
qed

lemma total_on_totalp_on_eq:
  "total_on A {(x, y). R x y} = totalp_on A R"
  by (simp add: total_on_def totalp_on_def)

lemmas nslexordp_totalp_on =
  nslexord_total_on[OF total_on_totalp_on_eq[THEN iffD2],
                    simplified nslexord_eq_nslexordp(1) totalp_on_total_on_eq[symmetric]]

lemma nslexord_total:
  "total r \<Longrightarrow> total (nslexord r)"
  using nslexord_total_on by fastforce

lemma nslexordp_totalp:
  "totalp r \<Longrightarrow> totalp (nslexordp r)"
  using nslexordp_totalp_on by fastforce

corollary nslexord_linear:
  "(\<forall>a b. (a,b) \<in> r \<or> a = b \<or> (b,a) \<in> r) \<Longrightarrow> (x,y) \<in> nslexord r \<or> x = y \<or> (y,x) \<in> nslexord r"
  using nslexord_total by (metis UNIV_I total_on_def)

lemma nslexord_irrefl_on:
  assumes "irrefl_on A R"
  shows "irrefl_on {xs. set xs \<subseteq> A} (nslexord R)"
proof (intro irrefl_onI)
  fix x
  assume "x \<in> {xs. set xs \<subseteq> A}"
  hence  "set x \<subseteq> A"
    by blast
  then show "(x, x) \<notin> nslexord R"
  proof (induct x)
    case Nil
    then show ?case
      by auto
  next
    case (Cons a x)
    then show ?case
      by (meson assms irrefl_onD list.set_intros(1) nslexord_cons_cons set_subset_Cons
                subset_code(1))
  qed
qed

lemma irrefl_on_irreflp_on_eq:
  "irrefl_on A {(x, y). R x y} = irreflp_on A R"
  by (simp add: irrefl_on_def irreflp_on_def)

lemmas nslexordp_irreflp_on =
   nslexord_irrefl_on[OF irrefl_on_irreflp_on_eq[THEN iffD2],
                    simplified nslexord_eq_nslexordp(1) irreflp_on_irrefl_on_eq[symmetric]]

lemma nslexord_irreflexive:
  "\<forall>x. (x,x) \<notin> r \<Longrightarrow> (xs,xs) \<notin> nslexord r"
  by (metis lex_take_index nslexord_lex)

lemma nslexord_irrefl:
  "irrefl R \<Longrightarrow> irrefl (nslexord R)"
  by (simp add: irrefl_def nslexord_irreflexive)

lemma nslexordp_irreflp:
  assumes "irreflp R"
  shows "irreflp (nslexordp R)"
  using assms nslexordp_irreflp_on by force

lemma asym_on_asymp_on_eq:
  "asym_on A {(x, y). R x y} = asymp_on A R"
  by (simp add: asym_on_def asymp_on_def)

lemma nslexord_asym_on:
  assumes "asym_on A R"
  shows "asym_on {xs. set xs \<subseteq> A} (nslexord R)"
proof (intro asym_onI)
  fix x y
  assume "x \<in> {xs. set xs \<subseteq> A}" "y \<in> {xs. set xs \<subseteq> A}" "(x, y) \<in> nslexord R"
  hence "set x \<subseteq> A" "set y \<subseteq> A" "(x, y) \<in> nslexord R"
    by blast+
  then show "(y, x) \<notin> nslexord R"
  proof (induct x arbitrary: y)
    case Nil
    then show ?case
      by force
  next
    case (Cons a x)
    note IH = this
    then show ?case
    proof (cases y)
      case Nil
      then show ?thesis
        by simp
    next
      case (Cons b z)
      hence "(a # x, b # z) \<in> nslexord R"
        using IH(4) by blast
      with nslexord_cons_cons[of a x b z R]
      have "(a, b) \<in> R \<or> a = b \<and> (x, z) \<in> nslexord R"
        by blast
      moreover
      have "(a, b) \<in> R \<Longrightarrow> ?thesis"
        by (metis IH(2,3) assms asym_onD list.set_intros(1) local.Cons nslexord_cons_cons
                  subset_code(1))
      moreover
      have "a = b \<and> (x, z) \<in> nslexord R \<Longrightarrow> ?thesis"
        using Cons.hyps IH(2,3) calculation(2) local.Cons by auto
      ultimately show ?thesis
        by blast
    qed
  qed
qed

lemmas nslexordp_asymp_on =
   nslexord_asym_on[OF asym_on_asymp_on_eq[THEN iffD2],
                    simplified nslexord_eq_nslexordp(1) asymp_on_asym_on_eq[symmetric]]

lemma nslexord_asym:
  assumes "asym R"
  shows "asym (nslexord R)"
  using assms nslexord_asym_on by force

lemma nslexordp_asymp:
  assumes "asymp R"
  shows "asymp (nslexordp R)"
  using assms nslexordp_asymp_on by force

lemma nslexord_asymmetric:
  assumes "asym R" "(a, b) \<in> nslexord R"
  shows "(b, a) \<notin> nslexord R"
  by (simp add: assms asymD nslexord_asym)

lemma trans_on_transp_on_eq:
  "trans_on A {(x, y). R x y} = transp_on A R"
  by (simp add: trans_on_def transp_on_def)

lemma nslexord_trans_on:
  assumes "trans_on A R"
  shows "trans_on {xs. set xs \<subseteq> A} (nslexord R)"
proof (intro trans_onI)
  fix x y z
  assume "x \<in> {xs. set xs \<subseteq> A}" "y \<in> {xs. set xs \<subseteq> A}" "z \<in> {xs. set xs \<subseteq> A}"
         "(x, y) \<in> nslexord R" "(y, z) \<in> nslexord R"
  hence "set x \<subseteq> A" "set y \<subseteq> A" "set z \<subseteq> A" "(x, y) \<in> nslexord R" "(y, z) \<in> nslexord R"
    by blast+
  then show "(x, z) \<in> nslexord R"
  proof (induct x arbitrary: y z)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a x)
    note IH = this
    then show ?case
    proof (cases y)
      case Nil
      then show ?thesis
        using IH(6) by auto
    next
      case (Cons b y')
      hence "(a # x, b # y') \<in> nslexord R"
        using IH(5) by blast
      with nslexord_cons_cons[of a x b y' R]
      have P: "(a, b) \<in> R \<or> a = b \<and> (x, y') \<in> nslexord R"
        by blast
      then show ?thesis
      proof (cases z)
        case Nil
        then show ?thesis
          by simp
      next
        case (Cons c z')
        hence "(b # y', c # z') \<in> nslexord R"
          using IH(6) \<open>y = b # y'\<close> by auto
        with nslexord_cons_cons[of b y' c z' R]
        have "(b, c) \<in> R \<or> b = c \<and> (y', z') \<in> nslexord R"
          by blast
        moreover
        have "a \<in> A" "set x \<subseteq> A"
          using IH(2) by auto
        moreover
        have "b \<in> A" "set y' \<subseteq> A"
          using IH(3) \<open>y = b # y'\<close> by force+
        moreover
        have "c \<in> A" "set z' \<subseteq> A"
          using IH(4) \<open>z = c # z'\<close> by force+
        moreover
        from P
        have "(b, c) \<in> R \<Longrightarrow> ?thesis"
          by (metis assms calculation(2,4,6) local.Cons nslexord_cons_cons trans_onD)
        moreover
        from P
        have "b = c \<and> (y', z') \<in> nslexord R \<Longrightarrow> ?thesis"
          by (metis Cons.hyps calculation(3,5,7) local.Cons nslexord_cons_cons)
        ultimately show ?thesis
          by blast
      qed
    qed
  qed
qed

lemmas nslexordp_transp_on =
   nslexord_trans_on[OF trans_on_transp_on_eq[THEN iffD2],
                    simplified nslexord_eq_nslexordp(1) transp_on_trans_on_eq[symmetric]]

lemma nslexord_trans:
  assumes "trans R"
  shows "trans (nslexord R)"
  using assms nslexord_trans_on by force

lemma nslexordp_transp:
  assumes "transp R"
  shows "transp (nslexordp R)"
  using assms nslexordp_transp_on by force

subsection \<open>Monotonicity\<close>

text \<open>Properties about monotonicity\<close>

lemma monotone_on_nslexordp:
  assumes "monotone_on A orda ordb f"
  shows "monotone_on {xs. set xs \<subseteq> A} (nslexordp orda) (nslexordp ordb) (map f)"
proof (rule monotone_onI)
  fix x y
  assume "x \<in> {xs. set xs \<subseteq> A}" "y \<in> {xs. set xs \<subseteq> A}" "nslexordp orda x y"
  hence "set x \<subseteq> A" "set y \<subseteq> A"
    by blast+

  let ?c1 = "\<exists>b c as bs cs. x = as @ b # bs \<and> y = as @ c # cs \<and> orda b c"
  and ?c2 = "\<exists>c cs. x = y @ c # cs"

  let ?g = "nslexordp ordb (map f x) (map f y)"
  from nslexordpE[OF \<open>nslexordp orda x y\<close>]
  have "?c1 \<or> ?c2" .
  moreover
  have "?c2 \<Longrightarrow> ?g"
    using nslexordpI2 by fastforce
  moreover
  have "?c1 \<Longrightarrow> ?g"
  proof (rule nslexordpI1)
    assume ?c1
    then obtain b c as bs cs where
      "x = as @ b # bs"
      "y = as @ c # cs"
      "orda b c"
      by blast
    moreover
    have "map f x = map f as @ f b # map f bs"
      by (simp add: calculation(1))
    moreover
    have "map f y =  map f as @ f c # map f cs"
      by (simp add: calculation(2))
    moreover
    have "ordb (f b) (f c)"
      by (metis \<open>set x \<subseteq> A\<close> \<open>set y \<subseteq> A\<close> assms calculation(1-3) in_set_conv_decomp monotone_on_def
                subset_code(1))
    ultimately show "\<exists>b c as bs cs. map f x = as @ b # bs \<and> map f y = as @ c # cs \<and> ordb b c"
      by blast
  qed
  ultimately show "nslexordp ordb (map f x) (map f y)"
    by blast
qed

lemma monotone_on_bij_betw_inv_nslexordp:
  assumes "monotone_on A orda ordb f"
  and     "asymp_on A orda"
  and     "totalp_on A orda"
  and     "asymp_on B ordb"
  and     "totalp_on B ordb"
  and     "bij_betw f A B"
  and     "bij_betw g B A"
  and     "inverses_on f g A B"
shows "monotone_on {xs. set xs \<subseteq> B} (nslexordp ordb) (nslexordp orda) (map g)"
  by (metis assms monotone_on_bij_betw_inv monotone_on_nslexordp)

lemma monotone_on_bij_betw_nslexordp:
  assumes "monotone_on A orda ordb f"
  and     "asymp_on A orda"
  and     "totalp_on A orda"
  and     "asymp_on B ordb"
  and     "totalp_on B ordb"
  and     "bij_betw f A B"
shows "\<exists>g. bij_betw (map g) {xs. set xs \<subseteq> B} {xs. set xs \<subseteq> A} \<and>
           inverses_on (map f) (map g) {xs. set xs \<subseteq> A} {xs. set xs \<subseteq> B} \<and>
           monotone_on {xs. set xs \<subseteq> B} (nslexordp ordb) (nslexordp orda) (map g)"
  by (metis assms bij_betw_inv_alt bij_betw_map inverses_on_map monotone_on_bij_betw_inv_nslexordp)

lemma monotone_on_iff_nslexordp:
  assumes "monotone_on A orda ordb f"
  and     "asymp_on A orda"
  and     "totalp_on A orda"
  and     "asymp_on B ordb"
  and     "totalp_on B ordb"
  and     "bij_betw f A B"
  and     "set xs \<subseteq> A"
  and     "set ys \<subseteq> A"
shows "nslexordp orda xs ys \<longleftrightarrow> nslexordp ordb (map f xs) (map f ys)"
proof
  assume "nslexordp orda xs ys"
  with monotone_onD[OF monotone_on_nslexordp[OF assms(1)], simplified, OF assms(7,8)]
  show "nslexordp ordb (map f xs) (map f ys)"
    by blast
next
  assume A: "nslexordp ordb (map f xs) (map f ys)"

  from monotone_on_bij_betw_nslexordp[OF assms(1-6)]
  obtain g where P:
    "bij_betw (map g) {xs. set xs \<subseteq> B} {xs. set xs \<subseteq> A}"
    "inverses_on (map f) (map g) {xs. set xs \<subseteq> A} {xs. set xs \<subseteq> B}"
    "monotone_on {xs. set xs \<subseteq> B} (nslexordp ordb) (nslexordp orda) (map g)"
    by blast

  have Q: "set (map f xs) \<subseteq> B"
    using assms(6,7) bij_betw_imp_surj_on by fastforce

  have R: "set (map f ys) \<subseteq> B"
    using assms(6,8) bij_betw_imp_surj_on by fastforce

  from monotone_onD[OF P(3), simplified, OF Q R A]
  show "nslexordp orda xs ys"
    by (metis P(2) assms(7,8) inverses_on_def mem_Collect_eq)
qed

subsection \<open>Other\<close>

lemma nslexordp_cons1_exE:
  assumes "nslexordp cmp xs (x # xs)"
  shows "\<exists>a as bs. x # xs = as @ x # a # bs \<and> cmp a x \<and> (\<forall>b \<in> set as. b = x)"
  using assms
proof (induct xs arbitrary: x)
  case Nil
  then show ?case
    using nslexord_Nil_left nslexord_eq_nslexordp(1) by blast
next
  case (Cons a xs)
  note IH = this

  have "cmp a x \<Longrightarrow> ?case"
    by fastforce
  moreover
  have "\<lbrakk>\<not>cmp a x; a \<noteq> x\<rbrakk> \<Longrightarrow> ?case"
    using IH(2) by force
  moreover
  have "\<lbrakk>\<not>cmp a x; a = x\<rbrakk> \<Longrightarrow> ?case"
  proof -
    assume "\<not>cmp a x" "a = x"
    with IH(2)
    have "nslexordp cmp xs (x # xs)"
      by simp
    with IH(1)[OF _] \<open>a = x\<close>
    have "\<exists>k as bs. a # xs = as @ x # k # bs \<and> cmp k x \<and> (\<forall>b\<in>set as. b = x)"
      by simp
    then obtain k as bs where P:
      "a # xs = as @ x # k # bs"  "cmp k x" "\<forall>b\<in>set as. b = x"
      by blast
    then show ?case
      by (metis Cons_eq_appendI set_ConsD)
  qed
  ultimately show ?case
    by blast
qed

lemma nslexordp_cons2_exE:
  assumes "nslexordp cmp (x # xs) xs"
  shows "(\<forall>k \<in> set xs. k = x) \<or> (\<exists>a as bs. x # xs = as @ x # a # bs \<and> cmp x a \<and> (\<forall>b \<in> set as. b = x))"
  using assms
proof (induct xs arbitrary: x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  note IH = this

  have "cmp x a \<Longrightarrow> ?case"
    by (metis append_Nil empty_iff empty_set)
  moreover
  have "\<lbrakk>\<not>cmp x a; a = x\<rbrakk> \<Longrightarrow> ?case"
  proof -
    assume "\<not>cmp x a" "a = x"
    with IH(2)
    have "nslexordp cmp (x # xs) xs"
      by simp
    with IH(1)[of x] \<open>a = x\<close>
    have "(\<forall>k\<in>set xs. k = x) \<or>
          (\<exists>k as bs. a # xs = as @ x # k # bs \<and> cmp x k \<and> (\<forall>b\<in>set as. b = x))"
      by simp
    then show ?thesis
    proof
      assume "\<forall>k\<in>set xs. k = x"
      then show ?thesis
        by (simp add: \<open>a = x\<close>)
    next
      assume "\<exists>k as bs. a # xs = as @ x # k # bs \<and> cmp x k \<and> (\<forall>b\<in>set as. b = x)"
      then obtain k as bs where P:
        "a # xs = as @ x # k # bs" "cmp x k" "\<forall>b\<in>set as. b = x"
        by blast
      then show ?thesis
        by (metis Cons_eq_appendI set_ConsD)
    qed
  qed
  moreover
  have "\<lbrakk>\<not>cmp x a; a \<noteq> x\<rbrakk> \<Longrightarrow> ?case"
    using Cons.prems by auto

  ultimately show ?case
    by blast
qed

section \<open>Order definitions on lists of linorder elements\<close>

definition list_less_ns :: "('a :: linorder) list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"list_less_ns xs ys =
  (\<exists>n. n \<le> length xs \<and> n \<le> length ys \<and>
    (\<forall>i < n. xs ! i = ys ! i) \<and>
      (length ys = n \<longrightarrow> n < length xs) \<and>
      (length ys \<noteq> n \<longrightarrow> length xs \<noteq> n \<and> xs ! n < ys ! n))"

definition list_less_eq_ns :: "('a :: linorder) list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"list_less_eq_ns xs ys =
  (\<exists>n. n \<le> length xs \<and> n \<le> length ys \<and>
    (\<forall>i < n. xs ! i = ys ! i) \<and>
      (length ys \<noteq> n \<longrightarrow> length xs \<noteq> n \<and> xs ! n < ys ! n))"

\<comment>\<open> Alternative definition \<close>

definition list_less_ns_ex :: "('a :: linorder) list \<Rightarrow> ('a :: linorder) list \<Rightarrow> bool"
  where
"list_less_ns_ex xs ys \<longleftrightarrow>
  (\<exists>b c as bs cs. xs = as @ b # bs \<and> ys = as @ c # cs \<and> b < c) \<or>
  (\<exists>c cs. xs = ys @ c # cs)"

section \<open>Helper list comparison theorems\<close>


lemma list_less_ns_alt_def:
  "list_less_ns xs ys = list_less_ns_ex xs ys"
proof
  assume "list_less_ns xs ys"
  with list_less_ns_def[THEN iffD1, of xs ys]
  obtain n where P:
    "n \<le> length xs" "n \<le> length ys" "\<forall>i<n. xs ! i = ys ! i" "length ys = n \<longrightarrow> n < length xs"
    "length ys \<noteq> n \<longrightarrow> length xs \<noteq> n \<and> xs ! n < ys ! n"
    by blast
  show "list_less_ns_ex xs ys"
  proof (cases "length ys = n")
    assume "length ys = n"
    then show ?thesis
      by (metis P(1,2,3,4) id_take_nth_drop list_less_ns_ex_def nth_take_lemma take_all)
  next
    assume "length ys \<noteq> n"
    then show ?thesis
      by (metis P(1,2,3,5) id_take_nth_drop le_neq_implies_less list_less_ns_ex_def nth_take_lemma)
  qed
next
  assume "list_less_ns_ex xs ys"
  hence "(\<exists>b c as bs cs. xs = as @ b # bs \<and> ys = as @ c # cs \<and> b < c) \<or> (\<exists>c cs. xs = ys @ c # cs)"
    using list_less_ns_ex_def by blast
  then show "list_less_ns xs ys"
  proof
    assume "\<exists>b c as bs cs. xs = as @ b # bs \<and> ys = as @ c # cs \<and> b < c"
    then obtain b c as bs cs where P:
      "xs = as @ b # bs" "ys = as @ c # cs" "b < c"
      by blast
    hence "length as < length xs"
      by simp
    moreover
    have "length as < length ys"
      by (simp add: P(2))
    moreover
    have "\<forall>i < length as. xs ! i = ys ! i"
      by (simp add: P(1) P(2) nth_append)
    moreover
    have "xs ! length as < ys ! length as"
      by (simp add: P(1) P(2) P(3))
    ultimately show "list_less_ns xs ys"
      using list_less_ns_def[THEN iffD2, OF exI, of "length as" xs ys] by simp
  next
    assume "\<exists>c cs. xs = ys @ c # cs"
    then obtain c cs where
      "xs = ys @ c # cs"
      by blast
    hence "length ys < length xs"
      by simp
    then show "list_less_ns xs ys"
      using list_less_ns_def[THEN iffD2, OF exI, of "length ys" xs ys]
      by (simp add: \<open>xs = ys @ c # cs\<close> nth_append)
  qed
qed

lemma nslexordp_eq_list_less_ns_ex:
  "nslexordp (<) = list_less_ns_ex"
  by (clarsimp simp: fun_eq_iff nslexordp_def list_less_ns_ex_def)

lemma nslexordp_eq_list_less_ns_ex_apply:
  "nslexordp (<) x y = list_less_ns_ex x y"
  by (simp add: nslexordp_eq_list_less_ns_ex)

lemma nslexordp_eq_list_less_ns:
  "nslexordp (<) = list_less_ns"
  by (clarsimp simp: fun_eq_iff list_less_ns_alt_def nslexordp_eq_list_less_ns_ex)

lemma nslexordp_eq_list_less_ns_app:
  "nslexordp (<) x y = list_less_ns x y"
  by (simp add: nslexordp_eq_list_less_ns)

lemma nslexordeqp_eq_list_less_eq_ns_apply:
  "nslexordeqp (<) x y = list_less_eq_ns x y"
proof (cases "x = y")
  assume "x = y"
  then show ?thesis
    by (simp add: list_less_eq_ns_def nslexordeqp_def)
next
  assume "x \<noteq> y"
  hence "nslexordeqp (<) x y = nslexordp (<) x y"
    by (simp add: nslexordeqp_def)
  moreover
  have "nslexordp (<) x y = list_less_ns x y"
    by (simp add: nslexordp_eq_list_less_ns)
  moreover
  have "list_less_eq_ns x y = list_less_ns x y"
    unfolding list_less_eq_ns_def list_less_ns_def
  proof (intro iffI; elim exE conjE)
    fix n
    assume "n \<le> length x" "n \<le> length y" "\<forall>i<n. x ! i = y ! i"
           "length y \<noteq> n \<longrightarrow> length x \<noteq> n \<and> x ! n < y ! n"
    then show "\<exists>n\<le>length x. n \<le> length y \<and> (\<forall>i<n. x ! i = y ! i) \<and>
                            (length y = n \<longrightarrow> n < length x) \<and>
                            (length y \<noteq> n \<longrightarrow> length x \<noteq> n \<and> x ! n < y ! n)"
      by (metis \<open>x \<noteq> y\<close> le_eq_less_or_eq nth_equalityI)
  next
    fix n
    assume "n \<le> length x" "n \<le> length y" "\<forall>i<n. x ! i = y ! i" "length y = n \<longrightarrow> n < length x"
           "length y \<noteq> n \<longrightarrow> length x \<noteq> n \<and> x ! n < y ! n"
    then show "\<exists>n\<le>length x. n \<le> length y \<and> (\<forall>i<n. x ! i = y ! i) \<and>
                            (length y \<noteq> n \<longrightarrow> length x \<noteq> n \<and> x ! n < y ! n)"
      by blast
  qed
  ultimately show ?thesis
    by blast
qed

section \<open>@{const list_less_ns} helpers\<close>

lemma list_less_ns_cons_same:
  "list_less_ns (a # xs) (a # ys) = list_less_ns xs ys"
  by (metis nslexordp_cons_cons nslexordp_eq_list_less_ns order_less_irrefl)

lemma list_less_ns_cons_diff:
  "a < b \<Longrightarrow> list_less_ns (a # xs) (b # ys)"
  using list_less_ns_def by fastforce

lemma list_less_ns_cons:
  "list_less_ns (a # xs) (b # ys) = (a \<le> b \<and> (a = b \<longrightarrow> list_less_ns xs ys))"
  by (metis length_Cons list_less_ns_cons_diff list_less_ns_cons_same list_less_ns_def nat.simps(3)
            not_less_iff_gr_or_eq not_less_zero nth_Cons_0 order.strict_iff_order
            order_class.order_eq_iff)

lemma list_less_eq_ns_cons_same:
  "list_less_eq_ns (a # xs) (a # ys) = list_less_eq_ns xs ys"
  by (metis list.inject list_less_ns_cons_same nslexordeqp_def nslexordeqp_eq_list_less_eq_ns_apply
            nslexordp_eq_list_less_ns_app)

lemma list_less_eq_ns_cons:
  "list_less_eq_ns (a # xs) (b # ys) = (a \<le> b \<and> (a = b \<longrightarrow> list_less_eq_ns xs ys))"
  by (metis list.inject list_less_ns_cons nle_le nslexordeqp_def
            nslexordeqp_eq_list_less_eq_ns_apply nslexordp_eq_list_less_ns)

lemma list_less_ns_hd_same:
  "\<lbrakk>hd xs = hd ys; xs \<noteq> []; ys \<noteq> []\<rbrakk> \<Longrightarrow> list_less_ns xs ys = list_less_ns (tl xs) (tl ys)"
  by (metis list.collapse list_less_ns_cons_same)


lemma list_less_ns_recurse:
  "\<lbrakk>xs \<noteq> []; ys \<noteq> []\<rbrakk> \<Longrightarrow>
   (hd xs = hd ys \<longrightarrow> list_less_ns xs ys = list_less_ns (tl xs) (tl ys)) \<and>
   (hd xs \<noteq> hd ys \<longrightarrow> list_less_ns xs ys = (hd xs < hd ys))"
  by (metis list.collapse list_less_ns_cons list_less_ns_hd_same nless_le)

lemma list_less_ns_nil:
  "xs \<noteq> [] \<Longrightarrow> list_less_ns xs []"
  using list_less_ns_def by auto


lemma list_less_ns_app:
  "bs \<noteq> [] \<Longrightarrow> list_less_ns (as @ bs) as"
  by (metis list.collapse nslexordpI2 nslexordp_eq_list_less_ns)

section \<open>Lists of linorder elements are linorders with a bottom element\<close>

lemma list_less_ns_imp_less_eq_not_less_eq:
  "list_less_ns x y \<Longrightarrow> (list_less_eq_ns x y \<and> \<not> list_less_eq_ns y x)"
  apply (clarsimp simp: nslexordp_eq_list_less_ns[symmetric]
                        nslexordeqp_eq_list_less_eq_ns_apply[symmetric]
                        nslexordeqp_def
                        nslexord_eq_nslexordp(1)[symmetric])
  apply (rule conjI)
  apply (erule nslexord_asymmetric[rotated], fastforce)
  by (metis Product_Type.Collect_case_prodD fst_conv nslexord_irreflexive order_less_irrefl
            snd_conv)

lemma list_less_eq_ns_not_less_eq_imp_less:
  "list_less_eq_ns x y \<and> \<not> list_less_eq_ns y x \<Longrightarrow> list_less_ns x y"
  by (metis nslexordeqp_eq_list_less_eq_ns_apply nslexordeqp_imp_eq_or_less
            nslexordp_eq_list_less_ns)

lemma list_less_eq_ns_trans:
  "\<lbrakk>list_less_eq_ns x y; list_less_eq_ns y z\<rbrakk> \<Longrightarrow> list_less_eq_ns x z"
  apply (clarsimp simp: nslexordp_eq_list_less_ns[symmetric]
                        nslexordeqp_eq_list_less_eq_ns_apply[symmetric]
                        nslexordeqp_def
                        nslexord_eq_nslexordp(1)[symmetric])
  apply safe
  apply (erule (1) transD[OF nslexord_trans, rotated])
  by (metis order_less_trans transp_def transp_trans)

lemma list_less_eq_ns_anti_sym:
  "\<lbrakk>list_less_eq_ns x y; list_less_eq_ns y x\<rbrakk> \<Longrightarrow> x = y"
  by (metis list_less_ns_imp_less_eq_not_less_eq nslexordeqp_eq_list_less_eq_ns_apply
            nslexordeqp_imp_eq_or_less nslexordp_eq_list_less_ns)

lemma list_less_eq_ns_linear:
  "list_less_eq_ns x y \<or> list_less_eq_ns y x"
  apply (simp add: nslexordp_eq_list_less_ns[symmetric]
                        nslexordeqp_eq_list_less_eq_ns_apply[symmetric]
                        nslexordeqp_def
                        nslexord_eq_nslexordp(1)[symmetric])
  by (metis case_prodI linorder_neqE mem_Collect_eq nslexord_linear)

interpretation ordlistns: linorder list_less_eq_ns list_less_ns
proof
  fix x y z :: "'a list"
  show "list_less_ns x y = (list_less_eq_ns x y \<and> \<not> list_less_eq_ns y x)"
    using list_less_ns_imp_less_eq_not_less_eq list_less_eq_ns_not_less_eq_imp_less
    by blast
  show "list_less_eq_ns x x"
    unfolding list_less_eq_ns_def
    by simp
  show "\<lbrakk>list_less_eq_ns x y; list_less_eq_ns y z\<rbrakk> \<Longrightarrow> list_less_eq_ns x z"
    by (rule list_less_eq_ns_trans)
  show "\<lbrakk>list_less_eq_ns x y; list_less_eq_ns y x\<rbrakk> \<Longrightarrow> x = y"
    by (rule list_less_eq_ns_anti_sym)
  show "list_less_eq_ns x y \<or> list_less_eq_ns y x"
    by (rule list_less_eq_ns_linear)
qed

interpretation ordlistns: order_top list_less_eq_ns list_less_ns "[]"
proof
  fix a :: "'a list"
  show "list_less_eq_ns a []"
    unfolding list_less_eq_ns_def
    by auto
qed

section \<open>Recursive Definition\<close>

fun lt_ns ::  "('a :: linorder) list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"lt_ns [] [] = False" |
"lt_ns [] _ = False" |
"lt_ns _ [] = True" |
"lt_ns (a # as) (b # bs) =
  (if a < b then True
   else if a > b then False
   else lt_ns as bs)"

lemma list_less_ns_lt_ns:
  "list_less_ns xs ys = lt_ns xs ys"
  apply (induct rule: lt_ns.induct)
     apply simp
    apply simp
   apply (simp add: list_less_ns_nil)
  apply (simp add: list_less_ns_cons)
  apply (safe; simp)
  done

section \<open>@{const list_less_ns_ex} helpers\<close>

lemma list_less_ns_exI1:
  "\<exists>b c as bs cs. xs = as @ b # bs \<and> ys = as @ c # cs \<and> b < c \<Longrightarrow> list_less_ns_ex xs ys"
  by (simp add: list_less_ns_ex_def)

lemma list_less_ns_exI2:
  "\<exists>c cs. xs = ys @ c # cs \<Longrightarrow> list_less_ns_ex xs ys"
  by (simp add: list_less_ns_ex_def)

lemma list_less_ns_exE:
  "list_less_ns_ex xs ys \<Longrightarrow>
   (\<exists>b c as bs cs. xs = as @ b # bs \<and> ys = as @ c # cs \<and> b < c) \<or>
   (\<exists>c cs. xs = ys @ c # cs)"
  by (simp add: list_less_ns_ex_def)

lemma list_less_ns_app_same:
  "list_less_ns (as @ xs) (as @ ys) = list_less_ns xs ys"
  apply (induct as arbitrary: xs ys)
   apply simp
  apply (simp add: list_less_ns_cons_same)
  done

lemma list_less_eq_ns_app_same:
  "list_less_eq_ns (as @ xs) (as @ ys) = list_less_eq_ns xs ys"
  apply (induct as arbitrary: xs ys)
   apply simp
  apply (simp add: list_less_eq_ns_cons_same)
  done

lemma list_less_ns_cons1_exE:
  assumes "list_less_ns xs (x # xs)"
  shows "\<exists>a as bs. x # xs = as @ x # a # bs \<and> x > a \<and> (\<forall>b \<in> set as. b = x)"
  by (metis assms nslexordp_cons1_exE nslexordp_eq_list_less_ns)

lemma list_less_ns_cons1_exI:
  assumes "\<exists>a as bs. x # xs = as @ x # a # bs \<and> x > a \<and> (\<forall>b \<in> set as. b = x)"
  shows "list_less_ns_ex xs (x # xs)"
proof -
  from assms
  obtain a as bs where
    "x # xs = as @ x # a # bs"
    "a < x"
    "\<forall>b \<in> set as. b = x"
    by blast

  have "as = [] \<Longrightarrow> ?thesis"
    using \<open>a < x\<close> \<open>x # xs = as @ x # a # bs\<close> list_less_ns_alt_def list_less_ns_cons_diff
    by fastforce
  moreover
  have "\<exists>c cs. as = cs @ [c] \<Longrightarrow> ?thesis"
  proof -
    assume "\<exists>c cs. as = cs @ [c]"
    then obtain c cs where
      "as = cs @ [c]"
      by blast
    with \<open>\<forall>b \<in> set as. b = x\<close>
    have "c = x"
      by auto
    hence "x # xs = cs @ x # x # a # bs"
      by (simp add: \<open>as = cs @ [c]\<close> \<open>x # xs = as @ x # a # bs\<close>)

    have "\<forall>b \<in> set cs. b = x"
      by (simp add: \<open>\<forall>b\<in>set as. b = x\<close> \<open>as = cs @ [c]\<close>)
    hence "\<exists>n. cs = replicate n x"
      by (meson replicate_eqI)
    then show ?thesis
      by (metis \<open>a < x\<close> \<open>x # xs = cs @ x # x # a # bs\<close> list_less_ns_alt_def list_less_ns_app_same
                list_less_ns_cons_diff list_less_ns_cons_same replicate_app_Cons_same)
  qed
  ultimately show ?thesis
    by (meson rev_exhaust)
qed

lemma list_less_ns_cons2_ex:
  assumes "list_less_ns (x # xs) xs"
  shows "(\<forall>k \<in> set xs. k = x) \<or> (\<exists>a as bs. x # xs = as @ x # a # bs \<and> x < a \<and> (\<forall>b \<in> set as. b = x))"
  by (metis assms nslexordp_cons2_exE nslexordp_eq_list_less_ns)

end