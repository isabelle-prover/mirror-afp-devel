section "A Theory of Blockchain Architectures"

theory Blockchain imports DynamicArchitectures.Dynamic_Architecture_Calculus
begin

subsection "Additions for Dynamic Components"
text {*
  These additions should go to theory Configuration\_Traces for the next version of the AFP.
*}

context dynamic_component
begin

lemma disjE3: "P \<or> Q \<or> R \<Longrightarrow> (P \<Longrightarrow> S) \<Longrightarrow> (Q \<Longrightarrow> S) \<Longrightarrow> (R \<Longrightarrow> S) \<Longrightarrow> S" by auto

lemma ge_induct[consumes 1, case_names step]:
  fixes i::nat and j::nat and P::"nat \<Rightarrow> bool"
  shows "i \<le> j \<Longrightarrow> (\<And>n. i \<le> n \<Longrightarrow> ((\<forall>m \<ge> i.  m<n \<longrightarrow> P m) \<Longrightarrow> P n)) \<Longrightarrow> P j"
proof -
  assume a0: "i \<le> j" and a1: "(\<And>n. i \<le> n \<Longrightarrow> ((\<forall>m \<ge> i.  m<n \<longrightarrow> P m) \<Longrightarrow> P n))"
  have "(\<And>n. \<forall>m<n. i \<le> m \<longrightarrow> P m \<Longrightarrow> i \<le> n \<longrightarrow> P n)"
  proof
    fix n
    assume a2: "\<forall>m<n. i \<le> m \<longrightarrow> P m"
    show "i \<le> n \<Longrightarrow> P n"
    proof -
      assume "i \<le> n"
      with a1 have "(\<forall>m \<ge> i.  m<n \<longrightarrow> P m) \<Longrightarrow> P n" by simp
      moreover from a2 have "\<forall>m \<ge> i.  m<n \<longrightarrow> P m" by simp
      ultimately show "P n" by simp
    qed
  qed
  with nat_less_induct[of "\<lambda>j. i \<le> j \<longrightarrow> P j" j] have "i \<le> j \<longrightarrow> P j" .
  with a0 show ?thesis by simp
qed

lemma nxtAct_eq:
  assumes "n'\<ge>n"
    and "\<parallel>c\<parallel>\<^bsub>t n'\<^esub>"
    and "\<forall>n''\<ge>n. n''<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>"
  shows "n' = \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
  by (metis assms(1) assms(2) assms(3) dynamic_component.nxtActI linorder_neqE_nat nxtActLe)

lemma globEANow:
  fixes c t t' n i \<gamma>
  assumes "n \<le> i"
    and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "eval c t t' n (\<box>\<gamma>)"
  shows "eval c t t' i \<gamma>"
proof -
  from \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>n \<le> i\<close> have "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by auto
  moreover from \<open>n \<le> i\<close> have "\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i" using dual_order.trans lNactLe by blast
  ultimately show ?thesis using globEA[of n c t t' \<gamma> i] \<open>eval c t t' n (\<box>\<gamma>)\<close> by simp
qed

abbreviation lastAct_cond:: "'id \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "lastAct_cond c t n n' \<equiv> n'<n \<and> \<parallel>c\<parallel>\<^bsub>t n'\<^esub>"

definition lastAct:: "'id \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> nat" ("\<langle>_ \<Leftarrow> _\<rangle>\<^bsub>_\<^esub>")
  where "lastAct c t n = (GREATEST n'. lastAct_cond c t n n')"

lemma lastActEx:
  assumes "\<exists>n'<n. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<exists>n'. lastAct_cond nid t n n' \<and> (\<forall>n''. lastAct_cond nid t n n'' \<longrightarrow> n'' \<le> n')"
proof -
  from assms obtain n' where "lastAct_cond nid t n n'" by auto
  moreover have "\<forall>n''>n. \<not> lastAct_cond nid t n n''" by simp
  ultimately obtain n' where "lastAct_cond nid t n n' \<and> (\<forall>n''. lastAct_cond nid t n n'' \<longrightarrow> n'' \<le> n')" using boundedGreatest[of "lastAct_cond nid t n" n'] by blast
  thus ?thesis ..
qed

lemma lastAct_prop:
  assumes "\<exists>n'<n. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<parallel>nid\<parallel>\<^bsub>t (lastAct nid t n)\<^esub>" and "lastAct nid t n<n"
proof -
  from assms lastActEx have "lastAct_cond nid t n (GREATEST x. lastAct_cond nid t n x)" using GreatestI_ex_nat[of "lastAct_cond nid t n"] by blast
  thus "\<parallel>nid\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and "lastAct nid t n<n" using lastAct_def by auto
qed

lemma lastAct_less:
  assumes "lastAct_cond nid t n n'"
  shows "n' \<le> \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
proof -
  from assms lastActEx have "n' \<le> (GREATEST x. lastAct_cond nid t n x)" using Greatest_le_nat[of "lastAct_cond nid t n"] by blast
  thus ?thesis using lastAct_def by auto
qed

lemma lastActNxt:
  assumes "\<exists>n'<n. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>=\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
  using assms lastAct_prop(1) nxtAct_active by auto

lemma lastActNxtAct:
  assumes "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> > \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
  by (meson assms lastAct_prop(2) less_le_trans nxtActI zero_le)

lemma lastActless:
  assumes "\<exists>n'\<ge>n\<^sub>S. n'<n \<and> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n\<^sub>S"
  by (meson assms dual_order.trans lastAct_less)

end

subsection "Blockchains"
text {*
  A blockchain itself is modeled as a simple list.
*}

type_synonym 'a BC = "'a list"

abbreviation max_cond:: "('a BC) set \<Rightarrow> 'a BC \<Rightarrow> bool"
  where "max_cond B b \<equiv> b \<in> B \<and> (\<forall>b'\<in>B. length b' \<le> length b)"

definition MAX:: "('a BC) set \<Rightarrow> 'a BC"
  where "MAX B = (SOME b. max_cond B b)"

lemma max_ex:
  fixes XS::"('a BC) set"
  assumes "XS \<noteq> {}"
    and "finite XS"
  shows "\<exists>xs\<in>XS. (\<forall>ys\<in>XS. length ys \<le> length xs)"
proof (rule Finite_Set.finite_ne_induct)
  show "finite XS" using assms by simp
next
  from assms show "XS \<noteq> {}" by simp
next
  fix x::"'a BC"
  show "\<exists>xs\<in>{x}. \<forall>ys\<in>{x}. length ys \<le> length xs" by simp
next
  fix zs::"'a BC" and F::"('a BC) set"
  assume "finite F" and "F \<noteq> {}" and "zs \<notin> F" and "\<exists>xs\<in>F. \<forall>ys\<in>F. length ys \<le> length xs"
  then obtain xs where "xs\<in>F" and "\<forall>ys\<in>F. length ys \<le> length xs" by auto
  show "\<exists>xs\<in>insert zs F. \<forall>ys\<in>insert zs F. length ys \<le> length xs"
  proof (cases)
    assume "length zs \<ge> length xs"
    with \<open>\<forall>ys\<in>F. length ys \<le> length xs\<close> show ?thesis by auto
  next
    assume "\<not> length zs \<ge> length xs"
    hence "length zs \<le> length xs" by simp
    with \<open>xs \<in> F\<close> show ?thesis using \<open>\<forall>ys\<in>F. length ys \<le> length xs\<close> by auto
  qed
qed

lemma max_prop:
  fixes XS::"('a BC) set"
  assumes "XS \<noteq> {}"
    and "finite XS"
  shows "MAX XS \<in> XS"
    and "\<forall>b'\<in>XS. length b' \<le> length (MAX XS)"
proof -
  from assms have "\<exists>xs\<in>XS. \<forall>ys\<in>XS. length ys \<le> length xs" using max_ex[of XS] by auto
  with MAX_def[of XS] show "MAX XS \<in> XS" and "\<forall>b'\<in>XS. length b' \<le> length (MAX XS)" using someI_ex[of "\<lambda>b. b \<in> XS \<and> (\<forall>b'\<in>XS. length b' \<le> length b)"] by auto
qed

lemma max_less:
  fixes b::"'a BC" and b'::"'a BC" and B::"('a BC) set"
  assumes "b\<in>B"
    and "finite B"
    and "length b > length b'"
  shows "length (MAX B) > length b'"
proof -
  from assms have "\<exists>xs\<in>B. \<forall>ys\<in>B. length ys \<le> length xs" using max_ex[of B] by auto
  with MAX_def[of B] have "\<forall>b'\<in>B. length b' \<le> length (MAX B)" using someI_ex[of "\<lambda>b. b \<in> B \<and> (\<forall>b'\<in>B. length b' \<le> length b)"] by auto
  with \<open>b\<in>B\<close> have "length b \<le> length (MAX B)" by simp
  with \<open>length b > length b'\<close> show ?thesis by simp
qed

subsection "Blockchain Architectures"
text {*
  In the following we describe the locale for blockchain architectures.
*}

locale Blockchain = dynamic_component cmp active
  for active :: "'nid \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
    and cmp :: "'nid \<Rightarrow> cnf \<Rightarrow> 'ND" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60) +
  fixes pin :: "'ND \<Rightarrow> ('nid BC) set"
    and pout :: "'ND \<Rightarrow> 'nid BC"
    and bc :: "'ND \<Rightarrow> 'nid BC"
    and mining :: "'ND \<Rightarrow> bool"
    and trusted :: "'nid \<Rightarrow> bool"
    and actTr :: "trace \<Rightarrow> nat \<Rightarrow> 'nid set"
    and actUt :: "trace \<Rightarrow> nat \<Rightarrow> 'nid set"
    and PoW:: "trace \<Rightarrow> nat \<Rightarrow> nat"
    and trNxt:: "trace \<Rightarrow> nat \<Rightarrow> bool"
  defines "actTr t n \<equiv> {nid. \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<and> trusted nid}"
    and "actUt t n \<equiv> {nid. \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<and> \<not> trusted nid}"
    and "PoW t n \<equiv> (LEAST x. \<forall>nid\<in>actTr t n. length (bc (\<sigma>\<^bsub>nid\<^esub>(t n))) \<le> x)"
    and "trNxt t n \<equiv> (\<exists>n'\<ge>n. PoW t n' > PoW t n \<and> (\<forall>n''>n. n'' \<le> n' \<longrightarrow> \<not>(\<exists>nid\<in>actUt t n''. \<parallel>nid\<parallel>\<^bsub>t n''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n''))))) \<or> (\<forall>n'>n. \<not>(\<exists>nid\<in>actUt t n'. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n'))))"
  assumes consensus: "\<And>kid t t' bc'::('nid BC). \<lbrakk>trusted kid\<rbrakk> \<Longrightarrow> eval kid t t' 0 (\<box>(ass (\<lambda>kt. bc' = (if (\<exists>b\<in>pin kt. length b > length (bc kt)) then (MAX (pin kt)) else (bc kt))) \<longrightarrow>\<^sup>b
      \<circle> (ass (\<lambda>kt.(\<not> mining kt \<and> bc kt = bc' \<or> mining kt \<and> bc kt = bc' @ [kid])))))"
    and attacker: "\<And>kid t t' bc'. \<lbrakk>\<not> trusted kid\<rbrakk> \<Longrightarrow> eval kid t t' 0 (\<box>(ass (\<lambda>kt. bc' = (SOME b. b \<in> (pin kt \<union> {bc kt}))) \<longrightarrow>\<^sup>b
      \<circle> (ass (\<lambda>kt.(\<not> mining kt \<and> prefix (bc kt) bc' \<or> mining kt \<and> bc kt = bc' @ [kid])))))"
    and forward: "\<And>kid t t'. eval kid t t' 0 (\<box>(ass (\<lambda>kt. pout kt = bc kt)))"
    -- "At each time point a node will forward its blockchain to the network"
    and conn: "\<And>k kid. active kid k
      \<Longrightarrow> pin (cmp kid k) = (\<Union>kid'\<in>{kid'. active kid' k}. {pout (cmp kid' k)})"
    and act: "\<And>t n::nat. finite {kid::'nid. \<parallel>kid\<parallel>\<^bsub>t n\<^esub>}"
    and actTr: "\<And>t n::nat. \<exists>nid. trusted nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<and> \<parallel>nid\<parallel>\<^bsub>t (Suc n)\<^esub>"
    and fair: "\<And>t kid n::nat. \<lbrakk>\<not> trusted kid; mining (\<sigma>\<^bsub>kid\<^esub>(t n))\<rbrakk> \<Longrightarrow> trNxt t n"
    and closed: "\<And>t kid b n::nat. \<lbrakk>b \<in> pin (\<sigma>\<^bsub>kid\<^esub>(t n))\<rbrakk> \<Longrightarrow> \<exists>kid'. \<parallel>kid'\<parallel>\<^bsub>t n\<^esub> \<and> pout (\<sigma>\<^bsub>kid'\<^esub>(t n)) = b"
begin

lemma fwd_bc:
  fixes nid and t::"nat \<Rightarrow> cnf" and t'::"nat \<Rightarrow> 'ND"
  assumes "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
  shows "pout (\<sigma>\<^bsub>nid\<^esub>t n) = bc (\<sigma>\<^bsub>nid\<^esub>t n)" using assms forward globEANow[THEN assEANow[of nid t t' n]] by blast

lemma finite_input:
  fixes t n kid
  assumes "\<parallel>kid\<parallel>\<^bsub>t n\<^esub>"
  shows "finite (pin (cmp kid (t n)))" using conn[of kid "t n"] act assms by auto

lemma nempty_input:
  fixes t n kid
  assumes "\<parallel>kid\<parallel>\<^bsub>t n\<^esub>"
  shows "pin (cmp kid (t n))\<noteq>{}" using conn[of kid "t n"] act assms by auto

lemma onlyone:
  assumes "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<exists>!i. \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t i\<^esub>"
proof
  show "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"
    by (metis assms dynamic_component.nxtActI lastAct_prop(1) lastAct_prop(2) less_le_trans order_refl)
next
  fix i
  show "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t i\<^esub> \<Longrightarrow> i = \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
    by (metis lastActless(1) leI le_less_Suc_eq le_less_trans nxtActI order_refl)
qed

subsubsection "Component Behavior"

lemma bhv_tr_ex:
  fixes t and t'::"nat \<Rightarrow> 'ND" and tid
  assumes "trusted tid"
    and "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
  shows "\<not> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [tid]"
proof -
  let ?cond = "\<lambda>kt. MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) = (if (\<exists>b\<in>pin kt. length b > length (bc kt)) then (MAX (pin kt)) else (bc kt))"
  let ?check = "\<lambda>kt. \<not> mining kt \<and> bc kt = MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> mining kt \<and> bc kt = MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [tid]"
  from \<open>trusted tid\<close> have "eval tid t t' 0 ((\<box>((ass ?cond) \<longrightarrow>\<^sup>b
        \<circle>ass ?check)))" using consensus[of tid _ _ "MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"] by simp
  moreover from assms have "\<exists>i\<ge>0. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" by auto
  moreover have "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>0\<^esub> \<le> \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
  ultimately have "eval tid t t' \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> (ass (?cond) \<longrightarrow>\<^sup>b
        \<circle>ass ?check)" using globEA[of 0 tid t t' "((ass ?cond) \<longrightarrow>\<^sup>b \<circle>ass ?check)" "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by fastforce
  moreover have "eval tid t t' \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> (ass (?cond))"
  proof (rule assIA)
    from \<open>\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> show "\<exists>i\<ge>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" using lastAct_prop(1) by blast
    from assms(3) assms(4) show "?cond (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>)" using lastActNxt by simp
  qed
  ultimately have "eval tid t t' \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> (\<circle>ass ?check)" using impE[of tid t t' _ "ass (?cond)" "\<circle>ass ?check"] by simp
  moreover have "\<exists>i>\<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>"
  proof -
    from assms have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using lastActNxtAct by simp
    with assms(3) have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using lastActNxt by simp
    moreover from \<open>\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"  using nxtActI by simp
    ultimately show ?thesis by auto
  qed
  moreover from assms have "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using lastActNxtAct by (simp add: order.strict_implies_order)
  moreover from assms have "\<exists>!i. \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" using onlyone by simp
  ultimately have "eval tid t t' \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> (ass ?check)" using nxtEA1[of tid t "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" t' "ass ?check" "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
  moreover from \<open>\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by simp
  ultimately show ?thesis using assEANow[of tid t t' "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" ?check] by simp
qed

lemma bhv_tr_in:
  fixes t and t'::"nat \<Rightarrow> 'ND" and tid
  assumes "trusted tid"
    and "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<not> (\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
  shows "\<not> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or> mining (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [tid]"
proof -
  let ?cond = "\<lambda>kt. bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) = (if (\<exists>b\<in>pin kt. length b > length (bc kt)) then (MAX (pin kt)) else (bc kt))"
  let ?check = "\<lambda>kt. \<not> mining kt \<and> bc kt = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or> mining kt \<and> bc kt = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [tid]"
  from \<open>trusted tid\<close> have "eval tid t t' 0 ((\<box>((ass ?cond) \<longrightarrow>\<^sup>b
        \<circle>ass ?check)))" using consensus[of tid _ _ "bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)"] by simp
  moreover from assms have "\<exists>i\<ge>0. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" by auto
  moreover have "\<langle>tid \<leftarrow> t\<rangle>\<^bsub>0\<^esub> \<le> \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
  ultimately have "eval tid t t' \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> (ass (?cond) \<longrightarrow>\<^sup>b
        \<circle>ass ?check)" using globEA[of 0 tid t t' "((ass ?cond) \<longrightarrow>\<^sup>b \<circle>ass ?check)" "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by fastforce
  moreover have "eval tid t t' \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> (ass (?cond))"
  proof (rule assIA)
    from \<open>\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> show "\<exists>i\<ge>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" using lastAct_prop(1) by blast
    from assms(3) assms(4) show "?cond (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>)" using lastActNxt by simp
  qed
  ultimately have "eval tid t t' \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> (\<circle>ass ?check)" using impE[of tid t t' _ "ass (?cond)" "\<circle>ass ?check"] by simp
  moreover have "\<exists>i>\<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>. \<parallel>tid\<parallel>\<^bsub>t i\<^esub>"
  proof -
    from assms have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using lastActNxtAct by simp
    with assms(3) have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>tid \<rightarrow> t\<rangle>\<^bsub>\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using lastActNxt by simp
    moreover from \<open>\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"  using nxtActI by simp
    ultimately show ?thesis by auto
  qed
  moreover from assms have "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using lastActNxtAct by (simp add: order.strict_implies_order)
  moreover from assms have "\<exists>!i. \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>tid\<parallel>\<^bsub>t i\<^esub>" using onlyone by simp
  ultimately have "eval tid t t' \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> (ass ?check)" using nxtEA1[of tid t "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" t' "ass ?check" "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
  moreover from \<open>\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by simp
  ultimately show ?thesis using assEANow[of tid t t' "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" ?check] by simp
qed

lemma bhv_ut:
  fixes t and t'::"nat \<Rightarrow> 'ND" and uid
  assumes "\<not> trusted uid"
    and "\<exists>n'\<ge>n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<not> mining (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)) (SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}) \<or> mining (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = (SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}) @ [uid]"
proof -
  let ?cond = "\<lambda>kt. (SOME b. b \<in> (pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)})) = (SOME b. b \<in> pin kt \<union> {bc kt})"
  let ?check = "\<lambda>kt. \<not> mining kt \<and> prefix (bc kt) (SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}) \<or> mining kt \<and> bc kt = (SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}) @ [uid]"
  from \<open>\<not> trusted uid\<close> have "eval uid t t' 0 ((\<box>((ass ?cond) \<longrightarrow>\<^sup>b
        \<circle>ass ?check)))" using attacker[of uid _ _ "(SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)})"] by simp
  moreover from assms have "\<exists>i\<ge>0. \<parallel>uid\<parallel>\<^bsub>t i\<^esub>" by auto
  moreover have "\<langle>uid \<leftarrow> t\<rangle>\<^bsub>0\<^esub> \<le> \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
  ultimately have "eval uid t t' \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> (ass (?cond) \<longrightarrow>\<^sup>b
        \<circle>ass ?check)" using globEA[of 0 uid t t' "((ass ?cond) \<longrightarrow>\<^sup>b \<circle>ass ?check)" "\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by fastforce
  moreover have "eval uid t t' \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> (ass (?cond))"
  proof (rule assIA)
    from \<open>\<exists>n'<n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>\<close> show "\<exists>i\<ge>\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>uid\<parallel>\<^bsub>t i\<^esub>" using lastAct_prop(1) by blast
    with assms(3) show "?cond (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>)" using lastActNxt by simp
  qed
  ultimately have "eval uid t t' \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> (\<circle>ass ?check)" using impE[of uid t t' _ "ass (?cond)" "\<circle>ass ?check"] by simp
  moreover have "\<exists>i>\<langle>uid \<rightarrow> t\<rangle>\<^bsub>\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>. \<parallel>uid\<parallel>\<^bsub>t i\<^esub>"
  proof -
    from assms have "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using lastActNxtAct by simp
    with assms(3) have "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>>\<langle>uid \<rightarrow> t\<rangle>\<^bsub>\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using lastActNxt by simp
    moreover from \<open>\<exists>n'\<ge>n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>uid\<parallel>\<^bsub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>"  using nxtActI by simp
    ultimately show ?thesis by auto
  qed
  moreover from assms have "\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using lastActNxtAct by (simp add: order.strict_implies_order)
  moreover from assms have "\<exists>!i. \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i \<and> i < \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>uid\<parallel>\<^bsub>t i\<^esub>" using onlyone by simp
  ultimately have "eval uid t t' \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> (ass ?check)" using nxtEA1[of uid t "\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" t' "ass ?check" "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
  moreover from \<open>\<exists>n'\<ge>n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>uid\<parallel>\<^bsub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by simp
  ultimately show ?thesis using assEANow[of uid t t' "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" ?check] by simp
qed

lemma bhv_tr_context:
  assumes "trusted tid"
      and "\<parallel>tid\<parallel>\<^bsub>t n\<^esub>"
      and "\<exists>n'\<ge>n\<^sub>S. n'<n \<and> \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
  shows "prefix (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) (bc (\<sigma>\<^bsub>tid\<^esub>t n)) \<or> 
                (\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<ge> length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) \<and> prefix (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) (bc (\<sigma>\<^bsub>tid\<^esub>t n)))"
proof cases
  assume casmp: "\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
  moreover from assms(2) have "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" by auto
  moreover from assms(3) have "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" by auto
  ultimately have "bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [tid]" using assms(1) bhv_tr_ex by auto
  moreover from assms(2) have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> = n" using nxtAct_active by simp
  ultimately have "bc (\<sigma>\<^bsub>tid\<^esub>t n) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> bc (\<sigma>\<^bsub>tid\<^esub>t n) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [tid]" by simp
  hence "prefix (Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) (bc (\<sigma>\<^bsub>tid\<^esub>t n))" by auto
  moreover have "length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) \<ge> length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))" ..
  moreover have "Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<in> pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)"
  proof -
    from \<open>\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<parallel>tid\<parallel>\<^bsub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using lastAct_prop(1) by simp
    hence "finite (pin (\<sigma>\<^bsub>tid\<^esub>(t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))" using finite_input[of tid t "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
    moreover from casmp obtain b where "b \<in> pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)" and "length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" by auto
    ultimately show ?thesis using max_prop(1) by auto
  qed
  with closed obtain nid where "\<parallel>nid\<parallel>\<^bsub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and "pout (\<sigma>\<^bsub>nid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" by blast
  with fwd_bc[of nid t "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"] have "\<parallel>nid\<parallel>\<^bsub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and "bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" by auto
  ultimately show ?thesis by auto
next
  assume "\<not> (\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
  moreover from assms(2) have "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" by auto
  moreover from assms(3) have "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" by auto
  ultimately have "bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or> bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [tid]" using assms(1) bhv_tr_in[of tid n t] by auto
  moreover from assms(2) have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> = n" using nxtAct_active by simp
  ultimately have "bc (\<sigma>\<^bsub>tid\<^esub>t n) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or> bc (\<sigma>\<^bsub>tid\<^esub>t n) = bc (\<sigma>\<^bsub>tid\<^esub>t \<langle>tid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [tid]" by simp
  thus ?thesis by auto
qed

lemma bhv_ut_context:
  assumes "\<not> trusted uid"
      and "\<parallel>uid\<parallel>\<^bsub>t n\<^esub>"
      and "\<exists>n'\<ge>n\<^sub>S. n'<n \<and> \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>"
  shows "(mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) (bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [uid])) \<or> \<not> mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) (bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or>
                (\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [uid]) \<or> \<not> mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))))"
proof -
  let ?bc="SOME b. b \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}"
  have bc_ex: "?bc \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or> ?bc \<in> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}"
  proof -
    have "\<exists>b. b\<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}" by auto
    hence "?bc \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<union> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}" using someI_ex by simp
    thus ?thesis by auto
  qed

  from assms(2) have "\<exists>n'\<ge>n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>" by auto
  moreover from assms(3) have "\<exists>n'<n. \<parallel>uid\<parallel>\<^bsub>t n'\<^esub>" by auto
  ultimately have "\<not> mining (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)) ?bc \<or> mining (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<and> bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = ?bc @ [uid]" using bhv_ut[of uid n t] assms(1) by simp
  moreover from assms(2) have "\<langle>uid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> = n" using nxtAct_active by simp
  ultimately have casmp: "\<not> mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) ?bc \<or> mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> bc (\<sigma>\<^bsub>uid\<^esub>t n) = ?bc @ [uid]" by simp

  from bc_ex have "?bc \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) \<or> ?bc \<in> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}" .
  thus ?thesis
  proof
    assume "?bc \<in> pin (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)"
    with closed obtain nid where "\<parallel>nid\<parallel>\<^bsub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and "pout (\<sigma>\<^bsub>nid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) = ?bc" by blast
    with fwd_bc[of nid t "\<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"] have "bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) = ?bc" by simp
    with casmp have "\<not> mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>uid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> mining (\<sigma>\<^bsub>uid\<^esub>t n) \<and> bc (\<sigma>\<^bsub>uid\<^esub>t n) = (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) @ [uid]" by simp
    with \<open>\<parallel>nid\<parallel>\<^bsub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> show ?thesis by auto
  next
    assume "?bc \<in> {bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)}"
    hence "?bc = bc (\<sigma>\<^bsub>uid\<^esub>t \<langle>uid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)" by simp
    with casmp show ?thesis by auto
  qed
qed

subsubsection "Maximal Trusted Blockchains"

abbreviation mbc_cond:: "trace \<Rightarrow> nat \<Rightarrow> 'nid \<Rightarrow> bool"
  where "mbc_cond t n nid \<equiv> nid\<in>actTr t n \<and> (\<forall>nid'\<in>actTr t n. length (bc (\<sigma>\<^bsub>nid'\<^esub>(t n))) \<le> length (bc (\<sigma>\<^bsub>nid\<^esub>(t n))))"

lemma mbc_ex:
  fixes t n
  shows "\<exists>x. mbc_cond t n x"
proof -
  let ?ALL="{b. \<exists>nid\<in>actTr t n. b = bc (\<sigma>\<^bsub>nid\<^esub>(t n))}"
  have "MAX ?ALL \<in> ?ALL"
  proof (rule max_prop)
    from actTr have "actTr t n \<noteq> {}" using actTr_def by blast
    thus "?ALL\<noteq>{}" by auto
    from act have "finite (actTr t n)" using actTr_def by simp
    thus "finite ?ALL" by simp
  qed
  then obtain nid where "nid \<in> actTr t n \<and> bc (\<sigma>\<^bsub>nid\<^esub>(t n)) = MAX ?ALL" by auto
  moreover have "\<forall>nid'\<in>actTr t n. length (bc (\<sigma>\<^bsub>nid'\<^esub>(t n))) \<le> length (MAX ?ALL)"
  proof
    fix nid
    assume "nid \<in> actTr t n"
    hence "bc (\<sigma>\<^bsub>nid\<^esub>(t n)) \<in> ?ALL" by auto
    moreover have "\<forall>b'\<in>?ALL. length b' \<le> length (MAX ?ALL)"
    proof (rule max_prop)
      from \<open>bc (\<sigma>\<^bsub>nid\<^esub>(t n)) \<in> ?ALL\<close> show "?ALL\<noteq>{}" by auto
      from act have "finite (actTr t n)" using actTr_def by simp
      thus "finite ?ALL" by simp
    qed
    ultimately show "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<le> length (Blockchain.MAX {b. \<exists>nid\<in>actTr t n. b = bc (\<sigma>\<^bsub>nid\<^esub>t n)})" by simp
  qed
  ultimately show ?thesis by auto
qed

definition MBC:: "trace \<Rightarrow> nat \<Rightarrow> 'nid"
  where "MBC t n = (SOME b. mbc_cond t n b)"

lemma mbc_prop:
  shows "mbc_cond t n (MBC t n)"
  using someI_ex[OF mbc_ex] MBC_def by simp

subsubsection "Trusted Proof of Work"
text {*
  An important construction is the maximal proof of work available in the trusted community.
  The construction was already introduces in the locale itself since it was used to express some of the locale assumptions.
*}

abbreviation pow_cond:: "trace \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "pow_cond t n n' \<equiv> \<forall>nid\<in>actTr t n. length (bc (\<sigma>\<^bsub>nid\<^esub>(t n))) \<le> n'"

lemma pow_ex:
  fixes t n
  shows "pow_cond t n (length (bc (\<sigma>\<^bsub>MBC t n\<^esub>(t n))))"
    and "\<forall>x'. pow_cond t n x' \<longrightarrow> x'\<ge>length (bc (\<sigma>\<^bsub>MBC t n\<^esub>(t n)))"
  using mbc_prop by auto

lemma pow_prop:
  "pow_cond t n (PoW t n)"
proof -
  from pow_ex have "pow_cond t n (LEAST x. pow_cond t n x)" using LeastI_ex[of "pow_cond t n"] by blast
  thus ?thesis using PoW_def by simp
qed 

lemma pow_eq:
  fixes n
  assumes "\<exists>tid\<in>actTr t n. length (bc (\<sigma>\<^bsub>tid\<^esub>(t n))) = x"
    and "\<forall>tid\<in>actTr t n. length (bc (\<sigma>\<^bsub>tid\<^esub>(t n))) \<le> x"
  shows "PoW t n = x"
proof -
  have "(LEAST x. pow_cond t n x) = x"
  proof (rule Least_equality)
    from assms(2) show "\<forall>nid\<in>actTr t n. length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<le> x" by simp
  next
    fix y
    assume "\<forall>nid\<in>actTr t n. length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<le> y"
    thus "x \<le> y" using assms(1) by auto
  qed
  with PoW_def show ?thesis by simp
qed

lemma pow_mbc:
  shows "length (bc (\<sigma>\<^bsub>MBC t n\<^esub>t n)) = PoW t n"
  by (metis mbc_prop pow_eq)

lemma pow_less:
  fixes t n nid
  assumes "pow_cond t n x"
  shows "PoW t n \<le> x"
proof -
  from pow_ex assms have "(LEAST x. pow_cond t n x) \<le> x" using Least_le[of "pow_cond t n"] by blast
  thus ?thesis using PoW_def by simp
qed

lemma pow_le_max:
  assumes "trusted tid"
    and "\<parallel>tid\<parallel>\<^bsub>t n\<^esub>"
  shows "PoW t n \<le> length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n)))"
proof -
  from mbc_prop have "trusted (MBC t n)" and "\<parallel>MBC t n\<parallel>\<^bsub>t n\<^esub>" using actTr_def by auto
  hence "pout (\<sigma>\<^bsub>MBC t n\<^esub>t n) = bc (\<sigma>\<^bsub>MBC t n\<^esub>t n)" using forward globEANow[THEN assEANow[of "MBC t n" t t' n "\<lambda>kt. pout kt = bc kt"]] by auto
  with assms \<open>\<parallel>MBC t n\<parallel>\<^bsub>t n\<^esub>\<close> \<open>trusted (MBC t n)\<close> have "bc (\<sigma>\<^bsub>MBC t n\<^esub>t n) \<in> pin (\<sigma>\<^bsub>tid\<^esub>t n)" using conn by auto
  moreover from assms (2) have "finite (pin (\<sigma>\<^bsub>tid\<^esub>t n))" using finite_input[of tid t n] by simp
  ultimately have "length (bc (\<sigma>\<^bsub>MBC t n\<^esub>t n)) \<le> length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n)))" using max_prop(2) by auto
  with pow_mbc show ?thesis by simp
qed

lemma pow_ge_lgth:
  assumes "trusted tid"
    and "\<parallel>tid\<parallel>\<^bsub>t n\<^esub>"
  shows "length (bc (\<sigma>\<^bsub>tid\<^esub>t n)) \<le> PoW t n"
proof -
  from assms have "tid \<in> actTr t n" using actTr_def by simp
  thus ?thesis using pow_prop by simp
qed

lemma pow_le_lgth:
  assumes "trusted tid"
    and "\<parallel>tid\<parallel>\<^bsub>t n\<^esub>"
    and "\<not>(\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t n). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t n)))"
  shows "length (bc (\<sigma>\<^bsub>tid\<^esub>t n)) \<ge> PoW t n"
proof -
  from assms (3) have "\<forall>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t n). length b \<le> length (bc (\<sigma>\<^bsub>tid\<^esub>t n))" by auto
  moreover from assms(2) nempty_input[of tid t n] finite_input[of tid t n] have "MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n)) \<in> pin (\<sigma>\<^bsub>tid\<^esub>t n)" using max_prop(1)[of "pin (\<sigma>\<^bsub>tid\<^esub>t n)"] by simp
  ultimately have "length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n))) \<le> length (bc (\<sigma>\<^bsub>tid\<^esub>t n))" by simp
  moreover from assms have "PoW t n \<le> length (MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n)))" using pow_le_max by simp
  ultimately show ?thesis by simp
qed

lemma pow_mono:
  shows "n'\<ge>n \<Longrightarrow> PoW t n' \<ge> PoW t n"
proof (induction n' rule: dec_induct)
  case base
  then show ?case by simp
next
  case (step n')
  hence "PoW t n \<le> PoW t n'" by simp
  moreover have "PoW t (Suc n') \<ge> PoW t n'"
  proof -
    from actTr obtain tid where "trusted tid" and "\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>" and "\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>" by auto
    show ?thesis
    proof cases
      assume "\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t n'). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t n'))"
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>Suc n'\<^esub> = Suc n'" using nxtAct_active by simp
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>Suc n'\<^esub> = n'" using lastAct_prop(2) lastActless le_less_Suc_eq by blast
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<exists>n''<Suc n'. \<parallel>tid\<parallel>\<^bsub>t n''\<^esub>" by blast
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "\<exists>n''\<ge>Suc n'. \<parallel>tid\<parallel>\<^bsub>t n''\<^esub>" by auto
      ultimately have "bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n')) \<or> bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')) = Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n')) @ [tid]" using \<open>trusted tid\<close> bhv_tr_ex[of tid "Suc n'" t] by auto
      hence "length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n'))) \<ge> length (Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n')))" by auto
      moreover from \<open>trusted tid\<close> \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "length (Blockchain.MAX (pin (\<sigma>\<^bsub>tid\<^esub>t n'))) \<ge> PoW t n'" using pow_le_max by simp
      ultimately have "PoW t n' \<le> length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')))" by simp
      moreover from \<open>trusted tid\<close> \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n'))) \<le> PoW t (Suc n')" using pow_ge_lgth by simp
      ultimately show ?thesis by simp
    next
      assume asmp: "\<not>(\<exists>b\<in>pin (\<sigma>\<^bsub>tid\<^esub>t n'). length b > length (bc (\<sigma>\<^bsub>tid\<^esub>t n')))"
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>Suc n'\<^esub> = Suc n'" using nxtAct_active by simp
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<langle>tid \<Leftarrow> t\<rangle>\<^bsub>Suc n'\<^esub> = n'" using lastAct_prop(2) lastActless le_less_Suc_eq by blast
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> have "\<exists>n''<Suc n'. \<parallel>tid\<parallel>\<^bsub>t n''\<^esub>" by blast
      moreover from \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "\<exists>n''\<ge>Suc n'. \<parallel>tid\<parallel>\<^bsub>t n''\<^esub>" by auto
      ultimately have "bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')) = bc (\<sigma>\<^bsub>tid\<^esub>t n') \<or> bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n')) = bc (\<sigma>\<^bsub>tid\<^esub>t n') @ [tid]" using \<open>trusted tid\<close> bhv_tr_in[of tid "Suc n'" t] by auto
      hence "length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n'))) \<ge> length (bc (\<sigma>\<^bsub>tid\<^esub>t n'))" by auto
      moreover from \<open>trusted tid\<close> \<open>\<parallel>tid\<parallel>\<^bsub>t n'\<^esub>\<close> asmp have "length (bc (\<sigma>\<^bsub>tid\<^esub>t n')) \<ge> PoW t n'" using pow_le_lgth by simp
      moreover from \<open>trusted tid\<close> \<open>\<parallel>tid\<parallel>\<^bsub>t (Suc n')\<^esub>\<close> have "length (bc (\<sigma>\<^bsub>tid\<^esub>t (Suc n'))) \<le> PoW t (Suc n')" using pow_ge_lgth by simp
      ultimately show ?thesis by simp
    qed
  qed
  ultimately show ?case by auto
qed

lemma pow_equals:
  assumes "PoW t n = PoW t n'"
  and "n'\<ge>n"
  and "n''\<ge>n"
  and "n''\<le>n'"
  shows "PoW t n = PoW t n''" by (metis pow_mono assms(1) assms(3) assms(4) eq_iff)

subsubsection "Trusted Next"

lemma pow_eq_trnxt:
  assumes "PoW t n = PoW t n'"
  and "trNxt t n"
  and "n'\<ge>n"
shows "trNxt t n'"
proof -
  from assms (2) have "(\<exists>n'\<ge>n. PoW t n' > PoW t n \<and> (\<forall>n''>n. n'' \<le> n' \<longrightarrow> \<not>(\<exists>nid\<in>actUt t n''. \<parallel>nid\<parallel>\<^bsub>t n''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n''))))) \<or> (\<forall>n'>n. \<not>(\<exists>nid\<in>actUt t n'. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n'))))" using trNxt_def by simp
  thus ?thesis
  proof
    assume "\<exists>n'\<ge>n. PoW t n' > PoW t n \<and> (\<forall>n''>n. n'' \<le> n' \<longrightarrow> \<not>(\<exists>nid\<in>actUt t n''. \<parallel>nid\<parallel>\<^bsub>t n''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n''))))"
    then obtain n'' where "n''\<ge> n" and "PoW t n'' > PoW t n" and "\<forall>n'''>n. n''' \<le> n'' \<longrightarrow> \<not>(\<exists>nid\<in>actUt t n'''. \<parallel>nid\<parallel>\<^bsub>t n'''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n''')))" by auto
    moreover have "n'' \<ge> n'"
    proof (rule ccontr)
      assume "\<not>n''\<ge>n'"
      hence "n''<n'" by simp
      with assms(1) \<open>n''\<ge> n\<close> \<open>PoW t n'' > PoW t n\<close> show False using pow_equals[of t n n' n''] by simp
    qed
    moreover from \<open>PoW t n'' > PoW t n\<close> assms(1) have "PoW t n'' > PoW t n'" by simp
    moreover from assms(3) \<open>\<forall>n'''>n. n''' \<le> n'' \<longrightarrow> \<not>(\<exists>nid\<in>actUt t n'''. \<parallel>nid\<parallel>\<^bsub>t n'''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n''')))\<close> have "\<forall>n'''>n'. n''' \<le> n'' \<longrightarrow> \<not>(\<exists>nid\<in>actUt t n'''. \<parallel>nid\<parallel>\<^bsub>t n'''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n''')))" using le_less_trans by blast
    ultimately show ?thesis using trNxt_def[of t n'] by auto
  next
    assume "\<forall>n'>n. \<not>(\<exists>nid\<in>actUt t n'. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n')))"
    with assms(3) have "\<forall>n''>n'. \<not>(\<exists>nid\<in>actUt t n''. \<parallel>nid\<parallel>\<^bsub>t n''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n'')))" by simp
    thus ?thesis using trNxt_def[of t n'] by simp
  qed
qed

lemma trnxt_pow_gr:
  assumes "trNxt t n"
    and "\<not> trusted nid"
    and "mining (\<sigma>\<^bsub>nid\<^esub>t n')"
    and "\<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
    and "n' > n"
  shows "PoW t n' > PoW t n"
proof -
  from assms(1) have "(\<exists>n'\<ge>n. PoW t n' > PoW t n \<and> (\<forall>n''>n. n'' \<le> n' \<longrightarrow> \<not>(\<exists>nid\<in>actUt t n''. \<parallel>nid\<parallel>\<^bsub>t n''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n''))))) \<or> (\<forall>n'>n. \<not>(\<exists>nid\<in>actUt t n'. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n'))))" using trNxt_def by simp
  moreover have "\<not>(\<forall>n'>n. \<not>(\<exists>nid\<in>actUt t n'. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n'))))"
  proof (rule ccontr)
    assume "\<not> \<not> (\<forall>n'>n. \<not> (\<exists>nid\<in>actUt t n'. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>t n')))"
    hence "\<forall>n'>n. \<not> (\<exists>nid\<in>actUt t n'. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>t n'))" by simp
    moreover from assms have "nid \<in> actUt t n'" using actUt_def by simp
    ultimately show False using assms by simp
  qed
  ultimately have "\<exists>n'\<ge>n. PoW t n' > PoW t n \<and> (\<forall>n''>n. n'' \<le> n' \<longrightarrow> \<not>(\<exists>nid\<in>actUt t n''. \<parallel>nid\<parallel>\<^bsub>t n''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n''))))" by auto
  then obtain n'' where "n''\<ge> n" and "PoW t n'' > PoW t n" and asmp: "\<forall>n'''>n. n''' \<le> n'' \<longrightarrow> \<not>(\<exists>nid\<in>actUt t n'''. \<parallel>nid\<parallel>\<^bsub>t n'''\<^esub> \<and> mining (\<sigma>\<^bsub>nid\<^esub>(t n''')))" by auto
  moreover have "n'' < n'"
  proof (rule ccontr)
    assume "\<not>n''<n'"
    hence "n''\<ge>n'" by simp
    moreover from assms have "nid \<in> actUt t n'" using actUt_def by simp
    ultimately show False using assms(3) assms(4) assms(5) asmp by simp
  qed
  hence "PoW t n' \<ge> PoW t n''" using pow_mono by simp
  ultimately show ?thesis by simp
qed

subsubsection "Secure Blockchains"

lemma ut_src_tr:
  assumes "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
    and build: "mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
    and "PoW t n > length sbc \<or> PoW t n = length sbc \<and> trNxt t n"
  shows "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) < PoW t n \<or> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) = PoW t n \<and> trNxt t n \<or> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t n))"
proof cases
  assume "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<ge> length sbc"
  with build assms(1) show ?thesis using prefix_length_prefix[of sbc "bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)"] by auto
next
  assume "\<not> length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<ge> length sbc"
  hence "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) < length sbc" by simp
  hence "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) < length sbc \<or> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) = length sbc" by auto
  thus ?thesis
  proof
    assume "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) < length sbc"
    with assms(3) show ?thesis by auto
  next
    assume asmp: "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) = length sbc"
    from assms(3) show ?thesis
    proof
      assume "PoW t n > length sbc"
      with asmp show ?thesis by simp
    next
      assume "PoW t n = length sbc \<and> trNxt t n"
      with asmp show ?thesis by simp
    qed
  qed
qed

lemma ut_src_ut_less:
  assumes "\<not> trusted nid"
      and "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
      and "\<not>mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid])"
      and "\<exists>n'\<ge>n\<^sub>S. n'<n \<and> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
      and "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
    shows "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) < PoW t n \<or> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) = PoW t n \<and> trNxt t n"
proof -
  from assms(2) have "Suc (Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> Suc (Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" by auto
  thus ?thesis
  proof
    assume "Suc (Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
    with assms(3) have "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using prefix_length_le by fastforce
    moreover from assms(4) have "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n" using lastAct_prop(2) order.strict_implies_order by blast
    ultimately show ?thesis using pow_mono[of "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" n t] by simp
  next
    assume asmp: "Suc (Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
    from assms (3) have "prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> bc (\<sigma>\<^bsub>nid\<^esub>t n) = (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid])" by auto
    thus ?thesis
    proof
      assume "prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
      with asmp have "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using prefix_length_le by fastforce
      moreover from assms(4) have "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n" using lastAct_prop(2) order.strict_implies_order by blast
      ultimately show ?thesis using pow_mono[of "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" n t] by simp
    next
      assume asmp2: "bc (\<sigma>\<^bsub>nid\<^esub>t n) = bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]"
      show ?thesis
      proof cases
        assume "PoW t n > PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
        with asmp asmp2 show ?thesis by simp
      next
        assume "\<not>(PoW t n > PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)"
        hence "PoW t n \<le> PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
        moreover have "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n" using assms(4) lastAct_prop(2) by auto
        hence "PoW t n \<ge> PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using pow_mono by simp
        ultimately have "PoW t n = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using pow_mono by simp
        with asmp asmp2 have "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) = PoW t n" by simp
        moreover from asmp2 assms(3) have "mining (\<sigma>\<^bsub>nid\<^esub>t n)" by simp
        with \<open>\<not> trusted nid\<close> have "trNxt t n" using fair by simp
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

lemma ut_src_ut_eq:
  assumes "\<not> trusted nid"
      and "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
      and "trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
      and "\<not>mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid])"
      and "\<exists>n'\<ge>n\<^sub>S. n'<n \<and> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
      and "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
    shows "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) < PoW t n \<or> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) = PoW t n \<and> trNxt t n"
proof cases
  assume "mining (\<sigma>\<^bsub>nid\<^esub>t n)"
  with assms(1) have "trNxt t n" using fair by simp
  moreover from assms(5) have "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n" using lastAct_prop(2) by blast
  with \<open>mining (\<sigma>\<^bsub>nid\<^esub>t n)\<close> \<open>trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<close> assms(1) have "PoW t n > PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using trnxt_pow_gr[of t "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" nid n] assms(6) by simp
  moreover from assms (4) have "prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid])" by auto
  hence "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<le> length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid])" using prefix_length_le by metis
  hence "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<le> Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))" by simp
  with assms(2) have "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<le> PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
  ultimately show ?thesis by auto
next
  assume "\<not>mining (\<sigma>\<^bsub>nid\<^esub>t n)"
  with assms(4) have "prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" by simp
  hence "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) < length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<or> length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) = length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using le_neq_implies_less prefix_length_le by blast
  thus ?thesis
  proof
    assume "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) < length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
    with assms(2) have "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
    moreover from assms(5) have "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n" using lastAct_prop(2) order.strict_implies_order by blast
    ultimately show ?thesis using pow_mono[of "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" n t] by simp
  next
    assume asmp: "length (bc (\<sigma>\<^bsub>nid\<^esub>t n)) = length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
    show ?thesis
    proof cases
      assume "PoW t n > PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
      with asmp assms(2) show ?thesis by simp
    next
      assume "\<not>(PoW t n > PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)"
      moreover have "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n" using assms(5) lastAct_prop(2) by auto
      hence "PoW t n \<ge> PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using pow_mono by simp
      ultimately have "PoW t n = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using pow_mono by simp
      with asmp assms(2) have "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) = PoW t n" by simp
      moreover from assms(5) have "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n" using \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n\<close> nat_less_le by blast
      with \<open>PoW t n = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<close> assms(3) have "trNxt t n" using pow_eq_trnxt[of t "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" n] by simp
      ultimately show ?thesis by simp
    qed
  qed 
qed

lemma sbc_pow:
  fixes t::"nat\<Rightarrow>cnf" and n\<^sub>S and sbc and n
  assumes "\<forall>nid. bc (\<sigma>\<^bsub>nid\<^esub>(t (\<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^sub>S\<^esub>))) = sbc"
    and "trNxt t n\<^sub>S"
  shows "n\<ge>n\<^sub>S \<Longrightarrow> PoW t n > length sbc \<or> PoW t n = length sbc \<and> trNxt t n"
proof (induction n rule: dec_induct)
  case base
  have "PoW t n\<^sub>S = length sbc"
  proof (rule pow_eq)
    show "\<exists>tid\<in>actTr t n\<^sub>S. length (bc (\<sigma>\<^bsub>tid\<^esub>t n\<^sub>S)) = length sbc"
    proof -
      from actTr have "actTr t n\<^sub>S \<noteq> {}" using actTr_def by blast
      then obtain tid where "tid\<in>actTr t n\<^sub>S" by auto
      moreover from \<open>tid\<in>actTr t n\<^sub>S\<close> have "\<parallel>tid\<parallel>\<^bsub>t n\<^sub>S\<^esub>" using actTr_def by simp
      hence "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^sub>S\<^esub>=n\<^sub>S" by (simp add: nxtAct_active)
      with assms(1) have "length (bc (\<sigma>\<^bsub>tid\<^esub>t n\<^sub>S)) = length sbc" by metis
      ultimately show "?thesis" by auto
    qed
  next
    show "\<forall>tid\<in>actTr t n\<^sub>S. length (bc (\<sigma>\<^bsub>tid\<^esub>t n\<^sub>S)) \<le> length sbc"
    proof
      fix tid
      assume "tid \<in> actTr t n\<^sub>S "
      hence "\<parallel>tid\<parallel>\<^bsub>t n\<^sub>S\<^esub>" using actTr_def by simp
      hence "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^sub>S\<^esub>=n\<^sub>S" by (simp add: nxtAct_active)
      with assms(1) show "length (bc (\<sigma>\<^bsub>tid\<^esub>t n\<^sub>S)) \<le> length sbc" by (metis order_refl)
    qed
  qed
  with assms(2) show ?case by simp
next
  case (step n)
  from step.IH show ?case
  proof
    assume "length sbc < PoW t n"
    with pow_mono[of n "Suc n" t] show ?thesis by simp
  next
    assume "PoW t n = length sbc \<and> trNxt t n"
    hence "PoW t n = length sbc" and "trNxt t n" by auto
    show ?thesis
    proof cases
      assume "PoW t n = PoW t (Suc n)"
      with \<open>PoW t n = length sbc\<close> have "PoW t (Suc n) = length sbc" by simp
      moreover from \<open>PoW t n = PoW t (Suc n)\<close> \<open>trNxt t n\<close> have"trNxt t (Suc n)" using pow_eq_trnxt[of t n "Suc n"] by simp
      ultimately show ?thesis by simp
    next
      assume "\<not> PoW t n = PoW t (Suc n)"
      moreover have "PoW t (Suc n) \<ge> PoW t n" using pow_mono by simp
      ultimately have "PoW t (Suc n) > PoW t n" by simp
      with \<open>PoW t n = length sbc\<close> show ?thesis by simp
    qed
  qed
qed

theorem blockchain_save:
  fixes t::"nat\<Rightarrow>cnf" and n\<^sub>S and sbc and n
  assumes "\<forall>nid. bc (\<sigma>\<^bsub>nid\<^esub>(t (\<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^sub>S\<^esub>))) = sbc"
    and "trNxt t n\<^sub>S"
    and prems:"n\<ge>n\<^sub>S"
  shows "n\<ge>n\<^sub>S \<Longrightarrow> \<forall>nid. (trusted nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<longrightarrow> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))) \<and> (\<not>trusted nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<longrightarrow> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))) < PoW t n \<or> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))) = PoW t n \<and> trNxt t n \<or> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>(t n))))"
proof (induction n rule: ge_induct)
  case (step n)
  show ?case
  proof
    fix nid
    show "(trusted nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<longrightarrow> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))) \<and>
      (\<not>trusted nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<longrightarrow> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))) < PoW t n \<or> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))) = PoW t n \<and> trNxt t n \<or> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>(t n))))"
    proof (rule conjI)
      show "trusted nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<longrightarrow> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t n))"
      proof
        assume "trusted nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
        hence "trusted nid" and "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>" by auto
        show "prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t n))"
        proof cases
          assume "\<forall>n'\<ge>n\<^sub>S. n'<n \<longrightarrow> \<not> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
          moreover from step.hyps have "n\<^sub>S \<le> n" by simp
          ultimately have "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^sub>S\<^esub> = n" using \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> nxtAct_eq[of n\<^sub>S n nid t] by simp
          thus ?thesis using assms by auto
        next
          assume "\<not> (\<forall>n'\<ge>n\<^sub>S. n'<n \<longrightarrow> \<not> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>)"
          hence act: "\<exists>n'\<ge>n\<^sub>S. n'<n \<and> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>" by simp
          hence "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S" using lastActless by simp
          moreover from act have "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n" using lastAct_prop(2) by auto
          moreover from act have "\<parallel>nid\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using lastAct_prop(1) by auto
          ultimately have "prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH \<open>trusted nid\<close> by simp
          show ?thesis
          proof -
            from \<open>trusted nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> act have "prefix (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) (bc (\<sigma>\<^bsub>nid\<^esub>t n)) \<or>
                (\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<ge> length (MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) \<and> prefix (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) (bc (\<sigma>\<^bsub>nid\<^esub>t n)))" using bhv_tr_context by simp
            thus ?thesis
            proof
              assume "prefix (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) (bc (\<sigma>\<^bsub>nid\<^esub>t n))"
              with \<open>prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))\<close> show ?thesis by simp
            next
              assume "\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<ge> length (MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) \<and> prefix (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) (bc (\<sigma>\<^bsub>nid\<^esub>t n))"
              then obtain nid' where "\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and maxbc: "length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<ge> length (MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))" and pref: "prefix (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) (bc (\<sigma>\<^bsub>nid\<^esub>t n))" by auto
              show ?thesis
              proof cases
                assume "trusted nid'"
                with \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S\<close> \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n\<close> have "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH by blast
                with pref show ?thesis by simp
              next                                                                                                             
                assume "\<not> trusted nid'"
                with \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S\<close> \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n\<close> by simp
                hence "length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" by auto
                thus ?thesis
                proof
                  assume "length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                  moreover from maxbc have "length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<ge> length (MAX (pin (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))" by simp
                  with \<open>trusted nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)) \<ge> PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" using pow_le_max[of nid t "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
                  ultimately show ?thesis by simp
                next
                  assume "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
                  with pref show ?thesis by simp
                qed
              qed
            qed
          qed
        qed
      qed
    next
      show "\<not>trusted nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub> \<longrightarrow> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))) < PoW t n \<or> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))) = PoW t n \<and> trNxt t n \<or> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>(t n)))"
      proof
        assume "\<not> trusted nid \<and> \<parallel>nid\<parallel>\<^bsub>t n\<^esub>"
        hence  "\<not> trusted nid" and "\<parallel>nid\<parallel>\<^bsub>t n\<^esub>" by auto
        show "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) < PoW t n \<or> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t n))) = PoW t n \<and> trNxt t n \<or> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t n))"
        proof cases
          assume "\<forall>n'\<ge>n\<^sub>S. n'<n \<longrightarrow> \<not> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
          moreover from step.hyps have "n\<^sub>S \<le> n" by simp
          ultimately have "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>n\<^sub>S\<^esub> = n" using \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> nxtAct_eq[of n\<^sub>S n nid t] by simp
          thus ?thesis using assms by auto
        next
          assume "\<not> (\<forall>n'\<ge>n\<^sub>S. n'<n \<longrightarrow> \<not> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>)"
          hence act: "\<exists>n'\<ge>n\<^sub>S. n'<n \<and> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>" by simp
          hence "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S" using lastActless by simp
          moreover from act have "\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n" using lastAct_prop(2) by auto
          moreover from act have "\<parallel>nid\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using lastAct_prop(1) by auto
          ultimately have "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH \<open>\<not> trusted nid\<close> by simp
          thus ?thesis
          proof (rule disjE3)
            assume cass1: "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
            show ?thesis
            proof -
              from \<open>\<not> trusted nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> act
              have "(mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or>
                                      \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) \<or> ((\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))))" using bhv_ut_context[of nid t n n\<^sub>S] by simp
              thus ?thesis
              proof
                assume "(mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
                with \<open>\<not> trusted nid\<close> act cass1 \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show ?thesis using ut_src_ut_less[of nid nid t n n\<^sub>S] by auto
              next
                assume "\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
                then obtain nid' where "\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and build: "mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" by auto
                show ?thesis
                proof cases
                  assume "trusted nid'"
                  with \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S\<close> \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n\<close> \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH by simp
                  moreover from assms(1) assms(2) step.hyps have "PoW t n > length sbc \<or> PoW t n = length sbc \<and> trNxt t n" using sbc_pow[of t n\<^sub>S sbc n] by simp
                  ultimately show ?thesis using build ut_src_tr by simp
                next
                  assume "\<not> trusted nid'"
                  with \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S\<close> \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n\<close> \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH by simp
                  thus ?thesis
                  proof (rule disjE3)
                    assume "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                    with \<open>\<not> trusted nid\<close> act build \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show ?thesis using ut_src_ut_less[of nid nid' t n n\<^sub>S] by auto
                  next
                    assume "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                    with \<open>\<not> trusted nid\<close> act build \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show ?thesis using ut_src_ut_eq[of nid nid' t n n\<^sub>S] by auto
                  next
                    assume "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
                    moreover from assms(1) assms(2) step.hyps have "PoW t n > length sbc \<or> PoW t n = length sbc \<and> trNxt t n" using sbc_pow[of t n\<^sub>S sbc n] by simp
                    ultimately show ?thesis using build ut_src_tr by simp
                  qed
                qed
              qed
            qed
          next
            assume cass2: "Suc (length (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
            show ?thesis
            proof -
              from \<open>\<not> trusted nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> act
              have "(mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or>
                                      \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) \<or> ((\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))))" using bhv_ut_context[of nid t n n\<^sub>S] by simp
              thus ?thesis
              proof
                assume "(mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or>
                                      \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
                with \<open>\<not> trusted nid\<close> act cass2 \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show ?thesis using ut_src_ut_eq[of nid nid t n n\<^sub>S] by auto
              next
                assume "\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
                then obtain nid' where "\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and build: "mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" by auto
                show ?thesis
                proof cases
                  assume "trusted nid'"
                  with \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S\<close> \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n\<close> \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH by simp
                  moreover from assms(1) assms(2) step.hyps have "PoW t n > length sbc \<or> PoW t n = length sbc \<and> trNxt t n" using sbc_pow[of t n\<^sub>S sbc n] by simp
                  ultimately show ?thesis using build ut_src_tr by simp
                next
                  assume "\<not> trusted nid'"
                  with \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S\<close> \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n\<close> \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH by simp
                  thus ?thesis
                  proof (rule disjE3)
                    assume "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                    with \<open>\<not> trusted nid\<close> act build \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show ?thesis using ut_src_ut_less[of nid nid' t n n\<^sub>S] by auto
                  next
                    assume "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                    with \<open>\<not> trusted nid\<close> act build \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show ?thesis using ut_src_ut_eq[of nid nid' t n n\<^sub>S] by auto
                  next
                    assume "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
                    moreover from assms(1) assms(2) step.hyps have "PoW t n > length sbc \<or> PoW t n = length sbc \<and> trNxt t n" using sbc_pow[of t n\<^sub>S sbc n] by simp
                    ultimately show ?thesis using build ut_src_tr by simp
                  qed
                qed
              qed
            qed
          next
            assume cass3: "prefix sbc (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
            show ?thesis
            proof -
              from \<open>\<not> trusted nid\<close> \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> act
              have "(mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or>
                                      \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) \<or> ((\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))))" using bhv_ut_context[of nid t n n\<^sub>S] by simp
              thus ?thesis
              proof
                assume "mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or>
                                      \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
                moreover from assms(1) assms(2) step.hyps have "PoW t n > length sbc \<or> PoW t n = length sbc \<and> trNxt t n" using sbc_pow[of t n\<^sub>S sbc n] by simp
                ultimately show ?thesis using cass3 ut_src_tr by simp
              next
                assume "\<exists>nid'. \<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>)))"
                then obtain nid' where "\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and build: "mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>) @ [nid]) \<or> \<not> mining (\<sigma>\<^bsub>nid\<^esub>t n) \<and> prefix (bc (\<sigma>\<^bsub>nid\<^esub>t n)) (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" by auto
                show ?thesis
                proof cases
                  assume "trusted nid'"
                  with \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S\<close> \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n\<close> \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH by simp
                  moreover from assms(1) assms(2) step.hyps have "PoW t n > length sbc \<or> PoW t n = length sbc \<and> trNxt t n" using sbc_pow[of t n\<^sub>S sbc n] by simp
                  ultimately show ?thesis using build ut_src_tr by simp
                next
                  assume "\<not> trusted nid'"
                  with \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n\<^sub>S\<close> \<open>\<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> < n\<close> \<open>\<parallel>nid'\<parallel>\<^bsub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>\<close> have "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<or> prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))" using step.IH by simp
                  thus ?thesis
                  proof (rule disjE3)
                    assume "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) < PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                    with \<open>\<not> trusted nid\<close> act build \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show ?thesis using ut_src_ut_less[of nid nid' t n n\<^sub>S] by auto
                  next
                    assume "Suc (length (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))) = PoW t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> trNxt t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
                    with \<open>\<not> trusted nid\<close> act build \<open>\<parallel>nid\<parallel>\<^bsub>t n\<^esub>\<close> show ?thesis using ut_src_ut_eq[of nid nid' t n n\<^sub>S] by auto
                  next
                    assume "prefix sbc (bc (\<sigma>\<^bsub>nid'\<^esub>t \<langle>nid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>))"
                    moreover from assms(1) assms(2) step.hyps have "PoW t n > length sbc \<or> PoW t n = length sbc \<and> trNxt t n" using sbc_pow[of t n\<^sub>S sbc n] by simp
                    ultimately show ?thesis using build ut_src_tr by simp
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

end

end