section {* Formalization of Bit Vectors *}

theory BitVector imports Main begin

type_synonym bit_vector = "bool list"

fun bv_leqs :: "bit_vector \<Rightarrow> bit_vector \<Rightarrow> bool" ("_ \<preceq>\<^sub>b _" 99)
  where bv_Nils:"[] \<preceq>\<^sub>b [] = True"
  | bv_Cons:"(x#xs) \<preceq>\<^sub>b (y#ys) = ((x \<longrightarrow> y) \<and> xs \<preceq>\<^sub>b ys)"
  | bv_rest:"xs \<preceq>\<^sub>b ys = False"


subsection {* Some basic properties *}

lemma bv_length: "xs \<preceq>\<^sub>b ys \<Longrightarrow> length xs = length ys"
by(induct rule:bv_leqs.induct)auto


lemma [dest!]: "xs \<preceq>\<^sub>b [] \<Longrightarrow> xs = []"
by(induct xs) auto


lemma bv_leqs_AppendI:
  "\<lbrakk>xs \<preceq>\<^sub>b ys; xs' \<preceq>\<^sub>b ys'\<rbrakk> \<Longrightarrow> (xs@xs') \<preceq>\<^sub>b (ys@ys')"
by(induct xs ys rule:bv_leqs.induct,auto)


lemma bv_leqs_AppendD:
  "\<lbrakk>(xs@xs') \<preceq>\<^sub>b (ys@ys'); length xs = length ys\<rbrakk>
  \<Longrightarrow> xs \<preceq>\<^sub>b ys \<and> xs' \<preceq>\<^sub>b ys'"
by(induct xs ys rule:bv_leqs.induct,auto)


lemma bv_leqs_eq:
  "xs \<preceq>\<^sub>b ys = ((\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i) \<and> length xs = length ys)"
proof(induct xs ys rule:bv_leqs.induct)
  case (2 x xs y ys)
  note eq = `xs \<preceq>\<^sub>b ys = 
    ((\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i) \<and> length xs = length ys)`
  show ?case
  proof
    assume leqs:"x#xs \<preceq>\<^sub>b y#ys"
    with eq have "x \<longrightarrow> y" and "\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i"
      and "length xs = length ys" by simp_all
    from `x \<longrightarrow> y` have "(x#xs) ! 0 \<longrightarrow> (y#ys) ! 0" by simp
    { fix i assume "i > 0" and "i < length (x#xs)"
      then obtain j where "i = Suc j" and "j < length xs" by(cases i) auto
      with `\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i` 
      have "(x#xs) ! i \<longrightarrow> (y#ys) ! i" by auto }
    hence "\<forall>i < length (x#xs). i > 0 \<longrightarrow> (x#xs) ! i \<longrightarrow> (y#ys) ! i" by simp
    with `(x#xs) ! 0 \<longrightarrow> (y#ys) ! 0` `length xs = length ys`
    show "(\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i) \<and> 
      length (x#xs) = length (y#ys)"
      by clarsimp(case_tac "i>0",auto)
  next
    assume "(\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i) \<and> 
      length (x#xs) = length (y#ys)"
    hence "\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i" 
      and "length (x#xs) = length (y#ys)" by simp_all
    from `\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i`
    have "\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i"
      by clarsimp(erule_tac x="Suc i" in allE,auto)
    with eq `length (x#xs) = length (y#ys)` have "xs \<preceq>\<^sub>b ys" by simp
    from `\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i`
    have "x \<longrightarrow> y" by(erule_tac x="0" in allE) simp
    with `xs \<preceq>\<^sub>b ys` show "x#xs \<preceq>\<^sub>b y#ys" by simp
  qed
qed simp_all


subsection {* $\preceq_b$ is an order on bit vectors with minimal and 
  maximal element *}

lemma minimal_element:
  "replicate (length xs) False \<preceq>\<^sub>b xs"
by(induct xs) auto

lemma maximal_element:
  "xs \<preceq>\<^sub>b replicate (length xs) True"
by(induct xs) auto

lemma bv_leqs_refl:"xs \<preceq>\<^sub>b xs"
  by(induct xs) auto


lemma bv_leqs_trans:"\<lbrakk>xs \<preceq>\<^sub>b ys; ys \<preceq>\<^sub>b zs\<rbrakk> \<Longrightarrow> xs \<preceq>\<^sub>b zs"
proof(induct xs ys arbitrary:zs rule:bv_leqs.induct)
  case (2 x xs y ys)
  note IH = `\<And>zs. \<lbrakk>xs \<preceq>\<^sub>b ys; ys \<preceq>\<^sub>b zs\<rbrakk> \<Longrightarrow> xs \<preceq>\<^sub>b zs`
  from `(x#xs) \<preceq>\<^sub>b (y#ys)` have "xs \<preceq>\<^sub>b ys" and "x \<longrightarrow> y" by simp_all
  from `(y#ys) \<preceq>\<^sub>b zs` obtain z zs' where "zs = z#zs'" by(cases zs) auto
  with `(y#ys) \<preceq>\<^sub>b zs` have "ys \<preceq>\<^sub>b zs'" and "y \<longrightarrow> z" by simp_all
  from IH[OF `xs \<preceq>\<^sub>b ys` `ys \<preceq>\<^sub>b zs'`] have "xs \<preceq>\<^sub>b zs'" .
  with `x \<longrightarrow> y` `y \<longrightarrow> z` `zs = z#zs'` show ?case by simp
qed simp_all


lemma bv_leqs_antisym:"\<lbrakk>xs \<preceq>\<^sub>b ys; ys \<preceq>\<^sub>b xs\<rbrakk> \<Longrightarrow> xs = ys"
  by(induct xs ys rule:bv_leqs.induct)auto


definition bv_less :: "bit_vector \<Rightarrow> bit_vector \<Rightarrow> bool" ("_ \<prec>\<^sub>b _" 99)
  where "xs \<prec>\<^sub>b ys \<equiv> xs \<preceq>\<^sub>b ys \<and> xs \<noteq> ys"


interpretation order "bv_leqs" "bv_less"
by(unfold_locales,
   auto intro:bv_leqs_refl bv_leqs_trans bv_leqs_antisym simp:bv_less_def)


end
