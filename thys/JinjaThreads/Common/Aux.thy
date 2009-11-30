(*  Title:      JinjaThreads/Common/Aux.thy
    Author:     Andreas Lochbihler, David von Oheimb, Tobias Nipkow

    Based on the Jinja theory Common/Aux.thy by David von Oheimb and Tobias Nipkow
*)

header {* 
  \isaheader{Auxiliary Definitions and Lemmata}
*}

theory Aux 
imports
  Main
  "../../FinFun/FinFun"
  "Transitive_Closure_Table"
  Code_Char
begin


(* FIXME move and possibly turn into a general simproc *)
lemma nat_add_max_le[simp]:
  "((n::nat) + max i j \<le> m) = (n + i \<le> m \<and> n + j \<le> m)"
 (*<*)by arith(*>*)

lemma Suc_add_max_le[simp]:
  "(Suc(n + max i j) \<le> m) = (Suc(n + i) \<le> m \<and> Suc(n + j) \<le> m)"
(*<*)by arith(*>*)

notation Some ("(\<lfloor>_\<rfloor>)")

(*<*)
declare
 option.splits[split]
 Let_def[simp]
 subset_insertI2 [simp]
(*>*)


subsection {*@{text distinct_fst}*}
 
definition
  distinct_fst  :: "('a \<times> 'b) list \<Rightarrow> bool"
where
  "distinct_fst  \<equiv>  distinct \<circ> map fst"

lemma distinct_fst_Nil [simp]:
  "distinct_fst []"
 (*<*)
apply (unfold distinct_fst_def)
apply (simp (no_asm))
done
(*>*)

lemma distinct_fst_Cons [simp]:
  "distinct_fst ((k,x)#kxs) = (distinct_fst kxs \<and> (\<forall>y. (k,y) \<notin> set kxs))"
(*<*)
apply (unfold distinct_fst_def)
apply (auto simp:image_def)
done
(*>*)

lemma distinct_fstD: "\<lbrakk> distinct_fst xs; (x, y) \<in> set xs; (x, z) \<in> set xs \<rbrakk> \<Longrightarrow> y = z"
by(induct xs) auto

lemma map_of_SomeI:
  "\<lbrakk> distinct_fst kxs; (k,x) \<in> set kxs \<rbrakk> \<Longrightarrow> map_of kxs k = Some x"
(*<*)by (induct kxs) (auto simp:fun_upd_apply)(*>*)


subsection {* Using @{term list_all2} for relations *}

definition
  fun_of :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where
  "fun_of S \<equiv> \<lambda>x y. (x,y) \<in> S"

text {* Convenience lemmas *}
(*<*)
declare fun_of_def [simp]
(*>*)
lemma rel_list_all2_Cons [iff]:
  "list_all2 (fun_of S) (x#xs) (y#ys) = 
   ((x,y) \<in> S \<and> list_all2 (fun_of S) xs ys)"
  (*<*)by simp(*>*)

lemma rel_list_all2_Cons1:
  "list_all2 (fun_of S) (x#xs) ys = 
  (\<exists>z zs. ys = z#zs \<and> (x,z) \<in> S \<and> list_all2 (fun_of S) xs zs)"
  (*<*)by (cases ys) auto(*>*)

lemma rel_list_all2_Cons2:
  "list_all2 (fun_of S) xs (y#ys) = 
  (\<exists>z zs. xs = z#zs \<and> (z,y) \<in> S \<and> list_all2 (fun_of S) zs ys)"
  (*<*)by (cases xs) auto(*>*)

lemma rel_list_all2_refl:
  "(\<And>x. (x,x) \<in> S) \<Longrightarrow> list_all2 (fun_of S) xs xs"
  (*<*)by (simp add: list_all2_refl)(*>*)

lemma rel_list_all2_antisym:
  "\<lbrakk> (\<And>x y. \<lbrakk>(x,y) \<in> S; (y,x) \<in> T\<rbrakk> \<Longrightarrow> x = y); 
     list_all2 (fun_of S) xs ys; list_all2 (fun_of T) ys xs \<rbrakk> \<Longrightarrow> xs = ys"
  (*<*)by (rule list_all2_antisym) auto(*>*)

lemma rel_list_all2_trans: 
  "\<lbrakk> \<And>a b c. \<lbrakk>(a,b) \<in> R; (b,c) \<in> S\<rbrakk> \<Longrightarrow> (a,c) \<in> T;
    list_all2 (fun_of R) as bs; list_all2 (fun_of S) bs cs\<rbrakk> 
  \<Longrightarrow> list_all2 (fun_of T) as cs"
  (*<*)by (rule list_all2_trans) auto(*>*)

lemma rel_list_all2_update_cong:
  "\<lbrakk> i<size xs; list_all2 (fun_of S) xs ys; (x,y) \<in> S \<rbrakk> 
  \<Longrightarrow> list_all2 (fun_of S) (xs[i:=x]) (ys[i:=y])"
  (*<*)by (simp add: list_all2_update_cong)(*>*)

lemma rel_list_all2_nthD:
  "\<lbrakk> list_all2 (fun_of S) xs ys; p < size xs \<rbrakk> \<Longrightarrow> (xs!p,ys!p) \<in> S"
  (*<*)by (drule list_all2_nthD) auto(*>*)

lemma rel_list_all2I:
  "\<lbrakk> length a = length b; \<And>n. n < length a \<Longrightarrow> (a!n,b!n) \<in> S \<rbrakk> \<Longrightarrow> list_all2 (fun_of S) a b"
  (*<*)by (erule list_all2_all_nthI) simp(*>*)

(*<*)declare fun_of_def [simp del](*>*)


fun flatten :: "'a list list \<Rightarrow> 'a list" ("\<down>_\<down>" [50] 80)
where
  "flatten [] = []"
| "flatten (xs # xss) = xs @ flatten xss"

lemma set_flatten_Union_set [simp]:
  "set (flatten xs) = Union (set (map set xs))"
by(induct xs, auto)

lemma flatten_append [simp]: "flatten (xs @ ys) = flatten xs @ flatten ys"
by(induct xs, auto)


lemma f_nth_set:
  "\<lbrakk> f (xs ! n) = v; n < length xs \<rbrakk> \<Longrightarrow> v \<in> f ` set xs"
apply(induct xs arbitrary: n)
 apply(simp)
apply(case_tac "n")
apply(auto)
done


lemma map_eq_imp_length_eq': 
  "map f xs = map g ys \<Longrightarrow> length xs = length ys"
apply(induct xs arbitrary: ys)
 apply(simp)
apply(auto simp add: Cons_eq_map_conv)
done


lemma replicate_eq_append_conv: 
  "(replicate n x = xs @ ys) = (\<exists>m\<le>n. xs = replicate m x \<and> ys = replicate (n-m) x)"
proof(induct n arbitrary: xs ys)
  case 0 thus ?case by simp
next
  case (Suc n xs ys)
  have IH: "\<And>xs ys. (replicate n x = xs @ ys) = (\<exists>m\<le>n. xs = replicate m x \<and> ys = replicate (n - m) x)" by fact
  show ?case
  proof(unfold replicate_Suc, rule iffI)
    assume a: "x # replicate n x = xs @ ys"
    show "\<exists>m\<le>Suc n. xs = replicate m x \<and> ys = replicate (Suc n - m) x"
    proof(cases xs)
      case Nil
      thus ?thesis using a
	by(auto)
    next
      case (Cons X XS)
      with a have x: "x = X" and "replicate n x = XS @ ys" by auto
      hence "\<exists>m\<le>n. XS = replicate m x \<and> ys = replicate (n - m) x"
	by -(rule IH[THEN iffD1])
      then obtain m where "m \<le> n" and XS: "XS = replicate m x" and ys: "ys = replicate (n - m) x" by blast
      with x Cons show ?thesis
	by(fastsimp)
    qed
  next
    assume "\<exists>m\<le>Suc n. xs = replicate m x \<and> ys = replicate (Suc n - m) x"
    then obtain m where m: "m \<le> Suc n" and xs: "xs = replicate m x" and ys: "ys = replicate (Suc n - m) x" by blast
    thus "x # replicate n x = xs @ ys"
      by(simp add: replicate_add[THEN sym])
  qed
qed

lemma map_eq_append_conv:
  "map f xs = ys @ zs \<longleftrightarrow> (\<exists>ys' zs'. map f ys' = ys \<and> map f zs' = zs \<and> xs = ys' @ zs')"
apply(rule iffI)
 apply(metis append_eq_conv_conj append_take_drop_id assms drop_map take_map)
by(clarsimp)

lemma append_eq_map_conv:
  "ys @ zs = map f xs \<longleftrightarrow> (\<exists>ys' zs'. map f ys' = ys \<and> map f zs' = zs \<and> xs = ys' @ zs')"
unfolding map_eq_append_conv[symmetric]
by auto

lemma map_eq_map_conv:
  "map f xs = map g ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x = g y) xs ys"
apply(induct xs arbitrary: ys)
apply(auto simp add: list_all2_Cons1 Cons_eq_map_conv)
done

lemma map_upd_map_add: "X(V \<mapsto> v) = (X ++ [V \<mapsto> v])"
by(simp)

lemma Collect_eq_singleton_conv:
  "{a. P a} = {a} \<longleftrightarrow> P a \<and> (\<forall>a'. P a' \<longrightarrow> a = a')"
by(auto)

lemmas filter_replicate_conv = filter_replicate

lemma if_else_if_else_eq_if_else [simp]:
  "(if b then x else if b then y else z) = (if b then x else z)"
by(simp)

lemma disjE3: "\<lbrakk> P \<or> Q \<or> R; P \<Longrightarrow> S; Q \<Longrightarrow> S; R \<Longrightarrow> S \<rbrakk> \<Longrightarrow> S"
by auto

lemma length_greater_Suc_0_conv: "Suc 0 < length xs \<longleftrightarrow> (\<exists>x x' xs'. xs = x # x' # xs')"
by(cases xs, auto simp add: neq_Nil_conv)

lemmas zip_same_conv = zip_same_conv_map

lemma map_eq_all_nth_conv:
  "map f xs = ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>n < length xs. f (xs ! n) = ys ! n)"
apply(induct xs arbitrary: ys)
apply(fastsimp simp add: nth_Cons Suc_length_conv split: nat.splits)+
done

lemma nth_Cons_subtract: "0 < n \<Longrightarrow> (x # xs) ! n = xs ! (n - 1)"
by(auto simp add: nth_Cons split: nat.split)

lemma prod_rec_split [simp]: "prod_rec = split"
by(simp add: expand_fun_eq)

lemma rtranclp_False [simp]: "(\<lambda>a b. False)\<^sup>*\<^sup>* = op ="
by(auto simp add: expand_fun_eq elim: rtranclp_induct)

lemmas rtranclp_induct3 =
  rtranclp_induct[where a="(ax, ay, az)" and b="(bx, by, bz)", split_rule, consumes 1, case_names refl step]

lemmas tranclp_induct3 =
  tranclp_induct[where a="(ax, ay, az)" and b="(bx, by, bz)", split_rule, consumes 1, case_names refl step]

lemmas rtranclp_induct4 =
  rtranclp_induct[where a="(ax, ay, az, aw)" and b="(bx, by, bz, bw)", split_rule, consumes 1, case_names refl step]

lemmas tranclp_induct4 =
  tranclp_induct[where a="(ax, ay, az, aw)" and b="(bx, by, bz, bw)", split_rule, consumes 1, case_names refl step]

lemma converse_tranclpE:
  assumes "tranclp r x z"
  obtains (base) "r x z"
        | (step) y where "r x y" "tranclp r y z"
using tranclpD[OF assms]
by(blast elim: converse_rtranclpE dest: rtranclp_into_tranclp2)

lemmas converse_tranclp_induct2 =
  converse_tranclp_induct [of _ "(ax,ay)" "(bx,by)", split_rule,
                 consumes 1, case_names base step]

lemma wfP_induct' [consumes 1, case_names wfP]:
  "\<lbrakk>wfP r; \<And>x. (\<And>y. r y x \<Longrightarrow> P y) \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P a"
by(blast intro: wfP_induct)

lemma wfP_induct2 [consumes 1, case_names wfP]:
  "\<lbrakk>wfP r; \<And>x x'. (\<And>y y'. r (y, y') (x, x') \<Longrightarrow> P y y') \<Longrightarrow> P x x' \<rbrakk> \<Longrightarrow> P x x'"
by(drule wfP_induct'[where P="\<lambda>(x, y). P x y"]) blast+

lemma wfP_minimalE:
  assumes "wfP r"
  and "P x"
  obtains z where "P z" "r^** z x" "\<And>y. r y z \<Longrightarrow> \<not> P y"
proof -
  let ?Q = "\<lambda>x'. P x' \<and> r^** x' x"
  from `P x` have "?Q x" by blast
  from `wfP r` have "\<And>Q. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. r y z \<longrightarrow> y \<notin> Q)"
    unfolding wfP_eq_minimal by blast
  from this[rule_format, of ?Q] `?Q x`
  obtain z where "?Q z" and min: "\<And>y. r y z \<Longrightarrow> \<not> ?Q y" by(auto simp add: mem_def)
  from `?Q z` have "P z" "r^** z x" by auto
  moreover
  { fix y
    assume "r y z"
    hence "\<not> ?Q y" by(rule min)
    moreover from `r y z` `r^** z x` have "r^** y x"
      by(rule converse_rtranclp_into_rtranclp)
    ultimately have "\<not> P y" by blast }
  ultimately show thesis ..
qed

subsection {* reflexive transitive closure for label relations *}

inductive converse3p :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
where
  converse3pI: "r a b c \<Longrightarrow> converse3p r c b a"

lemma converse3p_converse3p: "converse3p (converse3p r) = r"
by(auto intro: converse3pI intro!: ext elim: converse3p.cases)

lemma converse3pD: "converse3p r c b a \<Longrightarrow> r a b c"
by(auto elim: converse3p.cases)

inductive rtrancl3p :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where 
  rtrancl3p_refl [intro!, simp]: "rtrancl3p r a [] a"
| rtrancl3p_step: "\<lbrakk> rtrancl3p r a bs a'; r a' b a'' \<rbrakk> \<Longrightarrow> rtrancl3p r a (bs @ [b]) a''"

lemmas rtrancl3p_induct3 =
  rtrancl3p.induct[of _ "(ax,ay,az)" _ "(cx,cy,cz)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas rtrancl3p_induct4 = 
  rtrancl3p.induct[of _ "(ax,ay,az,aw)" _ "(cx,cy,cz,cw)", split_format (complete),
                 consumes 1, case_names refl step]

lemma rtrancl3p_induct4' [consumes 1, case_names refl step]:
  assumes major: "rtrancl3p r (ax, (ay, az), aw) bs (cx, (cy, cz), cw)"
  and refl: "\<And>a aa b ba. P a aa b ba [] a aa b ba"
  and step: "\<And>a aa b ba bs ab ac bb bc bd ad ae be bf.
       \<lbrakk> rtrancl3p r (a, (aa, b), ba) bs (ab, (ac, bb), bc);
         P a aa b ba bs ab ac bb bc; r (ab, (ac, bb), bc) bd (ad, (ae, be), bf) \<rbrakk>
       \<Longrightarrow> P a aa b ba (bs @ [bd]) ad ae be bf"
  shows "P ax ay az aw bs cx cy cz cw"
using major
apply -
apply(drule_tac P="\<lambda>(a, (aa, b), ba) bs (cx, (cy, cz), cw). P a aa b ba bs cx cy cz cw" in rtrancl3p.induct)
by(auto intro: refl step)

lemma rtrancl3p_induct1:
  "\<lbrakk> rtrancl3p r a bs c; P a; \<And>bs c b d. \<lbrakk> rtrancl3p r a bs c; r c b d; P c \<rbrakk> \<Longrightarrow> P d \<rbrakk> \<Longrightarrow> P c"
apply(induct rule: rtrancl3p.induct)
apply(auto)
done

lemma rtrancl3p_trans [trans]:
  assumes one: "rtrancl3p r a bs a'"
  and two: "rtrancl3p r a' bs' a''"
  shows "rtrancl3p r a (bs @ bs') a''"
using two one
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by simp
next
  case rtrancl3p_step thus ?case
    by(auto simp only: append_assoc[symmetric] intro: rtrancl3p.rtrancl3p_step)
qed

lemma rtrancl3p_step_converse:
  assumes step: "r a b a'"
  and stepify: "rtrancl3p r a' bs a''"
  shows "rtrancl3p r a (b # bs) a''"
using stepify step
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl 
  with rtrancl3p.rtrancl3p_refl[where r=r and a=a] show ?case 
    by(auto dest: rtrancl3p.rtrancl3p_step simp del: rtrancl3p.rtrancl3p_refl)
next
  case rtrancl3p_step thus ?case
    unfolding append_Cons[symmetric]
    by -(rule rtrancl3p.rtrancl3p_step)
qed

lemma converse_rtrancl3p_step:
  "rtrancl3p r a (b # bs) a'' \<Longrightarrow> \<exists>a'. r a b a' \<and> rtrancl3p r a' bs a''"
apply(induct bs arbitrary: a'' rule: rev_induct)
 apply(erule rtrancl3p.cases)
  apply(clarsimp)+
 apply(erule rtrancl3p.cases)
  apply(clarsimp)
  apply(rule_tac x="a''a" in exI)
  apply(clarsimp)
 apply(clarsimp)
apply(erule rtrancl3p.cases)
 apply(clarsimp)
apply(clarsimp)
by(fastsimp intro: rtrancl3p_step)

lemma converse_rtrancl3pD:
  "rtrancl3p (converse3p r) a' bs a \<Longrightarrow> rtrancl3p r a (rev bs) a'"
apply(induct rule: rtrancl3p.induct)
 apply(fastsimp intro: rtrancl3p.intros)
apply(auto dest: converse3pD intro: rtrancl3p_step_converse)
done

lemma rtrancl3p_converseD:
  "rtrancl3p r a bs a' \<Longrightarrow> rtrancl3p (converse3p r) a' (rev bs) a"
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case
    by(auto intro: rtrancl3p.intros)
next
  case rtrancl3p_step thus ?case
    by(auto intro: rtrancl3p_step_converse converse3p.intros)
qed

lemma rtrancl3p_converse_induct [consumes 1, case_names refl step]:
  assumes ih: "rtrancl3p r a bs a''"
  and refl: "\<And>a. P a [] a"
  and step: "\<And>a b a' bs a''. \<lbrakk> rtrancl3p r a' bs a''; r a b a'; P a' bs a'' \<rbrakk> \<Longrightarrow> P a (b # bs) a''"
  shows "P a bs a''"
  using ih
proof(induct bs arbitrary: a a'')
  case Nil thus ?case
    by(auto elim: rtrancl3p.cases intro: refl)
next
  case Cons thus ?case
    by(auto dest!: converse_rtrancl3p_step intro: step)
qed  

lemma rtrancl3p_converse_induct' [consumes 1, case_names refl step]:
  assumes ih: "rtrancl3p r a bs a''"
  and refl: "P a'' []"
  and step: "\<And>a b a' bs. \<lbrakk> rtrancl3p r a' bs a''; r a b a'; P a' bs \<rbrakk> \<Longrightarrow> P a (b # bs)"
  shows "P a bs"
using rtrancl3p_converse_induct[OF ih, where P="\<lambda>a bs a'. a' = a'' \<longrightarrow> P a bs"]
by(auto intro: refl step)

lemma rtrancl3p_converseE[consumes 1, case_names refl step]:
  "\<lbrakk> rtrancl3p r a bs a'';
     \<lbrakk> a = a''; bs = [] \<rbrakk> \<Longrightarrow> thesis;
     \<And>bs' b a'. \<lbrakk> bs = b # bs'; r a b a'; rtrancl3p r a' bs' a'' \<rbrakk> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
by(induct rule: rtrancl3p_converse_induct)(auto)


lemma rtrancl3p_induct' [consumes 1, case_names refl step]:
  assumes major: "rtrancl3p r a bs c"
  and refl: "P a [] a"
  and step: "\<And>bs a' b a''. \<lbrakk> rtrancl3p r a bs a'; P a bs a'; r a' b a'' \<rbrakk>
             \<Longrightarrow> P a (bs @ [b]) a''"
  shows "P a bs c"
proof -
  from major have "(P a [] a \<and> (\<forall>bs a' b a''. rtrancl3p r a bs a' \<and> P a bs a' \<and> r a' b a'' \<longrightarrow> P a (bs @ [b]) a'')) \<longrightarrow> P a bs c"
    by-(erule rtrancl3p.induct, blast+)
  with refl step show ?thesis by blast
qed



lemma list_all2_induct[consumes 1, case_names Nil Cons]:
  assumes major: "list_all2 P xs ys"
  and Nil: "Q [] []"
  and Cons: "\<And>x xs y ys. \<lbrakk> P x y; Q xs ys \<rbrakk> \<Longrightarrow> Q (x # xs) (y # ys)"
  shows "Q xs ys"
using major
by(induct xs arbitrary: ys)(auto simp add: list_all2_Cons1 Nil intro!: Cons)

lemma list_all2_split:
  assumes major: "list_all2 P xs ys"
  and split: "\<And>x y. P x y \<Longrightarrow> \<exists>z. Q x z \<and> R z y"
  shows "\<exists>zs. list_all2 Q xs zs \<and> list_all2 R zs ys"
using major
by(induct rule: list_all2_induct)(auto dest: split)

subsection {* Concatenation for @{typ String.literal} *}

definition concat :: "String.literal list \<Rightarrow> String.literal"
where [code del]: "concat xs = implode (List.concat (map explode xs))"

code_const concat
  (SML "String.concat")
  (Haskell "concat")
  (OCaml "String.concat \"\"")

hide (open) const concat

lemma map_le_SomeD: "\<lbrakk> m \<subseteq>\<^sub>m m'; m x = \<lfloor>y\<rfloor> \<rbrakk> \<Longrightarrow> m' x = \<lfloor>y\<rfloor>"
by(auto simp add: map_le_def dest: bspec)

lemma take_eq_take_le_eq:
  "\<lbrakk> take n xs = take n ys; m \<le> n \<rbrakk> \<Longrightarrow> take m xs = take m ys"
by(metis min_max.le_iff_inf take_take)

lemma take_list_update_beyond:
  "n \<le> m \<Longrightarrow> take n (xs[m := x]) = take n xs"
by(cases "n \<le> length xs")(rule nth_take_lemma, simp_all)

lemma nat_fun_sum_eq_conv:
  fixes f :: "'a \<Rightarrow> nat"
  shows "(\<lambda>a. f a + g a) = (\<lambda>a. 0) \<longleftrightarrow> f = (\<lambda>a .0) \<and> g = (\<lambda>a. 0)"
by(auto simp add: expand_fun_eq)

end
