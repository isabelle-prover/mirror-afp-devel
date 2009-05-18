(*  Title:      JinjaThreads/Common/Aux.thy
    Author:     Andreas Lochbihler, David von Oheimb, Tobias Nipkow

    Based on the Jinja theory Common/Aux.thy by David von Oheimb and Tobias Nipkow
*)

header {* 
  \isaheader{Auxiliary Definitions}
*}

theory Aux
imports FinFun
begin

(* FIXME move and possibly turn into a general simproc *)
lemma nat_add_max_le[simp]:
  "((n::nat) + max i j \<le> m) = (n + i \<le> m \<and> n + j \<le> m)"
 (*<*)by arith(*>*)

lemma Suc_add_max_le[simp]:
  "(Suc(n + max i j) \<le> m) = (Suc(n + i) \<le> m \<and> Suc(n + j) \<le> m)"
(*<*)by arith(*>*)

no_notation (xsymbols) floor  ("\<lfloor>_\<rfloor>")
notation Some ("(\<lfloor>_\<rfloor>)")

(*<*)
declare
 option.splits[split]
 Let_def[simp]
 subset_insertI2 [simp]
 Un_subset_iff[simp]
(*>*)


section {*@{text distinct_fst}*}
 
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


section {* Using @{term list_all2} for relations *}

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

lemma dom_eq_empty_conv [simp]: "dom f = {} \<longleftrightarrow> f = empty"
proof(rule iffI)
  assume "dom f = {}"
  thus "f = empty" by-(rule ext, auto)
qed(auto)

lemma Collect_eq_singleton_conv:
  "{a. P a} = {a} \<longleftrightarrow> P a \<and> (\<forall>a'. P a' \<longrightarrow> a = a')"
by(auto)

lemma dom_eq_singleton_conv: "dom f = {x} \<longleftrightarrow> (\<exists>v. f = [x \<mapsto> v])"
proof(rule iffI)
  assume "\<exists>v. f = [x \<mapsto> v]"
  thus "dom f = {x}" by(auto split: split_if_asm)
next
  assume "dom f = {x}"
  then obtain v where "f x = \<lfloor>v\<rfloor>" by auto
  hence "[x \<mapsto> v] \<subseteq>\<^sub>m f" by(auto simp add: map_le_def)
  moreover have "f \<subseteq>\<^sub>m [x \<mapsto> v]" using `dom f = {x}` `f x = \<lfloor>v\<rfloor>`
    by(auto simp add: map_le_def)
  ultimately have "f = [x \<mapsto> v]" by-(rule map_le_antisym)
  thus "\<exists>v. f = [x \<mapsto> v]" by blast
qed

lemma filter_replicate_conv:
  "filter P (replicate n x) = (if P x then replicate n x else [])"
apply(induct n)
by auto

lemma if_else_if_else_eq_if_else [simp]:
  "(if b then x else if b then y else z) = (if b then x else z)"
by(simp)

lemma disjE3: "\<lbrakk> P \<or> Q \<or> R; P \<Longrightarrow> S; Q \<Longrightarrow> S; R \<Longrightarrow> S \<rbrakk> \<Longrightarrow> S"
by auto

consts_code (* code for code generator setup *)
  "arbitrary :: nat" ("{* (0::nat) *}")
  "arbitrary :: string" ("{* ''''Arbitrary'''' *}")

lemma Plus_eq_empty_conv: "A <+> B = {} \<longleftrightarrow> A = {} \<and> B = {}"
by(auto)

lemma length_greater_Suc_0_conv: "Suc 0 < length xs \<longleftrightarrow> (\<exists>x x' xs'. xs = x # x' # xs')"
by(cases xs, auto simp add: neq_Nil_conv)

lemma zip_same_conv: "zip xs xs = map (\<lambda>x. (x, x)) xs"
by(induct xs) auto

lemma map_eq_all_nth_conv:
  "map f xs = ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>n < length xs. f (xs ! n) = ys ! n)"
apply(induct xs arbitrary: ys)
apply(fastsimp simp add: nth_Cons Suc_length_conv split: nat.splits)+
done

lemma nth_Cons_subtract: "0 < n \<Longrightarrow> (x # xs) ! n = xs ! (n - 1)"
by(auto simp add: nth_Cons split: nat.split)

lemma prod_rec_split [simp]: "prod_rec = split"
by(simp add: expand_fun_eq)

lemma update_zip: "(zip xs ys)[i := xy] = zip (xs[i := fst xy]) (ys[i := snd xy])"
  by(induct xs arbitrary: ys i)(auto,case_tac ys,auto split: nat.split)
(* generalizes update_zip in List *)


end
