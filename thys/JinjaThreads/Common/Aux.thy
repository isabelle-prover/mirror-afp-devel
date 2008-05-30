(*  Title:      JinjaThreads/Common/Aux.thy
    Author:     Andreas Lochbihler, David von Oheimb, Tobias Nipkow

    Based on the Jinja theory Common/Aux.thy by David von Oheimb and Tobias Nipkow
*)

header {* 
  \chapter{Jinja Source Language}\label{cha:j}
  \isaheader{Auxiliary Definitions}
*}

theory Aux imports Main begin
(* FIXME move and possibly turn into a general simproc *)
lemma nat_add_max_le[simp]:
  "((n::nat) + max i j \<le> m) = (n + i \<le> m \<and> n + j \<le> m)"
 (*<*)by arith(*>*)

lemma Suc_add_max_le[simp]:
  "(Suc(n + max i j) \<le> m) = (Suc(n + i) \<le> m \<and> Suc(n + j) \<le> m)"
(*<*)by arith(*>*)

(*<*)
syntax "_Some" :: "'a \<Rightarrow> 'a option" ("(\<lfloor>_\<rfloor>)")
(*>*)


translations "\<lfloor>x\<rfloor>" == "Some x"
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


end
