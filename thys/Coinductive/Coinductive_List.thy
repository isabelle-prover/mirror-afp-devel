(*  Title:      Coinductive_List.thy
    Author:     Andreas Lochbihler
*)

header {* Potentially infinite lists as greatest fixed-point *}

theory Coinductive_List
imports
  "~~/src/HOL/Library/Infinite_Set"
  "~~/src/HOL/Library/Simps_Case_Conv"
  "Coinductive_Nat"
begin

subsection {* Auxiliary lemmata *}

lemma funpow_Suc_conv [simp]: "(Suc ^^ n) m = m + n"
by(induct n arbitrary: m) simp_all

lemma wlog_linorder_le [consumes 0, case_names le symmetry]:
  assumes le: "\<And>a b :: 'a :: linorder. a \<le> b \<Longrightarrow> P a b"
  and sym: "P b a \<Longrightarrow> P a b"
  shows "P a b"
proof(cases "a \<le> b")
  case True thus ?thesis by(rule le)
next
  case False
  hence "b \<le> a" by simp
  hence "P b a" by(rule le)
  thus ?thesis by(rule sym)
qed

subsection {* Type definition *}

codatatype (lset: 'a) llist (map: lmap rel: llist_all2) =
    lnull: LNil (defaults lhd: undefined ltl: LNil)
  | LCons (lhd: 'a) (ltl: "'a llist")

text {*
  Coiterator setup.
*}

primcorec unfold_llist :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b llist" where
  "p a \<Longrightarrow> unfold_llist p g21 g22 a = LNil" |
  "_ \<Longrightarrow> unfold_llist p g21 g22 a = LCons (g21 a) (unfold_llist p g21 g22 (g22 a))"
thm unfold_llist.disc
declare
  unfold_llist.ctr(1) [simp]
  llist.corec(1) [simp]

text {*
  The following setup should be done by the BNF package.
*}

text {* congruence rule *}

declare llist.map_cong [cong]

text {* Code generator setup *}

lemma corec_llist_code [code]:
  "corec_llist IS_LNIL LHD endORmore LTL_end LTL_more b =
  (if IS_LNIL b then LNil
   else LCons (LHD b)
     (if endORmore b then LTL_end b
      else corec_llist IS_LNIL LHD endORmore LTL_end LTL_more (LTL_more b)))"
by(rule llist.expand) simp_all

lemma corec_llist_never_stop: "corec_llist IS_LNIL LHD (\<lambda>_. False) MORE LTL x = unfold_llist IS_LNIL LHD LTL x"
by(coinduction arbitrary: x) auto

text {* lemmas about generated constants *}

lemma eq_LConsD: "xs = LCons y ys \<Longrightarrow> lhd xs = y \<and> ltl xs = ys"
by auto

lemma lnull_lmap [simp]: "lnull (lmap f xs) \<longleftrightarrow> lnull xs"
by(cases xs) simp_all

lemma
  shows LNil_eq_lmap: "LNil = lmap f xs \<longleftrightarrow> xs = LNil"
  and lmap_eq_LNil: "lmap f xs = LNil \<longleftrightarrow> xs = LNil"
by(cases xs,simp_all)+

lemma [simp]:
  shows lhd_lmap: "\<not> lnull xs \<Longrightarrow> lhd (lmap f xs) = f (lhd xs)"
  and ltl_lmap: "ltl (lmap f xs) = lmap f (ltl xs)"
by(cases xs, simp_all)+

lemma lmap_ident [simp]: "lmap (\<lambda>x. x) xs = xs"
by(simp only: id_def[symmetric] llist.map_id)

lemma lmap_eq_LCons_conv:
  "lmap f xs = LCons y ys \<longleftrightarrow> 
  (\<exists>x xs'. xs = LCons x xs' \<and> y = f x \<and> ys = lmap f xs')"
by(cases xs)(auto)

lemma lmap_id: 
  "lmap id = id"
by(simp add: fun_eq_iff llist.map_id)

lemma lmap_unfold_llist:
  "lmap f (unfold_llist IS_LNIL LHD LTL b) = unfold_llist IS_LNIL (f \<circ> LHD) LTL b"
by(coinduction arbitrary: b) auto

lemma lmap_corec_llist:
  "lmap f (corec_llist IS_LNIL LHD endORmore TTL_end TTL_more b) =
   corec_llist IS_LNIL (f \<circ> LHD) endORmore (lmap f \<circ> TTL_end) TTL_more b"
by(coinduction arbitrary: b rule: llist.strong_coinduct) auto

lemma unfold_llist_ltl_unroll:
  "unfold_llist IS_LNIL LHD LTL (LTL b) = unfold_llist (IS_LNIL \<circ> LTL) (LHD \<circ> LTL) LTL b"
by(coinduction arbitrary: b) auto

lemma ltl_unfold_llist:
  "ltl (unfold_llist IS_LNIL LHD LTL a) =
  (if IS_LNIL a then LNil else unfold_llist IS_LNIL LHD LTL (LTL a))"
by(simp)

lemma unfold_llist_eq_LCons [simp]:
  "unfold_llist IS_LNIL LHD LTL b = LCons x xs \<longleftrightarrow>
  \<not> IS_LNIL b \<and> x = LHD b \<and> xs = unfold_llist IS_LNIL LHD LTL (LTL b)"
by(subst unfold_llist.code) auto

lemma unfold_llist_id [simp]: "unfold_llist lnull lhd ltl xs = xs"
by(coinduction arbitrary: xs) simp_all

lemma lset_eq_empty [simp]: "lset xs = {} \<longleftrightarrow> lnull xs"
by(cases xs) simp_all

lemma lhd_in_lset [simp]: "\<not> lnull xs \<Longrightarrow> lhd xs \<in> lset xs"
by(cases xs) auto

lemma lset_ltl: "lset (ltl xs) \<subseteq> lset xs"
by(cases xs) auto

lemma in_lset_ltlD: "x \<in> lset (ltl xs) \<Longrightarrow> x \<in> lset xs"
using lset_ltl[of xs] by auto

lemma case_llist_def':
"case_llist lnil lcons xs = (case dtor_llist xs of Inl _ \<Rightarrow> lnil | Inr (y, ys) \<Rightarrow> lcons y ys)"
apply (case_tac xs)
by auto (auto simp add: LNil_def LCons_def llist.dtor_ctor BNF_Comp.id_bnf_comp_def)

text {* induction rules *}

theorem llist_set_induct[consumes 1, case_names find step]:
  assumes "x \<in> lset xs" and "\<And>xs. \<not> lnull xs \<Longrightarrow> P (lhd xs) xs"
  and "\<And>xs y. \<lbrakk>\<not> lnull xs; y \<in> lset (ltl xs); P y (ltl xs)\<rbrakk> \<Longrightarrow> P y xs"
  shows "P x xs"
proof -
  have "\<forall>x\<in>lset xs. P x xs"
    apply(rule llist.dtor_set_induct)
    using assms
    apply(auto simp add: lhd_def ltl_def set2_pre_llist_def set1_pre_llist_def fsts_def snds_def case_llist_def' collect_def sum_set_simps sum.set_map split: sum.splits)
     apply(erule_tac x="b" in meta_allE)
     apply(erule meta_impE)
      apply(clarsimp simp add: LNil_def llist.dtor_ctor sum_set_simps lnull_def BNF_Comp.id_bnf_comp_def)
     apply(case_tac b)
     apply(simp_all add: LNil_def LCons_def llist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)[2]
    apply(rotate_tac -2)
    apply(erule_tac x="b" in meta_allE)
    apply(erule_tac x="xa" in meta_allE)
    apply(erule meta_impE)
     apply(clarsimp simp add: LNil_def llist.dtor_ctor sum_set_simps lnull_def BNF_Comp.id_bnf_comp_def)
    apply(case_tac b)
    apply(simp_all add: LNil_def LCons_def llist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)
    done
  with `x \<in> lset xs` show ?thesis by blast
qed


text {* Setup for quickcheck *}

notation fcomp (infixl "o>" 60)
notation scomp (infixl "o\<rightarrow>" 60)

definition (in term_syntax) valtermify_LNil ::
  "'a :: typerep llist \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  "valtermify_LNil = Code_Evaluation.valtermify LNil"

definition (in term_syntax) valtermify_LCons ::
  "'a :: typerep \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> 'a llist \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> 'a llist \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  "valtermify_LCons x xs = Code_Evaluation.valtermify LCons {\<cdot>} x {\<cdot>} xs"

instantiation llist :: (random) random begin

primrec random_aux_llist :: 
  "natural \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> ('a llist \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
where
  "random_aux_llist 0 j = 
   Quickcheck_Random.collapse (Random.select_weight 
     [(1, Pair valtermify_LNil)])"
| "random_aux_llist (Code_Numeral.Suc i) j =
   Quickcheck_Random.collapse (Random.select_weight
     [(Code_Numeral.Suc i, Quickcheck_Random.random j o\<rightarrow> (\<lambda>x. random_aux_llist i j o\<rightarrow> (\<lambda>xs. Pair (valtermify_LCons x xs)))),
      (1, Pair valtermify_LNil)])"
definition "Quickcheck_Random.random i = random_aux_llist i i"
instance ..
end

lemma random_aux_llist_code [code]:
  "random_aux_llist i j = Quickcheck_Random.collapse (Random.select_weight
     [(i, Quickcheck_Random.random j o\<rightarrow> (\<lambda>x. random_aux_llist (i - 1) j o\<rightarrow> (\<lambda>xs. Pair (valtermify_LCons x xs)))),
      (1, Pair valtermify_LNil)])"
  apply (cases i rule: natural.exhaust)
  apply (simp_all only: random_aux_llist.simps natural_zero_minus_one Suc_natural_minus_one)
  apply (subst select_weight_cons_zero) apply (simp only:)
  done

no_notation fcomp (infixl "o>" 60)
no_notation scomp (infixl "o\<rightarrow>" 60)

instantiation llist :: (full_exhaustive) full_exhaustive begin

fun full_exhaustive_llist 
  ::"('a llist \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "full_exhaustive_llist f i =
   (let A = Typerep.typerep TYPE('a);
        Llist = \<lambda>A. Typerep.Typerep (STR ''Coinductive_List.llist'') [A];
        fun = \<lambda>A B. Typerep.Typerep (STR ''fun'') [A, B]
    in
      if 0 < i then 
        case f (LNil, \<lambda>_. Code_Evaluation.Const (STR ''Coinductive_List.LNil'') (Llist A))
          of None \<Rightarrow> 
            Quickcheck_Exhaustive.full_exhaustive (\<lambda>(x, xt). full_exhaustive_llist (\<lambda>(xs, xst). 
              f (LCons x xs, \<lambda>_. Code_Evaluation.App (Code_Evaluation.App 
                   (Code_Evaluation.Const (STR ''Coinductive_List.LCons'') (fun A (fun (Llist A) (Llist A))))
                   (xt ())) (xst ())))
              (i - 1)) (i - 1)
      | Some ts \<Rightarrow> Some ts
    else None)"

instance ..

end

instantiation llist :: (narrowing) narrowing begin

context 
includes integer.lifting
begin

function narrowing_llist where
  "narrowing_llist n = Quickcheck_Narrowing.sum
    (Quickcheck_Narrowing.cons LNil)
    (Quickcheck_Narrowing.apply (Quickcheck_Narrowing.apply (Quickcheck_Narrowing.cons LCons) narrowing) narrowing_llist)
    n"
by pat_completeness simp
termination by(relation "measure nat_of_integer")(simp_all, transfer, simp)

instance ..
end
end

subsection {* Function definitions *}

primcorec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "lappend xs ys = (case xs of LNil \<Rightarrow> ys | LCons x xs' \<Rightarrow> LCons x (lappend xs' ys))"

primcorec iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist" 
where "iterates f x = LCons x (iterates f (f x))"

inductive lfinite :: "'a llist \<Rightarrow> bool"
where
  lfinite_LNil:  "lfinite LNil"
| lfinite_LConsI: "lfinite xs \<Longrightarrow> lfinite (LCons x xs)"

primrec llist_of :: "'a list \<Rightarrow> 'a llist"
where
  "llist_of [] = LNil"
| "llist_of (x#xs) = LCons x (llist_of xs)"

definition list_of :: "'a llist \<Rightarrow> 'a list"
where [code del]: "list_of xs = (if lfinite xs then inv llist_of xs else undefined)"

definition llength :: "'a llist \<Rightarrow> enat"
where [code del]:
  "llength = enat_unfold lnull ltl"

primcorec ltake :: "enat \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "n = 0 \<or> lnull xs \<Longrightarrow> lnull (ltake n xs)"
| "lhd (ltake n xs) = lhd xs"
| "ltl (ltake n xs) = ltake (epred n) (ltl xs)"

definition ldropn :: "nat \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where "ldropn n xs = (ltl ^^ n) xs"

primrec ldrop :: "enat \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "ldrop (enat n) xs = ldropn n xs"
| "ldrop \<infinity> xs = LNil"

primcorec ltakeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "lnull xs \<or> \<not> P (lhd xs) \<Longrightarrow> lnull (ltakeWhile P xs)"
| "lhd (ltakeWhile P xs) = lhd xs"
| "ltl (ltakeWhile P xs) = ltakeWhile P (ltl xs)"

definition ldropWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where [code del]: "ldropWhile P xs = ldrop (llength (ltakeWhile P xs)) xs"

primrec lnth :: "'a llist \<Rightarrow> nat \<Rightarrow> 'a"
where 
  "lnth xs 0 = (case xs of LNil \<Rightarrow> undefined (0 :: nat) | LCons x xs' \<Rightarrow> x)"
| "lnth xs (Suc n) = (case xs of LNil \<Rightarrow> undefined (Suc n) | LCons x xs' \<Rightarrow> lnth xs' n)"

declare lnth.simps [simp del]

primcorec lzip :: "'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a \<times> 'b) llist"
where
  "lnull xs \<or> lnull ys \<Longrightarrow> lnull (lzip xs ys)"
| "lhd (lzip xs ys) = (lhd xs, lhd ys)"
| "ltl (lzip xs ys) = lzip (ltl xs) (ltl ys)"

definition llast :: "'a llist \<Rightarrow> 'a"
where [nitpick_simp]:
  "llast xs = (case llength xs of enat n \<Rightarrow> (case n of 0 \<Rightarrow> undefined | Suc n' \<Rightarrow> lnth xs n') | \<infinity> \<Rightarrow> undefined)"

coinductive ldistinct :: "'a llist \<Rightarrow> bool"
where 
  LNil [simp]: "ldistinct LNil"
| LCons: "\<lbrakk> x \<notin> lset xs; ldistinct xs \<rbrakk> \<Longrightarrow> ldistinct (LCons x xs)"

hide_fact (open) LNil LCons

definition inf_llist :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a llist"
where [code del]: "inf_llist f = lmap f (iterates Suc 0)"

abbreviation repeat :: "'a \<Rightarrow> 'a llist"
where "repeat \<equiv> iterates (\<lambda>x. x)"

definition lprefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
where [code del]: "lprefix xs ys \<equiv> \<exists>zs. lappend xs zs = ys"

definition lstrict_prefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
where [code del]: "lstrict_prefix xs ys \<equiv> lprefix xs ys \<and> xs \<noteq> ys"

text {* longest common prefix *}
definition llcp :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> enat"
where [code del]:
  "llcp xs ys = 
   enat_unfold (\<lambda>(xs, ys). lnull xs \<or> lnull ys \<or> lhd xs \<noteq> lhd ys) (map_prod ltl ltl) (xs, ys)"

coinductive llexord :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  llexord_LCons_eq: "llexord r xs ys \<Longrightarrow> llexord r (LCons x xs) (LCons x ys)"
| llexord_LCons_less: "r x y \<Longrightarrow> llexord r (LCons x xs) (LCons y ys)"
| llexord_LNil [simp, intro!]: "llexord r LNil ys"

primcorec lfilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "lfilter P xs = 
  (case ldropWhile (Not \<circ> P) xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> LCons x (lfilter P xs'))"

definition lconcat :: "'a llist llist \<Rightarrow> 'a llist"
where [code del]:
  "lconcat xs =
   unfold_llist lnull (lhd \<circ> lhd)
     (\<lambda>xs. if lnull (ltl (lhd xs)) then ltl xs else LCons (ltl (lhd xs)) (ltl xs))
     (lfilter (\<lambda>xs. \<not> lnull xs) xs)"

definition lsublist :: "'a llist \<Rightarrow> nat set \<Rightarrow> 'a llist"
where "lsublist xs A = lmap fst (lfilter (\<lambda>(x, y). y \<in> A) (lzip xs (iterates Suc 0)))"

definition (in monoid_add) llistsum :: "'a llist \<Rightarrow> 'a"
where "llistsum xs = (if lfinite xs then listsum (list_of xs) else 0)"






subsection {* Properties of predefined functions *}

lemmas lhd_LCons = llist.sel(1)
lemmas ltl_simps = llist.sel(2,3)

lemmas lhd_LCons_ltl = llist.collapse(2)

lemma lnull_ltlI [simp]: "lnull xs \<Longrightarrow> lnull (ltl xs)"
unfolding lnull_def by simp

lemma neq_LNil_conv: "xs \<noteq> LNil \<longleftrightarrow> (\<exists>x xs'. xs = LCons x xs')"
by(cases xs) auto

lemma not_lnull_conv: "\<not> lnull xs \<longleftrightarrow> (\<exists>x xs'. xs = LCons x xs')"
unfolding lnull_def by(simp add: neq_LNil_conv)

lemma lset_LCons:
  "lset (LCons x xs) = insert x (lset xs)"
by simp

lemma lset_intros:
  "x \<in> lset (LCons x xs)"
  "x \<in> lset xs \<Longrightarrow> x \<in> lset (LCons x' xs)"
by simp_all

lemma lset_cases [elim?]:
  assumes "x \<in> lset xs"
  obtains xs' where "xs = LCons x xs'"
  | x' xs' where "xs = LCons x' xs'" "x \<in> lset xs'"
using assms by(cases xs) auto

lemma lset_induct' [consumes 1, case_names find step]:
  assumes major: "x \<in> lset xs"
  and 1: "\<And>xs. P (LCons x xs)"
  and 2: "\<And>x' xs. \<lbrakk> x \<in> lset xs; P xs \<rbrakk> \<Longrightarrow> P (LCons x' xs)"
  shows "P xs"
using major apply(induct y\<equiv>"x" xs rule: llist_set_induct)
using 1 2 by(auto simp add: not_lnull_conv)

lemma lset_induct [consumes 1, case_names find step, induct set: lset]:
  assumes major: "x \<in> lset xs"
  and find: "\<And>xs. P (LCons x xs)"
  and step: "\<And>x' xs. \<lbrakk> x \<in> lset xs; x \<noteq> x'; P xs \<rbrakk> \<Longrightarrow> P (LCons x' xs)"
  shows "P xs"
using major
apply(induct rule: lset_induct')
 apply(rule find)
apply(case_tac "x'=x")
apply(simp_all add: find step)
done

lemmas lset_LNil = llist.set(1)

lemma lset_lnull: "lnull xs \<Longrightarrow> lset xs = {}"
by(auto dest: llist.collapse)

text {* Alternative definition of @{term lset} for nitpick *}

inductive lsetp :: "'a llist \<Rightarrow> 'a \<Rightarrow> bool"
where
  "lsetp (LCons x xs) x"
| "lsetp xs x \<Longrightarrow> lsetp (LCons x' xs) x"

lemma lset_into_lsetp:
  "x \<in> lset xs \<Longrightarrow> lsetp xs x"
by(induct rule: lset_induct)(blast intro: lsetp.intros)+

lemma lsetp_into_lset:
  "lsetp xs x \<Longrightarrow> x \<in> lset xs"
by(induct rule: lsetp.induct)(blast intro: lset_intros)+

lemma lset_eq_lsetp [nitpick_unfold]:
  "lset xs = {x. lsetp xs x}"
by(auto intro: lset_into_lsetp dest: lsetp_into_lset)

hide_const (open) lsetp
hide_fact (open) lsetp.intros lsetp_def lsetp.cases lsetp.induct lset_into_lsetp lset_eq_lsetp

text {* code setup for @{term lset} *}

definition gen_lset :: "'a set \<Rightarrow> 'a llist \<Rightarrow> 'a set"
where "gen_lset A xs = A \<union> lset xs"

lemma gen_lset_code [code]:
  "gen_lset A LNil = A"
  "gen_lset A (LCons x xs) = gen_lset (insert x A) xs"
by(auto simp add: gen_lset_def)

lemma lset_code [code]:
  "lset = gen_lset {}"
by(simp add: gen_lset_def fun_eq_iff)

definition lmember :: "'a \<Rightarrow> 'a llist \<Rightarrow> bool"
where "lmember x xs \<longleftrightarrow> x \<in> lset xs"

lemma lmember_code [code]:
  "lmember x LNil \<longleftrightarrow> False"
  "lmember x (LCons y ys) \<longleftrightarrow> x = y \<or> lmember x ys"
by(simp_all add: lmember_def)

lemma lset_lmember [code_unfold]:
  "x \<in> lset xs \<longleftrightarrow> lmember x xs"
by(simp add: lmember_def)

lemmas lset_lmap [simp] = llist.set_map





subsection {* The subset of finite lazy lists @{term "lfinite"} *}

declare lfinite_LNil [iff]

lemma lnull_imp_lfinite [simp]: "lnull xs \<Longrightarrow> lfinite xs"
by(auto dest: llist.collapse)

lemma lfinite_LCons [simp]: "lfinite (LCons x xs) = lfinite xs"
by(auto elim: lfinite.cases intro: lfinite_LConsI)

lemma lfinite_ltl [simp]: "lfinite (ltl xs) = lfinite xs"
by(cases xs) simp_all

lemma lfinite_code [code]:
  "lfinite LNil = True"
  "lfinite (LCons x xs) = lfinite xs"
by simp_all

lemma lfinite_induct [consumes 1, case_names LNil LCons]:
  assumes lfinite: "lfinite xs"
  and LNil: "\<And>xs. lnull xs \<Longrightarrow> P xs"
  and LCons: "\<And>xs. \<lbrakk> lfinite xs; \<not> lnull xs; P (ltl xs) \<rbrakk> \<Longrightarrow> P xs"
  shows "P xs"
using lfinite by(induct)(auto intro: LCons LNil)

lemma lfinite_imp_finite_lset:
  assumes "lfinite xs"
  shows "finite (lset xs)"
using assms by induct auto

subsection {* @{term "lappend"} *}

simps_of_case lappend_code [code, simp, nitpick_simp]: lappend.code

lemmas lappend_LNil_LNil = lappend_code(1)[where ys = LNil]

lemma lappend_simps [simp]:
  shows lhd_lappend: "lhd (lappend xs ys) = (if lnull xs then lhd ys else lhd xs)"
  and ltl_lappend: "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"
by(case_tac [!] xs) simp_all

lemma lnull_lappend [simp]:
  "lnull (lappend xs ys) \<longleftrightarrow> lnull xs \<and> lnull ys"
by(auto simp add: lappend_def)

lemma lappend_eq_LNil_iff:
  "lappend xs ys = LNil \<longleftrightarrow> xs = LNil \<and> ys = LNil"
using lnull_lappend unfolding lnull_def .

lemma LNil_eq_lappend_iff:
  "LNil = lappend xs ys \<longleftrightarrow> xs = LNil \<and> ys = LNil"
by(auto dest: sym simp add: lappend_eq_LNil_iff)

lemma lappend_LNil2 [simp]: "lappend xs LNil = xs"
by(coinduction arbitrary: xs) simp_all

lemma shows lappend_lnull1: "lnull xs \<Longrightarrow> lappend xs ys = ys"
  and lappend_lnull2: "lnull ys \<Longrightarrow> lappend xs ys = xs"
unfolding lnull_def by simp_all

lemma lappend_assoc: "lappend (lappend xs ys) zs = lappend xs (lappend ys zs)"
by(coinduction arbitrary: xs rule: llist.strong_coinduct) auto

lemma lmap_lappend_distrib: 
  "lmap f (lappend xs ys) = lappend (lmap f xs) (lmap f ys)"
by(coinduction arbitrary: xs rule: llist.strong_coinduct) auto

lemma lappend_snocL1_conv_LCons2: 
  "lappend (lappend xs (LCons y LNil)) ys = lappend xs (LCons y ys)"
by(simp add: lappend_assoc)

lemma lappend_ltl: "\<not> lnull xs \<Longrightarrow> lappend (ltl xs) ys = ltl (lappend xs ys)"
by simp

lemma lfinite_lappend [simp]:
  "lfinite (lappend xs ys) \<longleftrightarrow> lfinite xs \<and> lfinite ys"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
  proof(induct zs\<equiv>"lappend xs ys" arbitrary: xs ys)
    case lfinite_LNil
    thus ?case by(simp add: LNil_eq_lappend_iff)
  next
    case (lfinite_LConsI zs z)
    thus ?case by(cases xs)(cases ys, simp_all)
  qed
next
  assume ?rhs (is "?xs \<and> ?ys")
  then obtain ?xs ?ys ..
  thus ?lhs by induct simp_all
qed

lemma lappend_inf: "\<not> lfinite xs \<Longrightarrow> lappend xs ys = xs"
by(coinduction arbitrary: xs) auto

lemma lfinite_lmap [simp]:
  "lfinite (lmap f xs) = lfinite xs"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by(induct zs\<equiv>"lmap f xs" arbitrary: xs rule: lfinite_induct) fastforce+
next
  assume ?rhs 
  thus ?lhs by(induct) simp_all
qed

lemma lset_lappend_lfinite [simp]:
  "lfinite xs \<Longrightarrow> lset (lappend xs ys) = lset xs \<union> lset ys"
by(induct rule: lfinite.induct) auto

lemma lset_lappend: "lset (lappend xs ys) \<subseteq> lset xs \<union> lset ys"
proof(cases "lfinite xs")
  case True
  thus ?thesis by simp
next
  case False
  thus ?thesis by(auto simp add: lappend_inf) 
qed

lemma lset_lappend1: "lset xs \<subseteq> lset (lappend xs ys)"
by(rule subsetI)(erule lset_induct, simp_all)

lemma lset_lappend_conv: "lset (lappend xs ys) = (if lfinite xs then lset xs \<union> lset ys else lset xs)"
by(simp add: lappend_inf)

lemma in_lset_lappend_iff: "x \<in> lset (lappend xs ys) \<longleftrightarrow> x \<in> lset xs \<or> lfinite xs \<and> x \<in> lset ys"
by(simp add: lset_lappend_conv)

lemma split_llist_first:
  assumes "x \<in> lset xs"
  shows "\<exists>ys zs. xs = lappend ys (LCons x zs) \<and> lfinite ys \<and> x \<notin> lset ys"
using assms
proof(induct)
  case find thus ?case by(auto intro: exI[where x=LNil])
next
  case step thus ?case by(fastforce intro: exI[where x="LCons a b" for a b])
qed

lemma split_llist: "x \<in> lset xs \<Longrightarrow> \<exists>ys zs. xs = lappend ys (LCons x zs) \<and> lfinite ys"
by(blast dest: split_llist_first)

subsection {* Converting ordinary lists to lazy lists: @{term "llist_of"} *}

lemma lhd_llist_of [simp]: "lhd (llist_of xs) = hd xs"
by(cases xs)(simp_all add: hd_def lhd_def)

lemma ltl_llist_of [simp]: "ltl (llist_of xs) = llist_of (tl xs)"
by(cases xs) simp_all

lemma lfinite_llist_of [simp]: "lfinite (llist_of xs)"
by(induct xs) auto

lemma lfinite_eq_range_llist_of: "lfinite xs \<longleftrightarrow> xs \<in> range llist_of"
proof
  assume "lfinite xs"
  thus "xs \<in> range llist_of"
    by(induct rule: lfinite.induct)(auto intro: llist_of.simps[symmetric])
next
  assume "xs \<in> range llist_of"
  thus "lfinite xs" by(auto intro: lfinite_llist_of)
qed

lemma lnull_llist_of [simp]: "lnull (llist_of xs) \<longleftrightarrow> xs = []"
by(cases xs) simp_all

lemma llist_of_eq_LNil_conv:
  "llist_of xs = LNil \<longleftrightarrow> xs = []"
by(cases xs) simp_all

lemma llist_of_eq_LCons_conv:
  "llist_of xs = LCons y ys \<longleftrightarrow> (\<exists>xs'. xs = y # xs' \<and> ys = llist_of xs')"
by(cases xs) auto

lemma lappend_llist_of_llist_of:
  "lappend (llist_of xs) (llist_of ys) = llist_of (xs @ ys)"
by(induct xs) simp_all

lemma lfinite_rev_induct [consumes 1, case_names Nil snoc]:
  assumes fin: "lfinite xs"
  and Nil: "P LNil"
  and snoc: "\<And>x xs. \<lbrakk> lfinite xs; P xs \<rbrakk> \<Longrightarrow> P (lappend xs (LCons x LNil))"
  shows "P xs"
proof -
  from fin obtain xs' where xs: "xs = llist_of xs'"
    unfolding lfinite_eq_range_llist_of by blast
  show ?thesis unfolding xs
    by(induct xs' rule: rev_induct)(auto simp add: Nil lappend_llist_of_llist_of[symmetric] dest: snoc[rotated])
qed

lemma lappend_llist_of_LCons: 
  "lappend (llist_of xs) (LCons y ys) = lappend (llist_of (xs @ [y])) ys"
by(induct xs) simp_all

lemma lmap_llist_of [simp]:
  "lmap f (llist_of xs) = llist_of (map f xs)"
by(induct xs) simp_all

lemma lset_llist_of [simp]: "lset (llist_of xs) = set xs"
by(induct xs) simp_all

lemma llist_of_inject [simp]: "llist_of xs = llist_of ys \<longleftrightarrow> xs = ys"
proof
  assume "llist_of xs = llist_of ys"
  thus "xs = ys"
  proof(induct xs arbitrary: ys)
    case Nil thus ?case by(cases ys) auto
  next
    case Cons thus ?case by(cases ys) auto
  qed
qed simp

lemma inj_llist_of [simp]: "inj llist_of"
by(rule inj_onI) simp

subsection {* Converting finite lazy lists to ordinary lists: @{term "list_of"} *}

lemma list_of_llist_of [simp]: "list_of (llist_of xs) = xs"
by(fastforce simp add: list_of_def intro: inv_f_f inj_onI)

lemma llist_of_list_of [simp]: "lfinite xs \<Longrightarrow> llist_of (list_of xs) = xs"
unfolding lfinite_eq_range_llist_of by auto

lemma list_of_LNil [simp, nitpick_simp]: "list_of LNil = []"
using list_of_llist_of[of "[]"] by simp

lemma list_of_LCons [simp]: "lfinite xs \<Longrightarrow> list_of (LCons x xs) = x # list_of xs"
proof(induct arbitrary: x rule: lfinite.induct)
  case lfinite_LNil
  show ?case using list_of_llist_of[of "[x]"] by simp
next
  case (lfinite_LConsI xs' x')
  from `list_of (LCons x' xs') = x' # list_of xs'` show ?case
    using list_of_llist_of[of "x # x' # list_of xs'"]
      llist_of_list_of[OF `lfinite xs'`] by simp
qed

lemma list_of_LCons_conv [nitpick_simp]:
  "list_of (LCons x xs) = (if lfinite xs then x # list_of xs else undefined)"
by(auto)(auto simp add: list_of_def)

lemma list_of_lappend:
  assumes "lfinite xs" "lfinite ys"
  shows "list_of (lappend xs ys) = list_of xs @ list_of ys"
using `lfinite xs` by induct(simp_all add: `lfinite ys`)

lemma list_of_lmap [simp]: 
  assumes "lfinite xs"
  shows "list_of (lmap f xs) = map f (list_of xs)"
using assms by induct simp_all

lemma set_list_of [simp]:
  assumes "lfinite xs"
  shows "set (list_of xs) = lset xs"
using assms by(induct)(simp_all)

lemma hd_list_of [simp]: "lfinite xs \<Longrightarrow> hd (list_of xs) = lhd xs"
by(clarsimp simp add: lfinite_eq_range_llist_of)

lemma tl_list_of: "lfinite xs \<Longrightarrow> tl (list_of xs) = list_of (ltl xs)"
by(auto simp add: lfinite_eq_range_llist_of)

text {* Efficient implementation via tail recursion suggested by Brian Huffman *}

definition list_of_aux :: "'a list \<Rightarrow> 'a llist \<Rightarrow> 'a list"
where "list_of_aux xs ys = (if lfinite ys then rev xs @ list_of ys else undefined)"

lemma list_of_code [code]: "list_of = list_of_aux []"
by(simp add: fun_eq_iff list_of_def list_of_aux_def)

lemma list_of_aux_code [code]:
  "list_of_aux xs LNil = rev xs"
  "list_of_aux xs (LCons y ys) = list_of_aux (y # xs) ys"
by(simp_all add: list_of_aux_def)

subsection {* The length of a lazy list: @{term "llength"} *}

lemma [simp, nitpick_simp]:
  shows llength_LNil: "llength LNil = 0"
  and llength_LCons: "llength (LCons x xs) = eSuc (llength xs)"
by(simp_all add: llength_def enat_unfold)

lemma llength_eq_0 [simp]: "llength xs = 0 \<longleftrightarrow> lnull xs"
by(cases xs) simp_all

lemma llength_lnull [simp]: "lnull xs \<Longrightarrow> llength xs = 0"
by simp

lemma epred_llength:
  "epred (llength xs) = llength (ltl xs)"
by(cases xs) simp_all

lemmas llength_ltl = epred_llength[symmetric]

lemma llength_lmap [simp]: "llength (lmap f xs) = llength xs"
by(coinduction arbitrary: xs rule: enat_coinduct)(auto simp add: epred_llength)

lemma llength_lappend [simp]: "llength (lappend xs ys) = llength xs + llength ys"
by(coinduction arbitrary: xs ys rule: enat_coinduct)(simp_all add: iadd_is_0 epred_iadd1 split_paired_all epred_llength, auto)

lemma llength_llist_of [simp]:
  "llength (llist_of xs) = enat (length xs)"
by(induct xs)(simp_all add: zero_enat_def eSuc_def)

lemma length_list_of:
  "lfinite xs \<Longrightarrow> enat (length (list_of xs)) = llength xs"
apply(rule sym)
by(induct rule: lfinite.induct)(auto simp add: eSuc_enat zero_enat_def)

lemma length_list_of_conv_the_enat:
  "lfinite xs \<Longrightarrow> length (list_of xs) = the_enat (llength xs)"
unfolding lfinite_eq_range_llist_of by auto

lemma llength_eq_enat_lfiniteD: "llength xs = enat n \<Longrightarrow> lfinite xs"
proof(induct n arbitrary: xs)
  case 0[folded zero_enat_def]
  thus ?case by simp
next
  case (Suc n)
  note len = `llength xs = enat (Suc n)`
  then obtain x xs' where "xs = LCons x xs'"
    by(cases xs)(auto simp add: zero_enat_def)
  moreover with len have "llength xs' = enat n"
    by(simp add: eSuc_def split: enat.split_asm)
  hence "lfinite xs'" by(rule Suc)
  ultimately show ?case by simp
qed

lemma lfinite_llength_enat:
  assumes "lfinite xs"
  shows "\<exists>n. llength xs = enat n"
using assms
by induct(auto simp add: eSuc_def zero_enat_def)

lemma lfinite_conv_llength_enat:
  "lfinite xs \<longleftrightarrow> (\<exists>n. llength xs = enat n)"
by(blast dest: llength_eq_enat_lfiniteD lfinite_llength_enat)

lemma not_lfinite_llength:
  "\<not> lfinite xs \<Longrightarrow> llength xs = \<infinity>"
by(simp add: lfinite_conv_llength_enat)

lemma llength_eq_infty_conv_lfinite:
  "llength xs = \<infinity> \<longleftrightarrow> \<not> lfinite xs"
by(simp add: lfinite_conv_llength_enat)

lemma lfinite_finite_index: "lfinite xs \<Longrightarrow> finite {n. enat n < llength xs}"
by(auto dest: lfinite_llength_enat)

text {* tail-recursive implementation for @{term llength} *}

definition gen_llength :: "nat \<Rightarrow> 'a llist \<Rightarrow> enat"
where "gen_llength n xs = enat n + llength xs"

lemma gen_llength_code [code]:
  "gen_llength n LNil = enat n"
  "gen_llength n (LCons x xs) = gen_llength (n + 1) xs"
by(simp_all add: gen_llength_def iadd_Suc eSuc_enat[symmetric] iadd_Suc_right)

lemma llength_code [code]: "llength = gen_llength 0"
by(simp add: gen_llength_def fun_eq_iff zero_enat_def)

subsection {* Taking and dropping from lazy lists: @{term "ltake"} and @{term "ldrop"} *}

lemma ltake_LNil [simp, code, nitpick_simp]: "ltake n LNil = LNil"
by simp

lemma ltake_0 [simp]: "ltake 0 xs = LNil"
by(simp add: ltake_def)

lemma ltake_eSuc_LCons [simp]: 
  "ltake (eSuc n) (LCons x xs) = LCons x (ltake n xs)"
by(rule llist.expand)(simp_all)

lemma ltake_eSuc:
  "ltake (eSuc n) xs =
  (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> LCons x (ltake n xs'))"
by(cases xs) simp_all

lemma lnull_ltake [simp]: "lnull (ltake n xs) \<longleftrightarrow> lnull xs \<or> n = 0"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemma ltake_eq_LNil_iff: "ltake n xs = LNil \<longleftrightarrow> xs = LNil \<or> n = 0"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemma LNil_eq_ltake_iff [simp]: "LNil = ltake n xs \<longleftrightarrow> xs = LNil \<or> n = 0"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemma ltake_LCons [code, nitpick_simp]:
  "ltake n (LCons x xs) =
  (case n of 0 \<Rightarrow> LNil | eSuc n' \<Rightarrow> LCons x (ltake n' xs))"
by(rule llist.expand)(simp_all split: co.enat.split)

lemma lhd_ltake [simp]: "n \<noteq> 0 \<Longrightarrow> lhd (ltake n xs) = lhd xs"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemma ltl_ltake: "ltl (ltake n xs) = ltake (epred n) (ltl xs)"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemmas ltake_epred_ltl = ltl_ltake [symmetric]

lemma ltake_ltl: "ltake n (ltl xs) = ltl (ltake (eSuc n) xs)"
by(cases xs) simp_all

lemma llength_ltake [simp]: "llength (ltake n xs) = min n (llength xs)"
by(coinduction arbitrary: n xs rule: enat_coinduct)(auto 4 3 simp add: enat_min_eq_0_iff epred_llength ltl_ltake)

lemma ltake_lmap [simp]: "ltake n (lmap f xs) = lmap f (ltake n xs)"
by(coinduction arbitrary: n xs)(auto 4 3 simp add: ltl_ltake)

lemma ltake_ltake [simp]: "ltake n (ltake m xs) = ltake (min n m) xs"
by(coinduction arbitrary: n m xs)(auto 4 4 simp add: enat_min_eq_0_iff ltl_ltake)

lemma lset_ltake: "lset (ltake n xs) \<subseteq> lset xs"
proof(rule subsetI)
  fix x
  assume "x \<in> lset (ltake n xs)"
  thus "x \<in> lset xs"
  proof(induct "ltake n xs" arbitrary: xs n rule: lset_induct)
    case find thus ?case 
      by(cases xs)(simp, cases n rule: enat_coexhaust, simp_all)
  next
    case step thus ?case
      by(cases xs)(simp, cases n rule: enat_coexhaust, simp_all)
  qed
qed

lemma ltake_all: "llength xs \<le> m \<Longrightarrow> ltake m xs = xs"
by(coinduction arbitrary: m xs)(auto simp add: epred_llength[symmetric] ltl_ltake intro: epred_le_epredI)

lemma ltake_llist_of [simp]:
  "ltake (enat n) (llist_of xs) = llist_of (take n xs)"
proof(induct n arbitrary: xs)
  case 0
  thus ?case unfolding zero_enat_def[symmetric]
    by(cases xs) simp_all
next
  case (Suc n)
  thus ?case unfolding eSuc_enat[symmetric]
    by(cases xs) simp_all
qed

lemma lfinite_ltake [simp]:
  "lfinite (ltake n xs) \<longleftrightarrow> lfinite xs \<or> n < \<infinity>"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by(induct ys\<equiv>"ltake n xs" arbitrary: n xs rule: lfinite_induct)(fastforce simp add: zero_enat_def ltl_ltake)+
next
  assume ?rhs (is "?xs \<or> ?n")
  thus ?lhs
  proof
    assume ?xs thus ?thesis
      by(induct xs arbitrary: n)(simp_all add: ltake_LCons split: enat_cosplit)
  next
    assume ?n
    then obtain n' where "n = enat n'" by auto
    moreover have "lfinite (ltake (enat n') xs)"
      by(induct n' arbitrary: xs)
        (auto simp add: zero_enat_def[symmetric] eSuc_enat[symmetric] ltake_eSuc
              split: llist.split)
    ultimately show ?thesis by simp
  qed
qed

lemma ltake_lappend1:  "n \<le> llength xs \<Longrightarrow> ltake n (lappend xs ys) = ltake n xs"
by(coinduction arbitrary: n xs)(auto intro!: exI simp add: llength_ltl epred_le_epredI ltl_ltake)

lemma ltake_lappend2: 
  "llength xs \<le> n \<Longrightarrow> ltake n (lappend xs ys) = lappend xs (ltake (n - llength xs) ys)"
by(coinduction arbitrary: n xs rule: llist.strong_coinduct)(auto intro!: exI simp add: llength_ltl epred_le_epredI ltl_ltake)

lemma ltake_lappend:
  "ltake n (lappend xs ys) = lappend (ltake n xs) (ltake (n - llength xs) ys)"
by(coinduction arbitrary: n xs ys rule: llist.strong_coinduct)(auto intro!: exI simp add: llength_ltl ltl_ltake)

lemma take_list_of:
  assumes "lfinite xs"
  shows "take n (list_of xs) = list_of (ltake (enat n) xs)"
using assms
by(induct arbitrary: n)
  (simp_all add: take_Cons zero_enat_def[symmetric] eSuc_enat[symmetric] split: nat.split)

lemma ltake_eq_ltake_antimono:
  "\<lbrakk> ltake n xs = ltake n ys; m \<le> n \<rbrakk> \<Longrightarrow> ltake m xs = ltake m ys"
by (metis ltake_ltake min.absorb1)

lemma ldropn_0 [simp]: "ldropn 0 xs = xs"
by(simp add: ldropn_def)

lemma ldropn_LNil [code, simp]: "ldropn n LNil = LNil"
by(induct n)(simp_all add: ldropn_def)

lemma ldropn_LCons [code]: 
  "ldropn n (LCons x xs) = (case n of 0 \<Rightarrow> LCons x xs | Suc n' \<Rightarrow> ldropn n' xs)"
by(cases n)(simp_all add: ldropn_def funpow_swap1)

lemma ldropn_Suc: "ldropn (Suc n) xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> ldropn n xs')"
by(simp split: llist.split)(simp add: ldropn_def funpow_swap1)

lemma ldrop_LNil [simp]: "ldrop n LNil = LNil"
by(cases n)(simp_all add: ldropn_Suc)

lemma ldropn_Suc_LCons [simp]: "ldropn (Suc n) (LCons x xs) = ldropn n xs"
by(simp add: ldropn_LCons)

lemma ltl_ldropn: "ltl (ldropn n xs) = ldropn n (ltl xs)"
proof(induct n arbitrary: xs)
  case 0 thus ?case by simp
next
  case (Suc n)
  thus ?case
    by(cases xs)(simp_all add: ldropn_Suc split: llist.split)
qed

lemma ltl_ldrop: "ltl (ldrop n xs) = ldrop n (ltl xs)"
by(cases n)(simp_all add: ltl_ldropn)

lemma ldrop_0 [simp]: "ldrop 0 xs = xs"
by(simp add: zero_enat_def)

lemma ldrop_eSuc_LCons [simp]: "ldrop (eSuc n) (LCons x xs) = ldrop n xs"
by(simp add: eSuc_def ldropn_Suc split: enat.split)

lemma ldrop_eSuc:
  "ldrop (eSuc n) xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> ldrop n xs')"
by(cases xs) simp_all

lemma ldrop_LCons:
  "ldrop n (LCons x xs) = (case n of 0 \<Rightarrow> LCons x xs | eSuc n' \<Rightarrow> ldrop n' xs)"
by(cases n rule: enat_coexhaust) simp_all

lemma lfinite_ldropn [simp]: "lfinite (ldropn n xs) = lfinite xs"
by(induct n arbitrary: xs)(simp_all add: ldropn_Suc split: llist.split)

lemma lfinite_ldrop [simp]:
  "lfinite (ldrop n xs) \<longleftrightarrow> lfinite xs \<or> n = \<infinity>"
by(cases n) simp_all

lemma ldropn_ltl: "ldropn n (ltl xs) = ldropn (Suc n) xs"
by(simp add: ldropn_def funpow_swap1)

lemmas ldrop_eSuc_ltl = ldropn_ltl[symmetric]

lemma ldrop_ltl: "ldrop n (ltl xs) = ldrop (eSuc n) xs"
by(cases n)(simp_all add: ldropn_ltl eSuc_enat)

lemma lnull_ldropn [simp]: "lnull (ldropn n xs) \<longleftrightarrow> llength xs \<le> enat n"
proof(induction n arbitrary: xs)
  case (Suc n)
  from Suc.IH[of "ltl xs"] show ?case
    by(cases xs)(simp_all add: eSuc_enat[symmetric])
qed(simp add: zero_enat_def[symmetric])

lemma lnull_ldrop [simp]: "lnull (ldrop n xs) \<longleftrightarrow> llength xs \<le> n"
by(cases n) simp_all

lemma ldropn_eq_LNil: "(ldropn n xs = LNil) = (llength xs \<le> enat n)"
using lnull_ldropn unfolding lnull_def .

lemma ldrop_eq_LNil [simp]: "ldrop n xs = LNil \<longleftrightarrow> llength xs \<le> n"
using lnull_ldrop unfolding lnull_def .

lemma ldropn_all: "llength xs \<le> enat m \<Longrightarrow> ldropn m xs = LNil"
by(simp add: ldropn_eq_LNil)

lemma ldrop_all: "llength xs \<le> m \<Longrightarrow> ldrop m xs = LNil"
by(simp)

lemma lset_ldropn_subset: "lset (ldropn n xs) \<subseteq> lset xs"
by(induct n arbitrary: xs)(fastforce simp add: ldropn_Suc split: llist.split_asm)+

lemma in_lset_ldropnD: "x \<in> lset (ldropn n xs) \<Longrightarrow> x \<in> lset xs"
using lset_ldropn_subset[of n xs] by auto

lemma lset_ldrop_subset: "lset (ldrop n xs) \<subseteq> lset xs"
by(cases n)(auto dest: in_lset_ldropnD)

lemma in_lset_ldropD: "x \<in> lset (ldrop n xs) \<Longrightarrow> x \<in> lset xs"
using lset_ldrop_subset[of n xs] by(auto)

lemma lappend_ltake_ldrop: "lappend (ltake n xs) (ldrop n xs) = xs"
by(coinduction arbitrary: n xs rule: llist.strong_coinduct)
  (auto simp add: ldrop_ltl ltl_ltake intro!: arg_cong2[where f=lappend])

lemma ldropn_lappend:
  "ldropn n (lappend xs ys) =
  (if enat n < llength xs then lappend (ldropn n xs) ys
   else ldropn (n - the_enat (llength xs)) ys)"
proof(induct n arbitrary: xs)
  case 0
  thus ?case by(simp add: zero_enat_def[symmetric] lappend_lnull1)
next
  case (Suc n)
  { fix zs
    assume "llength zs \<le> enat n"
    hence "the_enat (eSuc (llength zs)) = Suc (the_enat (llength zs))"
      by(auto intro!: the_enat_eSuc iff del: not_infinity_eq) }
  note eq = this
  from Suc show ?case
    by(cases xs)(auto simp add: not_less not_le eSuc_enat[symmetric] eq)
qed

lemma ldropn_lappend2:
  "llength xs \<le> enat n \<Longrightarrow> ldropn n (lappend xs ys) = ldropn (n - the_enat (llength xs)) ys"
by(auto simp add: ldropn_lappend)

lemma lappend_ltake_enat_ldropn [simp]: "lappend (ltake (enat n) xs) (ldropn n xs) = xs"
by(fold ldrop.simps)(rule lappend_ltake_ldrop)

lemma ldrop_lappend:
  "ldrop n (lappend xs ys) =
  (if n < llength xs then lappend (ldrop n xs) ys
   else ldrop (n - llength xs) ys)"
by(cases n)(cases "llength xs", simp_all add: ldropn_lappend not_less)

lemma ltake_is_lprefix [simp, intro]:
  "lprefix (ltake n xs) xs"
unfolding lprefix_def
by(rule exI)(rule lappend_ltake_ldrop)

lemma ltake_plus_conv_lappend:
  "ltake (n + m) xs = lappend (ltake n xs) (ltake m (ldrop n xs))"
by(coinduction arbitrary: n m xs rule: llist.strong_coinduct)(auto intro!: exI simp add: iadd_is_0 ltl_ltake epred_iadd1 ldrop_ltl)

lemma ldropn_eq_LConsD:
  "ldropn n xs = LCons y ys \<Longrightarrow> enat n < llength xs"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n) thus ?case by(cases xs)(simp_all add: Suc_ile_eq)
qed

lemma ldrop_eq_LConsD:
  "ldrop n xs = LCons y ys \<Longrightarrow> n < llength xs"
by(cases n)(auto dest: ldropn_eq_LConsD)

lemma ldropn_lmap [simp]: "ldropn n (lmap f xs) = lmap f (ldropn n xs)"
by(induct n arbitrary: xs)(simp_all add: ldropn_Suc split: llist.split)

lemma ldrop_lmap [simp]: "ldrop n (lmap f xs) = lmap f (ldrop n xs)"
by(cases n)(simp_all)

lemma ldropn_ldropn [simp]: 
  "ldropn n (ldropn m xs) = ldropn (n + m) xs"
by(induct m arbitrary: xs)(auto simp add: ldropn_Suc split: llist.split)

lemma ldrop_ldrop [simp]: 
  "ldrop n (ldrop m xs) = ldrop (n + m) xs"
by(cases n,cases m) simp_all

lemma llength_ldropn [simp]: "llength (ldropn n xs) = llength xs - enat n"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n) thus ?case by(cases xs)(simp_all add: eSuc_enat[symmetric])
qed

lemma enat_llength_ldropn:
  "enat n \<le> llength xs \<Longrightarrow> enat (n - m) \<le> llength (ldropn m xs)"
by(cases "llength xs") simp_all

lemma ldropn_llist_of [simp]: "ldropn n (llist_of xs) = llist_of (drop n xs)"
proof(induct n arbitrary: xs)
  case Suc thus ?case by(cases xs) simp_all
qed simp

lemma ldrop_llist_of: "ldrop (enat n) (llist_of xs) = llist_of (drop n xs)"
by simp

lemma drop_list_of:
  "lfinite xs \<Longrightarrow> drop n (list_of xs) = list_of (ldropn n xs)"
by (metis ldropn_llist_of list_of_llist_of llist_of_list_of)

lemma llength_ldrop: "llength (ldrop n xs) = (if n = \<infinity> then 0 else llength xs - n)"
by auto

subsection {* Taking the $n$-th element of a lazy list: @{term "lnth" } *}

lemma lnth_LNil:
  "lnth LNil n = undefined n"
by(cases n)(simp_all add: lnth.simps)

lemma lnth_0 [simp]:
  "lnth (LCons x xs) 0 = x"
by(simp add: lnth.simps)

lemma lnth_Suc_LCons [simp]:
  "lnth (LCons x xs) (Suc n) = lnth xs n"
by(simp add: lnth.simps)

lemma lnth_LCons:
  "lnth (LCons x xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> lnth xs n')"
by(cases n) simp_all

lemma lnth_LCons': "lnth (LCons x xs) n = (if n = 0 then x else lnth xs (n - 1))"
by(simp add: lnth_LCons split: nat.split)

lemma lhd_conv_lnth:
  "\<not> lnull xs \<Longrightarrow> lhd xs = lnth xs 0"
by(auto simp add: lhd_def not_lnull_conv)

lemmas lnth_0_conv_lhd = lhd_conv_lnth[symmetric]

lemma lnth_ltl: "\<not> lnull xs \<Longrightarrow> lnth (ltl xs) n = lnth xs (Suc n)"
by(auto simp add: not_lnull_conv)

lemma lhd_ldropn:
  "enat n < llength xs \<Longrightarrow> lhd (ldropn n xs) = lnth xs n"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) auto
next
  case (Suc n)
  from `enat (Suc n) < llength xs` obtain x xs'
    where [simp]: "xs = LCons x xs'" by(cases xs) auto
  from `enat (Suc n) < llength xs`
  have "enat n < llength xs'" by(simp add: Suc_ile_eq)
  hence "lhd (ldropn n xs') = lnth xs' n" by(rule Suc)
  thus ?case by simp
qed

lemma lhd_ldrop: "n < llength xs \<Longrightarrow> lhd (ldrop n xs) = lnth xs (the_enat n)"
by(cases n)(simp_all add: lhd_ldropn)

lemma lnth_beyond:
  "llength xs \<le> enat n \<Longrightarrow> lnth xs n = undefined (n - (case llength xs of enat m \<Rightarrow> m))"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric] lnth_def lnull_def)
next
  case Suc thus ?case
    by(cases xs)(simp_all add: zero_enat_def lnth_def eSuc_enat[symmetric] split: enat.split, auto simp add: eSuc_enat)
qed

lemma lnth_lmap [simp]: 
  "enat n < llength xs \<Longrightarrow> lnth (lmap f xs) n = f (lnth xs n)"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) simp_all
next
  case (Suc n)
  from `enat (Suc n) < llength xs` obtain x xs'
    where xs: "xs = LCons x xs'" and len: "enat n < llength xs'"
    by(cases xs)(auto simp add: Suc_ile_eq)
  from len have "lnth (lmap f xs') n = f (lnth xs' n)" by(rule Suc)
  with xs show ?case by simp
qed

lemma lnth_ldropn [simp]:
  "enat (n + m) < llength xs \<Longrightarrow> lnth (ldropn n xs) m = lnth xs (m + n)"
proof(induct n arbitrary: xs)
  case (Suc n)
  from `enat (Suc n + m) < llength xs`
  obtain x xs' where "xs = LCons x xs'" by(cases xs) auto
  moreover with `enat (Suc n + m) < llength xs`
  have "enat (n + m) < llength xs'" by(simp add: Suc_ile_eq)
  hence "lnth (ldropn n xs') m = lnth xs' (m + n)" by(rule Suc)
  ultimately show ?case by simp
qed simp

lemma in_lset_conv_lnth:
  "x \<in> lset xs \<longleftrightarrow> (\<exists>n. enat n < llength xs \<and> lnth xs n = x)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then obtain n where "enat n < llength xs" "lnth xs n = x" by blast
  thus ?lhs
  proof(induct n arbitrary: xs)
    case 0
    thus ?case
      by(auto simp add: zero_enat_def[symmetric] not_lnull_conv)
  next
    case (Suc n)
    thus ?case
      by(cases xs)(auto simp add: eSuc_enat[symmetric])
  qed
next
  assume ?lhs
  thus ?rhs
  proof(induct)
    case (find xs)
    show ?case by(auto intro: exI[where x=0] simp add: zero_enat_def[symmetric])
  next
    case (step x' xs)
    thus ?case 
      by(auto 4 4 intro: exI[where x="Suc n" for n] ileI1 simp add: eSuc_enat[symmetric])
  qed
qed

lemma lset_conv_lnth: "lset xs = {lnth xs n|n. enat n < llength xs}"
by(auto simp add: in_lset_conv_lnth)

lemma lnth_llist_of [simp]: "lnth (llist_of xs) = nth xs"
proof(rule ext)
  fix n
  show "lnth (llist_of xs) n = xs ! n"
  proof(induct xs arbitrary: n)
    case Nil thus ?case by(cases n)(simp_all add: nth_def lnth_def)
  next
    case Cons thus ?case by(simp add: lnth_LCons split: nat.split)
  qed
qed

lemma nth_list_of [simp]: 
  assumes "lfinite xs"
  shows "nth (list_of xs) = lnth xs"
using assms
by induct(auto intro: simp add: nth_def lnth_LNil nth_Cons split: nat.split)

lemma lnth_lappend1:
  "enat n < llength xs \<Longrightarrow> lnth (lappend xs ys) n = lnth xs n"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(auto simp add: zero_enat_def[symmetric] not_lnull_conv)
next
  case (Suc n)
  from `enat (Suc n) < llength xs` obtain x xs'
    where [simp]: "xs = LCons x xs'" and len: "enat n < llength xs'"
    by(cases xs)(auto simp add: Suc_ile_eq)
  from len have "lnth (lappend xs' ys) n = lnth xs' n" by(rule Suc)
  thus ?case by simp
qed

lemma lnth_lappend_llist_of: 
  "lnth (lappend (llist_of xs) ys) n = 
  (if n < length xs then xs ! n else lnth ys (n - length xs))"
proof(induct xs arbitrary: n)
  case (Cons x xs) thus ?case by(cases n) auto
qed simp

lemma lnth_lappend2:
  "\<lbrakk> llength xs = enat k; k \<le> n \<rbrakk> \<Longrightarrow> lnth (lappend xs ys) n = lnth ys (n - k)"
proof(induct n arbitrary: xs k)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric] lappend_lnull1)
next
  case (Suc n) thus ?case
    by(cases xs)(auto simp add: eSuc_def zero_enat_def split: enat.split_asm)
qed

lemma lnth_lappend:
  "lnth (lappend xs ys) n = (if enat n < llength xs then lnth xs n else lnth ys (n - the_enat (llength xs)))"
by(cases "llength xs")(auto simp add: lnth_lappend1 lnth_lappend2)

lemma lnth_ltake:
  "enat m < n \<Longrightarrow> lnth (ltake n xs) m = lnth xs m"
proof(induct m arbitrary: xs n)
  case 0 thus ?case
    by(cases n rule: enat_coexhaust)(auto, cases xs, auto)
next
  case (Suc m)
  from `enat (Suc m) < n` obtain n' where "n = eSuc n'"
    by(cases n rule: enat_coexhaust) auto
  with `enat (Suc m) < n` have "enat m < n'" by(simp add: eSuc_enat[symmetric])
  with Suc `n = eSuc n'` show ?case by(cases xs) auto
qed

lemma ldropn_Suc_conv_ldropn:
  "enat n < llength xs \<Longrightarrow> LCons (lnth xs n) (ldropn (Suc n) xs) = ldropn n xs"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) auto
next
  case (Suc n)
  from `enat (Suc n) < llength xs` obtain x xs'
    where [simp]: "xs = LCons x xs'" by(cases xs) auto
  from `enat (Suc n) < llength xs`
  have "enat n < llength xs'" by(simp add: Suc_ile_eq)
  hence "LCons (lnth xs' n) (ldropn (Suc n) xs') = ldropn n xs'" by(rule Suc)
  thus ?case by simp
qed

lemma ltake_Suc_conv_snoc_lnth:
  "enat m < llength xs \<Longrightarrow> ltake (enat (Suc m)) xs = lappend (ltake (enat m) xs) (LCons (lnth xs m) LNil)"
by(metis eSuc_enat eSuc_plus_1 ltake_plus_conv_lappend ldrop.simps(1) ldropn_Suc_conv_ldropn ltake_0 ltake_eSuc_LCons one_eSuc)

lemma lappend_eq_lappend_conv:
  assumes len: "llength xs = llength us"
  shows "lappend xs ys = lappend us vs \<longleftrightarrow>
         xs = us \<and> (lfinite xs \<longrightarrow> ys = vs)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  thus ?lhs by(auto simp add: lappend_inf)
next
  assume eq: ?lhs
  show ?rhs
  proof(intro conjI impI)
    show "xs = us" using len eq
    proof(coinduction arbitrary: xs us)
      case (Eq_llist xs us)
      thus ?case
        by(cases xs us rule: llist.exhaust[case_product llist.exhaust]) auto
    qed
    assume "lfinite xs"
    then obtain xs' where "xs = llist_of xs'"
      by(auto simp add: lfinite_eq_range_llist_of)
    hence "lappend (llist_of xs') ys = lappend (llist_of xs') vs"
      using eq `xs = us` by blast
    thus "ys = vs"
      by (induct xs') simp_all
  qed
qed


subsection{* iterates *}

lemmas iterates [code, nitpick_simp] = iterates.ctr
  and lnull_iterates = iterates.simps(1)
  and lhd_iterates = iterates.simps(2)
  and ltl_iterates = iterates.simps(3)

lemma lfinite_iterates [iff]: "\<not> lfinite (iterates f x)"
proof
  assume "lfinite (iterates f x)"
  thus False
    by(induct zs\<equiv>"iterates f x" arbitrary: x rule: lfinite_induct) auto
qed

lemma lmap_iterates: "lmap f (iterates f x) = iterates f (f x)"
by(coinduction arbitrary: x) auto

lemma iterates_lmap: "iterates f x = LCons x (lmap f (iterates f x))"
by(simp add: lmap_iterates)(rule iterates)

lemma lappend_iterates: "lappend (iterates f x) xs = iterates f x"
by(coinduction arbitrary: x) auto

lemma [simp]:
  fixes f :: "'a \<Rightarrow> 'a"
  shows lnull_funpow_lmap: "lnull ((lmap f ^^ n) xs) \<longleftrightarrow> lnull xs"
  and lhd_funpow_lmap: "\<not> lnull xs \<Longrightarrow> lhd ((lmap f ^^ n) xs) = (f ^^ n) (lhd xs)"
  and ltl_funpow_lmap: "\<not> lnull xs \<Longrightarrow> ltl ((lmap f ^^ n) xs) = (lmap f ^^ n) (ltl xs)"
by(induct n) simp_all

lemma iterates_equality:
  assumes h: "\<And>x. h x = LCons x (lmap f (h x))"
  shows "h = iterates f"
proof -
  { fix x
    have "\<not> lnull (h x)" "lhd (h x) = x" "ltl (h x) = lmap f (h x)"
      by(subst h, simp)+ }
  note [simp] = this

  { fix x
    def n \<equiv> "0 :: nat"
    have "(lmap f ^^ n) (h x) = (lmap f ^^ n) (iterates f x)"
      by(coinduction arbitrary: n)(auto simp add: funpow_swap1 lmap_iterates intro: exI[where x="Suc n" for n]) }
  thus ?thesis by auto
qed

lemma llength_iterates [simp]: "llength (iterates f x) = \<infinity>"
by(coinduction arbitrary: x rule: enat_coinduct)(auto simp add: epred_llength)

lemma ldropn_iterates: "ldropn n (iterates f x) = iterates f ((f ^^ n) x)"
proof(induct n arbitrary: x)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "ldropn (Suc n) (iterates f x) = ldropn n (iterates f (f x))"
    by(subst iterates)simp
  also have "\<dots> = iterates f ((f ^^ n) (f x))" by(rule Suc)
  finally show ?case by(simp add: funpow_swap1)
qed

lemma lnth_iterates [simp]: "lnth (iterates f x) n = (f ^^ n) x"
proof(induct n arbitrary: x)
  case 0 thus ?case by(subst iterates) simp
next
  case (Suc n)
  hence "lnth (iterates f (f x)) n = (f ^^ n) (f x)" .
  thus ?case by(subst iterates)(simp add: funpow_swap1)
qed

lemma lset_iterates:
  "lset (iterates f x) = {(f ^^ n) x|n. True}"
by(auto simp add: lset_conv_lnth)

subsection {* 
  The prefix ordering on lazy lists: @{term "lprefix"} and @{term "lstrict_prefix"} 
*}

lemma lprefix_refl [intro, simp]: "lprefix xs xs"
by(auto simp add: lprefix_def intro: exI[where x=LNil])

lemma lprefix_lnull: "lnull ys \<Longrightarrow> lprefix xs ys \<longleftrightarrow> lnull xs"
by(auto simp add: lprefix_def lappend_lnull1)

lemma lprefix_LNil [simp]: "lprefix xs LNil \<longleftrightarrow> lnull xs"
by(simp add: lprefix_lnull)

lemma lnull_lprefix: "lnull xs \<Longrightarrow> lprefix xs ys"
by(simp add: lprefix_def lappend_lnull1)

lemma LNil_lprefix [simp, intro!]: "lprefix LNil xs"
by(simp add: lnull_lprefix)

lemma lprefix_LCons_conv: 
  "lprefix xs (LCons y ys) \<longleftrightarrow> 
   xs = LNil \<or> (\<exists>xs'. xs = LCons y xs' \<and> lprefix xs' ys)"
by(cases xs)(auto simp add: lprefix_def)

lemma LCons_lprefix_LCons [simp]:
  "lprefix (LCons x xs) (LCons y ys) \<longleftrightarrow> x = y \<and> lprefix xs ys"
by(simp add: lprefix_LCons_conv)

lemma LCons_lprefix_conv:
  "lprefix (LCons x xs) ys \<longleftrightarrow> (\<exists>ys'. ys = LCons x ys' \<and> lprefix xs ys')"
by(cases ys)(auto)

lemma lprefix_ltlI: "lprefix xs ys \<Longrightarrow> lprefix (ltl xs) (ltl ys)"
by(cases ys)(auto simp add: lprefix_LCons_conv)

lemma lprefix_antisym:
  "\<lbrakk> lprefix xs ys; lprefix ys xs \<rbrakk> \<Longrightarrow> xs = ys"
by(coinduction arbitrary: xs ys)(auto simp add: not_lnull_conv lprefix_lnull)

lemma lprefix_trans [trans]:
  "\<lbrakk> lprefix xs ys; lprefix ys zs \<rbrakk> \<Longrightarrow> lprefix xs zs"
by(auto simp add: lprefix_def lappend_assoc)

lemma lprefix_code [code]:
  "lprefix LNil ys \<longleftrightarrow> True" 
  "lprefix (LCons x xs) LNil \<longleftrightarrow> False"
  "lprefix (LCons x xs) (LCons y ys) \<longleftrightarrow> x = y \<and> lprefix xs ys"
by simp_all

lemma lstrict_prefix_code [code, simp]:
  "lstrict_prefix LNil LNil \<longleftrightarrow> False"
  "lstrict_prefix LNil (LCons y ys) \<longleftrightarrow> True"
  "lstrict_prefix (LCons x xs) LNil \<longleftrightarrow> False"
  "lstrict_prefix (LCons x xs) (LCons y ys) \<longleftrightarrow> x = y \<and> lstrict_prefix xs ys"
by(auto simp add: lstrict_prefix_def)

lemma not_lfinite_lprefix_conv_eq:
  assumes nfin: "\<not> lfinite xs"
  shows "lprefix xs ys \<longleftrightarrow> xs = ys"
proof
  assume "lprefix xs ys" 
  with nfin show "xs = ys"
    by(coinduction arbitrary: xs ys)(auto simp add: not_lnull_conv lprefix_lnull)
qed simp

lemma lmap_lprefix: "lprefix xs ys \<Longrightarrow> lprefix (lmap f xs) (lmap f ys)"
by(auto simp add: lprefix_def lmap_lappend_distrib)

lemma lprefix_llength_eq_imp_eq:
  "\<lbrakk> lprefix xs ys; llength xs = llength ys \<rbrakk> \<Longrightarrow> xs = ys"
by(coinduction arbitrary: xs ys)(auto simp add: not_lnull_conv)

lemma lprefix_llength_le: "lprefix xs ys \<Longrightarrow> llength xs \<le> llength ys"
by(coinduction arbitrary: xs ys rule: enat_le_coinduct)(auto 4 4 simp add: epred_llength lprefix_lnull elim!: lprefix_ltlI)

lemma lstrict_prefix_llength_less:
  assumes "lstrict_prefix xs ys"
  shows "llength xs < llength ys"
proof(rule ccontr)
  assume "\<not> llength xs < llength ys"
  moreover from `lstrict_prefix xs ys` have "lprefix xs ys" "xs \<noteq> ys"
    unfolding lstrict_prefix_def by simp_all
  from `lprefix xs ys` have "llength xs \<le> llength ys"
    by(rule lprefix_llength_le)
  ultimately have "llength xs = llength ys" by auto
  with `lprefix xs ys` have "xs = ys" 
    by(rule lprefix_llength_eq_imp_eq)
  with `xs \<noteq> ys` show False by contradiction
qed

lemma lstrict_prefix_lfinite1: "lstrict_prefix xs ys \<Longrightarrow> lfinite xs"
by (metis lstrict_prefix_def not_lfinite_lprefix_conv_eq)

lemma wfP_lstrict_prefix: "wfP lstrict_prefix"
proof(unfold wfP_def)
  have "wf {(x :: enat, y). x < y}"
    unfolding wf_def by(blast intro: less_induct)
  hence "wf (inv_image {(x, y). x < y} llength)" by(rule wf_inv_image)
  moreover have "{(xs, ys). lstrict_prefix xs ys} \<subseteq> inv_image {(x, y). x < y} llength"
    by(auto intro: lstrict_prefix_llength_less)
  ultimately show "wf {(xs, ys). lstrict_prefix xs ys}" by(rule wf_subset)
qed

lemma llist_less_induct[case_names less]:
  "(\<And>xs. (\<And>ys. lstrict_prefix ys xs \<Longrightarrow> P ys) \<Longrightarrow> P xs) \<Longrightarrow> P xs"
by(rule wfP_induct[OF wfP_lstrict_prefix]) blast

coinductive_set lprefix_llist :: "('a llist \<times> 'a llist) set"
where
  Le_LNil: "(LNil, xs) \<in> lprefix_llist"
| Le_LCons: "(xs, ys) \<in> lprefix_llist \<Longrightarrow> (LCons x xs, LCons x ys) \<in> lprefix_llist"

lemma lprefix_into_lprefix_llist:
  assumes "lprefix xs ys"
  shows "(xs, ys) \<in> lprefix_llist"
proof -
  from assms have "(xs, ys) \<in> {(xs, ys). lprefix xs ys}" by blast
  thus ?thesis
  proof(coinduct)
    case (lprefix_llist xs ys)
    hence pref: "lprefix xs ys" by simp
    show ?case
    proof(cases xs)
      case LNil hence ?Le_LNil by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      with pref obtain ys' where "ys = LCons x ys'" "lprefix xs' ys'"
        by(auto simp add: LCons_lprefix_conv)
      with LCons have ?Le_LCons by auto
      thus ?thesis ..
    qed
  qed
qed

lemma lprefix_llist_implies_ltake_lprefix:
  "(xs, ys) \<in> lprefix_llist \<Longrightarrow> lprefix (ltake (enat n) xs) (ltake (enat n) ys)"
proof(induct n arbitrary: xs ys)
  case 0 show ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n)
  from `(xs, ys) \<in> lprefix_llist` show ?case
  proof cases
    case Le_LNil thus ?thesis by simp
  next
    case (Le_LCons xs' ys' x)
    from `(xs', ys') \<in> lprefix_llist`
    have "lprefix (ltake (enat n) xs') (ltake (enat n) ys')" by(rule Suc)
    with Le_LCons show ?thesis by(simp add: eSuc_enat[symmetric])
  qed
qed

lemma ltake_enat_eq_imp_eq: "(\<And>n. ltake (enat n) xs = ltake (enat n) ys) \<Longrightarrow> xs = ys"
by(coinduction arbitrary: xs ys)(auto simp add: zero_enat_def lnull_def neq_LNil_conv ltake_eq_LNil_iff eSuc_enat[symmetric] elim: allE[where x="Suc n" for n])

lemma ltake_enat_lprefix_imp_lprefix:
  assumes le: "\<And>n. lprefix (ltake (enat n) xs) (ltake (enat n) ys)"
  shows "lprefix xs ys"
proof(cases "lfinite xs")
  case True
  then obtain n where n: "llength xs = enat n" by(auto dest: lfinite_llength_enat)
  have "xs = ltake (enat n) xs" unfolding n[symmetric] by(simp add: ltake_all)
  also have "lprefix \<dots> (ltake (enat n) ys)" by(rule le)
  also have "lprefix \<dots> ys" ..
  finally show ?thesis .
next
  case False
  hence [simp]: "llength xs = \<infinity>" by(rule not_lfinite_llength)
  { fix n
    from le[of n] obtain zs where "lappend (ltake (enat n) xs) zs = ltake (enat n) ys"
      unfolding lprefix_def by blast
    hence "llength (lappend (ltake (enat n) xs) zs) = llength (ltake (enat n) ys)"
      by simp
    hence n: "enat n \<le> llength ys"
      by(cases "llength zs", cases "llength ys")
        (simp_all add: min_def split: split_if_asm)
    from le have "ltake (enat n) xs = ltake (enat n) ys"
      by(rule lprefix_llength_eq_imp_eq)(simp add: n min_def) }
  hence "xs = ys" by(rule ltake_enat_eq_imp_eq)
  thus ?thesis by simp
qed

lemma lprefix_llist_imp_lprefix:
  "(xs, ys) \<in> lprefix_llist \<Longrightarrow> lprefix xs ys"
by(rule ltake_enat_lprefix_imp_lprefix)(rule lprefix_llist_implies_ltake_lprefix)

lemma lprefix_llist_eq_lprefix:
  "(xs, ys) \<in> lprefix_llist \<longleftrightarrow> lprefix xs ys"
by(blast intro: lprefix_llist_imp_lprefix lprefix_into_lprefix_llist)

lemma lprefixI [consumes 1, case_names lprefix, 
                case_conclusion lprefix LeLNil LeLCons]:
  assumes major: "(xs, ys) \<in> X"
  and step:
      "\<And>xs ys. (xs, ys) \<in> X 
       \<Longrightarrow> lnull xs \<or> (\<exists>x xs' ys'. xs = LCons x xs' \<and> ys = LCons x ys' \<and> 
                                   ((xs', ys') \<in> X \<or> lprefix xs' ys'))"
  shows "lprefix xs ys"
proof -
  from major show ?thesis
    by(rule lprefix_llist.coinduct[unfolded lprefix_llist_eq_lprefix])
      (auto dest: step)
qed

lemma lprefix_coinduct [consumes 1, case_names lprefix, case_conclusion lprefix LNil LCons, coinduct pred: lprefix]:
  assumes major: "P xs ys"
  and step: "\<And>xs ys. P xs ys
    \<Longrightarrow> (lnull ys \<longrightarrow> lnull xs) \<and>
       (\<not> lnull xs \<longrightarrow> \<not> lnull ys \<longrightarrow> lhd xs = lhd ys \<and> (P (ltl xs) (ltl ys) \<or> lprefix (ltl xs) (ltl ys)))"
  shows "lprefix xs ys"
proof -
  from major have "(xs, ys) \<in> {(xs, ys). P xs ys}" by simp
  thus ?thesis
  proof(coinduct rule: lprefixI)
    case (lprefix xs ys)
    hence "P xs ys" by simp
    from step[OF this] show ?case
      by(cases xs)(auto simp add: not_lnull_conv)
  qed
qed

lemma lprefix_lappend: "lprefix xs (lappend xs ys)"
by(coinduction arbitrary: xs) auto

lemma lappend_lprefixE:
  assumes "lprefix (lappend xs ys) zs"
  obtains zs' where "zs = lappend xs zs'"
using assms unfolding lprefix_def by(auto simp add: lappend_assoc)

lemma lprefix_lfiniteD:
  "\<lbrakk> lprefix xs ys; lfinite ys \<rbrakk> \<Longrightarrow> lfinite xs"
unfolding lprefix_def by auto

lemma lprefix_lappendD:
  assumes "lprefix xs (lappend ys zs)"
  shows "lprefix xs ys \<or> lprefix ys xs"
proof(rule ccontr)
  assume "\<not> (lprefix xs ys \<or> lprefix ys xs)"
  hence "\<not> lprefix xs ys" "\<not> lprefix ys xs" by simp_all
  from `lprefix xs (lappend ys zs)` obtain xs' 
    where "lappend xs xs' = lappend ys zs"
    unfolding lprefix_def by auto
  hence eq: "lappend (ltake (llength ys) xs) (lappend (ldrop (llength ys) xs) xs') =
             lappend ys zs"
    unfolding lappend_assoc[symmetric] by(simp only: lappend_ltake_ldrop)
  moreover have "llength xs \<ge> llength ys"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "llength xs < llength ys" by simp
    hence "ltake (llength ys) xs = xs" by(simp add: ltake_all)
    hence "lappend xs (lappend (ldrop (llength ys) xs) xs') = 
           lappend (ltake (llength xs) ys) (lappend (ldrop (llength xs) ys) zs)"
      unfolding lappend_assoc[symmetric] lappend_ltake_ldrop
      using eq by(simp add: lappend_assoc)
    hence xs: "xs = ltake (llength xs) ys" using `llength xs < llength ys`
      by(subst (asm) lappend_eq_lappend_conv)(auto simp add: min_def)
    have "lprefix xs ys" by(subst xs) auto
    with `\<not> lprefix xs ys` show False by contradiction
  qed
  ultimately have ys: "ys = ltake (llength ys) xs"
    by(subst (asm) lappend_eq_lappend_conv)(simp_all add: min_def)
  have "lprefix ys xs" by(subst ys) auto
  with `\<not> lprefix ys xs` show False by contradiction
qed

lemma lprefix_down_linear:
  "\<lbrakk> lprefix xs zs; lprefix ys zs \<rbrakk> \<Longrightarrow> lprefix xs ys \<or> lprefix ys xs"
by (metis (lifting) lprefix_def lprefix_lappendD)

lemma lprefix_lappend_same [simp]:
  "lprefix (lappend xs ys) (lappend xs zs) \<longleftrightarrow> (lfinite xs \<longrightarrow> lprefix ys zs)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  show "?rhs"
  proof
    assume "lfinite xs"
    thus "lprefix ys zs" using `?lhs` by(induct) simp_all
  qed
next
  assume "?rhs"
  show ?lhs
  proof(cases "lfinite xs")
    case True
    hence yszs: "lprefix ys zs" by(rule `?rhs`[rule_format])
    from True show ?thesis by induct (simp_all add: yszs)
  next
    case False thus ?thesis by(simp add: lappend_inf)
  qed
qed

lemma lstrict_prefix_lappend_conv:
  "lstrict_prefix xs (lappend xs ys) \<longleftrightarrow> lfinite xs \<and> \<not> lnull ys"
proof -
  { assume "lfinite xs" "xs = lappend xs ys"
    hence "lnull ys" by induct auto }
  thus ?thesis
    by(auto simp add: lstrict_prefix_def lprefix_lappend lappend_inf lappend_lnull2
            elim: contrapos_np)
qed

lemma lprefix_llist_ofI:
  "\<exists>zs. ys = xs @ zs \<Longrightarrow> lprefix (llist_of xs) (llist_of ys)"
by(clarsimp simp add: lappend_llist_of_llist_of[symmetric] lprefix_lappend)

lemma llimit_induct [case_names LNil LCons limit]:
  assumes LNil: "P LNil"
  and LCons: "\<And>x xs. \<lbrakk> lfinite xs; P xs \<rbrakk> \<Longrightarrow> P (LCons x xs)"
  and limit: "(\<And>ys. lstrict_prefix ys xs \<Longrightarrow> P ys) \<Longrightarrow> P xs"
  shows "P xs"
proof(rule limit)
  fix ys
  assume "lstrict_prefix ys xs"
  hence "lfinite ys" by(rule lstrict_prefix_lfinite1)
  thus "P ys" by(induct)(blast intro: LNil LCons)+
qed

lemma lmap_lstrict_prefix:
  "lstrict_prefix xs ys \<Longrightarrow> lstrict_prefix (lmap f xs) (lmap f ys)"
by (metis llength_lmap lmap_lprefix lprefix_llength_eq_imp_eq lstrict_prefix_def)

lemma lprefix_lnthD:
  assumes "lprefix xs ys" and "enat n < llength xs"
  shows "lnth xs n = lnth ys n"
using assms by (metis lnth_lappend1 lprefix_def)

text {* Setup for @{term "lprefix"} for Nitpick *}

definition finite_lprefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
where "finite_lprefix = lprefix"

lemma finite_lprefix_nitpick_simps [nitpick_simp]:
  "finite_lprefix xs LNil \<longleftrightarrow> xs = LNil"
  "finite_lprefix LNil xs \<longleftrightarrow> True"
  "finite_lprefix xs (LCons y ys) \<longleftrightarrow> 
   xs = LNil \<or> (\<exists>xs'. xs = LCons y xs' \<and> finite_lprefix xs' ys)"
by(simp_all add: lprefix_LCons_conv finite_lprefix_def lnull_def)

lemma lprefix_nitpick_simps [nitpick_simp]:
  "lprefix xs ys = (if lfinite xs then finite_lprefix xs ys else xs = ys)"
by(simp add: finite_lprefix_def not_lfinite_lprefix_conv_eq)

hide_const (open) finite_lprefix
hide_fact (open) finite_lprefix_def finite_lprefix_nitpick_simps lprefix_nitpick_simps

subsection {* Length of the longest common prefix *}

lemma llcp_simps [simp, code, nitpick_simp]:
  shows llcp_LNil1: "llcp LNil ys = 0"
  and llcp_LNil2: "llcp xs LNil = 0"
  and llcp_LCons: "llcp (LCons x xs) (LCons y ys) = (if x = y then eSuc (llcp xs ys) else 0)"
by(simp_all add: llcp_def enat_unfold split: llist.split)

lemma llcp_eq_0_iff:
  "llcp xs ys = 0 \<longleftrightarrow> lnull xs \<or> lnull ys \<or> lhd xs \<noteq> lhd ys"
by(simp add: llcp_def)

lemma epred_llcp:
  "\<lbrakk> \<not> lnull xs; \<not> lnull ys; lhd xs = lhd ys \<rbrakk>
  \<Longrightarrow>  epred (llcp xs ys) = llcp (ltl xs) (ltl ys)"
by(simp add: llcp_def)

lemma llcp_commute: "llcp xs ys = llcp ys xs"
by(coinduction arbitrary: xs ys rule: enat_coinduct)(auto simp add: llcp_eq_0_iff epred_llcp)

lemma llcp_same_conv_length [simp]: "llcp xs xs = llength xs"
by(coinduction arbitrary: xs rule: enat_coinduct)(auto simp add: llcp_eq_0_iff epred_llcp epred_llength)

lemma llcp_lappend_same [simp]: 
  "llcp (lappend xs ys) (lappend xs zs) = llength xs + llcp ys zs"
by(coinduction arbitrary: xs rule: enat_coinduct)(auto simp add: iadd_is_0 llcp_eq_0_iff epred_iadd1 epred_llcp epred_llength)

lemma llcp_lprefix1 [simp]: "lprefix xs ys \<Longrightarrow> llcp xs ys = llength xs"
by (metis add_0_right lappend_LNil2 llcp_LNil1 llcp_lappend_same lprefix_def)

lemma llcp_lprefix2 [simp]: "lprefix ys xs \<Longrightarrow> llcp xs ys = llength ys"
by (metis llcp_commute llcp_lprefix1)

lemma llcp_le_length: "llcp xs ys \<le> min (llength xs) (llength ys)"
proof -
  def m \<equiv> "llcp xs ys" and n \<equiv> "min (llength xs) (llength ys)"
  hence "(m, n) \<in> {(llcp xs ys, min (llength xs) (llength ys)) |xs ys :: 'a llist. True}" by blast
  thus "m \<le> n"
  proof(coinduct rule: enat_leI)
    case (Leenat m n)
    then obtain xs ys :: "'a llist" where "m = llcp xs ys" "n = min (llength xs) (llength ys)" by blast
    thus ?case
      by(cases xs ys rule: llist.exhaust[case_product llist.exhaust])(auto 4 3 intro!: exI[where x="Suc 0"] simp add: eSuc_enat[symmetric] iadd_Suc_right zero_enat_def[symmetric])
  qed
qed

lemma llcp_ltake1: "llcp (ltake n xs) ys = min n (llcp xs ys)"
by(coinduction arbitrary: n xs ys rule: enat_coinduct)(auto simp add: llcp_eq_0_iff enat_min_eq_0_iff epred_llcp ltl_ltake)

lemma llcp_ltake2: "llcp xs (ltake n ys) = min n (llcp xs ys)"
by(metis llcp_commute llcp_ltake1)

lemma llcp_ltake [simp]: "llcp (ltake n xs) (ltake m ys) = min (min n m) (llcp xs ys)"
by(metis llcp_ltake1 llcp_ltake2 min.assoc)

subsection {* Zipping two lazy lists to a lazy list of pairs @{term "lzip" } *}

lemma lzip_simps [simp, code, nitpick_simp]:
  "lzip LNil ys = LNil"
  "lzip xs LNil = LNil"
  "lzip (LCons x xs) (LCons y ys) = LCons (x, y) (lzip xs ys)"
by(auto intro: llist.expand)

lemma lnull_lzip [simp]: "lnull (lzip xs ys) \<longleftrightarrow> lnull xs \<or> lnull ys"
by(simp add: lzip_def)

lemma lzip_eq_LNil_conv: "lzip xs ys = LNil \<longleftrightarrow> xs = LNil \<or> ys = LNil"
using lnull_lzip unfolding lnull_def .

lemmas lhd_lzip = lzip.sel(1)
  and ltl_lzip = lzip.sel(2)

lemma lzip_eq_LCons_conv:
  "lzip xs ys = LCons z zs \<longleftrightarrow>
   (\<exists>x xs' y ys'. xs = LCons x xs' \<and> ys = LCons y ys' \<and> z = (x, y) \<and> zs = lzip xs' ys')"
by(cases xs ys rule: llist.exhaust[case_product llist.exhaust]) auto

lemma lzip_lappend:
  "llength xs = llength us
  \<Longrightarrow> lzip (lappend xs ys) (lappend us vs) = lappend (lzip xs us) (lzip ys vs)"
by(coinduction arbitrary: xs ys us vs rule: llist.strong_coinduct)(auto 4 6 simp add: llength_ltl)

lemma llength_lzip [simp]:
  "llength (lzip xs ys) = min (llength xs) (llength ys)"
by(coinduction arbitrary: xs ys rule: enat_coinduct)(auto simp add: enat_min_eq_0_iff epred_llength)

lemma ltake_lzip: "ltake n (lzip xs ys) = lzip (ltake n xs) (ltake n ys)"
by(coinduction arbitrary: xs ys n)(auto simp add: ltl_ltake)

lemma ldropn_lzip [simp]:
  "ldropn n (lzip xs ys) = lzip (ldropn n xs) (ldropn n ys)"
by(induct n arbitrary: xs ys)(simp_all add: ldropn_Suc split: llist.split)

lemma ldrop_lzip [simp]: "ldrop n (lzip xs ys) = lzip (ldrop n xs) (ldrop n ys)"
by(cases n) simp_all

lemma lzip_iterates:
  "lzip (iterates f x) (iterates g y) = iterates (\<lambda>(x, y). (f x, g y)) (x, y)"
by(coinduction arbitrary: x y) auto

lemma lzip_llist_of [simp]:
  "lzip (llist_of xs) (llist_of ys) = llist_of (zip xs ys)"
proof(induct xs arbitrary: ys)
  case (Cons x xs')
  thus ?case by(cases ys) simp_all
qed simp

lemma lnth_lzip:
  "\<lbrakk> enat n < llength xs; enat n < llength ys \<rbrakk>
  \<Longrightarrow> lnth (lzip xs ys) n = (lnth xs n, lnth ys n)"
proof(induct n arbitrary: xs ys)
  case 0
  then obtain x xs' y ys' where "xs = LCons x xs'" "ys = LCons y ys'"
    unfolding zero_enat_def[symmetric]
    by(cases xs, simp)(cases ys, auto)
  thus ?case by simp
next
  case (Suc n)
  from `enat (Suc n) < llength xs` obtain x xs'
    where xs: "xs = LCons x xs'" by(cases xs) auto
  moreover from `enat (Suc n) < llength ys` obtain y ys'
    where ys: "ys = LCons y ys'" by(cases ys) auto
  moreover from `enat (Suc n) < llength xs` `enat (Suc n) < llength ys` xs ys
  have "enat n < llength xs'" "enat n < llength ys'"
    by(auto simp add: eSuc_enat[symmetric])
  hence "lnth (lzip xs' ys') n = (lnth xs' n, lnth ys' n)" by(rule Suc)
  ultimately show ?case by simp
qed

lemma lset_lzip: 
  "lset (lzip xs ys) =
   {(lnth xs n, lnth ys n)|n. enat n < min (llength xs) (llength ys)}"
by(auto simp add: lset_conv_lnth lnth_lzip)(auto intro!: exI simp add: lnth_lzip)

lemma lset_lzipD1: "(x, y) \<in> lset (lzip xs ys) \<Longrightarrow> x \<in> lset xs"
proof(induct "lzip xs ys" arbitrary: xs ys rule: lset_induct)
  case find[symmetric]
  thus ?case by(auto simp add: lzip_eq_LCons_conv)
next
  case (step z zs)
  thus ?case by -(drule sym, auto simp add: lzip_eq_LCons_conv)
qed

lemma lset_lzipD2: "(x, y) \<in> lset (lzip xs ys) \<Longrightarrow> y \<in> lset ys"
proof(induct "lzip xs ys" arbitrary: xs ys rule: lset_induct)
  case find[symmetric]
  thus ?case by(auto simp add: lzip_eq_LCons_conv)
next
  case (step z zs)
  thus ?case by -(drule sym, auto simp add: lzip_eq_LCons_conv)
qed

lemma lset_lzip_same [simp]: "lset (lzip xs xs) = (\<lambda>x. (x, x)) ` lset xs"
by(auto 4 3 simp add: lset_lzip in_lset_conv_lnth)

lemma lfinite_lzip [simp]:
  "lfinite (lzip xs ys) \<longleftrightarrow> lfinite xs \<or> lfinite ys" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by(induct zs\<equiv>"lzip xs ys" arbitrary: xs ys rule: lfinite_induct) fastforce+
next
  assume ?rhs (is "?xs \<or> ?ys")
  thus ?lhs
  proof
    assume ?xs
    thus ?thesis
    proof(induct arbitrary: ys)
      case (lfinite_LConsI xs x)
      thus ?case by(cases ys) simp_all
    qed simp
  next
    assume ?ys
    thus ?thesis
    proof(induct arbitrary: xs)
      case (lfinite_LConsI ys y)
      thus ?case by(cases xs) simp_all
    qed simp
  qed
qed

lemma lzip_eq_lappend_conv:
  assumes eq: "lzip xs ys = lappend us vs"
  shows "\<exists>xs' xs'' ys' ys''. xs = lappend xs' xs'' \<and> ys = lappend ys' ys'' \<and>
                             llength xs' = llength ys' \<and> us = lzip xs' ys' \<and>
                             vs = lzip xs'' ys''"
proof -
  let ?xs' = "ltake (llength us) xs"
  let ?xs'' = "ldrop (llength us) xs"
  let ?ys' = "ltake (llength us) ys"
  let ?ys'' = "ldrop (llength us) ys"

  from eq have "llength (lzip xs ys) = llength (lappend us vs)" by simp
  hence "min (llength xs) (llength ys) \<ge> llength us"
    by(auto simp add: enat_le_plus_same)
  hence len: "llength xs \<ge> llength us" "llength ys \<ge> llength us" by(auto)

  hence leneq: "llength ?xs' = llength ?ys'" by(simp add: min_def)
  have xs: "xs = lappend ?xs' ?xs''" and ys: "ys = lappend ?ys' ?ys''"
    by(simp_all add: lappend_ltake_ldrop)
  hence "lappend us vs = lzip (lappend ?xs' ?xs'') (lappend ?ys' ?ys'')"
    using eq by simp
  with len have "lappend us vs = lappend (lzip ?xs' ?ys') (lzip ?xs'' ?ys'')"
    by(simp add: lzip_lappend min_def)
  hence us: "us = lzip ?xs' ?ys'" 
    and vs: "lfinite us \<longrightarrow> vs = lzip ?xs'' ?ys''" using len
    by(simp_all add: min_def lappend_eq_lappend_conv)
  show ?thesis
  proof(cases "lfinite us")
    case True
    with leneq xs ys us vs len show ?thesis by fastforce
  next
    case False
    let ?xs'' = "lmap fst vs"
    let ?ys'' = "lmap snd vs"
    from False have "lappend us vs = us" by(simp add: lappend_inf)
    moreover from False have "llength us = \<infinity>"
      by(rule not_lfinite_llength)
    moreover with len
    have "llength xs = \<infinity>" "llength ys = \<infinity>" by auto
    moreover with `llength us = \<infinity>`
    have "xs = ?xs'" "ys = ?ys'" by(simp_all add: ltake_all)
    from `llength us = \<infinity>` len 
    have "\<not> lfinite ?xs'" "\<not> lfinite ?ys'"
      by(auto simp del: llength_ltake lfinite_ltake 
             simp add: ltake_all dest: lfinite_llength_enat)
    with `xs = ?xs'` `ys = ?ys'`
    have "xs = lappend ?xs' ?xs''" "ys = lappend ?ys' ?ys''"
      by(simp_all add: lappend_inf)
    moreover have "vs = lzip ?xs'' ?ys''" 
      by(coinduction arbitrary: vs) auto
    ultimately show ?thesis using eq by(fastforce simp add: ltake_all)
  qed
qed

lemma lzip_lmap [simp]:
  "lzip (lmap f xs) (lmap g ys) = lmap (\<lambda>(x, y). (f x, g y)) (lzip xs ys)"
by(coinduction arbitrary: xs ys) auto

lemma lzip_lmap1:
  "lzip (lmap f xs) ys = lmap (\<lambda>(x, y). (f x, y)) (lzip xs ys)"
by(subst (4) lmap_ident[symmetric])(simp only: lzip_lmap)

lemma lzip_lmap2: 
  "lzip xs (lmap f ys) = lmap (\<lambda>(x, y). (x, f y)) (lzip xs ys)"
by(subst (1) lmap_ident[symmetric])(simp only: lzip_lmap)

lemma lmap_fst_lzip_conv_ltake: 
  "lmap fst (lzip xs ys) = ltake (min (llength xs) (llength ys)) xs"
by(coinduction arbitrary: xs ys)(auto simp add: enat_min_eq_0_iff ltl_ltake epred_llength)

lemma lmap_snd_lzip_conv_ltake: 
  "lmap snd (lzip xs ys) = ltake (min (llength xs) (llength ys)) ys"
by(coinduction arbitrary: xs ys)(auto simp add: enat_min_eq_0_iff ltl_ltake epred_llength)

lemma lzip_conv_lzip_ltake_min_llength:
  "lzip xs ys = 
  lzip (ltake (min (llength xs) (llength ys)) xs) 
       (ltake (min (llength xs) (llength ys)) ys)"
by(coinduction arbitrary: xs ys)(auto simp add: enat_min_eq_0_iff ltl_ltake epred_llength)

subsection {* Taking and dropping from a lazy list: @{term "ltakeWhile"} and @{term "ldropWhile"} *}

lemma ltakeWhile_simps [simp, code, nitpick_simp]:
  shows ltakeWhile_LNil: "ltakeWhile P LNil = LNil"
  and ltakeWhile_LCons: "ltakeWhile P (LCons x xs) = (if P x then LCons x (ltakeWhile P xs) else LNil)"
by(auto simp add: ltakeWhile_def intro: llist.expand)

lemma ldropWhile_simps [simp, code]:
  shows ldropWhile_LNil: "ldropWhile P LNil = LNil"
  and ldropWhile_LCons: "ldropWhile P (LCons x xs) = (if P x then ldropWhile P xs else LCons x xs)"
by(simp_all add: ldropWhile_def)

lemma lnull_ltakeWhile [simp]: "lnull (ltakeWhile P xs) \<longleftrightarrow> (\<not> lnull xs \<longrightarrow> \<not> P (lhd xs))"
by(cases xs) simp_all

lemma ltakeWhile_eq_LNil_iff: "ltakeWhile P xs = LNil \<longleftrightarrow> (xs \<noteq> LNil \<longrightarrow> \<not> P (lhd xs))"
using lnull_ltakeWhile unfolding lnull_def .

lemmas lhd_ltakeWhile = ltakeWhile.sel(1)

lemma ltl_ltakeWhile:
  "ltl (ltakeWhile P xs) = (if P (lhd xs) then ltakeWhile P (ltl xs) else LNil)"
by(cases xs) simp_all

lemma lprefix_ltakeWhile: "lprefix (ltakeWhile P xs) xs"
by(coinduction arbitrary: xs)(auto simp add: ltl_ltakeWhile)

lemma llength_ltakeWhile_le: "llength (ltakeWhile P xs) \<le> llength xs"
by(rule lprefix_llength_le)(rule lprefix_ltakeWhile)

lemmas ldropWhile_eq_ldrop = ldropWhile_def

lemma ltakeWhile_nth: "enat i < llength (ltakeWhile P xs) \<Longrightarrow> lnth (ltakeWhile P xs) i = lnth xs i"
by(rule lprefix_lnthD[OF lprefix_ltakeWhile])

lemma ltakeWhile_all: "\<forall>x\<in>lset xs. P x \<Longrightarrow> ltakeWhile P xs = xs"
by(coinduction arbitrary: xs)(auto 4 3 simp add: ltl_ltakeWhile simp del: ltakeWhile.disc_iff dest: in_lset_ltlD)

lemma lset_ltakeWhileD:
  assumes "x \<in> lset (ltakeWhile P xs)"
  shows "x \<in> lset xs \<and> P x"
using assms
by(induct ys\<equiv>"ltakeWhile P xs" arbitrary: xs rule: llist_set_induct)(auto simp add: ltl_ltakeWhile dest: in_lset_ltlD)

lemma lset_ltakeWhile_subset:
  "lset (ltakeWhile P xs) \<subseteq> lset xs \<inter> {x. P x}"
by(auto dest: lset_ltakeWhileD)

lemma ltakeWhile_all_conv: "ltakeWhile P xs = xs \<longleftrightarrow> lset xs \<subseteq> {x. P x}"
by (metis Int_Collect Int_absorb2 le_infE lset_ltakeWhile_subset ltakeWhile_all)

lemma llength_ltakeWhile_all: "llength (ltakeWhile P xs) = llength xs \<longleftrightarrow> ltakeWhile P xs = xs"
by(auto intro: lprefix_llength_eq_imp_eq lprefix_ltakeWhile)

lemma lnull_ldropWhile [simp]: 
  "lnull (ldropWhile P xs) \<longleftrightarrow> (\<forall>x \<in> lset xs. P x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs 
  from ltakeWhile_all[OF this] show ?lhs by(simp add: ldropWhile_def)
next
  assume ?lhs
  hence "llength xs \<le> llength (ltakeWhile P xs)" by(simp add: ldropWhile_def)
  moreover have "\<dots> \<le> llength xs" by(rule llength_ltakeWhile_le)
  ultimately have "llength (ltakeWhile P xs) = llength xs" by simp
  thus ?rhs unfolding llength_ltakeWhile_all by(auto simp add: ltakeWhile_all_conv)
qed

lemma ldropWhile_eq_LNil_iff: "ldropWhile P xs = LNil \<longleftrightarrow> (\<forall>x \<in> lset xs. P x)"
using lnull_ldropWhile unfolding lnull_def .

lemma lset_ldropWhile_subset:
  "lset (ldropWhile P xs) \<subseteq> lset xs"
by(simp add: ldropWhile_def lset_ldrop_subset)

lemma in_lset_ldropWhileD: "x \<in> lset (ldropWhile P xs) \<Longrightarrow> x \<in> lset xs"
using lset_ldropWhile_subset[of P xs] by auto

lemma ltakeWhile_lmap: "ltakeWhile P (lmap f xs) = lmap f (ltakeWhile (P \<circ> f) xs)"
by(coinduction arbitrary: xs)(auto simp add: ltl_ltakeWhile)

lemma ldropWhile_lmap: "ldropWhile P (lmap f xs) = lmap f (ldropWhile (P \<circ> f) xs)"
by(simp add: ldropWhile_def ldrop_lmap[symmetric] ltakeWhile_lmap del: ldrop_lmap)

lemma llength_ltakeWhile_lt_iff: "llength (ltakeWhile P xs) < llength xs \<longleftrightarrow> (\<exists>x\<in>lset xs. \<not> P x)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  hence "ltakeWhile P xs \<noteq> xs" by auto
  thus ?rhs by(auto simp add: ltakeWhile_all_conv)
next
  assume ?rhs
  hence "ltakeWhile P xs \<noteq> xs" by(auto simp add: ltakeWhile_all_conv)
  thus ?lhs unfolding llength_ltakeWhile_all[symmetric]
    using llength_ltakeWhile_le[of P xs] by(auto)
qed

lemma ltakeWhile_K_False [simp]: "ltakeWhile (\<lambda>_. False) xs = LNil"
by(simp add: ltakeWhile_def)

lemma ltakeWhile_K_True [simp]: "ltakeWhile (\<lambda>_. True) xs = xs"
by(coinduction arbitrary: xs) simp

lemma ldropWhile_K_False [simp]: "ldropWhile (\<lambda>_. False) = id"
by(simp add: ldropWhile_def fun_eq_iff)

lemma ldropWhile_K_True [simp]: "ldropWhile (\<lambda>_. True) xs = LNil"
by(simp add: ldropWhile_def)

lemma lappend_ltakeWhile_ldropWhile [simp]:
  "lappend (ltakeWhile P xs) (ldropWhile P xs) = xs"
by(coinduction arbitrary: xs rule: llist.strong_coinduct)(auto 4 4 simp add: not_lnull_conv lset_lnull intro: ccontr)

lemma ltakeWhile_lappend:
  "ltakeWhile P (lappend xs ys) =
  (if \<exists>x\<in>lset xs. \<not> P x then ltakeWhile P xs
   else lappend xs (ltakeWhile P ys))"
by(coinduction arbitrary: xs rule: llist.strong_coinduct)
  (auto 4 3 simp add: ltl_ltakeWhile not_lnull_conv lset_lnull split: split_if_asm)

lemma ldropWhile_lappend:
  "ldropWhile P (lappend xs ys) =
  (if \<exists>x\<in>lset xs. \<not> P x then lappend (ldropWhile P xs) ys
   else if lfinite xs then ldropWhile P ys else LNil)"
apply(auto simp add: ldropWhile_def ltakeWhile_lappend lappend_inf ldrop_lappend llength_ltakeWhile_lt_iff llength_eq_infty_conv_lfinite[symmetric] iff del: not_infinity_eq)
apply(simp add: enat_add_sub_same llength_eq_infty_conv_lfinite)
done

lemma lfinite_ltakeWhile:
  "lfinite (ltakeWhile P xs) \<longleftrightarrow> lfinite xs \<or> (\<exists>x \<in> lset xs. \<not> P x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs by(auto simp add: ltakeWhile_all)
next
  assume "?rhs"
  thus ?lhs
  proof
    assume "lfinite xs"
    with lprefix_ltakeWhile show ?thesis by(rule lprefix_lfiniteD)
  next
    assume "\<exists>x\<in>lset xs. \<not> P x"
    then obtain x where "x \<in> lset xs" "\<not> P x" by blast
    thus ?thesis by(induct rule: lset_induct) simp_all
  qed
qed

lemma llength_ltakeWhile_eq_infinity:
  "llength (ltakeWhile P xs) = \<infinity> \<longleftrightarrow> \<not> lfinite xs \<and> ltakeWhile P xs = xs"
unfolding llength_ltakeWhile_all[symmetric] llength_eq_infty_conv_lfinite[symmetric]
by(auto)(auto simp add: llength_eq_infty_conv_lfinite lfinite_ltakeWhile intro: sym)

lemma lzip_ltakeWhile_fst: "lzip (ltakeWhile P xs) ys = ltakeWhile (P \<circ> fst) (lzip xs ys)"
by(coinduction arbitrary: xs ys)(auto simp add: ltl_ltakeWhile simp del: simp del: ltakeWhile.disc_iff)

lemma lzip_ltakeWhile_snd: "lzip xs (ltakeWhile P ys) = ltakeWhile (P \<circ> snd) (lzip xs ys)"
by(coinduction arbitrary: xs ys)(auto simp add: ltl_ltakeWhile)
  
lemma ltakeWhile_lappend1: 
  "\<lbrakk> x \<in> lset xs; \<not> P x \<rbrakk> \<Longrightarrow> ltakeWhile P (lappend xs ys) = ltakeWhile P xs"
by(induct rule: lset_induct) simp_all

lemma ltakeWhile_lappend2:
  "lset xs \<subseteq> {x. P x}
  \<Longrightarrow> ltakeWhile P (lappend xs ys) = lappend xs (ltakeWhile P ys)"
by(coinduction arbitrary: xs ys rule: llist.strong_coinduct)(auto 4 4 simp add: not_lnull_conv lappend_lnull1)

lemma ltakeWhile_cong [cong, fundef_cong]:
  assumes xs: "xs = ys"
  and PQ: "\<And>x. x \<in> lset ys \<Longrightarrow> P x = Q x"
  shows "ltakeWhile P xs = ltakeWhile Q ys"
using PQ unfolding xs
by(coinduction arbitrary: ys)(auto simp add: ltl_ltakeWhile not_lnull_conv)

lemma lnth_llength_ltakeWhile:
  assumes len: "llength (ltakeWhile P xs) < llength xs"
  shows "\<not> P (lnth xs (the_enat (llength (ltakeWhile P xs))))"
proof
  assume P: "P (lnth xs (the_enat (llength (ltakeWhile P xs))))"
  from len obtain len where "llength (ltakeWhile P xs) = enat len"
    by(cases "llength (ltakeWhile P xs)") auto
  with P len show False apply simp
  proof(induct len arbitrary: xs)
    case 0 thus ?case by(simp add: zero_enat_def[symmetric] lnth_0_conv_lhd)
  next
    case (Suc len) thus ?case by(cases xs)(auto split: split_if_asm simp add: eSuc_enat[symmetric])
  qed
qed

lemma assumes "\<exists>x\<in>lset xs. \<not> P x"
  shows lhd_ldropWhile: "\<not> P (lhd (ldropWhile P xs))" (is ?thesis1)
  and lhd_ldropWhile_in_lset: "lhd (ldropWhile P xs) \<in> lset xs" (is ?thesis2)
proof -
  from assms have len: "llength (ltakeWhile P xs) < llength xs"
    by(simp add: llength_ltakeWhile_lt_iff)
  thus ?thesis1
    by(simp add: ldropWhile_def lhd_ldrop lnth_llength_ltakeWhile)
  from len show ?thesis2
    by(cases "llength (ltakeWhile P xs)")(auto simp add: ldropWhile_def lhd_ldropn in_lset_conv_lnth)
qed

lemma ldropWhile_cong [cong]:
  "\<lbrakk> xs = ys; \<And>x. x \<in> lset ys \<Longrightarrow> P x = Q x \<rbrakk> \<Longrightarrow> ldropWhile P xs = ldropWhile Q ys"
by(simp add: ldropWhile_def)

lemma ltakeWhile_repeat: 
  "ltakeWhile P (repeat x) = (if P x then repeat x else LNil)"
by(coinduction arbitrary: x)(auto simp add: ltl_ltakeWhile)

lemma ldropWhile_repeat: "ldropWhile P (repeat x) = (if P x then LNil else repeat x)"
by(simp add: ldropWhile_def ltakeWhile_repeat)

lemma lfinite_ldropWhile: "lfinite (ldropWhile P xs) \<longleftrightarrow> (\<exists>x \<in> lset xs. \<not> P x) \<longrightarrow> lfinite xs"
by(auto simp add: ldropWhile_def llength_eq_infty_conv_lfinite lfinite_ltakeWhile)

lemma llength_ldropWhile: 
  "llength (ldropWhile P xs) = 
  (if \<exists>x\<in>lset xs. \<not> P x then llength xs - llength (ltakeWhile P xs) else 0)"
by(auto simp add: ldropWhile_def llength_ldrop llength_ltakeWhile_all ltakeWhile_all_conv llength_ltakeWhile_eq_infinity zero_enat_def dest!: lfinite_llength_enat)

lemma lhd_ldropWhile_conv_lnth:
  "\<exists>x\<in>lset xs. \<not> P x \<Longrightarrow> lhd (ldropWhile P xs) = lnth xs (the_enat (llength (ltakeWhile P xs)))"
by(simp add: ldropWhile_def lhd_ldrop llength_ltakeWhile_lt_iff)

subsection {* @{term "llist_all2"} *}

lemmas llist_all2_LNil_LNil = llist.rel_inject(1)
lemmas llist_all2_LNil_LCons = llist.rel_distinct(1)
lemmas llist_all2_LCons_LNil = llist.rel_distinct(2)
lemmas llist_all2_LCons_LCons = llist.rel_inject(2)

lemma llist_all2_LNil1 [simp]: "llist_all2 P LNil xs \<longleftrightarrow> xs = LNil" 
by(cases xs) simp_all

lemma llist_all2_LNil2 [simp]: "llist_all2 P xs LNil \<longleftrightarrow> xs = LNil"
by(cases xs) simp_all

lemma llist_all2_LCons1: 
  "llist_all2 P (LCons x xs) ys \<longleftrightarrow> (\<exists>y ys'. ys = LCons y ys' \<and> P x y \<and> llist_all2 P xs ys')"
by(cases ys) simp_all

lemma llist_all2_LCons2: 
  "llist_all2 P xs (LCons y ys) \<longleftrightarrow> (\<exists>x xs'. xs = LCons x xs' \<and> P x y \<and> llist_all2 P xs' ys)"
by(cases xs) simp_all

lemma llist_all2_llist_of [simp]:
  "llist_all2 P (llist_of xs) (llist_of ys) = list_all2 P xs ys"
by(induct xs ys rule: list_induct2')(simp_all)

lemma llist_all2_conv_lzip:
  "llist_all2 P xs ys \<longleftrightarrow> llength xs = llength ys \<and> (\<forall>(x, y) \<in> lset (lzip xs ys). P x y)"
by(auto 4 4 elim!: GrpE simp add:
  llist_all2_def lmap_fst_lzip_conv_ltake lmap_snd_lzip_conv_ltake ltake_all
  intro!: GrpI relcomppI[of _ xs _ _ ys])

lemma llist_all2_llengthD:
  "llist_all2 P xs ys \<Longrightarrow> llength xs = llength ys"
by(simp add: llist_all2_conv_lzip)

lemma llist_all2_lnullD: "llist_all2 P xs ys \<Longrightarrow> lnull xs \<longleftrightarrow> lnull ys"
unfolding lnull_def by auto

lemma llist_all2_all_lnthI:
  "\<lbrakk> llength xs = llength ys;
     \<And>n. enat n < llength xs \<Longrightarrow> P (lnth xs n) (lnth ys n) \<rbrakk>
  \<Longrightarrow> llist_all2 P xs ys"
by(auto simp add: llist_all2_conv_lzip lset_lzip)

lemma llist_all2_lnthD:
  "\<lbrakk> llist_all2 P xs ys; enat n < llength xs \<rbrakk> \<Longrightarrow> P (lnth xs n) (lnth ys n)"
by(fastforce simp add: llist_all2_conv_lzip lset_lzip)

lemma llist_all2_lnthD2:
  "\<lbrakk> llist_all2 P xs ys; enat n < llength ys \<rbrakk> \<Longrightarrow> P (lnth xs n) (lnth ys n)"
by(fastforce simp add: llist_all2_conv_lzip lset_lzip)

lemma llist_all2_conv_all_lnth:
  "llist_all2 P xs ys \<longleftrightarrow> 
   llength xs = llength ys \<and> 
   (\<forall>n. enat n < llength ys \<longrightarrow> P (lnth xs n) (lnth ys n))"
by(auto dest: llist_all2_llengthD llist_all2_lnthD2 intro: llist_all2_all_lnthI)

lemma llist_all2_reflI:
  "(\<And>x. x \<in> lset xs \<Longrightarrow> P x x) \<Longrightarrow> llist_all2 P xs xs"
by(auto simp add: llist_all2_conv_all_lnth lset_conv_lnth)

lemma llist_all2_lmap1:
  "llist_all2 P (lmap f xs) ys \<longleftrightarrow> llist_all2 (\<lambda>x. P (f x)) xs ys"
by(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_lmap2:
  "llist_all2 P xs (lmap g ys) \<longleftrightarrow> llist_all2 (\<lambda>x y. P x (g y)) xs ys"
by(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_lfiniteD: 
  "llist_all2 P xs ys \<Longrightarrow> lfinite xs \<longleftrightarrow> lfinite ys"
by(drule llist_all2_llengthD)(simp add: lfinite_conv_llength_enat)

lemma llist_all2_coinduct[consumes 1, case_names LNil LCons, case_conclusion LCons lhd ltl, coinduct pred]:
  assumes major: "X xs ys"
  and step:
  "\<And>xs ys. X xs ys \<Longrightarrow> lnull xs \<longleftrightarrow> lnull ys"
  "\<And>xs ys. \<lbrakk> X xs ys; \<not> lnull xs; \<not> lnull ys \<rbrakk> \<Longrightarrow> P (lhd xs) (lhd ys) \<and> (X (ltl xs) (ltl ys) \<or> llist_all2 P (ltl xs) (ltl ys))"
  shows "llist_all2 P xs ys"
proof(rule llist_all2_all_lnthI)
  from major show "llength xs = llength ys"
    by(coinduction arbitrary: xs ys rule: enat_coinduct)(auto 4 3 dest: step llist_all2_llengthD simp add: epred_llength)
    
  fix n
  assume "enat n < llength xs"
  thus "P (lnth xs n) (lnth ys n)"
    using major `llength xs = llength ys`
  proof(induct n arbitrary: xs ys)
    case 0 thus ?case
      by(cases "lnull xs")(auto dest: step simp add: zero_enat_def[symmetric] lnth_0_conv_lhd)
  next
    case (Suc n)
    from step[OF `X xs ys`] `enat (Suc n) < llength xs` Suc show ?case
      by(auto 4 3 simp add: not_lnull_conv Suc_ile_eq intro: Suc.hyps llist_all2_lnthD dest: llist_all2_llengthD)
  qed
qed

lemma llist_all2_cases[consumes 1, case_names LNil LCons, cases pred]:
  assumes "llist_all2 P xs ys"
  obtains (LNil) "xs = LNil" "ys = LNil"
  | (LCons) x xs' y ys'
    where "xs = LCons x xs'" and "ys = LCons y ys'" 
    and "P x y" and "llist_all2 P xs' ys'"
using assms
by(cases xs)(auto simp add: llist_all2_LCons1)

lemma llist_all2_mono:
  "\<lbrakk> llist_all2 P xs ys; \<And>x y. P x y \<Longrightarrow> P' x y \<rbrakk> \<Longrightarrow> llist_all2 P' xs ys"
by(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_left: "llist_all2 (\<lambda>x _. P x) xs ys \<longleftrightarrow> llength xs = llength ys \<and> (\<forall>x\<in>lset xs. P x)"
by(fastforce simp add: llist_all2_conv_all_lnth lset_conv_lnth)

lemma llist_all2_right: "llist_all2 (\<lambda>_. P) xs ys \<longleftrightarrow> llength xs = llength ys \<and> (\<forall>x\<in>lset ys. P x)"
by(fastforce simp add: llist_all2_conv_all_lnth lset_conv_lnth)

lemma llist_all2_lsetD1: "\<lbrakk> llist_all2 P xs ys; x \<in> lset xs \<rbrakk> \<Longrightarrow> \<exists>y\<in>lset ys. P x y"
by(auto 4 4 simp add: llist_all2_conv_lzip lset_lzip lset_conv_lnth split_beta lnth_lzip simp del: split_paired_All)

lemma llist_all2_lsetD2: "\<lbrakk> llist_all2 P xs ys; y \<in> lset ys \<rbrakk> \<Longrightarrow> \<exists>x\<in>lset xs. P x y"
by(auto 4 4 simp add: llist_all2_conv_lzip lset_lzip lset_conv_lnth split_beta lnth_lzip simp del: split_paired_All)

lemma llist_all2_conj: 
  "llist_all2 (\<lambda>x y. P x y \<and> Q x y) xs ys \<longleftrightarrow> llist_all2 P xs ys \<and> llist_all2 Q xs ys"
by(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_lhdD:
  "\<lbrakk> llist_all2 P xs ys; \<not> lnull xs \<rbrakk> \<Longrightarrow> P (lhd xs) (lhd ys)"
by(auto simp add: not_lnull_conv llist_all2_LCons1)

lemma llist_all2_lhdD2:
  "\<lbrakk> llist_all2 P xs ys; \<not> lnull ys \<rbrakk> \<Longrightarrow> P (lhd xs) (lhd ys)"
by(auto simp add: not_lnull_conv llist_all2_LCons2)

lemma llist_all2_ltlI:
  "llist_all2 P xs ys \<Longrightarrow> llist_all2 P (ltl xs) (ltl ys)"
by(cases xs)(auto simp add: llist_all2_LCons1)

lemma llist_all2_lappendI:
  assumes 1: "llist_all2 P xs ys"
  and 2: "\<lbrakk> lfinite xs; lfinite ys \<rbrakk> \<Longrightarrow> llist_all2 P xs' ys'"
  shows "llist_all2 P (lappend xs xs') (lappend ys ys')"
proof(cases "lfinite xs")
  case True
  with 1 have "lfinite ys" by(auto dest: llist_all2_lfiniteD)
  from 1 2[OF True this] show ?thesis
    by(coinduction arbitrary: xs ys)(auto dest: llist_all2_lnullD llist_all2_lhdD intro: llist_all2_ltlI simp add: lappend_eq_LNil_iff)
next
  case False
  with 1 have "\<not> lfinite ys" by(auto dest: llist_all2_lfiniteD)
  with False 1 show ?thesis by(simp add: lappend_inf)
qed

lemma llist_all2_lappend1D:
  assumes all: "llist_all2 P (lappend xs xs') ys"
  shows "llist_all2 P xs (ltake (llength xs) ys)" 
  and "lfinite xs \<Longrightarrow> llist_all2 P xs' (ldrop (llength xs) ys)"
proof -
  from all have len: "llength xs + llength xs' = llength ys" by(auto dest: llist_all2_llengthD)
  hence len_xs: "llength xs \<le> llength ys" and len_xs': "llength xs' \<le> llength ys"
    by (metis enat_le_plus_same llength_lappend)+

  show "llist_all2 P xs (ltake (llength xs) ys)"
  proof(rule llist_all2_all_lnthI)
    show "llength xs = llength (ltake (llength xs) ys)"
      using len_xs by(simp add: min_def)
  next
    fix n
    assume n: "enat n < llength xs"
    also have "\<dots> \<le> llength (lappend xs xs')" by(simp add: enat_le_plus_same)
    finally have "P (lnth (lappend xs xs') n) (lnth ys n)"
      using all by -(rule llist_all2_lnthD)
    also from n have "lnth ys n = lnth (ltake (llength xs) ys) n" by(rule lnth_ltake[symmetric])
    also from n have "lnth (lappend xs xs') n = lnth xs n" by(simp add: lnth_lappend1)
    finally show "P (lnth xs n) (lnth (ltake (llength xs) ys) n)" .
  qed

  assume fin: "lfinite xs"
  then obtain n where n: "llength xs = enat n" unfolding lfinite_conv_llength_enat by blast

  show "llist_all2 P xs' (ldrop (llength xs) ys)"
  proof(rule llist_all2_all_lnthI)
    show "llength xs' = llength (ldrop (llength xs) ys)"
      using n len by(cases "llength xs'")(cases "llength ys", simp_all)
  next
    fix n'
    assume "enat n' < llength xs'"
    hence nn': "enat (n + n') < llength (lappend xs xs')" using n
      by(cases "llength xs'")simp_all
    hence "P (lnth (lappend xs xs') (n + n')) (lnth ys (n + n'))"
      using all by -(rule llist_all2_lnthD)
    also have "lnth (lappend xs xs') (n + n') = lnth xs' n'"
      using n by(simp add: lnth_lappend2)
    also have "lnth ys (n + n') = lnth (ldrop (llength xs) ys) n'"
      using n nn' len by(simp add: add_ac)
    finally show "P (lnth xs' n') (lnth (ldrop (llength xs) ys) n')" .
  qed
qed

lemma lmap_eq_lmap_conv_llist_all2:
  "lmap f xs = lmap g ys \<longleftrightarrow> llist_all2 (\<lambda>x y. f x = g y) xs ys" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by(coinduction arbitrary: xs ys)(auto simp add: neq_LNil_conv lnull_def LNil_eq_lmap lmap_eq_LNil)
next
  assume ?rhs
  thus ?lhs
    by(coinduction arbitrary: xs ys)(auto dest: llist_all2_lnullD llist_all2_lhdD llist_all2_ltlI)
qed

lemma llist_all2_expand:
  "\<lbrakk> lnull xs \<longleftrightarrow> lnull ys; 
     \<lbrakk> \<not> lnull xs; \<not> lnull ys \<rbrakk> \<Longrightarrow> P (lhd xs) (lhd ys) \<and> llist_all2 P (ltl xs) (ltl ys) \<rbrakk>
   \<Longrightarrow> llist_all2 P xs ys"
by(cases xs)(auto simp add: not_lnull_conv)

lemma llist_all2_llength_ltakeWhileD:
  assumes major: "llist_all2 P xs ys"
  and Q: "\<And>x y. P x y \<Longrightarrow> Q1 x \<longleftrightarrow> Q2 y"
  shows "llength (ltakeWhile Q1 xs) = llength (ltakeWhile Q2 ys)"
using major
by(coinduction arbitrary: xs ys rule: enat_coinduct)(auto 4 3 simp add: not_lnull_conv llist_all2_LCons1 llist_all2_LCons2 dest!: Q)

lemma llist_all2_lzipI:
  "\<lbrakk> llist_all2 P xs ys; llist_all2 P' xs' ys' \<rbrakk>
  \<Longrightarrow> llist_all2 (prod_rel P P') (lzip xs xs') (lzip ys ys')"
by(coinduction arbitrary: xs xs' ys ys')(auto 6 6 dest: llist_all2_lhdD llist_all2_lnullD intro: llist_all2_ltlI)

lemma llist_all2_ltakeI:
  "llist_all2 P xs ys \<Longrightarrow> llist_all2 P (ltake n xs) (ltake n ys)"
by(auto simp add: llist_all2_conv_all_lnth lnth_ltake)

lemma llist_all2_ldropnI:
  "llist_all2 P xs ys \<Longrightarrow> llist_all2 P (ldropn n xs) (ldropn n ys)"
by(cases "llength ys")(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_ldropI:
  "llist_all2 P xs ys \<Longrightarrow> llist_all2 P (ldrop n xs) (ldrop n ys)"
by(cases n)(auto simp add: llist_all2_ldropnI)

lemma llist_all2_ldropWhileI:
  assumes major: "llist_all2 P xs ys"
  and Q: "\<And>x y. P x y \<Longrightarrow> Q1 x \<longleftrightarrow> Q2 y"
  shows "llist_all2 P (ldropWhile Q1 xs) (ldropWhile Q2 ys)"
proof -
  from major have len_eq: "llength xs = llength ys" by(rule llist_all2_llengthD)
  from major have len_eq': "llength (ltakeWhile Q1 xs) = llength (ltakeWhile Q2 ys)"
    by(rule llist_all2_llength_ltakeWhileD)(rule Q)

  show ?thesis
  proof(cases "lfinite (ltakeWhile Q1 xs)")
    case True
    from major
    have "llist_all2 P (lappend (ltakeWhile Q1 xs) (ldropWhile Q1 xs)) (lappend (ltakeWhile Q2 ys) (ldropWhile Q2 ys))"
      by simp
    with major len_eq' True show ?thesis
      by(auto dest: llist_all2_lappend1D(2) simp add: lfinite_conv_llength_enat ldrop_lappend simp del: lappend_ltakeWhile_ldropWhile)
  next
    case False
    thus ?thesis using major len_eq
      by(clarsimp simp add: lfinite_ltakeWhile)(fastforce simp add: in_lset_conv_lnth ldropWhile_eq_LNil_iff dest!: Q dest: llist_all2_lnthD2)
  qed
qed

lemma llist_all2_same [simp]: "llist_all2 P xs xs \<longleftrightarrow> (\<forall>x\<in>lset xs. P x x)"
by(auto simp add: llist_all2_conv_all_lnth in_lset_conv_lnth Ball_def)

lemma llist_all2_trans:
  "\<lbrakk> llist_all2 P xs ys; llist_all2 P ys zs; transp P \<rbrakk>
  \<Longrightarrow> llist_all2 P xs zs"
apply(rule llist_all2_all_lnthI)
 apply(simp add: llist_all2_llengthD)
apply(frule llist_all2_llengthD)
apply(drule (1) llist_all2_lnthD)
apply(drule llist_all2_lnthD)
 apply simp
apply(erule (2) transpD)
done

subsection {* The last element @{term "llast"} *}

lemma llast_LNil: "llast LNil = undefined"
by(simp add: llast_def zero_enat_def)

lemma llast_LCons: "llast (LCons x xs) = (if lnull xs then x else llast xs)"
by(cases "llength xs")(auto simp add: llast_def eSuc_def zero_enat_def not_lnull_conv split: enat.splits)

lemma llast_linfinite: "\<not> lfinite xs \<Longrightarrow> llast xs = undefined"
by(simp add: llast_def lfinite_conv_llength_enat)

lemma [simp, code]:
  shows llast_singleton: "llast (LCons x LNil) = x"
  and llast_LCons2: "llast (LCons x (LCons y xs)) = llast (LCons y xs)"
by(simp_all add: llast_LCons)

lemma llast_lappend: 
  "llast (lappend xs ys) = (if lnull ys then llast xs else if lfinite xs then llast ys else undefined)"
proof(cases "lfinite xs")
  case True
  hence "\<not> lnull ys \<Longrightarrow> llast (lappend xs ys) = llast ys"
    by(induct rule: lfinite.induct)(simp_all add: llast_LCons)
  with True show ?thesis by(simp add: lappend_lnull2)
next
  case False thus ?thesis by(simp add: llast_linfinite)
qed

lemma llast_lappend_LCons [simp]:
  "lfinite xs \<Longrightarrow> llast (lappend xs (LCons y ys)) = llast (LCons y ys)"
by(simp add: llast_lappend)

lemma llast_ldropn: "enat n < llength xs \<Longrightarrow> llast (ldropn n xs) = llast xs"
proof(induct n arbitrary: xs)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case by(cases xs)(auto simp add: Suc_ile_eq llast_LCons)
qed

lemma llast_ldrop: "n < llength xs \<Longrightarrow> llast (ldrop n xs) = llast xs"
by(cases n)(simp_all add: llast_ldropn)

lemma llast_llist_of [simp]: "llast (llist_of xs) = last xs"
by(induct xs)(auto simp add: last_def zero_enat_def llast_LCons llast_LNil)

lemma llast_conv_lnth: "llength xs = eSuc (enat n) \<Longrightarrow> llast xs = lnth xs n"
by(clarsimp simp add: llast_def zero_enat_def[symmetric] eSuc_enat split: nat.split)

lemma llast_lmap: 
  assumes "lfinite xs" "\<not> lnull xs"
  shows "llast (lmap f xs) = f (llast xs)"
using assms
proof induct
  case (lfinite_LConsI xs)
  thus ?case by(cases xs) simp_all
qed simp

subsection {* Distinct lazy lists @{term "ldistinct"} *}

inductive_simps ldistinct_LCons [code, simp]:
  "ldistinct (LCons x xs)"

lemma ldistinct_LNil_code [code]:
  "ldistinct LNil = True"
by simp

lemma ldistinct_llist_of [simp]:
  "ldistinct (llist_of xs) \<longleftrightarrow> distinct xs"
by(induct xs) auto

lemma ldistinct_coinduct [consumes 1, case_names ldistinct, coinduct pred: ldistinct]:
  assumes "X xs"
  and step: "\<And>xs. \<lbrakk> X xs; \<not> lnull xs \<rbrakk> 
    \<Longrightarrow> lhd xs \<notin> lset (ltl xs) \<and> (X (ltl xs) \<or> ldistinct (ltl xs))"
  shows "ldistinct xs"
using `X xs`
proof(coinduct)
  case (ldistinct xs)
  thus ?case by(cases xs)(auto dest: step)
qed

lemma ldistinct_lappend:
  "ldistinct (lappend xs ys) \<longleftrightarrow> ldistinct xs \<and> (lfinite xs \<longrightarrow> ldistinct ys \<and> lset xs \<inter> lset ys = {})"
  (is "?lhs = ?rhs")
proof(intro iffI conjI strip)
  assume "?lhs"
  thus "ldistinct xs"
    by(coinduct)(auto simp add: not_lnull_conv in_lset_lappend_iff)

  assume "lfinite xs"
  thus "ldistinct ys" "lset xs \<inter> lset ys = {}"
    using `?lhs` by induct simp_all
next
  assume "?rhs"
  thus ?lhs
    by(coinduction arbitrary: xs)(auto simp add: not_lnull_conv in_lset_lappend_iff)
qed

lemma ldistinct_lprefix:
  "\<lbrakk> ldistinct xs; lprefix ys xs \<rbrakk> \<Longrightarrow> ldistinct ys"
by(clarsimp simp add: lprefix_def ldistinct_lappend)

lemma ldistinct_ltake: "ldistinct xs \<Longrightarrow> ldistinct (ltake n xs)"
by (metis ldistinct_lprefix ltake_is_lprefix)

lemma ldistinct_ldropn:
  "ldistinct xs \<Longrightarrow> ldistinct (ldropn n xs)"
by(induct n arbitrary: xs)(simp, case_tac xs, simp_all)

lemma ldistinct_ldrop:
  "ldistinct xs \<Longrightarrow> ldistinct (ldrop n xs)"
by(cases n)(simp_all add: ldistinct_ldropn)

lemma ldistinct_conv_lnth:
  "ldistinct xs \<longleftrightarrow> (\<forall>i j. enat i < llength xs \<longrightarrow> enat j < llength xs \<longrightarrow> i \<noteq> j \<longrightarrow> lnth xs i \<noteq> lnth xs j)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI strip)
  assume "?rhs"
  thus "?lhs"
  proof(coinduct xs)
    case (ldistinct xs)
    from `\<not> lnull xs`
    obtain x xs' where LCons: "xs = LCons x xs'"
      by(auto simp add: not_lnull_conv)
    have "x \<notin> lset xs'"
    proof
      assume "x \<in> lset xs'"
      then obtain j where "enat j < llength xs'" "lnth xs' j = x"
        unfolding lset_conv_lnth by auto
      hence "enat 0 < llength xs" "enat (Suc j) < llength xs" "lnth xs (Suc j) = x" "lnth xs 0 = x" 
        by(simp_all add: LCons Suc_ile_eq zero_enat_def[symmetric])
      thus False by(auto dest: ldistinct(1)[rule_format])
    qed
    moreover {
      fix i j
      assume "enat i < llength xs'" "enat j < llength xs'" "i \<noteq> j"
      hence "enat (Suc i) < llength xs" "enat (Suc j) < llength xs"
        by(simp_all add: LCons Suc_ile_eq)
      with `i \<noteq> j` have "lnth xs (Suc i) \<noteq> lnth xs (Suc j)"
        by(auto dest: ldistinct(1)[rule_format])
      hence "lnth xs' i \<noteq> lnth xs' j" unfolding LCons by simp }
    ultimately show ?case using LCons by simp
  qed
next
  assume "?lhs"
  fix i j
  assume "enat i < llength xs" "enat j < llength xs" "i \<noteq> j"
  thus "lnth xs i \<noteq> lnth xs j"
  proof(induct i j rule: wlog_linorder_le)
    case symmetry thus ?case by simp
  next
    case (le i j)
    from `?lhs` have "ldistinct (ldropn i xs)" by(rule ldistinct_ldropn)
    also note ldropn_Suc_conv_ldropn[symmetric]
    also from le have "i < j" by simp
    hence "lnth xs j \<in> lset (ldropn (Suc i) xs)" using le unfolding in_lset_conv_lnth
      by(cases "llength xs")(auto intro!: exI[where x="j - Suc i"])
    ultimately show ?case using `enat i < llength xs` by auto
  qed
qed

lemma ldistinct_lmap [simp]:
  "ldistinct (lmap f xs) \<longleftrightarrow> ldistinct xs \<and> inj_on f (lset xs)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI conjI)
  assume dist: ?lhs
  thus "ldistinct xs"
    by(coinduct)(auto simp add: not_lnull_conv)

  show "inj_on f (lset xs)"
  proof(rule inj_onI)
    fix x y
    assume "x \<in> lset xs" and "y \<in> lset xs" and "f x = f y"
    then obtain i j
      where "enat i < llength xs" "x = lnth xs i" "enat j < llength xs" "y = lnth xs j"
      unfolding lset_conv_lnth by blast
    with dist `f x = f y` show "x = y"
      unfolding ldistinct_conv_lnth by auto
  qed
next
  assume ?rhs
  thus ?lhs
    by(coinduction arbitrary: xs)(auto simp add: not_lnull_conv)
qed

lemma ldistinct_lzipI1: "ldistinct xs \<Longrightarrow> ldistinct (lzip xs ys)"
by(coinduction arbitrary: xs ys)(auto simp add: not_lnull_conv dest: lset_lzipD1)
  
lemma ldistinct_lzipI2: "ldistinct ys \<Longrightarrow> ldistinct (lzip xs ys)"
by(coinduction arbitrary: xs ys)(auto 4 3 simp add: not_lnull_conv dest: lset_lzipD2)

subsection {* Lexicographic order on lazy lists: @{term "llexord"} *}

lemma llexord_coinduct [consumes 1, case_names llexord, coinduct pred: llexord]:
  assumes X: "X xs ys"
  and step: "\<And>xs ys. \<lbrakk> X xs ys; \<not> lnull xs \<rbrakk> 
    \<Longrightarrow> \<not> lnull ys \<and> 
       (\<not> lnull ys \<longrightarrow> r (lhd xs) (lhd ys) \<or> 
                     lhd xs = lhd ys \<and> (X (ltl xs) (ltl ys) \<or> llexord r (ltl xs) (ltl ys)))"
  shows "llexord r xs ys"
using X
proof(coinduct)
  case (llexord xs ys)
  thus ?case
    by(cases xs ys rule: llist.exhaust[case_product llist.exhaust])(auto dest: step)
qed

lemma llexord_refl [simp, intro!]:
  "llexord r xs xs"
proof -
  def ys == xs
  hence "xs = ys" by simp
  thus "llexord r xs ys"
    by(coinduct xs ys) auto
qed

lemma llexord_LCons_LCons [simp]:
  "llexord r (LCons x xs) (LCons y ys) \<longleftrightarrow> (x = y \<and> llexord r xs ys \<or> r x y)"
by(auto intro: llexord.intros(1,2) elim: llexord.cases)

lemma lnull_llexord [simp]: "lnull xs \<Longrightarrow> llexord r xs ys"
unfolding lnull_def by simp

lemma llexord_LNil_right [simp]:
  "lnull ys \<Longrightarrow> llexord r xs ys \<longleftrightarrow> lnull xs"
by(auto elim: llexord.cases)

lemma llexord_LCons_left:
  "llexord r (LCons x xs) ys \<longleftrightarrow>
   (\<exists>y ys'. ys = LCons y ys' \<and> (x = y \<and> llexord r xs ys' \<or> r x y))"
by(cases ys)(auto elim: llexord.cases)

lemma lprefix_imp_llexord:
  assumes "lprefix xs ys"
  shows "llexord r xs ys"
using assms
by(coinduct)(auto simp add: not_lnull_conv LCons_lprefix_conv)

lemma llexord_empty:
  "llexord (\<lambda>x y. False) xs ys = lprefix xs ys"
proof
  assume "llexord (\<lambda>x y. False) xs ys"
  thus "lprefix xs ys"
    by(coinduct)(auto elim: llexord.cases)
qed(rule lprefix_imp_llexord)

lemma llexord_append_right:
  "llexord r xs (lappend xs ys)"
by(rule lprefix_imp_llexord)(auto simp add: lprefix_def)

lemma llexord_lappend_leftI:
  assumes "llexord r ys zs"
  shows "llexord r (lappend xs ys) (lappend xs zs)"
proof(cases "lfinite xs")
  case True thus ?thesis by induct (simp_all add: assms)
next
  case False thus ?thesis by(simp add: lappend_inf)
qed

lemma llexord_lappend_leftD:
  assumes lex: "llexord r (lappend xs ys) (lappend xs zs)"
  and fin: "lfinite xs"
  and irrefl: "!!x. x \<in> lset xs \<Longrightarrow> \<not> r x x"
  shows "llexord r ys zs"
using fin lex irrefl by(induct) simp_all

lemma llexord_lappend_left:
  "\<lbrakk> lfinite xs; !!x. x \<in> lset xs \<Longrightarrow> \<not> r x x \<rbrakk> 
  \<Longrightarrow> llexord r (lappend xs ys) (lappend xs zs) \<longleftrightarrow> llexord r ys zs"
by(blast intro: llexord_lappend_leftI llexord_lappend_leftD)

lemma antisym_llexord:
  assumes r: "antisymP r"
  and irrefl: "\<And>x. \<not> r x x"
  shows "antisymP (llexord r)"
proof(rule antisymI)
  fix xs ys
  assume "(xs, ys) \<in> {(xs, ys). llexord r xs ys}"
    and "(ys, xs) \<in> {(xs, ys). llexord r xs ys}"
  hence "llexord r xs ys \<and> llexord r ys xs" by auto
  thus "xs = ys"
    by(coinduct rule: llist.coinduct)(auto 4 3 simp add: not_lnull_conv irrefl dest: antisymD[OF r, simplified])
qed

lemma llexord_antisym:
  "\<lbrakk> llexord r xs ys; llexord r ys xs; 
    !!a b. \<lbrakk> r a b; r b a \<rbrakk> \<Longrightarrow> False \<rbrakk> 
  \<Longrightarrow> xs = ys"
using antisymD[OF antisym_llexord, of r xs ys]
by(auto intro: antisymI)

lemma llexord_trans:
  assumes 1: "llexord r xs ys"
  and 2: "llexord r ys zs"
  and trans: "!!a b c. \<lbrakk> r a b; r b c \<rbrakk> \<Longrightarrow> r a c"
  shows "llexord r xs zs"
proof -
  from 1 2 have "\<exists>ys. llexord r xs ys \<and> llexord r ys zs" by blast
  thus ?thesis
    by(coinduct)(auto 4 3 simp add: not_lnull_conv llexord_LCons_left dest: trans)
qed      

lemma trans_llexord:
  "transP r \<Longrightarrow> transP (llexord r)"
by(auto intro!: transI elim: llexord_trans dest: transD)
  
lemma llexord_linear:
  assumes linear: "!!x y. r x y \<or> x = y \<or> r y x"
  shows "llexord r xs ys \<or> llexord r ys xs"
proof(rule disjCI)
  assume "\<not> llexord r ys xs"
  thus "llexord r xs ys"
  proof(coinduct rule: llexord_coinduct)
    case (llexord xs ys)
    show ?case
    proof(cases xs)
      case LNil thus ?thesis using llexord by simp
    next
      case (LCons x xs')
      with `\<not> llexord r ys xs` obtain y ys'
        where ys: "ys = LCons y ys'" "\<not> r y x" "y \<noteq> x \<or> \<not> llexord r ys' xs'"
        by(cases ys) auto
      with `\<not> r y x` linear[of x y] ys LCons show ?thesis by auto
    qed
  qed
qed

lemma llexord_code [code]:
  "llexord r LNil ys = True"
  "llexord r (LCons x xs) LNil = False"
  "llexord r (LCons x xs) (LCons y ys) = (r x y \<or> x = y \<and> llexord r xs ys)"
by auto

lemma llexord_conv:
 "llexord r xs ys \<longleftrightarrow> 
  xs = ys \<or>
  (\<exists>zs xs' y ys'. lfinite zs \<and> xs = lappend zs xs' \<and> ys = lappend zs (LCons y ys') \<and>
                  (xs' = LNil \<or> r (lhd xs') y))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  show ?rhs (is "_ \<or> ?prefix")
  proof(rule disjCI)
    assume "\<not> ?prefix"
    with `?lhs` show "xs = ys"
    proof(coinduction arbitrary: xs ys)
      case (Eq_llist xs ys)
      hence "llexord r xs ys"
        and prefix: "\<And>zs xs' y ys'. \<lbrakk> lfinite zs; xs = lappend zs xs';
                                      ys = lappend zs (LCons y ys') \<rbrakk>
                                     \<Longrightarrow> xs' \<noteq> LNil \<and> \<not> r (lhd xs') y"
        by auto
      from `llexord r xs ys` show ?case
      proof(cases)
        case (llexord_LCons_eq xs' ys' x)
        { fix zs xs'' y ys''
          assume "lfinite zs" "xs' = lappend zs xs''" 
            and "ys' = lappend zs (LCons y ys'')"
          hence "lfinite (LCons x zs)" "xs = lappend (LCons x zs) xs''"
            and "ys = lappend (LCons x zs) (LCons y ys'')"
            using llexord_LCons_eq by simp_all
          hence "xs'' \<noteq> LNil \<and> \<not> r (lhd xs'') y" by(rule prefix) }
        with llexord_LCons_eq show ?thesis by auto
      next
        case (llexord_LCons_less x y xs' ys')
        with prefix[of LNil xs y ys'] show ?thesis by simp
      next
        case llexord_LNil
        thus ?thesis using prefix[of LNil xs "lhd ys" "ltl ys"]
          by(cases ys) simp_all
      qed
    qed
  qed
next
  assume ?rhs
  thus ?lhs
  proof(coinduct xs ys)
    case (llexord xs ys)
    show ?case
    proof(cases xs)
      case LNil thus ?thesis using llexord by simp
    next
      case (LCons x xs')
      with llexord obtain y ys' where "ys = LCons y ys'"
        by(cases ys)(auto dest: sym simp add: LNil_eq_lappend_iff)
      show ?thesis
      proof(cases "x = y")
        case True
        from llexord(1) show ?thesis
        proof
          assume "xs = ys"
          with True LCons `ys = LCons y ys'` show ?thesis by simp
        next
          assume "\<exists>zs xs' y ys'. lfinite zs \<and> xs = lappend zs xs' \<and>
                                 ys = lappend zs (LCons y ys') \<and>
                                 (xs' = LNil \<or> r (lhd xs') y)"
          then obtain zs xs' y' ys''
            where "lfinite zs" "xs = lappend zs xs'"
            and "ys = lappend zs (LCons y' ys'')"
            and "xs' = LNil \<or> r (lhd xs') y'" by blast
          with True LCons `ys = LCons y ys'`
          show ?thesis by(cases zs) auto
        qed
      next
        case False
        with LCons llexord `ys = LCons y ys'`
        have "r x y" by(fastforce elim: lfinite.cases)
        with LCons `ys = LCons y ys'` show ?thesis by auto
      qed
    qed
  qed
qed

lemma llexord_conv_ltake_index:
  "llexord r xs ys \<longleftrightarrow>
   (llength xs \<le> llength ys \<and> ltake (llength xs) ys = xs) \<or>
   (\<exists>n. enat n < min (llength xs) (llength ys) \<and> 
        ltake (enat n) xs = ltake (enat n) ys \<and> r (lnth xs n) (lnth ys n))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs
  thus ?rhs (is "?A \<or> ?B") unfolding llexord_conv
  proof
    assume "xs = ys" thus ?thesis by(simp add: ltake_all)
  next
    assume "\<exists>zs xs' y ys'. lfinite zs \<and> xs = lappend zs xs' \<and>
                           ys = lappend zs (LCons y ys') \<and>
                           (xs' = LNil \<or> r (lhd xs') y)"
    then obtain zs xs' y ys'
      where "lfinite zs" "xs' = LNil \<or> r (lhd xs') y"
      and [simp]: "xs = lappend zs xs'" "ys = lappend zs (LCons y ys')"
      by blast
    show ?thesis
    proof(cases xs')
      case LNil
      hence ?A by(auto intro: enat_le_plus_same simp add: ltake_lappend1 ltake_all)
      thus ?thesis ..
    next
      case LCons
      with `xs' = LNil \<or> r (lhd xs') y` have "r (lhd xs') y" by simp
      from `lfinite zs` obtain zs' where [simp]: "zs = llist_of zs'"
        unfolding lfinite_eq_range_llist_of by blast
      with LCons have "enat (length zs') < min (llength xs) (llength ys)"
        by(auto simp add: less_enat_def eSuc_def split: enat.split)
      moreover have "ltake (enat (length zs')) xs = ltake (enat (length zs')) ys"
        by(simp add: ltake_lappend1)
      moreover have "r (lnth xs (length zs')) (lnth ys (length zs'))"
        using LCons `r (lhd xs') y`
        by(simp add: lappend_llist_of_LCons lnth_lappend1)
      ultimately have ?B by blast
      thus ?thesis ..
    qed
  qed
next
  assume ?rhs (is "?A \<or> ?B")
  thus ?lhs
  proof
    assume ?A thus ?thesis
    proof(coinduct)
      case (llexord xs ys)
      thus ?case by(cases xs, simp)(cases ys, auto)
    qed
  next
    assume "?B"
    then obtain n where len: "enat n < min (llength xs) (llength ys)"
      and takexs: "ltake (enat n) xs = ltake (enat n) ys"
      and r: "r (lnth xs n) (lnth ys n)" by blast
    have "xs = lappend (ltake (enat n) xs) (ldrop (enat n) xs)"
      by(simp only: lappend_ltake_ldrop)
    moreover from takexs len
    have "ys = lappend (ltake (enat n) xs) (LCons (lnth ys n) (ldrop (enat (Suc n)) ys))"
      by(simp add: ldropn_Suc_conv_ldropn)
    moreover from r len
    have "r (lhd (ldrop (enat n) xs)) (lnth ys n)"
      by(simp add: lhd_ldropn)
    moreover have "lfinite (ltake (enat n) xs)" by simp
    ultimately show ?thesis unfolding llexord_conv by blast
  qed
qed

lemma llexord_llist_of:
  "llexord r (llist_of xs) (llist_of ys) \<longleftrightarrow> 
   xs = ys \<or> (xs, ys) \<in> lexord {(x, y). r x y}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  { fix zs xs' y ys'
    assume "lfinite zs" "llist_of xs = lappend zs xs'"
      and "llist_of ys = lappend zs (LCons y ys')"
      and "xs' = LNil \<or> r (lhd xs') y"
    from `lfinite zs` obtain zs' where [simp]: "zs = llist_of zs'"
      unfolding lfinite_eq_range_llist_of by blast
    have "lfinite (llist_of xs)" by simp
    hence "lfinite xs'" unfolding `llist_of xs = lappend zs xs'` by simp
    then obtain XS' where [simp]: "xs' = llist_of XS'"
      unfolding lfinite_eq_range_llist_of by blast
    from `llist_of xs = lappend zs xs'` have [simp]: "xs = zs' @ XS'"
      by(simp add: lappend_llist_of_llist_of)
    have "lfinite (llist_of ys)" by simp
    hence "lfinite ys'" unfolding `llist_of ys = lappend zs (LCons y ys')` by simp
    then obtain YS' where [simp]: "ys' = llist_of YS'"
      unfolding lfinite_eq_range_llist_of by blast
    from `llist_of ys = lappend zs (LCons y ys')` have [simp]: "ys = zs' @ y # YS'"
      by(auto simp add: llist_of.simps(2)[symmetric] lappend_llist_of_llist_of simp del: llist_of.simps(2))
    have "(\<exists>a ys'. ys = xs @ a # ys') \<or>
          (\<exists>zs a b. r a b \<and> (\<exists>xs'. xs = zs @ a # xs') \<and> (\<exists>ys'. ys = zs @ b # ys'))"
      (is "?A \<or> ?B")
    proof(cases xs')
      case LNil thus ?thesis by(auto simp add: llist_of_eq_LNil_conv)
    next
      case (LCons x xs'')
      with `xs' = LNil \<or> r (lhd xs') y`
      have "r (lhd xs') y" by(auto simp add: llist_of_eq_LCons_conv)
      with LCons have ?B by(auto simp add: llist_of_eq_LCons_conv) fastforce
      thus ?thesis ..
    qed
    hence "(xs, ys) \<in> {(x, y). \<exists>a v. y = x @ a # v \<or>
                                    (\<exists>u a b v w. (a, b) \<in> {(x, y). r x y} \<and> 
                                                 x = u @ a # v \<and> y = u @ b # w)}"
      by auto }
  with `?lhs` show ?rhs
    unfolding lexord_def llexord_conv llist_of_inject by blast
next
  assume "?rhs"
  thus ?lhs
  proof
    assume "xs = ys" thus ?thesis by simp
  next
    assume "(xs, ys) \<in> lexord {(x, y). r x y}"
    thus ?thesis
      by(coinduction arbitrary: xs ys)(auto, auto simp add: neq_Nil_conv)
  qed
qed

subsection {* The filter functional on lazy lists: @{term "lfilter"} *}

lemma lfilter_LNil [simp]: "lfilter P LNil = LNil"
by simp

lemma lfilter_LCons [simp]:
  "lfilter P (LCons x xs) = (if P x then LCons x (lfilter P xs) else lfilter P xs)"
by(rule llist.expand)(auto simp add: lfilter_def)

lemmas lfilter_code [code] = lfilter_LNil lfilter_LCons

lemma lfilter_LCons_seek: "~ (p x) ==> lfilter p (LCons x l) = lfilter p l"
by simp

lemma lfilter_LCons_found:
  "P x \<Longrightarrow> lfilter P (LCons x xs) = LCons x (lfilter P xs)"
by simp

lemma diverge_lfilter_LNil [simp]:
  "\<forall>x\<in>lset xs. \<not> P x \<Longrightarrow> lfilter P xs = LNil"
by(simp add: lfilter_def)

lemmas lfilter_False = diverge_lfilter_LNil

lemma lnull_lfilter [simp]: "lnull (lfilter P xs) \<longleftrightarrow> (\<forall>x\<in>lset xs. \<not> P x)"
by(simp add: lfilter_def)

lemma lfilter_eq_LNil: "lfilter P xs = LNil \<longleftrightarrow> (\<forall>x\<in>lset xs. \<not> P x)"
using lnull_lfilter unfolding lnull_def .

lemmas lfilter_empty_conv = lfilter_eq_LNil

lemma lhd_lfilter [simp]: "lhd (lfilter P xs) = lhd (ldropWhile (Not \<circ> P) xs)"
by(cases "lnull (ldropWhile (Not \<circ> P) xs)")(simp_all, simp add: lhd_def)

lemma ltl_lfilter: "ltl (lfilter P xs) = lfilter P (ltl (ldropWhile (Not \<circ> P) xs))"
by(cases "lnull (ldropWhile (Not \<circ> P) xs)")(auto split: llist.split simp add: ldropWhile_eq_LNil_iff)

declare lfilter.simps[simp del]

lemma lfilter_eq_LCons:
  assumes "lfilter P xs = LCons x xs'"
  shows "\<exists>xs''. xs' = lfilter P xs'' \<and> ldropWhile (Not \<circ> P) xs = LCons x xs''"
using eq_LConsD[OF assms]
apply(clarsimp simp add: ltl_lfilter)
using assms by(auto 4 3 intro: llist.expand)

lemma lfilter_K_True [simp]: "lfilter (%_. True) xs = xs"
by(coinduction arbitrary: xs)(auto simp add: ltl_lfilter)

lemma lfitler_K_False [simp]: "lfilter (\<lambda>_. False) xs = LNil"
by(simp)

lemma lfilter_lappend_lfinite [simp]:
  "lfinite xs \<Longrightarrow> lfilter P (lappend xs ys) = lappend (lfilter P xs) (lfilter P ys)"
by(induct rule: lfinite.induct) auto

lemma lfinite_lfilterI [simp]: "lfinite xs \<Longrightarrow> lfinite (lfilter P xs)"
by(induct rule: lfinite.induct) simp_all

lemma lset_lfilter [simp]: "lset (lfilter P xs) = {x \<in> lset xs. P x}"
proof
  show "lset (lfilter P xs) \<subseteq> {x \<in> lset xs. P x}"
  proof
    fix x
    assume "x \<in> lset (lfilter P xs)"
    hence "x \<in> lset xs \<and> P x"
    proof(induct ys\<equiv>"lfilter P xs" arbitrary: xs rule: llist_set_induct)
      case find thus ?case
        by(auto simp add: lhd_ldropWhile_in_lset lhd_ldropWhile[where P="Not \<circ> P", simplified] split: llist.split)
    next
      case (step x xs)
      have "x \<in> lset (ltl (ldropWhile (Not \<circ> P) xs)) \<and> P x"
        by(rule step.hyps(3))(simp add: ltl_lfilter)
      thus ?case by(auto dest: in_lset_ltlD in_lset_ldropWhileD)
    qed
    thus "x \<in> {x \<in> lset xs. P x}" by simp
  qed
next
  show "{x \<in> lset xs. P x} \<subseteq> lset (lfilter P xs)"
  proof
    fix x
    assume "x \<in> {x \<in> lset xs. P x}"
    hence "x \<in> lset xs" "P x" by(auto)
    from split_llist[OF `x \<in> lset xs`] obtain ys zs
      where "xs = lappend ys (LCons x zs)" "lfinite ys" by blast
    with `P x` show "x \<in> lset (lfilter P xs)" by(simp add: lset_lappend)
  qed
qed

lemma [simp]:
  shows lhd_ldropWhile_lfilter:
  "lhd (ldropWhile P (lfilter Q xs)) = lhd (ldropWhile (\<lambda>x. P x \<or> \<not> Q x) xs)" (is ?thesis1)
  and ltl_ldropWhile_lfilter:
  "ltl (ldropWhile P (lfilter Q xs)) = lfilter Q (ltl (ldropWhile (\<lambda>x. P x \<or> \<not> Q x) xs))" (is ?thesis2)
proof -
  have "?thesis1 \<and> ?thesis2"
  proof(cases "\<exists>x. x \<in> lset xs \<and> Q x \<and> \<not> P x")
    case True
    then obtain x where "x \<in> lset xs" "Q x" "\<not> P x" by auto
    thus ?thesis by(induct) simp_all
  next
    case False
    hence "lnull (ldropWhile P (lfilter Q xs))" "lnull (ldropWhile (\<lambda>x. P x \<or> \<not> Q x) xs)" by auto
    thus ?thesis unfolding lnull_def by simp
  qed
  thus ?thesis1 ?thesis2 by simp_all
qed

lemma lfilter_lfilter: "lfilter P (lfilter Q xs) = lfilter (\<lambda>x. P x \<and> Q x) xs"
by(coinduction arbitrary: xs)(auto simp add: ltl_lfilter o_def)

lemma lfilter_idem [simp]: "lfilter P (lfilter P xs) = lfilter P xs"
by(simp add: lfilter_lfilter)

lemma lfilter_lmap: "lfilter P (lmap f xs) = lmap f (lfilter (P o f) xs)"
by(coinduction arbitrary: xs)(auto simp add: ldropWhile_lmap o_def ltl_lfilter)

lemma lfilter_llist_of [simp]:
  "lfilter P (llist_of xs) = llist_of (filter P xs)"
by(induct xs) simp_all

lemma lfilter_cong [cong]:
  assumes xsys: "xs = ys"
  and set: "\<And>x. x \<in> lset ys \<Longrightarrow> P x = Q x"
  shows "lfilter P xs = lfilter Q ys"
using set unfolding xsys
by(coinduction arbitrary: ys)(auto simp add: ltl_lfilter dest: in_lset_ldropWhileD in_lset_ltlD)

lemma llength_lfilter_ile:
  "llength (lfilter P xs) \<le> llength xs"
proof(coinduction arbitrary: xs rule: enat_le_coinduct)
  case (le xs)
  { assume xs: "\<not> lnull xs"
    have "\<exists>k. llength (ltl xs) = llength (ltl (ldropWhile (\<lambda>x. \<not> P x) xs)) + k"
    proof(cases "\<exists>x\<in>lset xs. P x")
      case False 
      thus ?thesis by simp
    next
      case True
      let ?xs = "ltakeWhile (\<lambda>x. \<not> P x) xs"
      from True have "lfinite ?xs" by(simp add: lfinite_ltakeWhile)
      then obtain n where "llength ?xs = enat n"
        unfolding lfinite_conv_llength_enat ..
      moreover from xs have "llength xs > enat 0"
        by(auto simp add: neq_LNil_conv zero_enat_def[symmetric])
      moreover have "llength ?xs < llength xs"
        using True by(simp add: llength_ltakeWhile_lt_iff)
      ultimately show ?thesis using True xs
        by(cases "llength xs")(auto simp add: llength_ltl llength_ldropWhile epred_inject gr0_conv_Suc exI[where x="enat n"])
    qed }
  thus ?case by(auto simp add: epred_llength ltl_lfilter lset_lnull)
qed

lemma lfinite_lfilter:
  "lfinite (lfilter P xs) \<longleftrightarrow> 
   lfinite xs \<or> finite {n. enat n < llength xs \<and> P (lnth xs n)}"
proof
  assume "lfinite (lfilter P xs)"
  { assume "\<not> lfinite xs"
    with `lfinite (lfilter P xs)`
    have "finite {n. enat n < llength xs \<and> P (lnth xs n)}"
    proof(induct ys\<equiv>"lfilter P xs" arbitrary: xs rule: lfinite_induct)
      case LNil
      hence "\<forall>x\<in>lset xs. \<not> P x" by(auto)
      hence eq: "{n. enat n < llength xs \<and> P (lnth xs n)} = {}" 
        by(auto simp add: lset_conv_lnth)
      show ?case unfolding eq ..
    next
      case (LCons xs)
      from `\<not> lnull (lfilter P xs)`
      have exP: "\<exists>x\<in>lset xs. P x" by simp
      let ?xs = "ltl (ldropWhile (\<lambda>x. \<not> P x) xs)"
      let ?xs' = "ltakeWhile (\<lambda>x. \<not> P x) xs"
      from exP obtain n where n: "llength ?xs' = enat n"
        using lfinite_conv_llength_enat[of ?xs']
        by(auto simp add: lfinite_ltakeWhile)
      have "finite ({n. enat n < llength ?xs} \<inter> {n. P (lnth ?xs n)})" (is "finite ?A")
        using LCons [[simproc add: finite_Collect]] by(auto simp add: ltl_lfilter lfinite_ldropWhile)
      hence "finite ((\<lambda>m. n + 1 + m) ` ({n. enat n < llength ?xs} \<inter> {n. P (lnth ?xs n)}))"
        (is "finite (?f ` _)")
        by(rule finite_imageI)
      moreover have xs: "xs = lappend ?xs' (LCons (lhd (ldropWhile (\<lambda>x. \<not> P x) xs)) ?xs)"
        using exP by simp
      { fix m
        assume "m < n"
        hence "lnth ?xs' m \<in> lset ?xs'" using n
          unfolding in_lset_conv_lnth by auto
        hence "\<not> P (lnth ?xs' m)" by(auto dest: lset_ltakeWhileD) }
      hence "{n. enat n < llength xs \<and> P (lnth xs n)} \<subseteq> insert (the_enat (llength ?xs')) (?f ` ?A)"
        using n by(subst (1 2) xs)(cases "llength ?xs", auto simp add: lnth_lappend not_less not_le lnth_LCons' eSuc_enat split: split_if_asm intro!: rev_image_eqI)
      ultimately show ?case by(auto intro: finite_subset)
    qed }
  thus "lfinite xs \<or> finite {n. enat n < llength xs \<and> P (lnth xs n)}" by blast
next
  assume "lfinite xs \<or> finite {n. enat n < llength xs \<and> P (lnth xs n)}"
  moreover {
    assume "lfinite xs"
    with llength_lfilter_ile[of P xs] have "lfinite (lfilter P xs)"
      by(auto simp add: lfinite_eq_range_llist_of)
  } moreover {
    assume nfin: "\<not> lfinite xs"
    hence len: "llength xs = \<infinity>" by(rule not_lfinite_llength)
    assume fin: "finite {n. enat n < llength xs \<and> P (lnth xs n)}"
    then obtain m where "{n. enat n < llength xs \<and> P (lnth xs n)} \<subseteq> {..<m}"
      unfolding finite_nat_iff_bounded by auto
    hence "\<And>n. \<lbrakk> m \<le> n; enat n < llength xs \<rbrakk> \<Longrightarrow> \<not> P (lnth xs n)" by auto
    hence "lfinite (lfilter P xs)"
    proof(induct m arbitrary: xs)
      case 0
      hence "lnull (lfilter P xs)" by(auto simp add: in_lset_conv_lnth)
      thus ?case by simp
    next
      case (Suc m)
      { fix n
        assume "m \<le> n" "enat n < llength (ltl xs)"
        hence "Suc m \<le> Suc n" "enat (Suc n) < llength xs"
          by(case_tac [!] xs)(auto simp add: Suc_ile_eq)
        hence "\<not> P (lnth xs (Suc n))" by(rule Suc)
        hence "\<not> P (lnth (ltl xs) n)"
          using `enat n < llength (ltl xs)` by(cases xs) (simp_all) }
      hence "lfinite (lfilter P (ltl xs))" by(rule Suc)
      thus ?case by(cases xs) simp_all
    qed }
  ultimately show "lfinite (lfilter P xs)" by blast
qed

lemma lfilter_eq_LConsD:
  assumes "lfilter P ys = LCons x xs"
  shows "\<exists>us vs. ys = lappend us (LCons x vs) \<and> lfinite us \<and>
                      (\<forall>u\<in>lset us. \<not> P u) \<and> P x \<and> xs = lfilter P vs"
proof -
  let ?us = "ltakeWhile (Not \<circ> P) ys"
    and ?vs = "ltl (ldropWhile (Not \<circ> P) ys)"
  from assms have "\<not> lnull (lfilter P ys)" by auto
  hence exP: "\<exists>x\<in>lset ys. P x" by simp
  from eq_LConsD[OF assms]
  have x: "x = lhd (ldropWhile (Not \<circ> P) ys)"
    and xs: "xs = ltl (lfilter P ys)" by auto
  from exP
  have "ys = lappend ?us (LCons x ?vs)" unfolding x by simp
  moreover have "lfinite ?us" using exP by(simp add: lfinite_ltakeWhile)
  moreover have "\<forall>u\<in>lset ?us. \<not> P u" by(auto dest: lset_ltakeWhileD)
  moreover have "P x" unfolding x o_def
    using exP by(rule lhd_ldropWhile[where P="Not \<circ> P", simplified])
  moreover have "xs = lfilter P ?vs" unfolding xs by(simp add: ltl_lfilter)
  ultimately show ?thesis by blast
qed

lemma lfilter_eq_lappend_lfiniteD:
  assumes "lfilter P xs = lappend ys zs" and "lfinite ys"
  shows "\<exists>us vs. xs = lappend us vs \<and> lfinite us \<and>
                      ys = lfilter P us \<and> zs = lfilter P vs"
using `lfinite ys` `lfilter P xs = lappend ys zs`
proof(induct arbitrary: xs zs)
  case lfinite_LNil
  hence "xs = lappend LNil xs" "LNil = lfilter P LNil" "zs = lfilter P xs"
    by simp_all
  thus ?case by blast
next
  case (lfinite_LConsI ys y)
  note IH = `\<And>xs zs. lfilter P xs = lappend ys zs \<Longrightarrow>
            \<exists>us vs. xs = lappend us vs \<and> lfinite us \<and>
                    ys = lfilter P us \<and> zs = lfilter P vs`
  from `lfilter P xs = lappend (LCons y ys) zs`
  have "lfilter P xs = LCons y (lappend ys zs)" by simp
  from lfilter_eq_LConsD[OF this] obtain us vs
    where xs: "xs = lappend us (LCons y vs)" "lfinite us" 
              "P y" "\<forall>u\<in>lset us. \<not> P u"
    and vs: "lfilter P vs = lappend ys zs" by auto
  from IH[OF vs] obtain us' vs' where "vs = lappend us' vs'" "lfinite us'"
    and "ys = lfilter P us'" "zs = lfilter P vs'" by blast
  with xs show ?case
    by(fastforce simp add: lappend_snocL1_conv_LCons2[symmetric, where ys="lappend us' vs'"]
                           lappend_assoc[symmetric])
qed

lemma ldistinct_lfilterI: "ldistinct xs \<Longrightarrow> ldistinct (lfilter P xs)"
proof(coinduction arbitrary: xs)
  case (ldistinct xs)
  from `\<not> lnull (lfilter P xs)` obtain x ys
    where "lfilter P xs = LCons x ys"
    by(auto simp only: not_lnull_conv)
  with lfilter_eq_LConsD[OF this]
  show ?case using `ldistinct xs` by(auto simp add: ldistinct_lappend)
qed

lemma ldistinct_lfilterD:
  "\<lbrakk> ldistinct (lfilter P xs); enat n < llength xs; enat m < llength xs; P a; lnth xs n = a; lnth xs m = a \<rbrakk> \<Longrightarrow> m = n"
proof(induct n m rule: wlog_linorder_le)
  case symmetry thus ?case by simp
next
  case (le n m)
  thus ?case
  proof(induct n arbitrary: xs m)
    case 0 thus ?case
    proof(cases m)
      case 0 thus ?thesis .
    next
      case (Suc m')
      with 0 show ?thesis
        by(cases xs)(simp_all add: Suc_ile_eq, auto simp add: lset_conv_lnth)
    qed
  next
    case (Suc n)
    from `Suc n \<le> m` obtain m' where m [simp]: "m = Suc m'" by(cases m) simp
    with `Suc n \<le> m` have "n \<le> m'" by simp
    moreover from `enat (Suc n) < llength xs`
    obtain x xs' where xs [simp]: "xs = LCons x xs'" by(cases xs) simp
    from `ldistinct (lfilter P xs)` have "ldistinct (lfilter P xs')" by(simp split: split_if_asm)
    moreover from `enat (Suc n) < llength xs` `enat m < llength xs`
    have "enat n < llength xs'" "enat m' < llength xs'" by(simp_all add: Suc_ile_eq)
    moreover note `P a`
    moreover have "lnth xs' n = a" "lnth xs' m' = a"
      using `lnth xs (Suc n) = a` `lnth xs m = a` by simp_all
    ultimately have "m' = n" by(rule Suc)
    thus ?case by simp
  qed
qed

lemma llist_all2_lfilterI: 
  assumes major: "llist_all2 P xs ys"
  and Q: "\<And>x y. P x y \<Longrightarrow> Q1 x \<longleftrightarrow> Q2 y"
  shows "llist_all2 P (lfilter Q1 xs) (lfilter Q2 ys)"
using major
proof(coinduction arbitrary: xs ys)
  case (LNil xs ys)
  with llist_all2_llengthD[OF this] show ?case
    by(fastforce simp add: in_lset_conv_lnth dest!: Q dest: llist_all2_lnthD2)
next
  case (LCons xs ys)
  from LCons(1)
  have "llength (ltakeWhile (Not \<circ> Q1) xs) = llength (ltakeWhile (Not \<circ> Q2) ys)"
    by(rule llist_all2_llength_ltakeWhileD)(simp add: Q)
  thus ?case using LCons
    by(auto 4 4 del: bexE disjCI simp add: lhd_ldropWhile_conv_lnth enat_the_enat llength_eq_infty_conv_lfinite lfinite_ltakeWhile llength_ltakeWhile_lt_iff Q ltl_lfilter elim!: llist_all2_lnthD2 intro!: llist_all2_ltlI llist_all2_ldropWhileI disjI1)
qed

lemma distinct_filterD:
  "\<lbrakk> distinct (filter P xs); n < length xs; m < length xs; P x; xs ! n = x; xs ! m = x \<rbrakk> \<Longrightarrow> m = n"
using ldistinct_lfilterD[of P "llist_of xs" n m x] by simp

lemma lprefix_lfilterI:
  "lprefix xs ys \<Longrightarrow> lprefix (lfilter P xs) (lfilter P ys)"
unfolding lprefix_def
by(cases "lfinite xs")(auto simp add: lappend_inf intro: lappend_LNil2)

subsection {* Concatenating all lazy lists in a lazy list: @{term "lconcat"} *}

lemma lconcat_LNil [simp, code]: "lconcat LNil = LNil"
by(simp add: lconcat_def)

lemma lnull_lconcat [simp]: "lnull (lconcat xss) \<longleftrightarrow> lset xss \<subseteq> {xs. lnull xs}"
by(auto simp add: lconcat_def)

lemma lconcat_eq_LNil: "lconcat xss = LNil \<longleftrightarrow> lset xss \<subseteq> {LNil}"
using lnull_lconcat[of xss] unfolding lnull_def by blast

lemma lconcat_LCons [simp, code]:
  "lconcat (LCons ys xss) = lappend ys (lconcat xss)"
proof(cases "ys = LNil")
  case True thus ?thesis by(simp add: lconcat_def)
next
  case False thus ?thesis
    by(coinduction arbitrary: ys rule: llist.strong_coinduct)(auto simp add: lconcat_def lappend_lnull1)
qed

lemma lconcat_llist_of:
  "lconcat (llist_of (map llist_of xs)) = llist_of (concat xs)"
by(induct xs)(simp_all add: lappend_llist_of_llist_of)

lemma lhd_lconcat [simp]:
  "\<lbrakk> \<not> lnull xss; \<not> lnull (lhd xss) \<rbrakk> \<Longrightarrow> lhd (lconcat xss) = lhd (lhd xss)"
by(auto simp add: lconcat_def not_lnull_conv)

lemma ltl_lconcat [simp]: 
  "\<lbrakk> \<not> lnull xss; \<not> lnull (lhd xss) \<rbrakk> \<Longrightarrow> ltl (lconcat xss) = lappend (ltl (lhd xss)) (lconcat (ltl xss))"
by(clarsimp simp add: not_lnull_conv)

lemma lmap_lconcat:
  fixes xss :: "'a llist llist"
  shows "lmap f (lconcat xss) = lconcat (lmap (lmap f) xss)"
proof -
  { fix xss :: "'a llist llist"
    assume "\<forall>xs \<in> lset xss. \<not> lnull xs"
    hence "lmap f (lconcat xss) = lconcat (lmap (lmap f) xss)"
    proof(coinduction arbitrary: xss)
      case (Eq_llist xss)
      show ?case
      proof(cases "lset xss \<subseteq> {xs. lnull xs}")
        case False
        hence [simp]: "\<not> lnull xss" unfolding lnull_def by auto
        from False have [simp]: "\<not> lnull (lhd xss)"
          using lhd_in_lset[of xss] Eq_llist by(auto simp del: lhd_in_lset)
        show ?thesis using Eq_llist
          by(cases "lnull (ltl (lhd xss))")(auto 4 5 dest: in_lset_ltlD spec[where x="LCons (ltl (lhd xss)) (ltl xss)"] simp add: lappend_lnull1)
      qed fastforce
    qed }
  note eq = this
  have "lmap f (lconcat (lfilter (\<lambda>xs. \<not> lnull xs) xss)) =
         lconcat (lmap (lmap f) (lfilter (\<lambda>xs. \<not> lnull xs) xss))"
    by(rule eq) simp
  also have "lconcat (lfilter (\<lambda>xs. \<not> lnull xs) xss) = lconcat xss"
    unfolding lconcat_def lfilter_idem ..
  also have "lconcat (lmap (lmap f) (lfilter (\<lambda>xs. \<not> lnull xs) xss)) =
            lconcat (lmap (lmap f) xss)"
    unfolding lconcat_def lfilter_lmap lfilter_lfilter by(simp add: o_def)
  finally show ?thesis .
qed

lemma lconcat_lappend [simp]:
  assumes "lfinite xss"
  shows "lconcat (lappend xss yss) = lappend (lconcat xss) (lconcat yss)"
using assms
by induct (simp_all add: lappend_assoc)

lemma lconcat_eq_LCons_conv:
  "lconcat xss = LCons x xs \<longleftrightarrow>
  (\<exists>xs' xss' xss''. xss = lappend (llist_of xss') (LCons (LCons x xs') xss'') \<and>
                    xs = lappend xs' (lconcat xss'') \<and> set xss' \<subseteq> {xs. lnull xs})"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?rhs"
  then obtain xs' xss' xss''
    where "xss = lappend (llist_of xss') (LCons (LCons x xs') xss'')"
    and "xs = lappend xs' (lconcat xss'')" 
    and "set xss' \<subseteq> {xs. lnull xs}" by blast
  moreover from `set xss' \<subseteq> {xs. lnull xs}`
  have "lnull (lconcat (llist_of xss'))" by simp
  ultimately show ?lhs by(simp add: lappend_lnull1)
next
  assume "?lhs"
  hence "\<not> lnull (lconcat xss)" by simp
  hence "\<not> lset xss \<subseteq> {xs. lnull xs}" by simp
  hence "\<not> lnull (lfilter (\<lambda>xs. \<not> lnull xs) xss)" by(auto)
  then obtain y ys where yys: "lfilter (\<lambda>xs. \<not> lnull xs) xss = LCons y ys"
    unfolding not_lnull_conv by auto
  from lfilter_eq_LConsD[OF this]
  obtain us vs where xss: "xss = lappend us (LCons y vs)" 
    and "lfinite us" 
    and "lset us \<subseteq> {xs. lnull xs}" "\<not> lnull y" 
    and ys: "ys = lfilter (\<lambda>xs. \<not> lnull xs) vs" by blast
  from `lfinite us` obtain us' where [simp]: "us = llist_of us'"
    unfolding lfinite_eq_range_llist_of by blast
  from `lset us \<subseteq> {xs. lnull xs}` have us: "lnull (lconcat us)"
    unfolding lnull_lconcat .
  from `\<not> lnull y` obtain y' ys' where y: "y = LCons y' ys'"
    unfolding not_lnull_conv by blast
  from `?lhs` us have [simp]: "y' = x" "xs = lappend ys' (lconcat vs)" 
    unfolding xss y by(simp_all add: lappend_lnull1)
  from `lset us \<subseteq> {xs. lnull xs}` ys show ?rhs unfolding xss y by simp blast
qed

lemma llength_lconcat_lfinite_conv_sum:
  assumes "lfinite xss"
  shows "llength (lconcat xss) = (\<Sum>i | enat i < llength xss. llength (lnth xss i))"
using assms
proof(induct)
  case lfinite_LNil thus ?case by simp
next
  case (lfinite_LConsI xss xs)
  have "{i. enat i \<le> llength xss} = insert 0 {Suc i|i. enat i < llength xss}"
    by(auto simp add: zero_enat_def[symmetric] Suc_ile_eq gr0_conv_Suc)
  also have "\<dots> = insert 0 (Suc ` {i. enat i < llength xss})" by auto
  also have "0 \<notin> Suc ` {i. enat i < llength xss}" by auto
  moreover from `lfinite xss` have "finite {i. enat i < llength xss}"
    by(rule lfinite_finite_index)
  ultimately show ?case using lfinite_LConsI
    by(simp add: setsum.reindex)
qed

lemma lconcat_lfilter_neq_LNil:
  "lconcat (lfilter (\<lambda>xs. \<not> lnull xs) xss) = lconcat xss"
unfolding lconcat_def by(simp)

lemma llength_lconcat_eqI:
  fixes xss :: "'a llist llist" and yss :: "'a llist llist"
  assumes "llist_all2 (\<lambda>xs ys. llength xs = llength ys) xss yss"
  shows "llength (lconcat xss) = llength (lconcat yss)"
proof -
  def xss' \<equiv> "lfilter (\<lambda>xs. \<not> lnull xs) xss"
    and yss' \<equiv> "lfilter (\<lambda>xs. \<not> lnull xs) yss"
  with assms have "\<forall>xs\<in>lset xss'. \<not> lnull xs" "\<forall>ys\<in>lset yss'. \<not> lnull ys" 
    "llist_all2 (\<lambda>xs ys. llength xs = llength ys) xss' yss'"
    by(auto intro: llist_all2_lfilterI)
  hence "llength (lconcat xss') = llength (lconcat yss')"
  proof(coinduction arbitrary: xss' yss' rule: enat_coinduct2)
    case zero thus ?case by(fastforce simp add: llist_all2_conv_all_lnth lset_conv_lnth)
  next
    case (eSuc xss yss)
    hence [simp]: "\<not> lnull xss" "\<not> lnull yss" by(auto simp add: lset_lnull)
    from eSuc have [simp]: "\<not> lnull (lhd xss)" "\<not> lnull (lhd yss)"
      using lhd_in_lset[of xss] lhd_in_lset[of yss] by auto
    then obtain x xs y ys 
      where x: "lhd xss = LCons x xs"
      and y: "lhd yss = LCons y ys"
      unfolding not_lnull_conv by blast
    from eSuc x y have len: "llength xs = llength ys"
      by(cases xss yss rule: llist.exhaust[case_product llist.exhaust]) simp_all
    show ?case
    proof(cases "lnull xs")
      case True
      with len x y eSuc(1-3) show ?thesis
        by(simp add: epred_llength)(blast dest: in_lset_ltlD intro: llist_all2_ltlI)
    next
      case False
      thus ?thesis using len x y eSuc(1-3)
        apply(intro disjI1)
        apply(rule exI[where x="LCons (ltl (lhd xss)) (ltl xss)"])
        apply(rule exI[where x="LCons (ltl (lhd yss)) (ltl yss)"])
        apply(auto simp add: epred_llength intro: in_lset_ltlD llist_all2_ltlI)
        done
    qed
  qed
  moreover have "lconcat xss' = lconcat xss" "lconcat yss' = lconcat yss"
    by(simp_all add: lconcat_lfilter_neq_LNil xss'_def yss'_def)
  ultimately show ?thesis by simp
qed

lemma lset_lconcat_lfinite:
  assumes fin: "\<forall>xs \<in> lset xss. lfinite xs"
  shows "lset (lconcat xss) = (\<Union>xs\<in>lset xss. lset xs)"
  (is "?lhs = ?rhs")
proof(intro equalityI subsetI)
  fix x
  assume "x \<in> ?lhs"
  thus "x \<in> ?rhs"
  proof(induct "lconcat xss" arbitrary: xss rule: lset_induct)
    case (find yss)
    obtain xs' xss' xss'' where xss: "xss = lappend (llist_of xss') (LCons (LCons x xs') xss'')"
      and "yss = lappend xs' (lconcat xss'')"
      and "set xss' \<subseteq> {xs. lnull xs}"
      using find[symmetric] unfolding lconcat_eq_LCons_conv by blast
    thus ?case by simp
  next
    case (step x' xs yss)
    from `LCons x' xs = lconcat yss`[symmetric]
    obtain xs' xss' xss''
      where "yss = lappend (llist_of xss') (LCons (LCons x' xs') xss'')" 
      and "xs = lappend xs' (lconcat xss'')"
      and "set xss' \<subseteq> {xs. lnull xs}" 
      unfolding lconcat_eq_LCons_conv by blast
    thus ?case
      using `x \<noteq> x'` `xs = lconcat (LCons xs' xss'') \<Longrightarrow> x \<in> (\<Union>xs \<in> lset (LCons xs' xss''). lset xs)`
      by auto
  qed
next
  fix x
  assume "x \<in> ?rhs"
  then obtain xs where "x \<in> lset xs" "xs \<in> lset xss" by blast
  from `xs \<in> lset xss` show "x \<in> ?lhs" using fin
    by(induct)(simp_all add: `x \<in> lset xs`)
qed

lemma lconcat_ltake:
  "lconcat (ltake (enat n) xss) = ltake (\<Sum>i<n. llength (lnth xss i)) (lconcat xss)"
proof(induct n arbitrary: xss)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n)
  show ?case
  proof(cases xss)
    case LNil thus ?thesis by simp
  next
    case (LCons xs xss')
    hence "lconcat (ltake (enat (Suc n)) xss) = lappend xs (lconcat (ltake (enat n) xss'))"
      by(simp add: eSuc_enat[symmetric])
    also have "lconcat (ltake (enat n) xss') = ltake (\<Sum>i<n. llength (lnth xss' i)) (lconcat xss')" by(rule Suc)
    also have "lappend xs \<dots> = ltake (llength xs + (\<Sum>i<n. llength (lnth xss' i))) (lappend xs (lconcat xss'))"
      by(cases "llength xs")(simp_all add: ltake_plus_conv_lappend ltake_lappend1 ltake_all ldropn_lappend2 lappend_inf lfinite_conv_llength_enat)
    also have "(\<Sum>i<n. llength (lnth xss' i)) = (\<Sum>i=1..<Suc n. llength (lnth xss i))"
      by(rule setsum_reindex_cong[symmetric, where f=Suc])(auto simp add: LCons image_iff less_Suc_eq_0_disj)
    also have "llength xs + \<dots> = (\<Sum>i<Suc n. llength (lnth xss i))"
      unfolding atLeast0LessThan[symmetric] LCons
      by(subst (2) setsum_head_upt_Suc) simp_all
    finally show ?thesis using LCons by simp
  qed
qed

lemma lnth_lconcat_conv:
  assumes "enat n < llength (lconcat xss)"
  shows "\<exists>m n'. lnth (lconcat xss) n = lnth (lnth xss m) n' \<and> enat n' < llength (lnth xss m) \<and> 
                enat m < llength xss \<and> enat n = (\<Sum>i<m . llength (lnth xss i)) + enat n'" 
using assms
proof(induct n arbitrary: xss)
  case 0
  hence "\<not> lnull (lconcat xss)" by auto
  then obtain x xs where concat_xss: "lconcat xss = LCons x xs"
    unfolding not_lnull_conv by blast
  then obtain xs' xss' xss'' 
    where xss: "xss = lappend (llist_of xss') (LCons (LCons x xs') xss'')"
    and xs: "xs = lappend xs' (lconcat xss'')" 
    and LNil: "set xss' \<subseteq> {xs. lnull xs}"
    unfolding lconcat_eq_LCons_conv by blast
  from LNil have "lnull (lconcat (llist_of xss'))" by simp
  moreover have [simp]: "lnth xss (length xss') = LCons x xs'"
    unfolding xss by(simp add: lnth_lappend2)
  ultimately have "lnth (lconcat xss) 0 = lnth (lnth xss (length xss')) 0" 
    using concat_xss xss by(simp)
  moreover have "enat 0 < llength (lnth xss (length xss'))"
    by(simp add: zero_enat_def[symmetric])
  moreover have "enat (length xss') < llength xss" unfolding xss 
    by simp
  moreover have "(\<Sum>i < length xss'. llength (lnth xss i)) = (\<Sum>i < length xss'. 0)"
  proof(rule setsum_cong)
    show "{..< length xss'} = {..< length xss'}" by simp
  next
    fix i
    assume "i \<in> {..< length xss'}"
    hence "xss' ! i \<in> set xss'" unfolding in_set_conv_nth by blast
    with LNil have "xss' ! i = LNil" by auto
    moreover from `i \<in> {..< length xss'}` have "lnth xss i = xss' ! i"
      unfolding xss by(simp add: lnth_lappend1)
    ultimately show "llength (lnth xss i) = 0" by simp
  qed
  hence "enat 0 = (\<Sum>i<length xss'. llength (lnth xss i)) + enat 0"
    by(simp add: zero_enat_def[symmetric])
  ultimately show ?case by blast
next
  case (Suc n)
  from `enat (Suc n) < llength (lconcat xss)`
  have "\<not> lnull (lconcat xss)" by auto
  then obtain x xs where concat_xss: "lconcat xss = LCons x xs"
    unfolding not_lnull_conv by blast
  then obtain xs' xss' xss'' where xss: "xss = lappend (llist_of xss') (LCons (LCons x xs') xss'')"
    and xs: "xs = lappend xs' (lconcat xss'')" 
    and LNil: "set xss' \<subseteq> {xs. lnull xs}"
    unfolding lconcat_eq_LCons_conv by blast
  from LNil have concat_xss': "lnull (lconcat (llist_of xss'))" by simp
  from xs have "xs = lconcat (LCons xs' xss'')" by simp
  with concat_xss `enat (Suc n) < llength (lconcat xss)`
  have "enat n < llength (lconcat (LCons xs' xss''))"
    by(simp add: Suc_ile_eq)
  from Suc.hyps[OF this] obtain m n'
    where nth_n: "lnth (lconcat (LCons xs' xss'')) n = lnth (lnth (LCons xs' xss'') m) n'"
    and n': "enat n' < llength (lnth (LCons xs' xss'') m)"
    and m': "enat m < llength (LCons xs' xss'')"
    and n_eq: "enat n = (\<Sum>i < m. llength (lnth (LCons xs' xss'') i)) + enat n'"
    by blast
  from n_eq obtain N where N: "(\<Sum>i < m. llength (lnth (LCons xs' xss'') i)) = enat N"
    and n: "n = N + n'"
    by(cases "\<Sum>i < m. llength (lnth (LCons xs' xss'') i)") simp_all


  { fix i
    assume i: "i < length xss'"
    hence "xss' ! i = LNil" using LNil unfolding set_conv_nth by auto
    hence "lnth xss i = LNil" using i unfolding xss
      by(simp add: lnth_lappend1) }
  note lnth_prefix = this

  show ?case
  proof(cases "m > 0")
    case True
    then obtain m' where [simp]: "m = Suc m'" by(cases m) auto
    have "lnth (lconcat xss) (Suc n) = lnth (lnth xss (m + length xss')) n'"
      using concat_xss' nth_n unfolding xss by(simp add: lnth_lappend2 lappend_lnull1)
    moreover have "enat n' < llength (lnth xss (m + length xss'))"
      using concat_xss' n' unfolding xss by(simp add: lnth_lappend2)
    moreover have "enat (m + length xss') < llength xss"
      using concat_xss' m' unfolding xss
      apply (simp add: Suc_ile_eq)
      apply (simp add: eSuc_enat[symmetric] eSuc_plus_1
        plus_enat_simps(1)[symmetric] del: plus_enat_simps(1))
      done
    moreover have "enat (m + length xss') < llength xss"
      using m' unfolding xss
      apply(simp add: Suc_ile_eq)
      apply (simp add: eSuc_enat[symmetric] eSuc_plus_1
        plus_enat_simps(1)[symmetric] del: plus_enat_simps(1))
      done
    moreover
    { have "(\<Sum>i < m + length xss'. llength (lnth xss i)) =
            (\<Sum>i < length xss'. llength (lnth xss i)) + 
            (\<Sum>i = length xss'..<m + length xss'. llength (lnth xss i))"
        by(subst (1 2) atLeast0LessThan[symmetric])(subst setsum_add_nat_ivl, simp_all)
      also from lnth_prefix have "(\<Sum>i < length xss'. llength (lnth xss i)) = 0" by simp
      also have "{length xss'..<m + length xss'} = {0+length xss'..<m+length xss'}" by auto
      also have "(\<Sum>i = 0 + length xss'..<m + length xss'. llength (lnth xss i)) =
                (\<Sum>i = 0..<m. llength (lnth xss (i + length xss')))"
        by(rule setsum_shift_bounds_nat_ivl)
      also have "\<dots> = (\<Sum>i = 0..<m. llength (lnth (LCons (LCons x xs') xss'') i))"
        unfolding xss by(subst lnth_lappend2) simp+
      also have "\<dots> = eSuc (llength xs') + (\<Sum>i = Suc 0..<m. llength (lnth (LCons (LCons x xs') xss'') i))"
        by(subst setsum_head_upt_Suc) simp_all
      also {
        fix i
        assume "i \<in> {Suc 0..<m}"
        then obtain i' where "i = Suc i'" by(cases i) auto
        hence "llength (lnth (LCons (LCons x xs') xss'') i) = llength (lnth (LCons xs' xss'') i)"
          by simp }
      hence "(\<Sum>i = Suc 0..<m. llength (lnth (LCons (LCons x xs') xss'') i)) =
             (\<Sum>i = Suc 0..<m. llength (lnth (LCons xs' xss'') i))" by(simp)
      also have "eSuc (llength xs') + \<dots> = 1 + (llength (lnth (LCons xs' xss'') 0) + \<dots>)"
        by(simp add: eSuc_plus_1 add_ac)
      also note setsum_head_upt_Suc[symmetric, OF `0 < m`]
      finally have "enat (Suc n) = (\<Sum>i<m + length xss'. llength (lnth xss i)) + enat n'"
        unfolding eSuc_enat[symmetric] n_eq by(simp add: eSuc_plus_1 add_ac atLeast0LessThan) }
    ultimately show ?thesis by blast
  next
    case False
    hence [simp]: "m = 0" by auto
    have "lnth (lconcat xss) (Suc n) = lnth (lnth xss (length xss')) (Suc n')"
      using concat_xss n_eq xs n'
      unfolding xss by(simp add: lnth_lappend1 lnth_lappend2)
    moreover have "enat (Suc n') < llength (lnth xss (length xss'))"
      using concat_xss n' unfolding xss by(simp add: lnth_lappend2 Suc_ile_eq)
    moreover have "enat (length xss') < llength xss" unfolding xss 
      by simp
    moreover from lnth_prefix have "(\<Sum>i<length xss'. llength (lnth xss i)) = 0" by simp
    hence "enat (Suc n) = (\<Sum>i<length xss'. llength (lnth xss i)) + enat (Suc n')"
      using n_eq by simp
    ultimately show ?thesis by blast
  qed
qed

lemma lprefix_lconcatI: 
  assumes "lprefix xss yss"
  shows "lprefix (lconcat xss) (lconcat yss)"
proof(cases "lfinite xss")
  case False thus ?thesis using assms by(simp add: not_lfinite_lprefix_conv_eq)
next
  case True thus ?thesis using assms by(auto simp add: lprefix_def)
qed

lemma lnth_lconcat_ltake:
  assumes "enat w < llength (lconcat (ltake (enat n) xss))"
  shows "lnth (lconcat (ltake (enat n) xss)) w = lnth (lconcat xss) w"
using assms by(auto intro: lprefix_lnthD lprefix_lconcatI)

lemma lfinite_lconcat [simp]:
  "lfinite (lconcat xss) \<longleftrightarrow> lfinite (lfilter (\<lambda>xs. \<not> lnull xs) xss) \<and> (\<forall>xs \<in> lset xss. lfinite xs)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  thus "?rhs" (is "?concl xss")
  proof(induct "lconcat xss" arbitrary: xss)
    case lfinite_LNil[symmetric]
    moreover hence "lnull (lfilter (\<lambda>xs. \<not> lnull xs) xss)"
      by(auto simp add: lconcat_eq_LNil)
    ultimately show ?case by(auto)
  next
    case (lfinite_LConsI xs x)
    from `LCons x xs = lconcat xss`[symmetric]
    obtain xs' xss' xss'' where xss [simp]: "xss = lappend (llist_of xss') (LCons (LCons x xs') xss'')"
      and xs [simp]: "xs = lappend xs' (lconcat xss'')"
      and xss': "set xss' \<subseteq> {xs. lnull xs}" unfolding lconcat_eq_LCons_conv by blast
    have "xs = lconcat (LCons xs' xss'')" by simp
    hence "?concl (LCons xs' xss'')" by(rule lfinite_LConsI)
    thus ?case using `lfinite xs` xss' by(auto split: split_if_asm)
  qed
next
  assume "?rhs"
  then obtain "lfinite (lfilter (\<lambda>xs. \<not> lnull xs) xss)" 
    and "\<forall>xs\<in>lset xss. lfinite xs" ..
  thus ?lhs
  proof(induct "lfilter (\<lambda>xs. \<not> lnull xs) xss" arbitrary: xss)
    case lfinite_LNil
    from `LNil = lfilter (\<lambda>xs. \<not> lnull xs) xss`[symmetric]
    have "lset xss \<subseteq> {xs. lnull xs}" unfolding lfilter_empty_conv by blast
    hence "lnull (lconcat xss)" by(simp)
    thus ?case by(simp)
  next
    case (lfinite_LConsI xs x)
    from lfilter_eq_LConsD[OF `LCons x xs = lfilter (\<lambda>xs. \<not> lnull xs) xss`[symmetric]]
    obtain xss' xss'' where xss [simp]: "xss = lappend xss' (LCons x xss'')"
      and xss': "lfinite xss'" "lset xss' \<subseteq> {xs. lnull xs}"
      and x: "\<not> lnull x"
      and xs [simp]: "xs = lfilter (\<lambda>xs. \<not> lnull xs) xss''" by blast
    moreover
    from `\<forall>xs\<in>lset xss. lfinite xs` xss' have "\<forall>xs\<in>lset xss''. lfinite xs" by auto
    with xs have "lfinite (lconcat xss'')" by(rule lfinite_LConsI)
    ultimately show ?case using `\<forall>xs\<in>lset xss. lfinite xs` by(simp)
  qed
qed

lemma list_of_lconcat:
  assumes "lfinite xss"
  and "\<forall>xs \<in> lset xss. lfinite xs"
  shows "list_of (lconcat xss) = concat (list_of (lmap list_of xss))"
using assms by induct(simp_all add: list_of_lappend)

lemma llist_all2_lconcatI:
  assumes "llist_all2 (llist_all2 A) xss yss"
  shows "llist_all2 A (lconcat xss) (lconcat yss)"
proof -
  def xss' \<equiv> "lfilter (\<lambda>xs. \<not> lnull xs) xss"
    and yss' \<equiv> "lfilter (\<lambda>xs. \<not> lnull xs) yss"
  from assms
  have "llist_all2 (llist_all2 A) xss' yss'"
    unfolding xss'_def yss'_def by(rule llist_all2_lfilterI)(auto dest: llist_all2_lnullD)
  hence "llist_all2 (\<lambda>xs ys. llist_all2 A xs ys \<and> \<not> lnull xs \<and> \<not> lnull ys) xss' yss'"
    (is "llist_all2 ?P xss' yss'")
    unfolding xss'_def yss'_def llist_all2_conj
    by(auto simp add: llist_all2_left llist_all2_right dest: llist_all2_llengthD)
  hence "llist_all2 A (lconcat xss') (lconcat yss')"
  proof(coinduction arbitrary: xss' yss')
    case (LNil xss yss) 
    thus ?case by(cases xss)(auto simp add: llist_all2_LCons1)
  next
    case (LCons xss yss)
    then obtain xs xss' ys yss' 
      where xss: "xss = LCons xs xss'"
      and xs: "\<not> lnull xs"
      and yss: "yss = LCons ys yss'"
      and ys: "\<not> lnull ys"
      and xsys: "llist_all2 A xs ys"
      and rest: "llist_all2 ?P xss' yss'"
      by(cases xss)(auto simp add: llist_all2_LCons1)
    from xsys rest xs ys
    have "\<not> lnull (ltl xs) \<Longrightarrow> llist_all2 ?P (LCons (ltl xs) xss') (LCons (ltl ys) yss')"
      by(auto intro: llist_all2_ltlI simp add: not_lnull_conv llist_all2_LCons1)
    thus ?case using xsys rest xs ys xss yss
      by(cases "lnull (ltl xs)" "lnull (ltl ys)" rule: bool.exhaust[case_product bool.exhaust])
        (auto 4 3 dest: llist_all2_lhdD llist_all2_ltlI llist_all2_lnullD simp add: lappend_lnull1 intro: exI[where x="LCons a c" for a c])
  qed
  thus ?thesis unfolding xss'_def yss'_def lconcat_def by simp
qed

subsection {* Sublist view of a lazy list: @{term "lsublist"} *}

lemma lsublist_empty [simp]: "lsublist xs {} = LNil"
by(auto simp add: lsublist_def split_def lfilter_empty_conv)

lemma lsublist_LNil [simp]: "lsublist LNil A = LNil"
by(simp add: lsublist_def)

lemma lsublist_LCons:
  "lsublist (LCons x xs) A = 
  (if 0 \<in> A then LCons x (lsublist xs {n. Suc n \<in> A}) else lsublist xs {n. Suc n \<in> A})"
proof -
  let ?it = "iterates Suc"
  let ?f = "\<lambda>(x, y). (x, Suc y)"
  { fix n
    have "lzip xs (?it (Suc n)) = lmap ?f (lzip xs (?it n))"
      by(coinduction arbitrary: xs n)(auto)
    hence "lmap fst (lfilter (\<lambda>(x, y). y \<in> A) (lzip xs (?it (Suc n)))) =
           lmap fst (lfilter (\<lambda>(x, y). Suc y \<in> A) (lzip xs (?it n)))"
      by(simp add: lfilter_lmap o_def split_def llist.map_comp) }
  thus ?thesis
    by(auto simp add: lsublist_def)(subst iterates, simp)+
qed

lemma lset_lsublist:
  "lset (lsublist xs I) = {lnth xs i|i. enat i<llength xs \<and> i \<in> I}"
apply(auto simp add: lsublist_def lset_lzip)
apply(rule_tac x="(lnth xs i, i)" in image_eqI)
apply auto
done

lemma lset_lsublist_subset: "lset (lsublist xs I) \<subseteq> lset xs"
by(auto simp add: lset_lsublist in_lset_conv_lnth)

lemma lsublist_singleton [simp]:
  "lsublist (LCons x LNil) A = (if 0 : A then LCons x LNil else LNil)"
by (simp add: lsublist_LCons)

lemma lsublist_upt_eq_ltake [simp]:
  "lsublist xs {..<n} = ltake (enat n) xs"
apply(rule sym)
proof(induct n arbitrary: xs)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n)
  thus ?case 
    by(cases xs)(simp_all add: eSuc_enat[symmetric] lsublist_LCons lessThan_def)
qed

lemma lsublist_llist_of [simp]:
  "lsublist (llist_of xs) A = llist_of (sublist xs A)"
by(induct xs arbitrary: A)(simp_all add: lsublist_LCons sublist_Cons)

lemma llength_lsublist_ile: "llength (lsublist xs A) \<le> llength xs"
proof -
  have "llength (lfilter (\<lambda>(x, y). y \<in> A) (lzip xs (iterates Suc 0))) \<le>
        llength (lzip xs (iterates Suc 0))"
    by(rule llength_lfilter_ile)
  thus ?thesis by(simp add: lsublist_def)
qed

lemma lsublist_lmap [simp]:
  "lsublist (lmap f xs) A = lmap f (lsublist xs A)"
by(simp add: lsublist_def lzip_lmap1 llist.map_comp lfilter_lmap o_def split_def)

lemma lfilter_conv_lsublist: 
  "lfilter P xs = lsublist xs {n. enat n < llength xs \<and> P (lnth xs n)}"
proof -
  have "lsublist xs {n. enat n < llength xs \<and> P (lnth xs n)} =
        lmap fst (lfilter (\<lambda>(x, y). enat y < llength xs \<and> P (lnth xs y)) 
                          (lzip xs (iterates Suc 0)))"
    by(simp add: lsublist_def)
  also have "\<forall>(x, y)\<in>lset (lzip xs (iterates Suc 0)). enat y < llength xs \<and> x = lnth xs y"
    by(auto simp add: lset_lzip)
  hence "lfilter (\<lambda>(x, y). enat y < llength xs \<and> P (lnth xs y)) (lzip xs (iterates Suc 0)) =
         lfilter (P \<circ> fst) (lzip xs (iterates Suc 0))"
    by -(rule lfilter_cong[OF refl], auto)
  also have "lmap fst (lfilter (P \<circ> fst) (lzip xs (iterates Suc 0))) =
            lfilter P (lmap fst (lzip xs (iterates Suc 0)))"
    unfolding lfilter_lmap ..
  also have "lmap fst (lzip xs (iterates Suc 0)) = xs"
    by(simp add: lmap_fst_lzip_conv_ltake ltake_all)
  finally show ?thesis ..
qed

lemma ltake_iterates_Suc:
  "ltake (enat n) (iterates Suc m) = llist_of [m..<n + m]"
proof(induct n arbitrary: m)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n)
  have "ltake (enat (Suc n)) (iterates Suc m) = 
        LCons m (ltake (enat n) (iterates Suc (Suc m)))"
    by(subst iterates)(simp add: eSuc_enat[symmetric])
  also note Suc
  also have "LCons m (llist_of [Suc m..<n + Suc m]) = llist_of [m..<Suc n+m]"
    unfolding llist_of.simps[symmetric]
    by(auto simp del: llist_of.simps simp add: upt_conv_Cons)
  finally show ?case .
qed

lemma lsublist_lappend_lfinite: 
  assumes len: "llength xs = enat k"
  shows "lsublist (lappend xs ys) A = 
         lappend (lsublist xs A) (lsublist ys {n. n + k \<in> A})"
proof -
  let ?it = "iterates Suc"
  from assms have fin: "lfinite xs" by(rule llength_eq_enat_lfiniteD)
  have "lsublist (lappend xs ys) A = 
    lmap fst (lfilter (\<lambda>(x, y). y \<in> A) (lzip (lappend xs ys) (?it 0)))"
    by(simp add: lsublist_def)
  also have "?it 0 = lappend (ltake (enat k) (?it 0)) (ldrop (enat k) (?it 0))"
    by(simp only: lappend_ltake_ldrop)
  also note lzip_lappend
  also note lfilter_lappend_lfinite
  also note lmap_lappend_distrib
  also have "lzip xs (ltake (enat k) (?it 0)) = lzip xs (?it 0)"
    using len by(subst (1 2) lzip_conv_lzip_ltake_min_llength) simp
  also note lsublist_def[symmetric]
  also have "ldrop (enat k) (?it 0) = ?it k"
    by(simp add: ldropn_iterates)
  also { fix n m
    have "?it (n + m) = lmap (\<lambda>n. n + m) (?it n)"
      by(coinduction arbitrary: n)(force)+ }
  from this[of 0 k] have "?it k = lmap (\<lambda>n. n + k) (?it 0)" by simp
  also note lzip_lmap2
  also note lfilter_lmap
  also note llist.map_comp
  also have "fst \<circ> (\<lambda>(x, y). (x, y + k)) = fst" 
    by(simp add: o_def split_def)
  also have "(\<lambda>(x, y). y \<in> A) \<circ> (\<lambda>(x, y). (x, y + k)) = (\<lambda>(x, y). y \<in> {n. n + k \<in> A})"
    by(simp add: fun_eq_iff)
  also note lsublist_def[symmetric]
  finally show ?thesis using len by simp
qed

lemma lsublist_split:
  "lsublist xs A = 
   lappend (lsublist (ltake (enat n) xs) A) (lsublist (ldropn n xs) {m. n + m \<in> A})"
proof(cases "enat n \<le> llength xs")
  case False thus ?thesis by(auto simp add: ltake_all ldropn_all)
next
  case True
  have "xs = lappend (ltake (enat n) xs) (ldrop (enat n) xs)"
    by(simp only: lappend_ltake_ldrop)
  hence "xs = lappend (ltake (enat n) xs) (ldropn n xs)" by simp
  hence "lsublist xs A = lsublist (lappend (ltake (enat n) xs) (ldropn n xs)) A"
    by(simp)
  also note lsublist_lappend_lfinite[where k=n]
  finally show ?thesis using True by(simp add: min_def add_ac)
qed

lemma lsublist_cong:
  assumes "xs = ys" and A: "\<And>n. enat n < llength ys \<Longrightarrow> n \<in> A \<longleftrightarrow> n \<in> B"
  shows "lsublist xs A = lsublist ys B"
proof -
  have "lfilter (\<lambda>(x, y). y \<in> A) (lzip ys (iterates Suc 0)) = 
        lfilter (\<lambda>(x, y). y \<in> B) (lzip ys (iterates Suc 0))"
    by(rule lfilter_cong[OF refl])(auto simp add: lset_lzip A)
  thus ?thesis unfolding `xs = ys` lsublist_def by simp
qed

lemma lsublist_insert:
  assumes n: "enat n < llength xs"
  shows "lsublist xs (insert n A) = 
         lappend (lsublist (ltake (enat n) xs) A) (LCons (lnth xs n) 
                 (lsublist (ldropn (Suc n) xs) {m. Suc (n + m) \<in> A}))"
proof -
  have "lsublist xs (insert n A) = 
        lappend (lsublist (ltake (enat n) xs) (insert n A)) 
                (lsublist (ldropn n xs) {m. n + m \<in> (insert n A)})"
    by(rule lsublist_split)
  also have "lsublist (ltake (enat n) xs) (insert n A) = 
            lsublist (ltake (enat n) xs) A"
    by(rule lsublist_cong[OF refl]) simp
  also { from n obtain X XS where "ldropn n xs = LCons X XS"
      by(cases "ldropn n xs")(auto simp add: ldropn_eq_LNil)
    moreover have "lnth (ldropn n xs) 0 = lnth xs n"
      using n by(simp)
    moreover have "ltl (ldropn n xs) = ldropn (Suc n) xs"
      by(cases xs)(simp_all add: ltl_ldropn)
    ultimately have "ldropn n xs = LCons (lnth xs n) (ldropn (Suc n) xs)" by simp
    hence "lsublist (ldropn n xs) {m. n + m \<in> insert n A} = 
           LCons (lnth xs n) (lsublist (ldropn (Suc n) xs) {m. Suc (n + m) \<in> A})"
      by(simp add: lsublist_LCons) }
  finally show ?thesis .
qed

lemma lfinite_lsublist [simp]:
  "lfinite (lsublist xs A) \<longleftrightarrow> lfinite xs \<or> finite A"
proof
  assume "lfinite (lsublist xs A)"
  hence "lfinite xs \<or> 
         finite {n. enat n < llength xs \<and> (\<lambda>(x, y). y \<in> A) (lnth (lzip xs (iterates Suc 0)) n)}"
    by(simp add: lsublist_def lfinite_lfilter)
  also have "{n. enat n < llength xs \<and> (\<lambda>(x, y). y \<in> A) (lnth (lzip xs (iterates Suc 0)) n)} =
            {n. enat n < llength xs \<and> n \<in> A}" by(auto simp add: lnth_lzip)
  finally show "lfinite xs \<or> finite A"
    by(auto simp add: not_lfinite_llength elim: contrapos_np)
next
  assume "lfinite xs \<or> finite A"
  moreover
  have "{n. enat n < llength xs \<and> (\<lambda>(x, y). y \<in> A) (lnth (lzip xs (iterates Suc 0)) n)} =
        {n. enat n < llength xs \<and> n \<in> A}" by(auto simp add: lnth_lzip)
  ultimately show "lfinite (lsublist xs A)"
    by(auto simp add: lsublist_def lfinite_lfilter)
qed

subsection {* @{term "llist_sum"} *}

context monoid_add begin

lemma llistsum_0 [simp]: "llistsum (lmap (\<lambda>_. 0) xs) = 0"
by(simp add: llistsum_def)

lemma llistsum_llist_of [simp]: "llistsum (llist_of xs) = listsum xs"
by(simp add: llistsum_def)

lemma llistsum_lappend: "\<lbrakk> lfinite xs; lfinite ys \<rbrakk> \<Longrightarrow> llistsum (lappend xs ys) = llistsum xs + llistsum ys"
by(simp add: llistsum_def list_of_lappend)

lemma llistsum_LNil [simp]: "llistsum LNil = 0"
by(simp add: llistsum_def)

lemma llistsum_LCons [simp]: "lfinite xs \<Longrightarrow> llistsum (LCons x xs) = x + llistsum xs"
by(simp add: llistsum_def)

lemma llistsum_inf [simp]: "\<not> lfinite xs \<Longrightarrow> llistsum xs = 0"
by(simp add: llistsum_def)

end

lemma llistsum_mono:
  fixes f :: "'a \<Rightarrow> 'b :: {monoid_add, ordered_ab_semigroup_add}"
  assumes "\<And>x. x \<in> lset xs \<Longrightarrow> f x \<le> g x"
  shows "llistsum (lmap f xs) \<le> llistsum (lmap g xs)"
using assms
by(auto simp add: llistsum_def intro: listsum_mono)

subsection {* 
  Alternative view on @{typ "'a llist"} as datatype 
  with constructors @{term "llist_of"} and @{term "inf_llist"}
*}

lemma lnull_inf_llist [simp]: "\<not> lnull (inf_llist f)"
by(simp add: inf_llist_def)

lemma inf_llist_neq_LNil: "inf_llist f \<noteq> LNil"
using lnull_inf_llist unfolding lnull_def .

lemmas LNil_neq_inf_llist = inf_llist_neq_LNil[symmetric]

lemma lhd_inf_llist [simp]: "lhd (inf_llist f) = f 0"
by(simp add: inf_llist_def)

lemma ltl_inf_llist [simp]: "ltl (inf_llist f) = inf_llist (\<lambda>n. f (Suc n))"
by(simp add: inf_llist_def lmap_iterates[symmetric] llist.map_comp)

lemma inf_llist_rec [code, nitpick_simp]:
  "inf_llist f = LCons (f 0) (inf_llist (\<lambda>n. f (Suc n)))"
by(rule llist.expand) simp_all

lemma lfinite_inf_llist [iff]: "\<not> lfinite (inf_llist f)"
by(simp add: inf_llist_def)

lemma iterates_conv_inf_llist:
  "iterates f a = inf_llist (\<lambda>n. (f ^^ n) a)"
by(coinduction arbitrary: a)(auto simp add: funpow_swap1)

lemma inf_llist_neq_llist_of [simp]:
  "llist_of xs \<noteq> inf_llist f"
   "inf_llist f \<noteq> llist_of xs"
using lfinite_llist_of[of xs] lfinite_inf_llist[of f] by fastforce+

lemma lnth_inf_llist [simp]: "lnth (inf_llist f) n = f n"
proof(induct n arbitrary: f)
  case 0 thus ?case by(subst inf_llist_rec) simp
next
  case (Suc n)
  from Suc[of "\<lambda>n. f (Suc n)"] show ?case
    by(subst inf_llist_rec) simp
qed

lemma inf_llist_lprefix [simp]: "lprefix (inf_llist f) xs \<longleftrightarrow> xs = inf_llist f"
by(auto simp add: not_lfinite_lprefix_conv_eq)

lemma llength_inf_llist [simp]: "llength (inf_llist f) = \<infinity>"
by(simp add: inf_llist_def)

lemma lset_inf_llist [simp]: "lset (inf_llist f) = range f"
by(auto simp add: lset_conv_lnth)

lemma inf_llist_inj [simp]:
  "inf_llist f = inf_llist g \<longleftrightarrow> f = g"
unfolding inf_llist_def lmap_eq_lmap_conv_llist_all2
by(simp add: iterates_conv_inf_llist fun_eq_iff)

lemma inf_llist_lnth [simp]: "\<not> lfinite xs \<Longrightarrow> inf_llist (lnth xs) = xs"
by(coinduction arbitrary: xs)(auto simp add: lnth_0_conv_lhd fun_eq_iff lnth_ltl)

lemma llist_exhaust:
  obtains (llist_of) ys where "xs = llist_of ys"
       | (inf_llist) f where "xs = inf_llist f"
proof(cases "lfinite xs")
  case True
  then obtain ys where "xs = llist_of ys"
    unfolding lfinite_eq_range_llist_of by auto
  thus ?thesis by(rule that)
next
  case False
  hence "xs = inf_llist (lnth xs)" by simp
  thus thesis by(rule that)
qed

lemma lappend_inf_llist [simp]: "lappend (inf_llist f) xs = inf_llist f"
by(simp add: lappend_inf)

lemma lmap_inf_llist [simp]: 
  "lmap f (inf_llist g) = inf_llist (f o g)"
by(simp add: inf_llist_def llist.map_comp)

lemma ltake_enat_inf_llist [simp]:
  "ltake (enat n) (inf_llist f) = llist_of (map f [0..<n])"
by(simp add: inf_llist_def ltake_iterates_Suc)

lemma ldropn_inf_llist [simp]:
  "ldropn n (inf_llist f) = inf_llist (\<lambda>m. f (m + n))"
unfolding inf_llist_def ldropn_lmap ldropn_iterates
by(simp add: iterates_conv_inf_llist o_def)

lemma ldrop_enat_inf_llist:
  "ldrop (enat n) (inf_llist f) = inf_llist (\<lambda>m. f (m + n))"
by simp

lemma lzip_inf_llist_inf_llist [simp]:
  "lzip (inf_llist f) (inf_llist g) = inf_llist (\<lambda>n. (f n, g n))"
by(coinduction arbitrary: f g) auto

lemma lzip_llist_of_inf_llist [simp]:
  "lzip (llist_of xs) (inf_llist f) = llist_of (zip xs (map f [0..<length xs]))"
proof(induct xs arbitrary: f)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "map f [0..<length (x # xs)] = f 0 # map (\<lambda>n. f (Suc n)) [0..<length xs]"
    by(simp add: upt_conv_Cons map_Suc_upt[symmetric] del: upt_Suc)
  with Cons[of "\<lambda>n. f (Suc n)"]
  show ?case by(subst inf_llist_rec)(simp)
qed

lemma lzip_inf_llist_llist_of [simp]:
  "lzip (inf_llist f) (llist_of xs) = llist_of (zip (map f [0..<length xs]) xs)"
proof(induct xs arbitrary: f)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "map f [0..<length (x # xs)] = f 0 # map (\<lambda>n. f (Suc n)) [0..<length xs]"
    by(simp add: upt_conv_Cons map_Suc_upt[symmetric] del: upt_Suc)
  with Cons[of "\<lambda>n. f (Suc n)"]
  show ?case by(subst inf_llist_rec)(simp)
qed

lemma llist_all2_inf_llist [simp]:
  "llist_all2 P (inf_llist f) (inf_llist g) \<longleftrightarrow> (\<forall>n. P (f n) (g n))"
by(simp add: llist_all2_conv_lzip)

lemma llist_all2_llist_of_inf_llist [simp]:
  "\<not> llist_all2 P (llist_of xs) (inf_llist f)"
by(simp add: llist_all2_conv_lzip)

lemma llist_all2_inf_llist_llist_of [simp]:
  "\<not> llist_all2 P (inf_llist f) (llist_of xs)"
by(simp add: llist_all2_conv_lzip)

lemma (in monoid_add) llistsum_infllist: "llistsum (inf_llist f) = 0"
by simp

subsubsection {* Relator and predicator properties *}

definition llist_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool"
where "llist_all P xs = (\<forall>x\<in>lset xs. P x)"

lemmas llist_all2_eq [relator_eq, simp] = llist.rel_eq

lemmas llist_all2_mono2 [relator_mono] = llist.rel_mono

lemmas llist_all2_OO [symmetric, relator_distr] = llist.rel_compp

lemma Domainp_llist [relator_domain]:
  assumes "Domainp A = P"
  shows "Domainp (llist_all2 A) = (llist_all P)"
  unfolding Domainp_iff[abs_def]
proof
  fix xs
  from assms have P: "\<And>x. P x \<longleftrightarrow> (\<exists>y. A x y)"
    by(auto simp add: Domainp_iff[abs_def])

  show "(\<exists>ys. llist_all2 A xs ys) \<longleftrightarrow> llist_all P xs" (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs thus ?rhs
      by(auto 4 3 simp add: llist_all_def in_lset_conv_lnth P dest: llist_all2_lnthD)
  next
    assume ?rhs
    hence "llist_all2 A xs (lmap (\<lambda>x. SOME y. A x y) xs)"
      by(coinduction arbitrary: xs)(auto simp add: llist_all_def P dest: in_lset_ltlD intro: someI)
    thus ?lhs ..
  qed
qed

lemma reflp_llist_all2 [reflexivity_rule]: "reflp R \<Longrightarrow> reflp (llist_all2 R)"
  by (auto intro!: reflpI elim: reflpE simp add: llist_all2_conv_all_lnth)

lemma llist_all2_left_total [reflexivity_rule]:
  assumes "left_total R"
  shows "left_total (llist_all2 R)"
proof (rule left_totalI)
  fix xs
  have *: "\<And>x. R x (SOME y. R x y)"
    using assms by(rule left_totalE)(rule someI_ex)

  have "llist_all2 R xs (lmap (\<lambda>x. SOME y. R x y) xs)"
    by(coinduction arbitrary: xs)(auto simp add: *)
  thus "\<exists>ys. llist_all2 R xs ys" ..
qed

lemma left_unique_llist_all2 [reflexivity_rule]:
  assumes "left_unique A"
  shows "left_unique (llist_all2 A)"
proof(rule left_uniqueI)
  fix xs ys zs
  assume "llist_all2 A xs zs" "llist_all2 A ys zs"
  thus "xs = ys"
    by(coinduction arbitrary: xs ys zs rule: llist.strong_coinduct)(auto simp add: not_lnull_conv llist_all2_LCons1 llist_all2_LCons2 dest: left_uniqueD[OF assms] llist_all2_lnullD)
qed

lemma llist_all2_right_total [transfer_rule]:
  assumes "right_total R"
  shows "right_total (llist_all2 R)"
  unfolding right_total_def
proof
  fix ys
  have *: "\<And>y. R (SOME x. R x y) y"
    using assms unfolding right_total_def by - (rule someI_ex, blast)

  have "llist_all2 R (lmap (\<lambda>y. SOME x. R x y) ys) ys"
    by(coinduction arbitrary: ys)(auto simp add: *)
  thus "\<exists>xs. llist_all2 R xs ys" ..
qed

lemma bi_total_llist_all2 [transfer_rule]:
  "bi_total A \<Longrightarrow> bi_total (llist_all2 A)"
by(simp add: bi_total_conv_left_right llist_all2_right_total llist_all2_left_total)

lemma right_unique_llist_all2 [transfer_rule]:
  assumes "right_unique A"
  shows "right_unique (llist_all2 A)"
proof(rule right_uniqueI)
  fix xs ys zs
  assume "llist_all2 A xs ys" "llist_all2 A xs zs"
  thus "ys = zs"
    by(coinduction arbitrary: xs ys zs rule: llist.strong_coinduct)(auto simp add: not_lnull_conv llist_all2_LCons1 llist_all2_LCons2 dest: right_uniqueD[OF assms] llist_all2_lnullD)
qed

lemma bi_unique_list_all2 [transfer_rule]:
  "bi_unique A \<Longrightarrow> bi_unique (llist_all2 A)"
unfolding bi_unique_conv_left_right
by(simp add: right_unique_llist_all2 left_unique_llist_all2)

lemma llist_all2_invariant_commute [invariant_commute]:
  "llist_all2 (Lifting.invariant P) = Lifting.invariant (llist_all P)" (is "?lhs = ?rhs")
proof(intro ext iffI)
  fix xs ys
  assume "?lhs xs ys"
  moreover hence "llist_all2 op = xs ys"
    by(rule llist_all2_mono)(simp add: Lifting.invariant_def)
  ultimately show "?rhs xs ys" unfolding Lifting.invariant_def
    by(simp add: llist_all_def)
qed(simp add: Lifting.invariant_def llist_all_def)

subsubsection {* Quotient theorem for the Lifting package *}

lemma Quotient_llist [quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (llist_all2 R) (lmap Abs) (lmap Rep) (llist_all2 T)"
unfolding Quotient_alt_def
proof(intro conjI strip)
  from assms have 1: "\<And>x y. T x y \<Longrightarrow> Abs x = y"
    unfolding Quotient_alt_def by simp
  fix xs ys
  assume "llist_all2 T xs ys"
  thus "lmap Abs xs = ys"
    by(coinduction arbitrary: xs ys)(auto simp add: not_lnull_conv 1 dest: llist_all2_lnullD)
next
  from assms have 2: "\<And>x. T (Rep x) x"
    unfolding Quotient_alt_def by simp
  fix xs
  show "llist_all2 T (lmap Rep xs) xs" by(simp add: llist_all2_lmap1 2)
next
  from assms have 3: "R = (\<lambda>x y. T x (Abs x) \<and> T y (Abs y) \<and> Abs x = Abs y)"
    unfolding Quotient_alt_def by(simp add: fun_eq_iff)
  fix xs ys
  show "llist_all2 R xs ys \<longleftrightarrow> llist_all2 T xs (lmap Abs xs) \<and> llist_all2 T ys (lmap Abs ys) \<and> lmap Abs xs = lmap Abs ys"
    unfolding 3 lmap_eq_lmap_conv_llist_all2 by(auto simp add: llist_all2_conv_all_lnth)
qed

subsubsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

lemma set1_pre_llist_transfer [transfer_rule]:
  "(rel_pre_llist A B ===> rel_set A) set1_pre_llist set1_pre_llist"
by(auto simp add: rel_pre_llist_def vimage2p_def fun_rel_def set1_pre_llist_def rel_set_def collect_def sum_set_defs fsts_def sum_rel_def split: sum.split_asm)

lemma set2_pre_llist_transfer [transfer_rule]:
  "(rel_pre_llist A B ===> rel_set B) set2_pre_llist set2_pre_llist"
by(auto simp add: rel_pre_llist_def vimage2p_def fun_rel_def set2_pre_llist_def rel_set_def collect_def sum_set_defs snds_def sum_rel_def split: sum.split_asm)

lemma dtor_llist_transfer [transfer_rule]:
  "(llist_all2 A ===> rel_pre_llist A (llist_all2 A)) dtor_llist dtor_llist"
apply(rule fun_relI)
apply(erule llist_all2_cases)
apply(auto simp add: rel_pre_llist_def vimage2p_def BNF_Comp.id_bnf_comp_def sum_rel_def LNil_def LCons_def llist.dtor_ctor split: sum.split)
done

lemma LNil_transfer [transfer_rule]: "llist_all2 P LNil LNil"
by simp

lemma LCons_transfer [transfer_rule]:
  "(A ===> llist_all2 A ===> llist_all2 A) LCons LCons"
unfolding fun_rel_def by simp

lemma case_llist_transfer [transfer_rule]:
  "(B ===> (A ===> llist_all2 A ===> B) ===> llist_all2 A ===> B)
    case_llist case_llist"
unfolding fun_rel_def by (simp split: llist.split)

lemma unfold_llist_transfer [transfer_rule]:
  "((A ===> op =) ===> (A ===> B) ===> (A ===> A) ===> A ===> llist_all2 B) unfold_llist unfold_llist"
proof(rule fun_relI)+
  fix IS_LNIL1 :: "'a \<Rightarrow> bool" and IS_LNIL2 LHD1 LHD2 LTL1 LTL2 x y
  assume rel: "(A ===> op =) IS_LNIL1 IS_LNIL2" "(A ===> B) LHD1 LHD2" "(A ===> A) LTL1 LTL2"
    and "A x y"
  from `A x y`
  show "llist_all2 B (unfold_llist IS_LNIL1 LHD1 LTL1 x) (unfold_llist IS_LNIL2 LHD2 LTL2 y)"
    apply(coinduction arbitrary: x y)
    using rel by(auto 4 4 elim: fun_relE)
qed

lemma corec_llist_transfer [transfer_rule]:
  "((A ===> op =) ===> (A ===> B) ===> (A ===> op =) ===> (A ===> llist_all2 B) ===> (A ===> A) ===> A ===> llist_all2 B) corec_llist corec_llist"
proof(rule fun_relI)+
  fix IS_LNIL1 :: "'a \<Rightarrow> bool" and IS_LNIL2 LHD1 LHD2
    and STOP1 :: "'a \<Rightarrow> bool" and STOP2 MORE1 MORE2 LTL1 LTL2 x y
  assume [transfer_rule]: "(A ===> op =) IS_LNIL1 IS_LNIL2 " "(A ===> B) LHD1 LHD2"
    "(A ===> op =) STOP1 STOP2" "(A ===> llist_all2 B) MORE1 MORE2" "(A ===> A) LTL1 LTL2"
  assume "A x y"
  thus "llist_all2 B (corec_llist IS_LNIL1 LHD1 STOP1 MORE1 LTL1 x) (corec_llist IS_LNIL2 LHD2 STOP2 MORE2 LTL2 y)"
  proof(coinduction arbitrary: x y)
    case (LNil x y)[transfer_rule]
    show ?case by simp transfer_prover
  next
    case (LCons x y)
    note [transfer_rule] = `A x y`
    have ?lhd by(simp add: LCons[simplified]) transfer_prover
    moreover
    have "STOP1 x = STOP2 y" "llist_all2 B (MORE1 x) (MORE2 y)" "A (LTL1 x) (LTL2 y)" by transfer_prover+
    hence ?ltl by(auto simp add: LCons[simplified])
    ultimately show ?case ..
  qed
qed    

lemma ltl_transfer [transfer_rule]:
  "(llist_all2 A ===> llist_all2 A) ltl ltl"
  unfolding ltl_def[abs_def] by transfer_prover

lemma lset_transfer [transfer_rule]:
  "(llist_all2 A ===> rel_set A) lset lset"
by (intro fun_relI rel_setI) (auto simp only: in_lset_conv_lnth llist_all2_conv_all_lnth Bex_def)

lemma lmap_transfer [transfer_rule]:
  "((A ===> B) ===> llist_all2 A ===> llist_all2 B) lmap lmap"
by(auto simp add: fun_rel_def llist_all2_lmap1 llist_all2_lmap2 elim: llist_all2_mono)

lemma lappend_transfer [transfer_rule]:
  "(llist_all2 A ===> llist_all2 A ===> llist_all2 A) lappend lappend"
by(auto simp add: fun_rel_def intro: llist_all2_lappendI)

lemma iterates_transfer [transfer_rule]:
  "((A ===> A) ===> A ===> llist_all2 A) iterates iterates"
unfolding iterates_def split_def corec_llist_never_stop by transfer_prover

lemma lfinite_transfer [transfer_rule]:
  "(llist_all2 A ===> op =) lfinite lfinite"
by(auto dest: llist_all2_lfiniteD)

lemma llist_of_transfer [transfer_rule]:
  "(list_all2 A ===> llist_all2 A) llist_of llist_of"
unfolding llist_of_def by transfer_prover

lemma llength_transfer [transfer_rule]:
  "(llist_all2 A ===> op =) llength llength"
by(auto dest: llist_all2_llengthD)

lemma ltake_transfer [transfer_rule]:
  "(op = ===> llist_all2 A ===> llist_all2 A) ltake ltake"
by(auto intro: llist_all2_ltakeI)

lemma ldropn_transfer [transfer_rule]:
  "(op = ===> llist_all2 A ===> llist_all2 A) ldropn ldropn"
unfolding ldropn_def[abs_def] by transfer_prover

lemma ldrop_transfer [transfer_rule]:
  "(op = ===> llist_all2 A ===> llist_all2 A) ldrop ldrop"
by(auto intro: llist_all2_ldropI)

lemma ltakeWhile_transfer [transfer_rule]:
  "((A ===> op =) ===> llist_all2 A ===> llist_all2 A) ltakeWhile ltakeWhile"
proof(rule fun_relI)+
  fix P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool" and xs :: "'a llist" and ys :: "'b llist"
  assume PQ: "(A ===> op =) P Q"
  assume "llist_all2 A xs ys"
  thus "llist_all2 A (ltakeWhile P xs) (ltakeWhile Q ys)"
    apply(coinduction arbitrary: xs ys)
    using PQ by(auto 4 4 elim: fun_relE simp add: not_lnull_conv llist_all2_LCons2 llist_all2_LCons1)
qed

lemma ldropWhile_transfer [transfer_rule]:
  "((A ===> op =) ===> llist_all2 A ===> llist_all2 A) ldropWhile ldropWhile"
unfolding ldropWhile_def[abs_def] by transfer_prover

lemma lzip_ltransfer [transfer_rule]:
  "(llist_all2 A ===> llist_all2 B ===> llist_all2 (prod_rel A B)) lzip lzip"
by(auto intro: llist_all2_lzipI)

lemma inf_llist_transfer [transfer_rule]:
  "((op = ===> A) ===> llist_all2 A) inf_llist inf_llist"
unfolding inf_llist_def[abs_def] by transfer_prover

lemma lfilter_transfer [transfer_rule]:
  "((A ===> op =) ===> llist_all2 A ===> llist_all2 A) lfilter lfilter"
by(auto simp add: fun_rel_def intro: llist_all2_lfilterI)

lemma lconcat_transfer [transfer_rule]:
  "(llist_all2 (llist_all2 A) ===> llist_all2 A) lconcat lconcat"
by(auto intro: llist_all2_lconcatI)

lemma lsublist_transfer [transfer_rule]:
  "(llist_all2 A ===> op = ===> llist_all2 A) lsublist lsublist"
unfolding lsublist_def[abs_def] by transfer_prover

lemma llist_all_transfer [transfer_rule]:
  "((A ===> op =) ===> llist_all2 A ===> op =) llist_all llist_all"
  unfolding llist_all_def[abs_def] by transfer_prover

lemma llist_all2_rsp:
  assumes r: "\<forall>x y. R x y \<longrightarrow> (\<forall>a b. R a b \<longrightarrow> S x a = T y b)"
  and l1: "llist_all2 R x y"
  and l2: "llist_all2 R a b"
  shows "llist_all2 S x a = llist_all2 T y b"
proof(cases "llength x = llength a")
  case True
  thus ?thesis using l1 l2
    by(simp add: llist_all2_conv_all_lnth)(blast dest: r[rule_format])
next
  case False
  with llist_all2_llengthD[OF l1] llist_all2_llengthD[OF l2]
  show ?thesis by(simp add: llist_all2_conv_all_lnth)
qed

lemma llist_all2_transfer [transfer_rule]:
  "((R ===> R ===> op =) ===> llist_all2 R ===> llist_all2 R ===> op =) llist_all2 llist_all2"
by (simp add: llist_all2_rsp fun_rel_def)

end

end
