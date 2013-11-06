(*  Title:      Containers/Set_Impl.thy
    Author:     Andreas Lochbihler, KIT
                René Thiemann, UIBK *)

theory Set_Impl imports
  Collection_Enum
  DList_Set
  RBT_Set2
  Closure_Set
  Containers_Generator
begin

section {* Different implementations of sets *}

subsection {* Auxiliary functions *}

text {* A simple quicksort implementation *}

context ord begin

function (sequential) quicksort_acc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  and quicksort_part :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "quicksort_acc ac [] = ac"
| "quicksort_acc ac [x] = x # ac"
| "quicksort_acc ac (x # xs) = quicksort_part ac x [] [] [] xs"
| "quicksort_part ac x lts eqs gts [] = quicksort_acc (eqs @ x # quicksort_acc ac gts) lts"
| "quicksort_part ac x lts eqs gts (z # zs) =
  (if z > x then quicksort_part ac x lts eqs (z # gts) zs
   else if z < x then quicksort_part ac x (z # lts) eqs gts zs
   else quicksort_part ac x lts (z # eqs) gts zs)"
by pat_completeness simp_all

lemma length_quicksort_accp:
  "quicksort_acc_quicksort_part_dom (Inl (ac, xs)) \<Longrightarrow> length (quicksort_acc ac xs) = length ac + length xs"
  and length_quicksort_partp:
  "quicksort_acc_quicksort_part_dom (Inr (ac, x, lts, eqs, gts, zs)) 
  \<Longrightarrow> length (quicksort_part ac x lts eqs gts zs) = length ac + 1 + length lts + length eqs + length gts + length zs"
apply(induct rule: quicksort_acc_quicksort_part.pinduct)
apply(simp_all add: quicksort_acc.psimps quicksort_part.psimps)
done

termination
apply(relation "measure (sum_case (\<lambda>(_, xs). 2 * length xs ^ 2) (\<lambda>(_, _, lts, eqs, gts, zs). 2 * (length lts + length eqs + length gts + length zs) ^ 2 + length zs + 1))")
apply(simp_all add: power2_eq_square add_mult_distrib add_mult_distrib2 length_quicksort_accp)
done

definition quicksort :: "'a list \<Rightarrow> 'a list"
where "quicksort = quicksort_acc []"

lemma set_quicksort_acc [simp]: "set (quicksort_acc ac xs) = set ac \<union> set xs"
  and set_quicksort_part [simp]:
  "set (quicksort_part ac x lts eqs gts zs) =
  set ac \<union> {x} \<union> set lts \<union> set eqs \<union> set gts \<union> set zs"
by(induct ac xs and ac x lts eqs gts zs rule: quicksort_acc_quicksort_part.induct)(auto split: split_if_asm)

lemma set_quicksort [simp]: "set (quicksort xs) = set xs"
by(simp add: quicksort_def)

lemma distinct_quicksort_acc: 
  "distinct (quicksort_acc ac xs) = distinct (ac @ xs)"
  and distinct_quicksort_part:
  "distinct (quicksort_part ac x lts eqs gts zs) = distinct (ac @ [x] @ lts @ eqs @ gts @ zs)"
by(induct ac xs and ac x lts eqs gts zs rule: quicksort_acc_quicksort_part.induct) auto

lemma distinct_quicksort [simp]: "distinct (quicksort xs) = distinct xs"
by(simp add: quicksort_def distinct_quicksort_acc)

end

lemmas [code] =
  ord.quicksort_acc.simps quicksort_acc.simps
  ord.quicksort_part.simps quicksort_part.simps
  ord.quicksort_def quicksort_def

context linorder begin

lemma sorted_quicksort_acc:
  "\<lbrakk> sorted ac; \<forall>x \<in> set xs. \<forall>a \<in> set ac. x < a \<rbrakk>
  \<Longrightarrow> sorted (quicksort_acc ac xs)"
  and sorted_quicksort_part:
  "\<lbrakk> sorted ac; \<forall>y \<in> set lts \<union> {x} \<union> set eqs \<union> set gts \<union> set zs. \<forall>a \<in> set ac. y < a;
     \<forall>y \<in> set lts. y < x; \<forall>y \<in> set eqs. y = x; \<forall>y \<in> set gts. y > x \<rbrakk>
  \<Longrightarrow> sorted (quicksort_part ac x lts eqs gts zs)"
proof(induction ac xs and ac x lts eqs gts zs rule: quicksort_acc_quicksort_part.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by(auto simp add: sorted_Cons)
next
  case 3 thus ?case by simp
next
  case (4 ac x lts eqs gts)
  note ac_greater = `\<forall>y\<in>set lts \<union> {x} \<union> set eqs \<union> set gts \<union> set []. \<forall>a\<in>set ac. y < a`
  have "sorted eqs" "set eqs \<subseteq> {x}" using `\<forall>y\<in>set eqs. y = x` 
    by(induct eqs)(simp_all add: sorted_Cons)
  moreover have "\<forall>y \<in> set ac \<union> set gts. x \<le> y"
    using `\<forall>a\<in>set gts. x < a` ac_greater by auto
  moreover have "sorted (quicksort_acc ac gts)" 
    using `sorted ac` ac_greater by(auto intro: "4.IH")
  ultimately have "sorted (eqs @ x # quicksort_acc ac gts)"
    by(auto simp add: sorted_append sorted_Cons)
  moreover have "\<forall>y\<in>set lts. \<forall>a\<in>set (eqs @ x # quicksort_acc ac gts). y < a"
    using `\<forall>y\<in>set lts. y < x` ac_greater `\<forall>a\<in>set gts. x < a` `\<forall>y\<in>set eqs. y = x`
    by fastforce
  ultimately show ?case by(simp add: "4.IH")
next
  case 5 thus ?case by(simp add: not_less eq_iff)
qed

lemma sorted_quicksort [simp]: "sorted (quicksort xs)"
by(simp add: quicksort_def sorted_quicksort_acc)

lemma insort_key_append1:
  "\<forall>y \<in> set ys. f x < f y \<Longrightarrow> insort_key f x (xs @ ys) = insort_key f x xs @ ys"
proof(induct xs)
  case Nil
  thus ?case by(cases ys) auto
qed simp

lemma insort_key_append2:
  "\<forall>y \<in> set xs. f x > f y \<Longrightarrow> insort_key f x (xs @ ys) = xs @ insort_key f x ys"
by(induct xs) auto

lemma sort_key_append:
  "\<forall>x\<in>set xs. \<forall>y\<in>set ys. f x < f y \<Longrightarrow> sort_key f (xs @ ys) = sort_key f xs @ sort_key f ys"
by(induct xs)(simp_all add: insort_key_append1)

definition single_list :: "'a \<Rightarrow> 'a list" where "single_list a = [a]"

lemma to_single_list: "x # xs = single_list x @ xs"
by(simp add: single_list_def)

lemma sort_snoc: "sort (xs @ [x]) = insort x (sort xs)"
by(induct xs)(simp_all add: insort_left_comm)

lemma sort_append_swap: "sort (xs @ ys) = sort (ys @ xs)"
by(induct xs arbitrary: ys rule: rev_induct)(simp_all add: sort_snoc[symmetric])

lemma sort_append_swap2: "sort (xs @ ys @ zs) = sort (ys @ xs @ zs)"
by(induct xs)(simp_all, subst (1 2) sort_append_swap, simp)


lemma sort_Cons_append_swap: "sort (x # xs) = sort (xs @ [x])"
by(subst sort_append_swap) simp

lemma sort_append_Cons_swap: "sort (ys @ x # xs) = sort (ys @ xs @ [x])"
apply(induct ys)
 apply(simp only: append.simps sort_Cons_append_swap)
apply simp
done

lemma quicksort_acc_conv_sort: 
  "quicksort_acc ac xs = sort xs @ ac"
  and quicksort_part_conv_sort: 
  "\<lbrakk> \<forall>y \<in> set lts. y < x; \<forall>y \<in> set eqs. y = x; \<forall>y \<in> set gts. y > x \<rbrakk> 
  \<Longrightarrow> quicksort_part ac x lts eqs gts zs = sort (lts @ eqs @ gts @ x # zs) @ ac"
proof(induct ac xs and ac x lts eqs gts zs rule: quicksort_acc_quicksort_part.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case 3 thus ?case by simp
next
  case (4 ac x lts eqs gts)
  note eqs = `\<forall>y\<in>set eqs. y = x`
  { fix eqs
    assume "\<forall>y\<in>set eqs. y = x"
    hence "insort x eqs = x # eqs" by(induct eqs) simp_all }
  note [simp] = this
  from eqs have [simp]: "sort eqs = eqs" by(induct eqs) simp_all
  from eqs have [simp]: "eqs @ [x] = x # eqs" by(induct eqs) simp_all

  show ?case using 4
    apply(subst sort_key_append)
     apply(auto 4 3 dest: bspec)[1]
    apply(simp add: append_assoc[symmetric] sort_snoc del: append_assoc)
    apply(subst sort_key_append)
    apply(auto 4 3 simp add: insort_key_append1 dest: bspec)
    done
next
  case (5 ac x lts eqs gts z zs)
  have "\<lbrakk> \<not> z < x; \<not> x < z \<rbrakk> \<Longrightarrow> z = x" by simp
  thus ?case using 5
    apply(simp del: sort_key_simps)
    apply(safe, simp_all del: sort_key_simps add: to_single_list)
      apply(subst sort_append_swap)
      apply(fold append_assoc)
      apply(subst (2) sort_append_swap)
      apply(subst sort_append_swap2)
      apply(unfold append_assoc)
      apply(rule refl)
     apply(subst (1 5) append_assoc[symmetric])
     apply(subst (1 2) sort_append_swap)
     apply(unfold append_assoc)
     apply(subst sort_append_swap2)
     apply(subst (1 2) sort_append_swap)
     apply(unfold append_assoc)
     apply(subst sort_append_swap2)
     apply(rule refl)
    apply(subst (2 6) append_assoc[symmetric])
    apply(subst (2 5) append_assoc[symmetric])
    apply(subst (1 2) sort_append_swap2)
    apply(subst (4) append_assoc)
    apply(subst (2) sort_append_swap2)
    apply simp
    done
qed

lemma quicksort_conv_sort: "quicksort xs = sort xs"
by(simp add: quicksort_def quicksort_acc_conv_sort)

lemma sort_remdups: "sort (remdups xs) = remdups (sort xs)"
by(rule sorted_distinct_set_unique) simp_all

end

text {* Removing duplicates from a sorted list *}

context ord begin

fun remdups_sorted :: "'a list \<Rightarrow> 'a list"
where
  "remdups_sorted [] = []"
| "remdups_sorted [x] = [x]"
| "remdups_sorted (x#y#xs) = (if x < y then x # remdups_sorted (y#xs) else remdups_sorted (y#xs))"

end

lemmas [code] = ord.remdups_sorted.simps

context linorder begin

lemma [simp]:
  assumes "sorted xs"
  shows sorted_remdups_sorted: "sorted (remdups_sorted xs)"
  and set_remdups_sorted: "set (remdups_sorted xs) = set xs"
using assms by(induct xs rule: remdups_sorted.induct)(auto simp add: sorted_Cons)

lemma distinct_remdups_sorted [simp]: "sorted xs \<Longrightarrow> distinct (remdups_sorted xs)"
by(induct xs rule: remdups_sorted.induct)(auto simp add: sorted_Cons)

lemma remdups_sorted_conv_remdups: "sorted xs \<Longrightarrow> remdups_sorted xs = remdups xs"
by(induct xs rule: remdups_sorted.induct)(auto simp add: sorted_Cons)

end

text {* An specialised operation to convert a finite set into a sorted list *}

definition csorted_list_of_set :: "'a :: corder set \<Rightarrow> 'a list"
where [code del]: 
  "csorted_list_of_set A = 
  (if ID CORDER('a) = None \<or> \<not> finite A then undefined else linorder.sorted_list_of_set cless_eq A)"

lemma csorted_list_of_set_set [simp]:
  "\<lbrakk> ID CORDER('a :: corder) = Some (le, lt); linorder.sorted le xs; distinct xs \<rbrakk> 
  \<Longrightarrow> linorder.sorted_list_of_set le (set xs) = xs"
by(simp add: distinct_remdups_id linorder.sorted_list_of_set_sort_remdups[OF ID_corder] linorder.sorted_sort_id[OF ID_corder])

lemma csorted_list_of_set_split:
  fixes A :: "'a :: corder set" shows
  "P (csorted_list_of_set A) \<longleftrightarrow> 
  (\<forall>xs. ID CORDER('a) \<noteq> None \<longrightarrow> finite A \<longrightarrow> A = set xs \<longrightarrow> distinct xs \<longrightarrow> linorder.sorted cless_eq xs \<longrightarrow> P xs) \<and> 
  (ID CORDER('a) = None \<or> \<not> finite A \<longrightarrow> P undefined)"
by(auto simp add: csorted_list_of_set_def linorder.sorted_list_of_set[OF ID_corder])


code_modulename SML
  Set Set_Impl
  Set_Impl Set_Impl

subsection {* Delete code equation with set as constructor *}

lemma [code, code del]:
  "Set.empty = Set.empty" ..

lemma [code, code del]:
  "Set.is_empty = Set.is_empty" ..

lemma is_empty_unfold [code_unfold]:
  "set_eq A {} = Set.is_empty A"
  "set_eq {} A = Set.is_empty A"
by(auto simp add: Set.is_empty_def set_eq_def)

definition is_UNIV :: "'a set \<Rightarrow> bool"
where [code del]: "is_UNIV A \<longleftrightarrow> A = UNIV"

lemma is_UNIV_unfold [code_unfold]: 
  "A = UNIV \<longleftrightarrow> is_UNIV A" 
  "UNIV = A \<longleftrightarrow> is_UNIV A"
  "set_eq A UNIV \<longleftrightarrow> is_UNIV A"
  "set_eq UNIV A \<longleftrightarrow> is_UNIV A"
by(auto simp add: is_UNIV_def set_eq_def)

lemma [code, code del]:
  "uminus_set_inst.uminus_set = uminus_set_inst.uminus_set" ..

lemma [code, code del]:
  "Set.member = Set.member" ..

lemma [code_unfold del, symmetric, code_post del]:
  "x \<in> set xs \<equiv> List.member xs x" 
by(simp add: List.member_def)

lemma [code, code del]:
  "Set.insert = Set.insert" ..

lemma [code, code del]:
  "Set.remove = Set.remove" ..

lemma [code, code del]:
  "UNIV = UNIV" ..

lemma [code, code del]:
  "Set.filter = Set.filter" ..

lemma [code, code del]:
  "image = image" ..

lemma [code, code del]:
  "Set.subset_eq = Set.subset_eq" ..

lemma [code, code del]:
  "Ball = Ball" ..

lemma [code, code del]:
  "Bex = Bex" ..

lemma [code, code del]:
  "Set.union = Set.union" ..

lemma [code, code del]:
  "minus_set_inst.minus_set = minus_set_inst.minus_set" ..

lemma [code, code del]:
  "Set.inter = Set.inter" ..

lemma [code, code del]:
  "card = card" ..

lemma [code, code del]:
  "Set.bind = Set.bind" ..

lemma [code, code del]:
  "the_elem = the_elem" ..

lemma [code, code del]:
  "Pow = Pow" ..

lemma [code, code del]:
  "setsum = setsum" ..

lemma [code, code del]:
  "Product_Type.product = Product_Type.product"  ..

lemma [code, code del]:
  "Id_on = Id_on" ..

lemma [code, code del]:
  "Image = Image" ..

lemma [code, code del]:
  "trancl = trancl" ..

lemma [code, code del]:
  "relcomp = relcomp" ..

lemma [code, code del]:
  "wf = wf" ..

lemma [code, code del]:
  "Min = Min" ..

lemma [code, code del]:
  "Inf_fin = Inf_fin" ..

lemma [code, code del]:
  "INFI = INFI" ..

lemma [code, code del]:
  "Max = Max" ..

lemma [code, code del]:
  "Sup_fin = Sup_fin" ..

lemma [code, code del]:
  "SUPR = SUPR" ..

lemma [code, code del]:
  "(Inf :: 'a set set \<Rightarrow> 'a set) = Inf" ..

lemma [code, code del]:
  "(Sup :: 'a set set \<Rightarrow> 'a set) = Sup" ..

lemma [code, code del]:
  "sorted_list_of_set = sorted_list_of_set" ..

lemma [code, code del]: 
  "List.map_project = List.map_project" ..

lemma [code, code del]:
  "Sup_pred_inst.Sup_pred = Sup_pred_inst.Sup_pred" ..

lemma [code, code del]: "finite = finite" ..
lemma [code, code del]: "Cardinality.finite' = Cardinality.finite'" ..
lemma [code_unfold del, symmetric, code_post del]:
  "finite \<equiv> Cardinality.finite'" by(simp)
declare finite'_def[code]

lemma [code, code del]: "card = card" ..
lemma [code, code del]: "Cardinality.card' = Cardinality.card'" ..
lemma [code_unfold del, symmetric, code_post del]:
  "card \<equiv> Cardinality.card'" by simp
declare card'_def[code]

lemma [code, code del]:
  "Inf_pred_inst.Inf_pred = Inf_pred_inst.Inf_pred" ..

lemma [code, code del]:
  "pred_of_set = pred_of_set" ..

lemma [code, code del]:
  "Cardinality.subset' = Cardinality.subset'" ..

lemma [code, code del]:
  "Cardinality.eq_set = Cardinality.eq_set" ..

lemma [code, code del]:
  "acc = acc" ..

lemma [code, code del]:
  "Bleast = Bleast" ..

lemma [code, code del]:
  "can_select = can_select" ..

subsection {* Set implementations *}

definition Collect_set :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set"
where [simp]: "Collect_set = Collect"

definition DList_set :: "'a :: ceq set_dlist \<Rightarrow> 'a set"
where "DList_set = Collect o DList_Set.member"

definition RBT_set :: "'a :: corder set_rbt \<Rightarrow> 'a set"
where "RBT_set = Collect o RBT_Set2.member"

definition Complement :: "'a set \<Rightarrow> 'a set"
where [simp]: "Complement A = - A"

definition Set_Monad :: "'a list \<Rightarrow> 'a set"
where [simp]: "Set_Monad = set"

code_datatype Collect_set DList_set RBT_set Set_Monad Complement

lemma DList_set_empty [simp]: "DList_set DList_Set.empty = {}"
by(simp add: DList_set_def)

lemma RBT_set_empty [simp]: "RBT_set RBT_Set2.empty = {}"
by(simp add: RBT_set_def)

lemma RBT_set_conv_keys: 
  "ID CORDER('a :: corder) \<noteq> None 
  \<Longrightarrow> RBT_set (t :: 'a set_rbt) = set (RBT_Set2.keys t)"
by(clarsimp simp add: RBT_set_def member_conv_keys)

subsection {* Set operations *}

text {*
  A collection of all the theorems about @{const Complement}.
*}
ML {*
structure Set_Complement_Eqs = Named_Thms
(
  val name = @{binding set_complement_code}
  val description = "Code equations involving set complement"
)
*}
setup {* Set_Complement_Eqs.setup *}

lemma Collect_code [code]:
  fixes P :: "'a :: cenum \<Rightarrow> bool" shows
  "Collect P =
  (case ID CENUM('a) of None \<Rightarrow> Collect_set P
            | Some (enum, _) \<Rightarrow> Set_Monad (filter P enum))"
by(auto split: option.split dest: in_cenum)

lemma finite_code [code]:
  fixes dxs :: "'a :: ceq set_dlist" 
  and rbt :: "'b :: corder set_rbt"
  and A :: "'c :: finite_UNIV set" and P :: "'c \<Rightarrow> bool" shows
  "finite (DList_set dxs) = 
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''finite DList_set: ceq = None'') (\<lambda>_. finite (DList_set dxs))
                 | Some _ \<Rightarrow> True)"
  "finite (RBT_set rbt) =
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''finite RBT_set: corder = None'') (\<lambda>_. finite (RBT_set rbt))
                     | Some _ \<Rightarrow> True)"
  and finite_Complement [set_complement_code]:
  "finite (Complement A) \<longleftrightarrow>
  (if of_phantom (finite_UNIV :: 'c finite_UNIV) then True
   else if finite A then False
   else Code.abort (STR ''finite Complement: infinite set'') (\<lambda>_. finite (Complement A)))"
  and
  "finite (Set_Monad xs) = True"
  "finite (Collect_set P) \<longleftrightarrow>
  of_phantom (finite_UNIV :: 'c finite_UNIV) \<or> Code.abort (STR ''finite Collect_set'') (\<lambda>_. finite (Collect_set P))"
by(auto simp add: DList_set_def RBT_set_def member_conv_keys card_gt_0_iff finite_UNIV split: option.split elim: finite_subset[rotated 1])

lemma card_code [code]:
  fixes dxs :: "'a :: ceq set_dlist" and xs :: "'a list"
  and rbt :: "'b :: corder set_rbt" 
  and A :: "'c :: card_UNIV set" shows
  "card (DList_set dxs) = 
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''card DList_set: ceq = None'') (\<lambda>_. card (DList_set dxs))
                  | Some _ \<Rightarrow> DList_Set.length dxs)"
  "card (RBT_set rbt) = 
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''card RBT_set: corder = None'') (\<lambda>_. card (RBT_set rbt))
                    | Some _ \<Rightarrow> length (RBT_Set2.keys rbt))"
  "card (Set_Monad xs) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''card Set_Monad: ceq = None'') (\<lambda>_. card (Set_Monad xs))
                 | Some eq \<Rightarrow> length (equal_base.list_remdups eq xs))"
  and card_Complement [set_complement_code]:
  "card (Complement A) =
   (let a = card A; s = CARD('c)
    in if s > 0 then s - a 
       else if finite A then 0
       else Code.abort (STR ''card Complement: infinite'') (\<lambda>_. card (Complement A)))" 
by(auto simp add: RBT_set_def member_conv_keys distinct_card DList_set_def Let_def card_UNIV Compl_eq_Diff_UNIV card_Diff_subset_Int card_gt_0_iff finite_subset[of A UNIV] List.card_set dest: Collection_Eq.ID_ceq split: option.split)

lemma is_UNIV_code [code]:
  fixes rbt :: "'a :: {cproper_interval, finite_UNIV} set_rbt" 
  and A :: "'b :: card_UNIV set" shows
  "is_UNIV A \<longleftrightarrow>
   (let a = CARD('b);
        b = card A
    in if a > 0 then a = b
       else if b > 0 then False
       else Code.abort (STR ''is_UNIV called on infinite type and set'') (\<lambda>_. is_UNIV A))"
  (is ?generic)
  "is_UNIV (RBT_set rbt) = 
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''is_UNIV RBT_set: corder = None'') (\<lambda>_. is_UNIV (RBT_set rbt))
                     | Some _ \<Rightarrow> of_phantom (finite_UNIV :: 'a finite_UNIV) \<and> proper_intrvl.exhaustive_fusion cproper_interval rbt_keys_generator (RBT_Set2.init rbt))"
  (is ?rbt)
proof -
  {
    fix leq lt
    assume linorder: "ID CORDER('a) = Some (leq, lt)"
    have "is_UNIV (RBT_set rbt) =
      (finite (UNIV :: 'a set) \<and> proper_intrvl.exhaustive cproper_interval (RBT_Set2.keys rbt))"
      (is "?lhs \<longleftrightarrow> ?rhs")
    proof
      assume ?lhs
      have "finite (UNIV :: 'a set)"
        unfolding `?lhs`[unfolded is_UNIV_def, symmetric]
        using linorder 
        by(simp add: finite_code)
      moreover
      hence "proper_intrvl.exhaustive cproper_interval (RBT_Set2.keys rbt)"
        using linorder `?lhs`
        by(simp add: linorder_proper_interval.exhaustive_correct[OF ID_corder_interval[OF linorder]] sorted_RBT_Set_keys is_UNIV_def RBT_set_conv_keys)
      ultimately show ?rhs ..
    next
      assume ?rhs
      thus ?lhs using linorder
        by(auto simp add: linorder_proper_interval.exhaustive_correct[OF ID_corder_interval[OF linorder]] sorted_RBT_Set_keys is_UNIV_def RBT_set_conv_keys)
    qed }
  thus ?rbt
    by(auto simp add: finite_UNIV proper_intrvl.exhaustive_fusion_def unfoldr_rbt_keys_generator is_UNIV_def split: option.split)

  show ?generic
    by(auto simp add: Let_def is_UNIV_def dest: card_seteq[of UNIV A] dest!: card_ge_0_finite)
qed

lemma is_empty_code [code]:
  fixes dxs :: "'a :: ceq set_dlist" 
  and rbt :: "'b :: corder set_rbt" 
  and A :: "'c set" shows
  "Set.is_empty (Set_Monad xs) \<longleftrightarrow> xs = []"
  "Set.is_empty (DList_set dxs) \<longleftrightarrow> 
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''is_empty DList_set: ceq = None'') (\<lambda>_. Set.is_empty (DList_set dxs))
                  | Some _ \<Rightarrow> DList_Set.null dxs)" (is ?DList_set)
  "Set.is_empty (RBT_set rbt) \<longleftrightarrow> 
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''is_empty RBT_set: corder = None'') (\<lambda>_. Set.is_empty (RBT_set rbt))
                  | Some _ \<Rightarrow> RBT_Set2.is_empty rbt)" (is ?RBT_set)
  and is_empty_Complement [set_complement_code]:
  "Set.is_empty (Complement A) \<longleftrightarrow> is_UNIV A" (is ?Complement)
proof -
  show ?DList_set
    by(clarsimp simp add: DList_set_def Set.is_empty_def DList_Set.member_empty_empty split: option.split)

  show ?RBT_set
    by(clarsimp simp add: RBT_set_def Set.is_empty_def RBT_Set2.member_empty_empty[symmetric] fun_eq_iff simp del: RBT_Set2.member_empty_empty split: option.split)

  show ?Complement
    by(auto simp add: is_UNIV_def Set.is_empty_def)
qed(simp_all add: Set.is_empty_def List.null_def)

lemma Set_insert_code [code]:
  fixes dxs :: "'a :: ceq set_dlist" 
  and rbt :: "'b :: corder set_rbt" shows
  "\<And>x. Set.insert x (Collect_set A) = 
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''insert Collect_set: ceq = None'') (\<lambda>_. Set.insert x (Collect_set A))
                | Some eq \<Rightarrow> Collect_set (equal_base.fun_upd eq A x True))"
  "\<And>x. Set.insert x (Set_Monad xs) = Set_Monad (x # xs)"
  "\<And>x. Set.insert x (DList_set dxs) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''insert DList_set: ceq = None'') (\<lambda>_. Set.insert x (DList_set dxs))
                  | Some _ \<Rightarrow> DList_set (DList_Set.insert x dxs))"
  "\<And>x. Set.insert x (RBT_set rbt) =
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''insert RBT_set: corder = None'') (\<lambda>_. Set.insert x (RBT_set rbt))
                     | Some _ \<Rightarrow> RBT_set (RBT_Set2.insert x rbt))"
  and insert_Complement [set_complement_code]:
  "\<And>x. Set.insert x (Complement X) = Complement (Set.remove x X)"
by(auto split: option.split dest: equal.equal_eq[OF ID_ceq] simp add: DList_set_def DList_Set.member_insert RBT_set_def)

lemma Set_member_code [code]:
  fixes xs :: "'a :: ceq list" shows
  "\<And>x. x \<in> Collect_set A \<longleftrightarrow> A x"
  "\<And>x. x \<in> DList_set dxs \<longleftrightarrow> DList_Set.member dxs x"
  "\<And>x. x \<in> RBT_set rbt \<longleftrightarrow> RBT_Set2.member rbt x"
  and mem_Complement [set_complement_code]:
  "\<And>x. x \<in> Complement X \<longleftrightarrow> x \<notin> X"
  and
  "\<And>x. x \<in> Set_Monad xs \<longleftrightarrow>
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''member Set_Monad: ceq = None'') (\<lambda>_. x \<in> Set_Monad xs)
                 | Some eq \<Rightarrow> equal_base.list_member eq xs x)"
by(auto simp add: DList_set_def RBT_set_def List.member_def split: option.split dest!: Collection_Eq.ID_ceq)

lemma Set_remove_code [code]:
  fixes rbt :: "'a :: corder set_rbt"
  and dxs :: "'b :: ceq set_dlist" shows
  "\<And>x. Set.remove x (Collect_set A) =
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''remove Collect: ceq = None'') (\<lambda>_. Set.remove x (Collect_set A))
                 | Some eq \<Rightarrow> Collect_set (equal_base.fun_upd eq A x False))"
  "\<And>x. Set.remove x (DList_set dxs) = 
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''remove DList_set: ceq = None'') (\<lambda>_. Set.remove x (DList_set dxs))
                  | Some _ \<Rightarrow> DList_set (DList_Set.remove x dxs))"
  "\<And>x. Set.remove x (RBT_set rbt) =
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''remove RBT_set: corder = None'') (\<lambda>_. Set.remove x (RBT_set rbt))
                     | Some _ \<Rightarrow> RBT_set (RBT_Set2.remove x rbt))"
  and remove_Complement [set_complement_code]:
  "\<And>x A. Set.remove x (Complement A) = Complement (Set.insert x A)"
by(auto split: option.split split_if_asm dest: equal.equal_eq[OF ID_ceq] simp add: DList_set_def DList_Set.member_remove RBT_set_def)

lemma Set_uminus_code [code, set_complement_code]:
  "- A = Complement A"
  "- (Collect_set P) = Collect_set (\<lambda>x. \<not> P x)"
  "- (Complement B) = B"
by auto

text {*
  These equations represent complements as true complements.
  If you want that the complement operations returns an explicit enumeration of the elements, use the following set of equations which use @{class cenum}.
*}

lemma Set_uminus_cenum:
  fixes A :: "'a :: cenum set" shows
  "- A =
  (case ID CENUM('a) of None \<Rightarrow> Complement A
            | Some (enum, _) \<Rightarrow> Set_Monad (filter (\<lambda>x. x \<notin> A) enum))"
  and "- (Complement B) = B"
by(auto split: option.split dest: ID_cEnum)

lemma Set_minus_code [code]: "A - B = A \<inter> (- B)"
by(rule Diff_eq)

lemma Set_union_code [code]:
  fixes rbt1 rbt2 :: "'a :: corder set_rbt"
  and rbt :: "'b :: {corder, ceq} set_rbt"
  and dxs :: "'b set_dlist"
  and dxs1 dxs2 :: "'c :: ceq set_dlist" shows
  "RBT_set rbt1 \<union> RBT_set rbt2 =
   (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''union RBT_set RBT_set: corder = None'') (\<lambda>_. RBT_set rbt1 \<union> RBT_set rbt2)
                      | Some _ \<Rightarrow> RBT_set (RBT_Set2.union rbt1 rbt2))" (is ?RBT_set_RBT_set)
  "RBT_set rbt \<union> DList_set dxs =
   (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''union RBT_set DList_set: corder = None'') (\<lambda>_. RBT_set rbt \<union> DList_set dxs)
                      | Some _ \<Rightarrow>
       case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''union RBT_set DList_set: ceq = None'') (\<lambda>_. RBT_set rbt \<union> DList_set dxs)
                      | Some _ \<Rightarrow> RBT_set (DList_Set.fold RBT_Set2.insert dxs rbt))" (is ?RBT_set_DList_set)
  "DList_set dxs \<union> RBT_set rbt =
   (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''union DList_set RBT_set: corder = None'') (\<lambda>_. RBT_set rbt \<union> DList_set dxs)
                      | Some _ \<Rightarrow>
       case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''union DList_set RBT_set: ceq = None'') (\<lambda>_. RBT_set rbt \<union> DList_set dxs)
                      | Some _ \<Rightarrow> RBT_set (DList_Set.fold RBT_Set2.insert dxs rbt))" (is ?DList_set_RBT_set)
  "DList_set dxs1 \<union> DList_set dxs2 = 
   (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''union DList_set DList_set: ceq = None'') (\<lambda>_. DList_set dxs1 \<union> DList_set dxs2)
                      | Some _ \<Rightarrow> DList_set (DList_Set.union dxs1 dxs2))" (is ?DList_set_DList_set)
  "Set_Monad zs \<union> RBT_set rbt2 =
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''union Set_Monad RBT_set: corder = None'') (\<lambda>_. Set_Monad zs \<union> RBT_set rbt2)
                      | Some _ \<Rightarrow> RBT_set (fold RBT_Set2.insert zs rbt2))" (is ?Set_Monad_RBT_set)
  "RBT_set rbt1 \<union> Set_Monad zs =
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''union RBT_set Set_Monad: corder = None'') (\<lambda>_. RBT_set rbt1 \<union> Set_Monad zs)
                      | Some _ \<Rightarrow> RBT_set (fold RBT_Set2.insert zs rbt1))" (is ?RBT_set_Set_Monad)
  "Set_Monad ws \<union> DList_set dxs2 =
  (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''union Set_Monad DList_set: ceq = None'') (\<lambda>_. Set_Monad ws \<union> DList_set dxs2)
                  | Some _ \<Rightarrow> DList_set (fold DList_Set.insert ws dxs2))" (is ?Set_Monad_DList_set)
  "DList_set dxs1 \<union> Set_Monad ws =
  (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''union DList_set Set_Monad: ceq = None'') (\<lambda>_. DList_set dxs1 \<union> Set_Monad ws)
                  | Some _ \<Rightarrow> DList_set (fold DList_Set.insert ws dxs1))" (is ?DList_set_Set_Monad)
  "Set_Monad xs \<union> Set_Monad ys = Set_Monad (xs @ ys)"
  "Collect_set A \<union> B = Collect_set (\<lambda>x. A x \<or> x \<in> B)"
  "B \<union> Collect_set A = Collect_set (\<lambda>x. A x \<or> x \<in> B)"
  and Set_union_Complement [set_complement_code]:
  "Complement B \<union> B' = Complement (B \<inter> - B')"
  "B' \<union> Complement B = Complement (- B' \<inter> B)"
proof -
  show ?RBT_set_RBT_set ?Set_Monad_RBT_set ?RBT_set_Set_Monad
    by(auto split: option.split simp add: RBT_set_def)

  show ?RBT_set_DList_set ?DList_set_RBT_set
    by(auto split: option.split simp add: RBT_set_def DList_set_def DList_Set.fold_def DList_Set.member_def List.member_def dest: equal.equal_eq[OF ID_ceq])

  show ?DList_set_Set_Monad ?Set_Monad_DList_set
    by(auto split: option.split simp add: DList_set_def DList_Set.member_fold_insert)

  show ?DList_set_DList_set 
    by(auto split: option.split simp add: DList_set_def DList_Set.member_union)
qed(auto)

lemma Set_inter_code [code]:
  fixes rbt1 rbt2 :: "'a :: corder set_rbt"
  and rbt :: "'b :: {corder, ceq} set_rbt"
  and dxs :: "'b set_dlist"
  and dxs1 dxs2 :: "'c :: ceq set_dlist" 
  and xs1 xs2 :: "'c list"
  shows
  "Collect_set A'' \<inter> J = Collect_set (\<lambda>x. A'' x \<and> x \<in> J)" (is ?collect1)
  "J \<inter> Collect_set A'' = Collect_set (\<lambda>x. A'' x \<and> x \<in> J)" (is ?collect2)

  "Set_Monad xs'' \<inter> I = Set_Monad (filter (\<lambda>x. x \<in> I) xs'')" (is ?monad1)
  "I \<inter> Set_Monad xs'' = Set_Monad (filter (\<lambda>x. x \<in> I) xs'')" (is ?monad2)

  "DList_set dxs1 \<inter> H =
   (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''inter DList_set1: ceq = None'') (\<lambda>_. DList_set dxs1 \<inter> H)
                  | Some eq \<Rightarrow> DList_set (DList_Set.filter (\<lambda>x. x \<in> H) dxs1))" (is ?dlist1)
  "H \<inter> DList_set dxs2 =
   (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''inter DList_set2: ceq = None'') (\<lambda>_. H \<inter> DList_set dxs2)
                  | Some eq \<Rightarrow> DList_set (DList_Set.filter (\<lambda>x. x \<in> H) dxs2))" (is ?dlist2)

  "RBT_set rbt1 \<inter> G =
   (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''inter RBT_set1: corder = None'') (\<lambda>_. RBT_set rbt1 \<inter> G)
                      | Some _ \<Rightarrow> RBT_set (RBT_Set2.filter (\<lambda>x. x \<in> G) rbt1))" (is ?rbt1)
  "G \<inter> RBT_set rbt2 =
   (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''inter RBT_set2: corder = None'') (\<lambda>_. G \<inter> RBT_set rbt2)
                      | Some _ \<Rightarrow> RBT_set (RBT_Set2.filter (\<lambda>x. x \<in> G) rbt2))" (is ?rbt2)
  and Set_inter_Complement [set_complement_code]:
  "Complement B'' \<inter> Complement B''' = Complement (B'' \<union> B''')" (is ?complement)
  and
  "Set_Monad xs \<inter> RBT_set rbt1 =
   (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''inter Set_Monad RBT_set: corder = None'') (\<lambda>_. RBT_set rbt1 \<inter> Set_Monad xs)
                      | Some _ \<Rightarrow> RBT_set (RBT_Set2.inter_list rbt1 xs))" (is ?monad_rbt)
  "Set_Monad xs' \<inter> DList_set dxs2 =
   (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''inter Set_Monad DList_set: ceq = None'') (\<lambda>_. Set_Monad xs' \<inter> DList_set dxs2)
                  | Some eq \<Rightarrow> DList_set (DList_Set.filter (equal_base.list_member eq xs') dxs2))" (is ?monad_dlist)
  "Set_Monad xs1 \<inter> Set_Monad xs2 =
  (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''inter Set_Monad Set_Monad: ceq = None'') (\<lambda>_. Set_Monad xs1 \<inter> Set_Monad xs2)
                 | Some eq \<Rightarrow> Set_Monad (filter (equal_base.list_member eq xs2) xs1))" (is ?monad)

  "DList_set dxs \<inter> RBT_set rbt = 
   (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''inter DList_set RBT_set: corder = None'') (\<lambda>_. DList_set dxs \<inter> RBT_set rbt)
                      | Some _ \<Rightarrow>
       case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''inter DList_set RBT_set: ceq = None'') (\<lambda>_. DList_set dxs \<inter> RBT_set rbt)
                      | Some _ \<Rightarrow> RBT_set (RBT_Set2.inter_list rbt (list_of_dlist dxs)))" (is ?dlist_rbt)
  "DList_set dxs1 \<inter> DList_set dxs2 =
   (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''inter DList_set DList_set: ceq = None'') (\<lambda>_. DList_set dxs1 \<inter> DList_set dxs2)
                   | Some _ \<Rightarrow> DList_set (DList_Set.filter (DList_Set.member dxs2) dxs1))" (is ?dlist)
  "DList_set dxs1 \<inter> Set_Monad xs' =
   (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''inter DList_set Set_Monad: ceq = None'') (\<lambda>_. DList_set dxs1 \<inter> Set_Monad xs')
                  | Some eq \<Rightarrow> DList_set (DList_Set.filter (equal_base.list_member eq xs') dxs1))" (is ?dlist_monad)

  "RBT_set rbt1 \<inter> RBT_set rbt2 =
   (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''inter RBT_set RBT_set: corder = None'') (\<lambda>_. RBT_set rbt1 \<inter> RBT_set rbt2)
                      | Some _ \<Rightarrow> RBT_set (RBT_Set2.inter rbt1 rbt2))" (is ?rbt_rbt)
  "RBT_set rbt \<inter> DList_set dxs = 
   (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''inter RBT_set DList_set: corder = None'') (\<lambda>_. RBT_set rbt \<inter> DList_set dxs)
                      | Some _ \<Rightarrow>
       case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''inter RBT_set DList_set: ceq = None'') (\<lambda>_. RBT_set rbt \<inter> DList_set dxs)
                      | Some _ \<Rightarrow> RBT_set (RBT_Set2.inter_list rbt (list_of_dlist dxs)))" (is ?rbt_dlist)
  "RBT_set rbt1 \<inter> Set_Monad xs =
   (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''inter RBT_set Set_Monad: corder = None'') (\<lambda>_. RBT_set rbt1 \<inter> Set_Monad xs)
                      | Some _ \<Rightarrow> RBT_set (RBT_Set2.inter_list rbt1 xs))" (is ?rbt_monad) 
proof -
  show ?rbt_rbt ?rbt1 ?rbt2 ?rbt_dlist ?rbt_monad ?dlist_rbt ?monad_rbt
    by(auto simp add: RBT_set_def DList_set_def DList_Set.member_def List.member_def dest: equal.equal_eq[OF ID_ceq] split: option.split)
  show ?dlist ?dlist1 ?dlist2 ?dlist_monad ?monad_dlist ?monad ?monad1 ?monad2 ?collect1 ?collect2 ?complement
    by(auto simp add: DList_set_def List.member_def dest!: Collection_Eq.ID_ceq split: option.splits)
qed

lemma Set_bind_code [code]:
  fixes dxs :: "'a :: ceq set_dlist"
  and rbt :: "'b :: corder set_rbt" shows
  "Set.bind (Set_Monad xs) f = fold (op \<union> \<circ> f) xs (Set_Monad [])" (is ?Set_Monad)
  "Set.bind (DList_set dxs) f' =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''bind DList_set: ceq = None'') (\<lambda>_. Set.bind (DList_set dxs) f')
                  | Some _ \<Rightarrow> DList_Set.fold (union \<circ> f') dxs {})" (is ?DList)
  "Set.bind (RBT_set rbt) f'' = 
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''bind RBT_set: corder = None'') (\<lambda>_. Set.bind (RBT_set rbt) f'')
                     | Some _ \<Rightarrow> RBT_Set2.fold (union \<circ> f'') rbt {})" (is ?RBT)
proof -
  show ?Set_Monad by(simp add: set_bind_conv_fold)
  show ?DList by(auto simp add: DList_set_def DList_Set.member_def List.member_def List.member_def[abs_def] set_bind_conv_fold DList_Set.fold_def split: option.split dest: equal.equal_eq[OF ID_ceq] ID_ceq)
  show ?RBT by(clarsimp split: option.split simp add: RBT_set_def RBT_Set2.fold_conv_fold_keys RBT_Set2.member_conv_keys set_bind_conv_fold)
qed

lemma UNIV_code [code]: "UNIV = - {}"
by(simp)

lemma Inf_fin_code [code]:
  fixes rbt :: "'a :: {corder, lattice} set_rbt"
  and dxs :: "'b :: {ceq, lattice} set_dlist" shows
  "Inf_fin (Set_Monad (x # xs)) = fold inf xs x"
  "Inf_fin (DList_set dxs) =
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''Inf_fin DList_set: ceq = None'') (\<lambda>_. Inf_fin (DList_set dxs))
                  | Some _ \<Rightarrow> if DList_Set.null dxs then Code.abort (STR ''Inf_fin DList_set: empty set'') (\<lambda>_. Inf_fin (DList_set dxs))
                              else DList_Set.fold inf (DList_Set.tl dxs) (DList_Set.hd dxs))"
  "Inf_fin (RBT_set rbt) =
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''Inf_fin RBT_set: corder = None'') (\<lambda>_. Inf_fin (RBT_set rbt))
                     | Some _ \<Rightarrow> if RBT_Set2.is_empty rbt then Code.abort (STR ''Inf_fin RBT_set: empty set'') (\<lambda>_. Inf_fin (RBT_set rbt))
                                 else RBT_Set2.fold1 inf rbt)"
by(simp_all add: Inf_fin.set_eq_fold DList_set_def DList_Set.Inf_fin_member RBT_Set2.Inf_fin_member RBT_set_def del: set.simps split: option.splits)

lemma Sup_fin_code [code]:
  fixes rbt :: "'a :: {corder, lattice} set_rbt"
  and dxs :: "'b :: {ceq, lattice} set_dlist" shows
  "Sup_fin (Set_Monad (x # xs)) = fold sup xs x"
  "Sup_fin (DList_set dxs) =
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''Sup_fin DList_set: ceq = None'') (\<lambda>_. Sup_fin (DList_set dxs))
                  | Some _ \<Rightarrow> if DList_Set.null dxs then Code.abort (STR ''Sup_fin DList_set: empty set'') (\<lambda>_. Sup_fin (DList_set dxs))
                              else DList_Set.fold sup (DList_Set.tl dxs) (DList_Set.hd dxs))"
  "Sup_fin (RBT_set rbt) =
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''Sup_fin RBT_set: corder = None'') (\<lambda>_. Sup_fin (RBT_set rbt))
                     | Some _ \<Rightarrow> if RBT_Set2.is_empty rbt then Code.abort (STR ''Sup_fin RBT_set: empty set'') (\<lambda>_. Sup_fin (RBT_set rbt))
                                 else RBT_Set2.fold1 sup rbt)"
by(simp_all add: Sup_fin.set_eq_fold DList_set_def DList_Set.Sup_fin_member RBT_Set2.Sup_fin_member RBT_set_def del: set.simps split: option.splits)

lemma Inf_code:
  fixes xs :: "'a :: complete_lattice list"
  and dxs :: "'b :: {complete_lattice, ceq} set_dlist"
  and rbt :: "'c :: {complete_lattice, corder} set_rbt"
  shows Inf_Set_Monad: "Inf (Set_Monad xs) = fold inf xs top"
  and Inf_DList_set:
  "Inf (DList_set dxs) =
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''Inf DList_set: ceq = None'') (\<lambda>_. Inf (DList_set dxs))
                  | Some _ \<Rightarrow> DList_Set.fold inf dxs top)"
  and Inf_RBT_set:
  "Inf (RBT_set rbt) =
  (case ID CORDER('c) of None \<Rightarrow> Code.abort (STR ''Inf RBT_set: corder = None'') (\<lambda>_. Inf (RBT_set rbt))
                  | Some _ \<Rightarrow> RBT_Set2.fold inf rbt top)"
by(auto simp add: DList_set_def RBT_set_def Inf_set_fold Collect_member DList_Set.fold.rep_eq RBT_Set2.member_conv_keys RBT_Set2.keys.rep_eq RBT_Set2.fold_conv_fold_keys split: option.split)

lemma Sup_code:
  fixes xs :: "'a :: complete_lattice list"
  and dxs :: "'b :: {complete_lattice, ceq} set_dlist"
  and rbt :: "'c :: {complete_lattice, corder} set_rbt"
  shows Sup_Set_Monad:
  "Sup (Set_Monad xs) = fold sup xs bot"
  and Sup_DList_set:
  "Sup (DList_set dxs) =
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''Sup DList_set: ceq = None'') (\<lambda>_. Sup (DList_set dxs))
                  | Some _ \<Rightarrow> DList_Set.fold sup dxs bot)"
  and Sup_RBT_set:
  "Sup (RBT_set rbt) =
  (case ID CORDER('c) of None \<Rightarrow> Code.abort (STR ''Sup RBT_set: corder = None'') (\<lambda>_. Sup (RBT_set rbt))
                  | Some _ \<Rightarrow> RBT_Set2.fold sup rbt bot)"
by(auto simp add: DList_set_def RBT_set_def Sup_set_fold Collect_member DList_Set.fold.rep_eq RBT_Set2.member_conv_keys RBT_Set2.keys.rep_eq RBT_Set2.fold_conv_fold_keys split: option.split)

lemmas Inter_code [code] = 
  Inf_Set_Monad[where ?'a = "_ :: type set"]
  Inf_DList_set[where ?'b = "_ :: ceq set"]
  Inf_RBT_set[where ?'c = "_ :: corder set"]

lemmas Union_code [code] =
  Sup_Set_Monad[where ?'a="_ :: type set"]
  Sup_DList_set[where ?'b="_ :: ceq set"]
  Sup_RBT_set[where ?'c="_ :: corder set"]

lemmas Predicate_Inf_code [code] =
  Inf_Set_Monad[where ?'a = "_ :: type Predicate.pred"]
  Inf_DList_set[where ?'b = "_ :: ceq Predicate.pred"]
  -- {* no @{class corder} instance for @{typ "'a Predicate.pred"} yet *}
(*  Inf_RBT_set[where ?'c = "_ :: corder Predicate.pred"] *)

lemmas Predicate_Sup_code [code] =
  Sup_Set_Monad[where ?'a = "_ :: type Predicate.pred"]
  Sup_DList_set[where ?'b = "_ :: ceq Predicate.pred"]
  -- {* no @{class corder} instance for @{typ "'a Predicate.pred"} yet *}
(*  Sup_RBT_set[where ?'c = "_ :: corder Predicate.pred"] *)

lemmas Inf_fun_code [code] =
  Inf_Set_Monad[where ?'a = "_ :: type \<Rightarrow> _ :: complete_lattice"]
  Inf_DList_set[where ?'b = "_ :: type \<Rightarrow> _ :: complete_lattice"]
  Inf_RBT_set[where ?'c = "_ :: type \<Rightarrow> _ :: complete_lattice"]

lemmas Sup_fun_code [code] =
  Sup_Set_Monad[where ?'a = "_ :: type \<Rightarrow> _ :: complete_lattice"]
  Sup_DList_set[where ?'b = "_ :: type \<Rightarrow> _ :: complete_lattice"]
  Sup_RBT_set[where ?'c = "_ :: type \<Rightarrow> _ :: complete_lattice"]

lemma INFI_code [code]: "INFI A f = Inf (f ` A)"
by(rule INF_def)

lemma SUPR_code [code]: "SUPR A f = Sup (f ` A)"
by(rule SUP_def)

lemma Min_code [code]:
  fixes xs :: "'a :: linorder list" 
  and dxs :: "'b :: {ceq, linorder} set_dlist"
  and rbt :: "'c :: {corder, linorder} set_rbt" shows
  "Min (Set_Monad (x # xs)) = fold min xs x" (is ?Monad)
  "Min (DList_set dxs) = 
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''Min DList_set: ceq = None'') (\<lambda>_. Min (DList_set dxs))
                  | Some _ \<Rightarrow> 
    if DList_Set.null dxs then Code.abort (STR ''Min DList_set: empty set'') (\<lambda>_. Min (DList_set dxs))
    else DList_Set.fold min (DList_Set.tl dxs) (DList_Set.hd dxs))" (is ?DList)
  "Min (RBT_set rbt) = 
  (case ID CORDER('c) of None \<Rightarrow> Code.abort (STR ''Min RBT_set: corder = None'') (\<lambda>_. Min (RBT_set rbt))
                     | Some _ \<Rightarrow> 
    if RBT_Set2.is_empty rbt then Code.abort (STR ''Min RBT_set: empty set'') (\<lambda>_. Min (RBT_set rbt))
    else RBT_Set2.fold1 min rbt)" (is ?rbt)
proof -
  show ?Monad by(simp del: set.simps add: Min.set_eq_fold)
  show ?DList
    by(clarsimp simp add: DList_set_def DList_Set.Collect_member split: option.split)(transfer, clarsimp simp add: neq_Nil_conv Min.set_eq_fold simp del: set.simps)
  show ?rbt
    by(clarsimp simp add: RBT_set_conv_keys split: option.split)(transfer, drule non_empty_rbt_keys, clarsimp simp add: neq_Nil_conv RBT_Impl_fold1_def Min.set_eq_fold simp del: set.simps)
qed

lemma Max_code [code]:
  fixes xs :: "'a :: linorder list" 
  and dxs :: "'b :: {ceq, linorder} set_dlist"
  and rbt :: "'c :: {corder, linorder} set_rbt" shows
  "Max (Set_Monad (x # xs)) = fold max xs x" (is ?Monad)
  "Max (DList_set dxs) = 
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''Max DList_set: ceq = None'') (\<lambda>_. Max (DList_set dxs))
                  | Some _ \<Rightarrow> 
    if DList_Set.null dxs then Code.abort (STR ''Max DList_set: empty set'') (\<lambda>_. Max (DList_set dxs))
    else DList_Set.fold max (DList_Set.tl dxs) (DList_Set.hd dxs))" (is ?DList)
  "Max (RBT_set rbt) = 
  (case ID CORDER('c) of None \<Rightarrow> Code.abort (STR ''Max RBT_set: corder = None'') (\<lambda>_. Max (RBT_set rbt))
                     | Some _ \<Rightarrow> 
    if RBT_Set2.is_empty rbt then Code.abort (STR ''Max RBT_set: empty set'') (\<lambda>_. Max (RBT_set rbt))
    else RBT_Set2.fold1 max rbt)" (is ?rbt)
proof -
  show ?Monad by(simp del: set.simps add: Max.set_eq_fold)
  show ?DList
    by(clarsimp simp add: DList_set_def DList_Set.Collect_member split: option.split)(transfer, clarsimp simp add: neq_Nil_conv Max.set_eq_fold simp del: set.simps)
  show ?rbt
    by(clarsimp simp add: RBT_set_conv_keys split: option.split)(transfer, drule non_empty_rbt_keys, clarsimp simp add: neq_Nil_conv RBT_Impl_fold1_def Max.set_eq_fold simp del: set.simps)
qed

text {*
  We do not implement @{term Ball}, @{term Bex}, and @{term sorted_list_of_set} for @{term Collect_set} using @{term cEnum},
  because it should already have been converted to an explicit list of elements if that is possible.
*}

lemma Ball_code [code]:
  fixes rbt :: "'a :: corder set_rbt"
  and dxs :: "'b :: ceq set_dlist" shows
  "Ball (Set_Monad xs) P = list_all P xs"
  "Ball (DList_set dxs) P' = 
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''Ball DList_set: ceq = None'') (\<lambda>_. Ball (DList_set dxs) P')
                  | Some _ \<Rightarrow> DList_Set.dlist_all P' dxs)"
  "Ball (RBT_set rbt) P'' = 
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''Ball RBT_set: corder = None'') (\<lambda>_. Ball (RBT_set rbt) P'')
                     | Some _ \<Rightarrow> RBT_Set2.all P'' rbt)"
by(simp_all add: DList_set_def RBT_set_def list_all_iff dlist_all_conv_member RBT_Set2.all_conv_all_member split: option.splits)

lemma Bex_code [code]:
  fixes rbt :: "'a :: corder set_rbt"
  and dxs :: "'b :: ceq set_dlist" shows
  "Bex (Set_Monad xs) P = list_ex P xs"
  "Bex (DList_set dxs) P' = 
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''Bex DList_set: ceq = None'') (\<lambda>_. Bex (DList_set dxs) P')
                  | Some _ \<Rightarrow> DList_Set.dlist_ex P' dxs)"
  "Bex (RBT_set rbt) P'' = 
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''Bex RBT_set: corder = None'') (\<lambda>_. Bex (RBT_set rbt) P'')
                     | Some _ \<Rightarrow> RBT_Set2.ex P'' rbt)"
by(simp_all add: DList_set_def RBT_set_def list_ex_iff dlist_ex_conv_member RBT_Set2.ex_conv_ex_member split: option.splits)

lemma csorted_list_of_set_code [code]:
  fixes rbt :: "'a :: corder set_rbt" 
  and dxs :: "'b :: {corder, ceq} set_dlist" 
  and xs :: "'a :: corder list" shows
  "csorted_list_of_set (RBT_set rbt) =
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''csorted_list_of_set RBT_set: corder = None'') (\<lambda>_. csorted_list_of_set (RBT_set rbt))
                     | Some _ \<Rightarrow> RBT_Set2.keys rbt)"
  "csorted_list_of_set (DList_set dxs) =
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''csorted_list_of_set DList_set: ceq = None'') (\<lambda>_. csorted_list_of_set (DList_set dxs))
              | Some _ \<Rightarrow>
     case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''csorted_list_of_set DList_set: corder = None'') (\<lambda>_. csorted_list_of_set (DList_set dxs))
                 | Some (le, lt) \<Rightarrow> ord.quicksort lt (list_of_dlist dxs))"
  "csorted_list_of_set (Set_Monad xs) =
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''csorted_list_of_set Set_Monad: corder = None'') (\<lambda>_. csorted_list_of_set (Set_Monad xs))
              | Some (le, lt) \<Rightarrow> ord.remdups_sorted lt (ord.quicksort lt xs))"
by(auto split: option.split simp add: RBT_set_def DList_set_def DList_Set.Collect_member member_conv_keys sorted_RBT_Set_keys linorder.sorted_list_of_set_sort_remdups[OF ID_corder] linorder.quicksort_conv_sort[OF ID_corder] distinct_remdups_id distinct_list_of_dlist linorder.remdups_sorted_conv_remdups[OF ID_corder] linorder.sorted_sort[OF ID_corder] linorder.sort_remdups[OF ID_corder] csorted_list_of_set_def)

lemma cless_set_code [code]:
  fixes rbt rbt' :: "'a :: corder set_rbt"
  and rbt1 rbt2 :: "'b :: cproper_interval set_rbt"
  and A B :: "'a set" 
  and A' B' :: "'b set" shows
  "cless_set A B \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cless_set: corder = None'') (\<lambda>_. cless_set A B)
              | Some (le, lt) \<Rightarrow>
     if finite A \<and> finite B then ord.lexord (\<lambda>x y. lt y x) (csorted_list_of_set A) (csorted_list_of_set B)
     else Code.abort (STR ''cless_set: infinite set'') (\<lambda>_. cless_set A B))"
  (is "?fin_fin")
  and cless_set_Complement2 [set_complement_code]:
  "cless_set A' (Complement B') \<longleftrightarrow>
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''cless_set Complement2: corder = None'') (\<lambda>_. cless_set A' (Complement B'))
              | Some (le, lt) \<Rightarrow>
     if finite A' \<and> finite B' then
        finite (UNIV :: 'b set) \<longrightarrow>
        proper_intrvl.set_less_aux_Compl lt cproper_interval None (csorted_list_of_set A') (csorted_list_of_set B')
     else Code.abort (STR ''cless_set Complement2: infinite set'') (\<lambda>_. cless_set A' (Complement B')))"
  (is "?fin_Compl_fin")
  and cless_set_Complement1 [set_complement_code]:
  "cless_set (Complement A') B' \<longleftrightarrow>
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''cless_set Complement1: corder = None'') (\<lambda>_. cless_set (Complement A') B')
              | Some (le, lt) \<Rightarrow>
      if finite A' \<and> finite B' then
        finite (UNIV :: 'b set) \<and>
        proper_intrvl.Compl_set_less_aux lt cproper_interval None (csorted_list_of_set A') (csorted_list_of_set B')
      else Code.abort (STR ''cless_set Complement1: infinite set'') (\<lambda>_. cless_set (Complement A') B'))"
  (is "?Compl_fin_fin")
  and cless_set_Complement12 [set_complement_code]:
  "cless_set (Complement A) (Complement B) \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cless_set Complement Complement: corder = None'') (\<lambda>_. cless_set (Complement A) (Complement B))
                     | Some _ \<Rightarrow> cless B A)" (is ?Compl_Compl)
  and
  "cless_set (RBT_set rbt) (RBT_set rbt') \<longleftrightarrow> 
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cless_set RBT_set RBT_set: corder = None'') (\<lambda>_. cless_set (RBT_set rbt) (RBT_set rbt'))
             | Some (leq, lt) \<Rightarrow> ord.lexord_fusion (\<lambda>x y. lt y x) rbt_keys_generator rbt_keys_generator (RBT_Set2.init rbt) (RBT_Set2.init rbt'))"
    (is ?rbt_rbt)
  and cless_set_rbt_Complement2 [set_complement_code]:
  "cless_set (RBT_set rbt1) (Complement (RBT_set rbt2)) \<longleftrightarrow>
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''cless_set RBT_set (Complement RBT_set): corder = None'') (\<lambda>_. cless_set (RBT_set rbt1) (Complement (RBT_set rbt2)))
             | Some (leq, lt) \<Rightarrow>
     finite (UNIV :: 'b set) \<longrightarrow>
     proper_intrvl.set_less_aux_Compl_fusion lt cproper_interval rbt_keys_generator rbt_keys_generator None (RBT_Set2.init rbt1) (RBT_Set2.init rbt2))"
    (is ?rbt_Compl)
  and cless_set_rbt_Complement1 [set_complement_code]:
  "cless_set (Complement (RBT_set rbt1)) (RBT_set rbt2) \<longleftrightarrow>
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''cless_set (Complement RBT_set) RBT_set: corder = None'') (\<lambda>_. cless_set (Complement (RBT_set rbt1)) (RBT_set rbt2))
             | Some (leq, lt) \<Rightarrow>
     finite (UNIV :: 'b set) \<and> 
     proper_intrvl.Compl_set_less_aux_fusion lt cproper_interval rbt_keys_generator rbt_keys_generator None (RBT_Set2.init rbt1) (RBT_Set2.init rbt2))"
    (is ?Compl_rbt)
proof -
  note [split] = option.split csorted_list_of_set_split
    and [simp] = 
    finite_subset[OF subset_UNIV] corder_set_def ID_Some
    ord.lexord_fusion_def proper_intrvl.Compl_set_less_aux_fusion_def
    proper_intrvl.set_less_aux_Compl_fusion_def
    unfoldr_rbt_keys_generator
    RBT_set_def sorted_RBT_Set_keys member_conv_keys
    linorder.set_less_finite_iff[OF ID_corder]
    linorder.set_less_aux_code[OF ID_corder, symmetric]
    linorder.Compl_set_less_Compl[OF ID_corder]
    linorder.infinite_set_less_Complement[OF ID_corder]
    linorder.infinite_Complement_set_less[OF ID_corder]
    linorder_proper_interval.set_less_aux_Compl2_conv_set_less_aux_Compl[OF ID_corder_interval, symmetric]
    linorder_proper_interval.Compl1_set_less_aux_conv_Compl_set_less_aux[OF ID_corder_interval, symmetric]

  show ?Compl_Compl by simp
  show ?rbt_rbt by auto
  show ?rbt_Compl by(cases "finite (UNIV :: 'b set)") auto
  show ?Compl_rbt by(cases "finite (UNIV :: 'b set)") auto
  show ?fin_fin by auto
  show ?fin_Compl_fin by(cases "finite (UNIV :: 'b set)") auto
  show ?Compl_fin_fin by(cases "finite (UNIV :: 'b set)") auto
qed

lemma cless_eq_set_code [code]:
  fixes rbt rbt' :: "'a :: corder set_rbt"
  and rbt1 rbt2 :: "'b :: cproper_interval set_rbt"
  and A B :: "'a set" 
  and A' B' :: "'b set" shows
  "cless_eq_set A B \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cless_eq_set: corder = None'') (\<lambda>_. cless_eq_set A B)
              | Some (le, lt) \<Rightarrow>
     if finite A \<and> finite B then 
        ord.lexord_eq (\<lambda>x y. lt y x) (csorted_list_of_set A) (csorted_list_of_set B)
     else Code.abort (STR ''cless_eq_set: infinite set'') (\<lambda>_. cless_eq_set A B))"
  (is "?fin_fin")
  and cless_eq_set_Complement2 [set_complement_code]:
  "cless_eq_set A' (Complement B') \<longleftrightarrow>
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''cless_eq_set Complement2: corder = None'') (\<lambda>_. cless_eq_set A' (Complement B'))
              | Some (le, lt) \<Rightarrow>
     if finite A' \<and> finite B' then 
        finite (UNIV :: 'b set) \<longrightarrow>
        proper_intrvl.set_less_eq_aux_Compl lt cproper_interval None (csorted_list_of_set A') (csorted_list_of_set B')
     else Code.abort (STR ''cless_eq_set Complement2: infinite set'') (\<lambda>_. cless_eq_set A' (Complement B')))"
  (is "?fin_Compl_fin")
  and cless_eq_set_Complement1 [set_complement_code]:
  "cless_eq_set (Complement A') B' \<longleftrightarrow>
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''cless_eq_set Complement1: corder = None'') (\<lambda>_. cless_eq_set (Complement A') B')
              | Some (le, lt) \<Rightarrow>
    if finite A' \<and> finite B' then 
      finite (UNIV :: 'b set) \<and>
      proper_intrvl.Compl_set_less_eq_aux lt cproper_interval None (csorted_list_of_set A') (csorted_list_of_set B')
    else Code.abort (STR ''cless_eq_set Complement1: infinite set'') (\<lambda>_. cless_eq_set (Complement A') B'))"
  (is "?Compl_fin_fin")
  and cless_eq_set_Complement12 [set_complement_code]:
  "cless_eq_set (Complement A) (Complement B) \<longleftrightarrow> 
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cless_eq_set Complement Complement: corder = None'') (\<lambda>_. cless_eq (Complement A) (Complement B))
             | Some (lt, leq) \<Rightarrow> cless_eq_set B A)" 
  (is ?Compl_Compl)

  "cless_eq_set (RBT_set rbt) (RBT_set rbt') \<longleftrightarrow> 
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cless_eq_set RBT_set RBT_set: corder = None'') (\<lambda>_. cless_eq_set (RBT_set rbt) (RBT_set rbt'))
             | Some (leq, lt) \<Rightarrow> ord.lexord_eq_fusion (\<lambda>x y. lt y x) rbt_keys_generator rbt_keys_generator (RBT_Set2.init rbt) (RBT_Set2.init rbt'))" 
    (is ?rbt_rbt)
  and cless_eq_set_rbt_Complement2 [set_complement_code]:
  "cless_eq_set (RBT_set rbt1) (Complement (RBT_set rbt2)) \<longleftrightarrow>
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''cless_eq_set RBT_set (Complement RBT_set): corder = None'') (\<lambda>_. cless_eq_set (RBT_set rbt1) (Complement (RBT_set rbt2)))
             | Some (leq, lt) \<Rightarrow>
     finite (UNIV :: 'b set) \<longrightarrow>
     proper_intrvl.set_less_eq_aux_Compl_fusion lt cproper_interval rbt_keys_generator rbt_keys_generator None (RBT_Set2.init rbt1) (RBT_Set2.init rbt2))"
    (is ?rbt_Compl)
  and cless_eq_set_rbt_Complement1 [set_complement_code]:
  "cless_eq_set (Complement (RBT_set rbt1)) (RBT_set rbt2) \<longleftrightarrow>
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''cless_eq_set (Complement RBT_set) RBT_set: corder = None'') (\<lambda>_. cless_eq_set (Complement (RBT_set rbt1)) (RBT_set rbt2))
             | Some (leq, lt) \<Rightarrow>
     finite (UNIV :: 'b set) \<and> 
     proper_intrvl.Compl_set_less_eq_aux_fusion lt cproper_interval rbt_keys_generator rbt_keys_generator None (RBT_Set2.init rbt1) (RBT_Set2.init rbt2))"
    (is ?Compl_rbt)
proof -
  note [split] = option.split csorted_list_of_set_split
    and [simp] = 
    finite_subset[OF subset_UNIV] corder_set_def ID_Some
    ord.lexord_eq_fusion_def proper_intrvl.Compl_set_less_eq_aux_fusion_def
    proper_intrvl.set_less_eq_aux_Compl_fusion_def
    unfoldr_rbt_keys_generator
    RBT_set_def sorted_RBT_Set_keys member_conv_keys
    linorder.set_less_eq_finite_iff[OF ID_corder]
    linorder.set_less_eq_aux_code[OF ID_corder, symmetric]
    linorder.Compl_set_less_eq_Compl[OF ID_corder]
    linorder.infinite_set_less_eq_Complement[OF ID_corder]
    linorder.infinite_Complement_set_less_eq[OF ID_corder]
    linorder_proper_interval.set_less_eq_aux_Compl2_conv_set_less_eq_aux_Compl[OF ID_corder_interval, symmetric]
    linorder_proper_interval.Compl1_set_less_eq_aux_conv_Compl_set_less_eq_aux[OF ID_corder_interval, symmetric]

  show ?Compl_Compl by simp
  show ?rbt_rbt by auto
  show ?rbt_Compl by(cases "finite (UNIV :: 'b set)") auto
  show ?Compl_rbt by(cases "finite (UNIV :: 'b set)") auto
  show ?fin_fin by auto
  show ?fin_Compl_fin by(cases "finite (UNIV :: 'b set)") auto
  show ?Compl_fin_fin by(cases "finite (UNIV :: 'b set)") auto
qed

lemma cproper_interval_set_Some_Some_code [code]:
  fixes rbt1 rbt2 :: "'a :: cproper_interval set_rbt" 
  and A B :: "'a set" shows

  "cproper_interval (Some A) (Some B) \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cproper_interval: corder = None'') (\<lambda>_. cproper_interval (Some A) (Some B))
              | Some (le, lt) \<Rightarrow>
       finite (UNIV :: 'a set) \<and> proper_intrvl.proper_interval_set_aux lt cproper_interval (csorted_list_of_set A) (csorted_list_of_set B))"
  (is ?fin_fin)
  and cproper_interval_set_Some_Some_Complement [set_complement_code]:
  "cproper_interval (Some A) (Some (Complement B)) \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cproper_interval Complement2: corder = None'') (\<lambda>_. cproper_interval (Some A) (Some (Complement B)))
              | Some (le, lt) \<Rightarrow>
       finite (UNIV :: 'a set) \<and> proper_intrvl.proper_interval_set_Compl_aux lt cproper_interval None 0 (csorted_list_of_set A) (csorted_list_of_set B))"
  (is ?fin_Compl_fin)
  and cproper_interval_set_Some_Complement_Some [set_complement_code]:
  "cproper_interval (Some (Complement A)) (Some B) \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cproper_interval Complement1: corder = None'') (\<lambda>_. cproper_interval (Some (Complement A)) (Some B))
              | Some (le, lt) \<Rightarrow>
       finite (UNIV :: 'a set) \<and> proper_intrvl.proper_interval_Compl_set_aux lt cproper_interval None (csorted_list_of_set A) (csorted_list_of_set B))"
  (is ?Compl_fin_fin)
  and cproper_interval_set_Some_Complement_Some_Complement [set_complement_code]:
  "cproper_interval (Some (Complement A)) (Some (Complement B)) \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cproper_interval Complement Complement: corder = None'') (\<lambda>_. cproper_interval (Some (Complement A)) (Some (Complement B)))
             | Some _ \<Rightarrow> cproper_interval (Some B) (Some A))"
  (is ?Compl_Compl)

  "cproper_interval (Some (RBT_set rbt1)) (Some (RBT_set rbt2)) \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cproper_interval RBT_set RBT_set: corder = None'') (\<lambda>_. cproper_interval (Some (RBT_set rbt1)) (Some (RBT_set rbt2)))
             | Some (leq, lt) \<Rightarrow>
     finite (UNIV :: 'a set) \<and> proper_intrvl.proper_interval_set_aux_fusion lt cproper_interval rbt_keys_generator rbt_keys_generator (RBT_Set2.init rbt1) (RBT_Set2.init rbt2))"
  (is ?rbt_rbt)
  and cproper_interval_set_Some_rbt_Some_Complement [set_complement_code]:
  "cproper_interval (Some (RBT_set rbt1)) (Some (Complement (RBT_set rbt2))) \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cproper_interval RBT_set (Complement RBT_set): corder = None'') (\<lambda>_. cproper_interval (Some (RBT_set rbt1)) (Some (Complement (RBT_set rbt2))))
             | Some (leq, lt) \<Rightarrow>
     finite (UNIV :: 'a set) \<and> proper_intrvl.proper_interval_set_Compl_aux_fusion lt cproper_interval rbt_keys_generator rbt_keys_generator None 0 (RBT_Set2.init rbt1) (RBT_Set2.init rbt2))"
  (is ?rbt_Compl_rbt)
  and cproper_interval_set_Some_Complement_Some_rbt [set_complement_code]:
  "cproper_interval (Some (Complement (RBT_set rbt1))) (Some (RBT_set rbt2)) \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''cproper_interval (Complement RBT_set) RBT_set: corder = None'') (\<lambda>_. cproper_interval (Some (Complement (RBT_set rbt1))) (Some (RBT_set rbt2)))
             | Some (leq, lt) \<Rightarrow>
     finite (UNIV :: 'a set) \<and> proper_intrvl.proper_interval_Compl_set_aux_fusion lt cproper_interval rbt_keys_generator rbt_keys_generator None (RBT_Set2.init rbt1) (RBT_Set2.init rbt2))"
  (is ?Compl_rbt_rbt)
proof -
  note [split] = option.split csorted_list_of_set_split
    and [simp] = 
    finite_subset[OF subset_UNIV] corder_set_def ID_Some
    linorder.set_less_finite_iff[OF ID_corder]
    RBT_set_def sorted_RBT_Set_keys member_conv_keys
    linorder.distinct_entries[OF ID_corder]
    unfoldr_rbt_keys_generator
    proper_intrvl.proper_interval_set_aux_fusion_def
    proper_intrvl.proper_interval_set_Compl_aux_fusion_def
    proper_intrvl.proper_interval_Compl_set_aux_fusion_def 
    linorder_proper_interval.proper_interval_set_aux[OF ID_corder_interval]
    linorder_proper_interval.proper_interval_set_Compl_aux[OF ID_corder_interval]
    linorder_proper_interval.proper_interval_Compl_set_aux[OF ID_corder_interval]
    and [cong] = conj_cong

  show ?Compl_Compl
    by(clarsimp simp add: Complement_cproper_interval_set_Complement simp del: cproper_interval_set_Some_Some)
  
  show ?rbt_rbt ?rbt_Compl_rbt ?Compl_rbt_rbt by auto
  show ?fin_fin ?fin_Compl_fin ?Compl_fin_fin by auto
qed

context ord begin

fun sorted_list_subset :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "sorted_list_subset eq [] ys = True"
| "sorted_list_subset eq (x # xs) [] = False"
| "sorted_list_subset eq (x # xs) (y # ys) \<longleftrightarrow>
  (if eq x y then sorted_list_subset eq xs ys
   else x > y \<and> sorted_list_subset eq (x # xs) ys)"

end

context linorder begin

lemma sorted_list_subset_correct:
  "\<lbrakk> sorted xs; distinct xs; sorted ys; distinct ys \<rbrakk> 
  \<Longrightarrow> sorted_list_subset op = xs ys \<longleftrightarrow> set xs \<subseteq> set ys"
apply(induct "op = :: 'a \<Rightarrow> 'a \<Rightarrow> bool" xs ys rule: sorted_list_subset.induct)
apply(auto 6 2 simp add: sorted_Cons)
apply auto
by (metis eq_iff insert_iff set_mp)

end

context ord begin

definition sorted_list_subset_fusion :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where "sorted_list_subset_fusion eq g1 g2 s1 s2 = sorted_list_subset eq (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

lemma sorted_list_subset_fusion_code:
  "sorted_list_subset_fusion eq g1 g2 s1 s2 =
  (if list.has_next g1 s1 then
     let (x, s1') = list.next g1 s1
     in list.has_next g2 s2 \<and> (
        let (y, s2') = list.next g2 s2 
        in if eq x y then sorted_list_subset_fusion eq g1 g2 s1' s2' 
           else y < x \<and> sorted_list_subset_fusion eq g1 g2 s1 s2')
   else True)"
unfolding sorted_list_subset_fusion_def
by(subst (1 2 5) list.unfoldr.simps)(simp add: split_beta Let_def)

end

lemmas [code] = ord.sorted_list_subset_fusion_code

definition mk_eq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where "mk_eq le x y \<longleftrightarrow> le x y \<and> le y x"

lemma corder_mk_eq_eq:
  assumes "ID CORDER('a :: corder) = Some (le, lt)"
  shows "mk_eq le = op ="
proof -
  interpret linorder le lt by(rule ID_corder) fact
  show ?thesis by(auto intro!: ext simp add: mk_eq_def)
qed

text {* 
  Define a new constant for the subset operation
  because @{theory Cardinality} introduces @{const "Cardinality.subset'"}
  and rewrites @{const "subset"} to @{const "Cardinality.subset'"} 
  based on the sort of the element type.
*}

definition subset_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where [simp, code del]: "subset_eq = op \<subseteq>"

lemma subseteq_code [code]: "op \<subseteq> = subset_eq"
by simp

lemma subset'_code [code]: "Cardinality.subset' = subset_eq"
by simp

lemma subset_eq_code [folded subset_eq_def, code]:
  fixes A1 A2 :: "'a set"
  and rbt :: "'b :: corder set_rbt"
  and rbt1 rbt2 :: "'d :: {corder, ceq} set_rbt"
  and dxs :: "'c :: ceq set_dlist" 
  and xs :: "'c list" shows
  "RBT_set rbt \<subseteq> B \<longleftrightarrow> 
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''subset RBT_set1: corder = None'') (\<lambda>_. RBT_set rbt \<subseteq> B)
                     | Some _ \<Rightarrow> list_all_fusion rbt_keys_generator (\<lambda>x. x \<in> B) (RBT_Set2.init rbt))" (is ?rbt)
  "DList_set dxs \<subseteq> C \<longleftrightarrow> 
  (case ID CEQ('c) of None \<Rightarrow> Code.abort (STR ''subset DList_set1: ceq = None'') (\<lambda>_. DList_set dxs \<subseteq> C)
                     | Some _ \<Rightarrow> DList_Set.dlist_all (\<lambda>x. x \<in> C) dxs)" (is ?dlist)
  "Set_Monad xs \<subseteq> C \<longleftrightarrow> list_all (\<lambda>x. x \<in> C) xs" (is ?Set_Monad)
  and Collect_subset_eq_Complement [folded subset_eq_def, set_complement_code]:
  "Collect_set P \<subseteq> Complement A \<longleftrightarrow> A \<subseteq> {x. \<not> P x}" (is ?Collect_set_Compl)
  and Complement_subset_eq_Complement [folded subset_eq_def, set_complement_code]:
  "Complement A1 \<subseteq> Complement A2 \<longleftrightarrow> A2 \<subseteq> A1" (is ?Compl)
  and
  "RBT_set rbt1 \<subseteq> RBT_set rbt2 \<longleftrightarrow>
  (case ID CORDER('d) of None \<Rightarrow> Code.abort (STR ''subset RBT_set RBT_set: corder = None'') (\<lambda>_. RBT_set rbt1 \<subseteq> RBT_set rbt2)
                     | Some (le, lt) \<Rightarrow> 
    (case ID CEQ('d) of None \<Rightarrow> ord.sorted_list_subset_fusion lt (mk_eq le) rbt_keys_generator rbt_keys_generator (RBT_Set2.init rbt1) (RBT_Set2.init rbt2)
                   | Some eq \<Rightarrow> ord.sorted_list_subset_fusion lt eq rbt_keys_generator rbt_keys_generator (RBT_Set2.init rbt1) (RBT_Set2.init rbt2)))" 
  (is ?rbt_rbt)
proof -
  show ?rbt_rbt using corder_mk_eq_eq[where ?'a ="'d"]
    by(auto simp add: RBT_set_def member_conv_keys unfoldr_rbt_keys_generator ord.sorted_list_subset_fusion_def linorder.sorted_list_subset_correct[OF ID_corder] sorted_RBT_Set_keys split: option.split dest!: ID_ceq[THEN equal.equal_eq] del: iffI)
  show ?rbt
    by(auto simp add: RBT_set_def member_conv_keys list_all_fusion_def unfoldr_rbt_keys_generator keys.rep_eq list_all_iff split: option.split)
  show ?dlist by(auto simp add: DList_set_def dlist_all_conv_member split: option.split)
  show ?Set_Monad by(auto simp add: list_all_iff split: option.split)
  show ?Collect_set_Compl ?Compl by auto
qed

hide_const (open) subset_eq
hide_fact (open) subset_eq_def

lemma [code, code del]: "(set_eq :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool) = set_eq" ..

lemma eq_set_code [code]: "Cardinality.eq_set = set_eq"
by(simp add: set_eq_def)

lemma set_eq_code [code]:
  fixes rbt1 rbt2 :: "'b :: {corder, ceq} set_rbt" shows
  "set_eq A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  and set_eq_Complement_Complement [set_complement_code]:
  "set_eq (Complement A) (Complement B) = set_eq A B"
  and
  "set_eq (RBT_set rbt1) (RBT_set rbt2) = 
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''set_eq RBT_set RBT_set: corder = None'') (\<lambda>_. set_eq (RBT_set rbt1) (RBT_set rbt2))
                     | Some (le, lt) \<Rightarrow> 
     (case ID CEQ('b) of None \<Rightarrow> list_all2_fusion (mk_eq le) rbt_keys_generator rbt_keys_generator (RBT_Set2.init rbt1) (RBT_Set2.init rbt2)
                    | Some eq \<Rightarrow> list_all2_fusion eq rbt_keys_generator rbt_keys_generator (RBT_Set2.init rbt1) (RBT_Set2.init rbt2)))"
  (is ?rbt_rbt)
proof -
  show ?rbt_rbt using corder_mk_eq_eq[where ?'a="'b"]
    by(auto 4 3 split: option.split simp add: sorted_RBT_Set_keys list_all2_fusion_def unfoldr_rbt_keys_generator RBT_set_conv_keys set_eq_def list_all2_eq' dest!: ID_ceq[THEN equal.equal_eq] intro: linorder.sorted_distinct_set_unique[OF ID_corder])
qed(auto simp add: set_eq_def)

lemma Set_project_code [code]:
  "Set.filter P A = A \<inter> Collect_set P"
by(auto simp add: Set.filter_def)

lemma Set_image_code [code]:
  fixes dxs :: "'a :: ceq set_dlist" 
  and rbt :: "'b :: corder set_rbt" shows
  "image f (Set_Monad xs) = Set_Monad (map f xs)"
  "image f (Collect_set A) = Code.abort (STR ''image Collect_set'') (\<lambda>_. image f (Collect_set A))"
  and image_Complement_Complement [set_complement_code]:
  "image f (Complement (Complement B)) = image f B"
  and
  "image g (DList_set dxs) = 
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''image DList_set: ceq = None'') (\<lambda>_. image g (DList_set dxs))
                  | Some _ \<Rightarrow> DList_Set.fold (insert \<circ> g) dxs {})"
  (is ?dlist)
  "image h (RBT_set rbt) = 
   (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''image RBT_set: corder = None'') (\<lambda>_. image h (RBT_set rbt))
                      | Some _ \<Rightarrow> RBT_Set2.fold (insert \<circ> h) rbt {})"
   (is ?rbt)
proof -
  { fix xs have "fold (insert \<circ> g) xs {} = g ` set xs"
      by(induct xs rule: rev_induct) simp_all }
  thus ?dlist
    by(simp add: DList_set_def DList_Set.fold_def DList_Set.Collect_member split: option.split)
  { fix xs have "fold (insert \<circ> h) xs {} = h ` set xs"
      by(induct xs rule: rev_induct) simp_all }
  thus ?rbt by(auto simp add: RBT_set_def fold_conv_fold_keys member_conv_keys split: option.split)
qed simp_all

lemma the_elem_code [code]:
  fixes dxs :: "'a :: ceq set_dlist" 
  and rbt :: "'b :: corder set_rbt" shows
  "the_elem (Set_Monad [x]) = x"
  "the_elem (DList_set dxs) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''the_elem DList_set: ceq = None'') (\<lambda>_. the_elem (DList_set dxs))
                  | Some _ \<Rightarrow> 
     case list_of_dlist dxs of [x] \<Rightarrow> x 
       | _ \<Rightarrow> Code.abort (STR ''the_elem DList_set: not unique'') (\<lambda>_. the_elem (DList_set dxs)))"
  "the_elem (RBT_set rbt) =
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''the_elem RBT_set: corder = None'') (\<lambda>_. the_elem (RBT_set rbt))
                     | Some _ \<Rightarrow> 
     case RBT_Mapping2.impl_of rbt of RBT_Impl.Branch _ RBT_Impl.Empty x _ RBT_Impl.Empty \<Rightarrow> x
       | _ \<Rightarrow> Code.abort (STR ''the_elem RBT_set: not unique'') (\<lambda>_. the_elem (RBT_set rbt)))"
by(auto simp add: RBT_set_def DList_set_def DList_Set.Collect_member the_elem_def member_conv_keys split: option.split list.split rbt.split)(simp add: RBT_Set2.keys_def)

lemma Pow_set_conv_fold:
  "Pow (set xs \<union> A) = fold (\<lambda>x A. A \<union> insert x ` A) xs (Pow A)"
by(induct xs rule: rev_induct)(auto simp add: Pow_insert)

lemma Pow_code [code]:
  fixes dxs :: "'a :: ceq set_dlist" 
  and rbt :: "'b :: corder set_rbt" shows
  "Pow A = Collect_set (\<lambda>B. B \<subseteq> A)"
  "Pow (Set_Monad xs) = fold (\<lambda>x A. A \<union> insert x ` A) xs {{}}"
  "Pow (DList_set dxs) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''Pow DList_set: ceq = None'') (\<lambda>_. Pow (DList_set dxs))
                  | Some _ \<Rightarrow> DList_Set.fold (\<lambda>x A. A \<union> insert x ` A) dxs {{}})"
  "Pow (RBT_set rbt) =
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''Pow RBT_set: corder = None'') (\<lambda>_. Pow (RBT_set rbt))
                     | Some _ \<Rightarrow> RBT_Set2.fold (\<lambda>x A. A \<union> insert x ` A) rbt {{}})"
by(auto simp add: DList_set_def DList_Set.Collect_member DList_Set.fold_def RBT_set_def fold_conv_fold_keys member_conv_keys Pow_set_conv_fold[where A="{}", simplified] split: option.split)

lemma fold_singleton: "Finite_Set.fold f x {y} = f y x"
by(fastforce simp add: Finite_Set.fold_def intro: fold_graph.intros elim: fold_graph.cases)

lemma setsum_code [code]:
  fixes xs :: "'a :: ceq list" 
  and dxs :: "'a set_dlist" 
  and rbt :: "'b :: corder set_rbt" shows
  "setsum f A = (if finite A then Code.abort (STR ''setsum: finite set'') (\<lambda>_. setsum f A) else 0)"
  (is ?generic)

  "setsum f (Set_Monad xs) = 
  (case ID CEQ('a) of None \<Rightarrow> 
       case xs of [] \<Rightarrow> 0 | [x] \<Rightarrow> f x | _ \<Rightarrow> Code.abort (STR ''setsum Set_Monad: ceq = None'') (\<lambda>_. setsum f (Set_Monad xs))
     | Some eq \<Rightarrow> fold (plus \<circ> f) (equal_base.list_remdups eq xs) 0)" (is ?Set_Monad)

  "setsum f (DList_set dxs) =
  (case ID CEQ('a) of None \<Rightarrow>
       case list_of_dlist dxs of [] \<Rightarrow> 0 | _ \<Rightarrow> Code.abort (STR ''setsum DList_set: ceq = None'') (\<lambda>_. setsum f (DList_set dxs))
     | Some _ \<Rightarrow> DList_Set.fold (plus \<circ> f) dxs 0)" (is ?DList)

  "setsum g (RBT_set rbt) = 
  (case ID CORDER('b) of None \<Rightarrow>
       case RBT_Mapping2.impl_of rbt of rbt.Empty \<Rightarrow> 0 | _ \<Rightarrow> Code.abort (STR ''setsum RBT_set: corder = None'') (\<lambda>_. setsum g (RBT_set rbt))
     | Some _ \<Rightarrow> RBT_Set2.fold (plus \<circ> g) rbt 0)" (is ?rbt)
proof -
  have comm: "comp_fun_commute (\<lambda>x. op + (f x))" by default (auto simp: add_ac)

  show ?Set_Monad using equal.equal_eq[where ?'a='a, OF equal_ceq]
    by(auto simp add: setsum.eq_fold fold_singleton comp_fun_commute.fold_set_fold_remdups[OF comm] o_def simp del: set.simps not_None_eq split: option.split list.split)(auto simp add: o_def List.member_def)

  have "ID CEQ('a) \<noteq> None \<Longrightarrow> distinct (list_of_dlist dxs)"
    by transfer(auto simp add: equal.equal_eq[OF equal_ceq])
  thus ?DList
    by(auto simp add: DList_set_def setsum.eq_fold DList_Set.Collect_member o_def comp_fun_commute.fold_set_fold_remdups[OF comm] DList_Set.fold_def distinct_remdups_id simp del: set.simps split: option.split list.split)

  have comm: "comp_fun_commute (\<lambda>x. op + (g x))" by default (auto simp: add_ac)
  show ?rbt
    apply(auto simp add: RBT_set_def setsum.eq_fold member_conv_keys o_def comp_fun_commute.fold_set_fold_remdups[OF comm] RBT_Set2.fold_def distinct_remdups_id cong: rbt.case_cong split: option.split)
     apply(auto split: rbt.split)
    apply(simp_all add: RBT_Set2.member_def ord.rbt_lookup.simps[abs_def] RBT_Impl.fold_def distinct_remdups_id RBT_Set2.keys_def RBT_Impl.keys_def fold_map o_def split_def)
    done

  show ?generic by(simp add: setsum.eq_fold)
qed

lemma product_code [code]:
  fixes dxs :: "'a :: ceq set_dlist"
  and dys :: "'b :: ceq set_dlist" 
  and rbt1 :: "'c :: corder set_rbt"
  and rbt2 :: "'d :: corder set_rbt" shows
  "Product_Type.product A B = Collect_set (\<lambda>(x, y). x \<in> A \<and> y \<in> B)"

  "Product_Type.product (Set_Monad xs) (Set_Monad ys) = 
   Set_Monad (fold (\<lambda>x. fold (\<lambda>y rest. (x, y) # rest) ys) xs [])"
  (is ?Set_Monad)

  "Product_Type.product (DList_set dxs) B1 = 
   (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''product DList_set1: ceq = None'') (\<lambda>_. Product_Type.product (DList_set dxs) B1)
                   | Some _ \<Rightarrow>  DList_Set.fold (\<lambda>x rest. Pair x ` B1 \<union> rest) dxs {})" 
  (is "?dlist1")

  "Product_Type.product A1 (DList_set dys) = 
   (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''product DList_set2: ceq = None'') (\<lambda>_. Product_Type.product A1 (DList_set dys))
                   | Some _ \<Rightarrow> DList_Set.fold (\<lambda>y rest. (\<lambda>x. (x, y)) ` A1 \<union> rest) dys {})"
  (is "?dlist2")

  "Product_Type.product (DList_set dxs) (DList_set dys) = 
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''product DList_set DList_set: ceq1 = None'') (\<lambda>_. Product_Type.product (DList_set dxs) (DList_set dys))
                  | Some _ \<Rightarrow> 
     case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''product DList_set DList_set: ceq2 = None'') (\<lambda>_. Product_Type.product (DList_set dxs) (DList_set dys))
                    | Some _ \<Rightarrow> DList_set (DList_Set.product dxs dys))"

  "Product_Type.product (RBT_set rbt1) B2 =
  (case ID CORDER('c) of None \<Rightarrow> Code.abort (STR ''product RBT_set: corder1 = None'') (\<lambda>_. Product_Type.product (RBT_set rbt1) B2)
                     | Some _ \<Rightarrow> RBT_Set2.fold (\<lambda>x rest. Pair x ` B2 \<union> rest) rbt1 {})"
  (is "?rbt1")

  "Product_Type.product A2 (RBT_set rbt2) =
  (case ID CORDER('d) of None \<Rightarrow> Code.abort (STR ''product RBT_set: corder2 = None'') (\<lambda>_. Product_Type.product A2 (RBT_set rbt2))
                     | Some _ \<Rightarrow> RBT_Set2.fold (\<lambda>y rest. (\<lambda>x. (x, y)) ` A2 \<union> rest) rbt2 {})"
  (is "?rbt2")

  "Product_Type.product (RBT_set rbt1) (RBT_set rbt2) =
  (case ID CORDER('c) of None \<Rightarrow> Code.abort (STR ''product RBT_set RBT_set: corder1 = None'') (\<lambda>_. Product_Type.product (RBT_set rbt1) (RBT_set rbt2))
                     | Some _ \<Rightarrow>
     case ID CORDER('d) of None \<Rightarrow> Code.abort (STR ''product RBT_set RBT_set: corder2 = None'') (\<lambda>_. Product_Type.product (RBT_set rbt1) (RBT_set rbt2))
                       | Some _ \<Rightarrow> RBT_set (RBT_Set2.product rbt1 rbt2))"
proof -
  have [simp]: "\<And>a zs. fold (\<lambda>y. op # (a, y)) ys zs = rev (map (Pair a) ys) @ zs"
    by(induct ys) simp_all
  have [simp]: "\<And>zs. fold (\<lambda>x. fold (\<lambda>y rest. (x, y) # rest) ys) xs zs = rev (concat (map (\<lambda>x. map (Pair x) ys) xs)) @ zs"
    by(induct xs) simp_all
  show ?Set_Monad by(auto simp add: Product_Type.product_def)

  { fix xs :: "'a list"
    have "fold (\<lambda>x. op \<union> (Pair x ` B1)) xs {} = set xs \<times> B1"
      by(induct xs rule: rev_induct) auto }
  thus ?dlist1 
    by(simp add: Product_Type.product_def DList_set_def DList_Set.fold.rep_eq DList_Set.Collect_member split: option.split) 

  { fix ys :: "'b list"
    have "fold (\<lambda>y. op \<union> ((\<lambda>x. (x, y)) ` A1)) ys {} = A1 \<times> set ys"
      by(induct ys rule: rev_induct) auto }
  thus ?dlist2
    by(simp add: Product_Type.product_def DList_set_def DList_Set.fold.rep_eq DList_Set.Collect_member split: option.split)

  { fix xs :: "'c list"
    have "fold (\<lambda>x. op \<union> (Pair x ` B2)) xs {} = set xs \<times> B2"
      by(induct xs rule: rev_induct) auto }
  thus ?rbt1
    by(simp add: Product_Type.product_def RBT_set_def RBT_Set2.member_product RBT_Set2.member_conv_keys fold_conv_fold_keys split: option.split)

  { fix ys :: "'d list"
    have "fold (\<lambda>y. op \<union> ((\<lambda>x. (x, y)) ` A2)) ys {} = A2 \<times> set ys"
      by(induct ys rule: rev_induct) auto }
  thus ?rbt2
    by(simp add: Product_Type.product_def RBT_set_def RBT_Set2.member_product RBT_Set2.member_conv_keys fold_conv_fold_keys split: option.split)
qed(auto simp add: RBT_set_def DList_set_def Product_Type.product_def DList_Set.product_member RBT_Set2.member_product split: option.split)

lemma Id_on_code [code]: 
  fixes A :: "'a :: ceq set"
  and dxs :: "'a set_dlist" 
  and P :: "'a \<Rightarrow> bool" 
  and rbt :: "'b :: corder set_rbt" shows
  "Id_on B = (\<lambda>x. (x, x)) ` B"
  and Id_on_Complement [set_complement_code]:
  "Id_on (Complement A) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''Id_on Complement: ceq = None'') (\<lambda>_. Id_on (Complement A))
                 | Some eq \<Rightarrow> Collect_set (\<lambda>(x, y). eq x y \<and> x \<notin> A))"
  and
  "Id_on (Collect_set P) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''Id_on Collect_set: ceq = None'') (\<lambda>_. Id_on (Collect_set P))
                 | Some eq \<Rightarrow> Collect_set (\<lambda>(x, y). eq x y \<and> P x))"
  "Id_on (DList_set dxs) = 
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''Id_on DList_set: ceq = None'') (\<lambda>_. Id_on (DList_set dxs))
                  | Some _ \<Rightarrow> DList_set (DList_Set.Id_on dxs))"
  "Id_on (RBT_set rbt) =
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''Id_on RBT_set: corder = None'') (\<lambda>_. Id_on (RBT_set rbt))
                     | Some _ \<Rightarrow> RBT_set (RBT_Set2.Id_on rbt))"
by(auto simp add: DList_set_def RBT_set_def DList_Set.member_Id_on RBT_Set2.member_Id_on dest: equal.equal_eq[OF ID_ceq] split: option.split)

lemma Image_code [code]:
  fixes dxs :: "('a :: ceq \<times> 'b :: ceq) set_dlist" 
  and rbt :: "('c :: corder \<times> 'd :: corder) set_rbt" shows
  "X `` Y = snd ` Set.filter (\<lambda>(x, y). x \<in> Y) X"
  (is ?generic)

  "Set_Monad rxs `` A = Set_Monad (fold (\<lambda>(x, y) rest. if x \<in> A then y # rest else rest) rxs [])"
  (is ?Set_Monad)
  "DList_set dxs `` B = 
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''Image DList_set: ceq1 = None'') (\<lambda>_. DList_set dxs `` B)
                  | Some _ \<Rightarrow>
     case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''Image DList_set: ceq2 = None'') (\<lambda>_. DList_set dxs `` B)
                    | Some _ \<Rightarrow>
        DList_Set.fold (\<lambda>(x, y) acc. if x \<in> B then insert y acc else acc) dxs {})"
  (is ?DList_set)
  "RBT_set rbt `` C =
   (case ID CORDER('c) of None \<Rightarrow> Code.abort (STR ''Image RBT_set: corder1 = None'') (\<lambda>_. RBT_set rbt `` C)
                      | Some _ \<Rightarrow>
      case ID CORDER('d) of None \<Rightarrow> Code.abort (STR ''Image RBT_set: corder2 = None'') (\<lambda>_. RBT_set rbt `` C)
                        | Some _ \<Rightarrow>
        RBT_Set2.fold (\<lambda>(x, y) acc. if x \<in> C then insert y acc else acc) rbt {})"
  (is ?RBT_set)
proof -
  show ?generic by(auto intro: rev_image_eqI)

  have "set (fold (\<lambda>(x, y) rest. if x \<in> A then y # rest else rest) rxs []) = set rxs `` A"
    by(induct rxs rule: rev_induct)(auto split: split_if_asm)
  thus ?Set_Monad by(auto)

  { fix dxs :: "('a \<times> 'b) list"
    have "fold (\<lambda>(x, y) acc. if x \<in> B then insert y acc else acc) dxs {} = set dxs `` B"
      by(induct dxs rule: rev_induct)(auto split: split_if_asm) }
  thus ?DList_set
    by(clarsimp simp add: DList_set_def Collect_member ceq_prod_def ID_Some DList_Set.fold.rep_eq split: option.split)


  { fix rbt :: "(('c \<times> 'd) \<times> unit) list"
    have "fold (\<lambda>(a, _). case a of (x, y) \<Rightarrow> \<lambda>acc. if x \<in> C then insert y acc else acc) rbt {} = (fst ` set rbt) `` C"
      by(induct rbt rule: rev_induct)(auto simp add: split_beta split: split_if_asm) }
  thus ?RBT_set
    by(clarsimp simp add: RBT_set_def corder_prod_def ID_Some RBT_Set2.fold.rep_eq member_conv_keys RBT_Set2.keys.rep_eq RBT_Impl.fold_def RBT_Impl.keys_def split: option.split)
qed

lemma insert_relcomp: "insert (a, b) A O B = A O B \<union> {a} \<times> {c. (b, c) \<in> B}"
by auto

lemma trancl_code [code]:
  "trancl A = 
  (if finite A then ntrancl (card A - 1) A else Code.abort (STR ''trancl: infinite set'') (\<lambda>_. trancl A))"
by (simp add: finite_trancl_ntranl)

lemma set_relcomp_set:
  "set xs O set ys = fold (\<lambda>(x, y). fold (\<lambda>(y', z) A. if y = y' then insert (x, z) A else A) ys) xs {}"
proof(induct xs rule: rev_induct)
  case Nil show ?case by simp
next
  case (snoc x xs)
  note [[show_types]]
  { fix a :: 'a and b :: 'c and X :: "('a \<times> 'b) set"
    have "fold (\<lambda>(y', z) A. if b = y' then insert (a, z) A else A) ys X = X \<union> {a} \<times> {c. (b, c) \<in> set ys}"
      by(induct ys arbitrary: X rule: rev_induct)(auto split: split_if_asm) }
  thus ?case using snoc by(cases x)(simp add: insert_relcomp)
qed

lemma If_not: "(if \<not> a then b else c) = (if a then c else b)" 
by auto

lemma relcomp_code [code]:
  fixes rbt1 :: "('a :: corder \<times> 'b :: corder) set_rbt"
  and rbt2 :: "('b \<times> 'c :: corder) set_rbt"
  and rbt3 :: "('a \<times> 'd :: {corder, ceq}) set_rbt" 
  and rbt4 :: "('d \<times> 'a) set_rbt"
  and rbt5 :: "('b \<times> 'a) set_rbt"
  and dxs1 :: "('d \<times> 'e :: ceq) set_dlist" 
  and dxs2 :: "('e \<times> 'd) set_dlist"
  and dxs3 :: "('e \<times> 'f :: ceq) set_dlist"
  and dxs4 :: "('f \<times> 'g :: ceq) set_dlist"
  and xs1 :: "('h \<times> 'i :: ceq) list"
  and xs2 :: "('i \<times> 'j) list"
  and xs3 :: "('b \<times> 'h) list"
  and xs4 :: "('h \<times> 'b) list"
  and xs5 :: "('f \<times> 'h) list"
  and xs6 :: "('h \<times> 'f) list"
  shows
  "RBT_set rbt1 O RBT_set rbt2 = 
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''relcomp RBT_set RBT_set: corder1 = None'') (\<lambda>_. RBT_set rbt1 O RBT_set rbt2)
                     | Some _ \<Rightarrow>
     case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''relcomp RBT_set RBT_set: corder2 = None'') (\<lambda>_. RBT_set rbt1 O RBT_set rbt2)
           | Some (leq_b, lt_b) \<Rightarrow>
       case ID CORDER('c) of None \<Rightarrow> Code.abort (STR ''relcomp RBT_set RBT_set: corder3 = None'') (\<lambda>_. RBT_set rbt1 O RBT_set rbt2)
                         | Some _ \<Rightarrow> RBT_Set2.fold (\<lambda>(x, y). RBT_Set2.fold (\<lambda>(y', z) A. if lt_b y y' \<or> lt_b y' y then A else insert (x, z) A) rbt2) rbt1 {})"
  (is ?rbt_rbt)

  "RBT_set rbt3 O DList_set dxs1 = 
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''relcomp RBT_set DList_set: corder1 = None'') (\<lambda>_. RBT_set rbt3 O DList_set dxs1)
                     | Some _ \<Rightarrow>
     case ID CORDER('d) of None \<Rightarrow> Code.abort (STR ''relcomp RBT_set DList_set: corder2 = None'') (\<lambda>_. RBT_set rbt3 O DList_set dxs1)
                       | Some _ \<Rightarrow>
       case ID CEQ('d) of None \<Rightarrow> Code.abort (STR ''relcomp RBT_set DList_set: ceq2 = None'') (\<lambda>_. RBT_set rbt3 O DList_set dxs1)
                     | Some eq \<Rightarrow>
         case ID CEQ('e) of None \<Rightarrow> Code.abort (STR ''relcomp RBT_set DList_set: ceq3 = None'') (\<lambda>_. RBT_set rbt3 O DList_set dxs1)
                        | Some _ \<Rightarrow> RBT_Set2.fold (\<lambda>(x, y). DList_Set.fold (\<lambda>(y', z) A. if eq y y' then insert (x, z) A else A) dxs1) rbt3 {})"
  (is ?rbt_dlist)

  "DList_set dxs2 O RBT_set rbt4 = 
  (case ID CEQ('e) of None \<Rightarrow> Code.abort (STR ''relcomp DList_set RBT_set: ceq1 = None'') (\<lambda>_. DList_set dxs2 O RBT_set rbt4)
                  | Some _ \<Rightarrow>
     case ID CORDER('d) of None \<Rightarrow> Code.abort (STR ''relcomp DList_set RBT_set: ceq2 = None'') (\<lambda>_. DList_set dxs2 O RBT_set rbt4)
                       | Some _ \<Rightarrow>
       case ID CEQ('d) of None \<Rightarrow> Code.abort (STR ''relcomp DList_set RBT_set: corder2 = None'') (\<lambda>_. DList_set dxs2 O RBT_set rbt4)
                     | Some eq \<Rightarrow>
         case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''relcomp DList_set RBT_set: corder3 = None'') (\<lambda>_. DList_set dxs2 O RBT_set rbt4)
                           | Some _ \<Rightarrow> DList_Set.fold (\<lambda>(x, y). RBT_Set2.fold (\<lambda>(y', z) A. if eq y y' then insert (x, z) A else A) rbt4) dxs2 {})"
  (is ?dlist_rbt)

  "DList_set dxs3 O DList_set dxs4 =
  (case ID CEQ('e) of None \<Rightarrow> Code.abort (STR ''relcomp DList_set DList_set: ceq1 = None'') (\<lambda>_. DList_set dxs3 O DList_set dxs4)
                  | Some _ \<Rightarrow>
     case ID CEQ('f) of None \<Rightarrow> Code.abort (STR ''relcomp DList_set DList_set: ceq2 = None'') (\<lambda>_. DList_set dxs3 O DList_set dxs4)
                   | Some eq \<Rightarrow>
       case ID CEQ('g) of None \<Rightarrow> Code.abort (STR ''relcomp DList_set DList_set: ceq3 = None'') (\<lambda>_. DList_set dxs3 O DList_set dxs4)
                      | Some _ \<Rightarrow> DList_Set.fold (\<lambda>(x, y). DList_Set.fold (\<lambda>(y', z) A. if eq y y' then insert (x, z) A else A) dxs4) dxs3 {})"
  (is ?dlist_dlist)

  "Set_Monad xs1 O Set_Monad xs2 =
  (case ID CEQ('i) of None \<Rightarrow> Code.abort (STR ''relcomp Set_Monad Set_Monad: ceq = None'') (\<lambda>_. Set_Monad xs1 O Set_Monad xs2)
                 | Some eq \<Rightarrow> fold (\<lambda>(x, y). fold (\<lambda>(y', z) A. if eq y y' then insert (x, z) A else A) xs2) xs1 {})"
  (is ?monad_monad)

  "RBT_set rbt1 O Set_Monad xs3 =
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''relcomp RBT_set Set_Monad: corder1 = None'') (\<lambda>_. RBT_set rbt1 O Set_Monad xs3)
                     | Some _ \<Rightarrow>
     case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''relcomp RBT_set Set_Monad: corder2 = None'') (\<lambda>_. RBT_set rbt1 O Set_Monad xs3)
           | Some (leq_b, lt_b) \<Rightarrow> RBT_Set2.fold (\<lambda>(x, y). fold (\<lambda>(y', z) A. if lt_b y y' \<or> lt_b y' y then A else insert (x, z) A) xs3) rbt1 {})"
  (is ?rbt_monad)

  "Set_Monad xs4 O RBT_set rbt5 =
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''relcomp Set_Monad RBT_set: corder1 = None'') (\<lambda>_. Set_Monad xs4 O RBT_set rbt5)
                     | Some _ \<Rightarrow>
     case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''relcomp Set_Monad RBT_set: corder2 = None'') (\<lambda>_. Set_Monad xs4 O RBT_set rbt5)
           | Some (leq_b, lt_b) \<Rightarrow> fold (\<lambda>(x, y). RBT_Set2.fold (\<lambda>(y', z) A. if lt_b y y' \<or> lt_b y' y then A else insert (x, z) A) rbt5) xs4 {})"
  (is ?monad_rbt)

  "DList_set dxs3 O Set_Monad xs5 =
  (case ID CEQ('e) of None \<Rightarrow> Code.abort (STR ''relcomp DList_set Set_Monad: ceq1 = None'') (\<lambda>_. DList_set dxs3 O Set_Monad xs5)
                  | Some _ \<Rightarrow>
     case ID CEQ('f) of None \<Rightarrow> Code.abort (STR ''relcomp DList_set Set_Monad: ceq2 = None'') (\<lambda>_. DList_set dxs3 O Set_Monad xs5)
                   | Some eq \<Rightarrow> DList_Set.fold (\<lambda>(x, y). fold (\<lambda>(y', z) A. if eq y y' then insert (x, z) A else A) xs5) dxs3 {})"
  (is ?dlist_monad)

  "Set_Monad xs6 O DList_set dxs4 =
  (case ID CEQ('f) of None \<Rightarrow> Code.abort (STR ''relcomp Set_Monad DList_set: ceq1 = None'') (\<lambda>_. Set_Monad xs6 O DList_set dxs4)
                      | Some eq \<Rightarrow>
     case ID CEQ('g) of None \<Rightarrow> Code.abort (STR ''relcomp Set_Monad DList_set: ceq2 = None'') (\<lambda>_. Set_Monad xs6 O DList_set dxs4)
                   | Some _ \<Rightarrow> fold (\<lambda>(x, y). DList_Set.fold (\<lambda>(y', z) A. if eq y y' then insert (x, z) A else A) dxs4) xs6 {})"
  (is ?monad_dlist)
proof -

  { fix leq_b lt_b
    assume "ID CORDER('b) = Some (leq_b, lt_b)"
    hence "\<And>y y'. lt_b y y' \<or> lt_b y' y \<longleftrightarrow> y \<noteq> y'"
      by(rule linorder.neq_iff[OF ID_corder, symmetric]) }
  thus ?rbt_rbt ?rbt_monad ?monad_rbt
    by(auto simp add: RBT_set_def corder_prod_def member_conv_keys ID_Some RBT_Set2.fold_conv_fold_keys' RBT_Set2.keys.rep_eq If_not set_relcomp_set split: option.split del: equalityI)

  show ?rbt_dlist ?dlist_rbt ?dlist_dlist ?monad_monad ?dlist_monad ?monad_dlist
    by(auto simp add: RBT_set_def DList_set_def member_conv_keys ID_Some corder_prod_def ceq_prod_def Collect_member RBT_Set2.fold_conv_fold_keys' RBT_Set2.keys.rep_eq DList_Set.fold.rep_eq set_relcomp_set dest: equal.equal_eq[OF ID_ceq] split: option.split del: equalityI)
qed

lemma [code, code del]: "irrefl = irrefl" ..

lemma irrefl_code [code]:
  fixes r :: "('a :: {ceq, corder} \<times> 'a) set" shows
  "irrefl r \<longleftrightarrow> 
  (case ID CEQ('a) of Some eq \<Rightarrow> (\<forall>(x, y) \<in> r. \<not> eq x y) | None \<Rightarrow>
    case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''irrefl: ceq = None & corder = None'') (\<lambda>_. irrefl r)
                | Some (le, lt) \<Rightarrow> (\<forall>(x, y) \<in> r. lt x y \<or> lt y x))"
apply(auto simp add: irrefl_distinct linorder.not_less_iff_gr_or_eq[OF ID_corder] split: option.split dest!: ID_ceq[THEN equal.equal_eq])
apply(auto dest!: ID_corder bspec simp add: class.linorder_def class.order_def preorder.less_irrefl)
done

lemma wf_code [code]:
  fixes rbt :: "('a :: corder \<times> 'a) set_rbt" 
  and dxs :: "('b :: ceq \<times> 'b) set_dlist" shows
  "wf (Set_Monad xs) = acyclic (Set_Monad xs)"
  "wf (RBT_set rbt) = 
  (case ID CORDER('a) of None \<Rightarrow> Code.abort (STR ''wf RBT_set: corder = None'') (\<lambda>_. wf (RBT_set rbt))
                     | Some _ \<Rightarrow> acyclic (RBT_set rbt))"
  "wf (DList_set dxs) =
  (case ID CEQ('b) of None \<Rightarrow> Code.abort (STR ''wf DList_set: ceq = None'') (\<lambda>_. wf (DList_set dxs))
                     | Some _ \<Rightarrow> acyclic (DList_set dxs))"
by(auto simp add: wf_iff_acyclic_if_finite split: option.split del: iffI)(simp_all add: wf_iff_acyclic_if_finite finite_code corder_prod_def ceq_prod_def ID_Some)

lemma [code, code del]: "bacc = bacc" ..

lemma bacc_code [code]:
  "bacc R 0 = - snd ` R"
  "bacc R (Suc n) = (let rec = bacc R n in rec \<union> - snd ` (Set.filter (\<lambda>(y, x). y \<notin> rec) R))"
by(auto intro: rev_image_eqI simp add: Let_def)

(* TODO: acc could also be computed for infinite universes if r is finite *)

lemma acc_code [code]:
  fixes A :: "('a :: {finite, card_UNIV} \<times> 'a) set" shows
  "acc A = bacc A (of_phantom (card_UNIV :: 'a card_UNIV))"
by(simp add: card_UNIV acc_bacc_eq)

lemma sorted_list_of_set_code [code]:
  fixes dxs :: "'a :: {linorder, ceq} set_dlist"
  and rbt :: "'b :: {linorder, corder} set_rbt"
  shows
  "sorted_list_of_set (Set_Monad xs) = sort (remdups xs)"
  "sorted_list_of_set (DList_set dxs) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''sorted_list_of_set DList_set: ceq = None'') (\<lambda>_. sorted_list_of_set (DList_set dxs))
                  | Some _ \<Rightarrow> sort (list_of_dlist dxs))"
  "sorted_list_of_set (RBT_set rbt) =
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''sorted_list_of_set RBT_set: corder = None'') (\<lambda>_. sorted_list_of_set (RBT_set rbt))
                     | Some _ \<Rightarrow> sort (RBT_Set2.keys rbt))"
  -- {* We must sort the keys because @{term corder}'s ordering need not coincide with @{term linorder}'s. *}
by(auto simp add: DList_set_def RBT_set_def sorted_list_of_set_sort_remdups Collect_member distinct_remdups_id distinct_list_of_dlist member_conv_keys split: option.split)

lemma map_project_set: "List.map_project f (set xs) = set (List.map_filter f xs)"
by(auto simp add: List.map_project_def List.map_filter_def intro: rev_image_eqI)

lemma map_project_simps:
  shows map_project_empty: "List.map_project f {} = {}"
  and map_project_insert: 
  "List.map_project f (insert x A) = 
  (case f x of None \<Rightarrow> List.map_project f A 
   | Some y \<Rightarrow> insert y (List.map_project f A))"
by(auto simp add: List.map_project_def split: option.split)

lemma map_project_conv_fold: 
  "List.map_project f (set xs) = 
   fold (\<lambda>x A. case f x of None \<Rightarrow> A | Some y \<Rightarrow> insert y A) xs {}"
by(induct xs rule: rev_induct)(simp_all add: map_project_simps cong: option.case_cong)

lemma map_project_code [code]:
  fixes dxs :: "'a :: ceq set_dlist" 
  and rbt :: "'b :: corder set_rbt" shows
  "List.map_project f (Set_Monad xs) = Set_Monad (List.map_filter f xs)"
  "List.map_project g (DList_set dxs) = 
   (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''map_project DList_set: ceq = None'') (\<lambda>_. List.map_project g (DList_set dxs))
                   | Some _ \<Rightarrow> DList_Set.fold (\<lambda>x A. case g x of None \<Rightarrow> A | Some y \<Rightarrow> insert y A) dxs {})"
  (is ?dlist)
  "List.map_project h (RBT_set rbt) = 
   (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''map_project RBT_set: corder = None'') (\<lambda>_. List.map_project h (RBT_set rbt))
                      | Some _ \<Rightarrow> RBT_Set2.fold (\<lambda>x A. case h x of None \<Rightarrow> A | Some y \<Rightarrow> insert y A) rbt {})"
  (is ?rbt)
proof -
  show ?dlist ?rbt
    by(auto split: option.split simp add: RBT_set_def DList_set_def DList_Set.fold.rep_eq Collect_member map_project_conv_fold RBT_Set2.fold_conv_fold_keys member_conv_keys del: equalityI)
qed(auto simp add: List.map_project_def List.map_filter_def intro: rev_image_eqI)

lemma Bleast_code [code]:
  "Bleast A P = 
  (if finite A then case filter P (sorted_list_of_set A) of [] \<Rightarrow> abort_Bleast A P | x # xs \<Rightarrow> x 
   else abort_Bleast A P)"
proof(cases "finite A")
  case True
  hence *: "A = set (sorted_list_of_set A)" by(simp add: sorted_list_of_set)
  show ?thesis using True
    by(subst (1 3) *)(unfold Bleast_code, simp add: sorted_sort_id)
qed(simp add: abort_Bleast_def Bleast_def)

lemma can_select_code [code]:
  fixes xs :: "'a :: ceq list" 
  and dxs :: "'a :: ceq set_dlist" 
  and rbt :: "'b :: corder set_rbt" shows
  "can_select P (Set_Monad xs) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''can_select Set_Monad: ceq = None'') (\<lambda>_. can_select P (Set_Monad xs))
                 | Some eq \<Rightarrow> case filter P xs of Nil \<Rightarrow> False | x # xs \<Rightarrow> list_all (eq x) xs)"
  (is ?Set_Monad)
  "can_select Q (DList_set dxs) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''can_select DList_set: ceq = None'') (\<lambda>_. can_select Q (DList_set dxs))
                  | Some _ \<Rightarrow> DList_Set.length (DList_Set.filter Q dxs) = 1)"
  (is ?dlist)
  "can_select R (RBT_set rbt) =
  (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''can_select RBT_set: corder = None'') (\<lambda>_. can_select R (RBT_set rbt))
                 | Some _ \<Rightarrow> singleton_list_fusion (filter_generator R rbt_keys_generator) (RBT_Set2.init rbt))"
  (is ?rbt)
proof -
  show ?Set_Monad
    apply(auto split: option.split list.split dest!: ID_ceq[THEN equal.equal_eq] dest: filter_eq_ConsD simp add: can_select_def filter_empty_conv list_all_iff)
    apply(drule filter_eq_ConsD, fastforce)
    apply(drule filter_eq_ConsD, clarsimp, blast)
    done
  
  show ?dlist
    by(clarsimp simp add: can_select_def card_eq_length[symmetric] Set_member_code card_eq_Suc_0_ex1 simp del: card_eq_length split: option.split)
  
  note [simp del] = distinct_keys
  show ?rbt
    using distinct_keys[of rbt]
    apply(auto simp add: can_select_def singleton_list_fusion_def unfoldr_filter_generator unfoldr_rbt_keys_generator Set_member_code member_conv_keys filter_empty_conv empty_filter_conv split: option.split list.split dest: filter_eq_ConsD)
      apply(drule filter_eq_ConsD, fastforce)
     apply(drule filter_eq_ConsD, fastforce simp add: empty_filter_conv)
    apply(drule filter_eq_ConsD)
    apply clarsimp
    apply(drule Cons_eq_filterD)
    apply clarify
    apply(simp (no_asm_use))
    apply blast
    done
qed

lemma pred_of_set_code [code]:
  fixes dxs :: "'a :: ceq set_dlist" 
  and rbt :: "'b :: corder set_rbt" shows
  "pred_of_set (Set_Monad xs) = fold (sup \<circ> Predicate.single) xs bot"
  "pred_of_set (DList_set dxs) =
   (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''pred_of_set DList_set: ceq = None'') (\<lambda>_. pred_of_set (DList_set dxs))
                   | Some _ \<Rightarrow> DList_Set.fold (sup \<circ> Predicate.single) dxs bot)"
  "pred_of_set (RBT_set rbt) =
   (case ID CORDER('b) of None \<Rightarrow> Code.abort (STR ''pred_of_set RBT_set: corder = None'') (\<lambda>_. pred_of_set (RBT_set rbt))
                      | Some _ \<Rightarrow> RBT_Set2.fold (sup \<circ> Predicate.single) rbt bot)"
by(auto simp add: pred_of_set_set_fold_sup fold_map DList_set_def RBT_set_def Collect_member member_conv_keys DList_Set.fold.rep_eq fold_conv_fold_keys split: option.split)

text {* 
  @{typ "'a Predicate.pred"} is implemented as a monad, 
  so we keep the monad when converting to @{typ "'a set"}. 
  For this case, @{term insert_monad} and @{term union_monad} 
  avoid the unnecessary dictionary construction.
*}

definition insert_monad :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
where [simp]: "insert_monad = insert"

definition union_monad :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
where [simp]: "union_monad = op \<union>"

lemma insert_monad_code [code]:
  "insert_monad x (Set_Monad xs) = Set_Monad (x # xs)"
by simp

lemma union_monad_code [code]:
  "union_monad (Set_Monad xs) (Set_Monad ys) = Set_Monad (xs @ ys)"
by(simp)

lemma [code, code del]: "set_of_pred = set_of_pred" ..
lemma [code, code del]: "set_of_seq = set_of_seq" ..

lemma set_of_pred_code [code]:
  "set_of_pred (Predicate.Seq f) = 
  (case f () of seq.Empty \<Rightarrow> Set_Monad []
   | seq.Insert x P \<Rightarrow> insert_monad x (set_of_pred P)
   | seq.Join P xq \<Rightarrow> union_monad (set_of_pred P) (set_of_seq xq))"
by(simp add: of_pred_code cong: seq.case_cong)

lemma set_of_seq_code [code]:
  "set_of_seq seq.Empty = Set_Monad []"
  "set_of_seq (seq.Insert x P) = insert_monad x (set_of_pred P)"
  "set_of_seq (seq.Join P xq) = union_monad (set_of_pred P) (set_of_seq xq)"
by(simp_all add: of_seq_code)

hide_const (open) insert_monad union_monad

subsection {* Type class instantiations *}

datatype set_impl = Set_IMPL
declare
  set_impl.eq.simps [code del]
  set_impl.size [code del]
  set_impl.recs [code del]
  set_impl.cases [code del]

lemma [code]: 
  fixes x :: set_impl
  shows "size x = 0"
  and "set_impl_size x = 0"
by(case_tac [!] x) simp_all

definition set_Choose :: set_impl where [simp]: "set_Choose = Set_IMPL"
definition set_Collect :: set_impl where [simp]: "set_Collect = Set_IMPL"
definition set_DList :: set_impl where [simp]: "set_DList = Set_IMPL"
definition set_RBT :: set_impl where [simp]: "set_RBT = Set_IMPL"
definition set_Monad :: set_impl where [simp]: "set_Monad = Set_IMPL"

code_datatype set_Choose set_Collect set_DList set_RBT set_Monad

definition set_empty_choose :: "'a set" where [simp]: "set_empty_choose = {}"

lemma set_empty_choose_code [code]:
  "(set_empty_choose :: 'a :: {ceq, corder} set) =
   (case CORDER('a) of Some _  \<Rightarrow> RBT_set RBT_Set2.empty
    | None \<Rightarrow> case CEQ('a) of None \<Rightarrow> Set_Monad [] | Some _ \<Rightarrow> DList_set (DList_Set.empty))"
by(simp split: option.split)

definition set_impl_choose2 :: "set_impl \<Rightarrow> set_impl \<Rightarrow> set_impl"
where [simp]: "set_impl_choose2 = (\<lambda>_ _. Set_IMPL)"

lemma set_impl_choose2_code [code]:
  "set_impl_choose2 x y = set_Choose"
  "set_impl_choose2 set_Collect set_Collect = set_Collect"
  "set_impl_choose2 set_DList set_DList = set_DList"
  "set_impl_choose2 set_RBT set_RBT = set_RBT"
  "set_impl_choose2 set_Monad set_Monad = set_Monad"
by(simp_all)

definition set_empty :: "set_impl \<Rightarrow> 'a set"
where [simp]: "set_empty = (\<lambda>_. {})"

lemma set_empty_code [code]:
  "set_empty set_Collect = Collect_set (\<lambda>_. False)"
  "set_empty set_DList = DList_set DList_Set.empty"
  "set_empty set_RBT = RBT_set RBT_Set2.empty"
  "set_empty set_Monad = Set_Monad []"
  "set_empty set_Choose = set_empty_choose"
by(simp_all)

class set_impl =
  fixes set_impl :: "('a, set_impl) phantom"

syntax (input)
  "_SET_IMPL" :: "type => logic"  ("(1SET'_IMPL/(1'(_')))")

parse_translation {*
let
  fun set_impl_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "set_impl"} $
       (Syntax.const @{type_syntax phantom} $ ty $ Syntax.const @{type_syntax set_impl}))
    | set_impl_tr ts = raise TERM ("set_impl_tr", ts);
in [(@{syntax_const "_SET_IMPL"}, K set_impl_tr)] end
*}

lemma [code, code del]: "{} = {}" ..

lemma empty_code [code, code_unfold]: 
  "({} :: 'a :: set_impl set) = set_empty (of_phantom SET_IMPL('a))"
by simp

subsection {* Generator for the @{class set_impl}-class *}

text {*
This generator registers itself at the derive-manager for the classes @{class set_impl}.
Here, one can choose
the desired implementation via the parameter.

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (rbt,dlist,collect,monad,choose, or arbitrary constant name) set-impl}
\end{itemize}
*}


text {*
This generator can be used for arbitrary types, not just datatypes. 
*}

ML_file "set_impl_generator.ML" 
setup {*
  Set_Impl_Generator.setup
*}

derive (dlist) set_impl unit
derive (dlist) set_impl bool
derive (rbt) set_impl nat
derive (set_RBT) set_impl int (* shows usage of constant names *)
derive (dlist) set_impl Enum.finite_1
derive (dlist) set_impl Enum.finite_2
derive (dlist) set_impl Enum.finite_3
derive (rbt) set_impl integer
derive (rbt) set_impl natural
derive (dlist) set_impl nibble
derive (rbt) set_impl char

instantiation sum :: (set_impl, set_impl) set_impl begin
definition "SET_IMPL('a + 'b) = Phantom('a + 'b) 
  (set_impl_choose2 (of_phantom SET_IMPL('a)) (of_phantom SET_IMPL('b)))"
instance ..
end

instantiation prod :: (set_impl, set_impl) set_impl begin
definition "SET_IMPL('a * 'b) = Phantom('a * 'b) 
  (set_impl_choose2 (of_phantom SET_IMPL('a)) (of_phantom SET_IMPL('b)))"
instance ..
end

derive (choose) set_impl list
derive (rbt) set_impl String.literal

instantiation option :: (set_impl) set_impl begin
definition "SET_IMPL('a option) = Phantom('a option) (of_phantom SET_IMPL('a))"
instance ..
end

derive (monad) set_impl "fun"
derive (choose) set_impl set

instantiation phantom :: (type, set_impl) set_impl begin
definition "SET_IMPL(('a, 'b) phantom) = Phantom (('a, 'b) phantom) (of_phantom SET_IMPL('b))"
instance ..
end

text {*
  We enable automatic implementation selection for sets constructed by @{const set},
  although they could be directly converted using @{const Set_Monad} in constant time.
  However, then it is more likely that the parameters of binary operators have 
  different implementations, which can lead to less efficient execution.

  However, we test whether automatic selection picks @{const Set_Monad} anyway and
  take a short-cut.
*}

definition set_aux :: "set_impl \<Rightarrow> 'a list \<Rightarrow> 'a set"
where [simp, code del]: "set_aux _ = set"

lemma set_aux_code [code]:
  defines "conv \<equiv> foldl (\<lambda>s (x :: 'a). insert x s)"
  shows
  "set_aux impl = conv (set_empty impl)" (is "?thesis1")
  "set_aux set_Choose = 
   (case CORDER('a :: {corder, ceq}) of Some _  \<Rightarrow> conv (RBT_set RBT_Set2.empty)
    | None \<Rightarrow> case CEQ('a) of None \<Rightarrow> Set_Monad
              | Some _ \<Rightarrow> conv (DList_set DList_Set.empty))" (is "?thesis2")
  "set_aux set_Monad = Set_Monad"
proof -
  have "conv {} = set"
    by(rule ext)(induct_tac x rule: rev_induct, simp_all add: conv_def)
  thus ?thesis1 ?thesis2
    by(simp_all split: option.split)
qed simp

lemma set_code [code]:
  fixes xs :: "'a :: set_impl list"
  shows "set xs = set_aux (of_phantom (ID SET_IMPL('a))) xs"
by(simp)

subsection {* Pretty printing for sets *}

text {*
  @{term code_post} marks contexts (as hypothesis) in which we use code\_post as a
  decision procedure rather than a pretty-printing engine. 
  The intended use is to enable more rules when proving assumptions of rewrite rules.
*}

definition code_post :: bool where "code_post = True"

lemma conj_code_post [code_post]: 
  assumes code_post
  shows "True & x \<longleftrightarrow> x" "False & x \<longleftrightarrow> False"
by simp_all

text {*
  A flag to switch post-processing of sets on and off.
  Use \verb$declare pretty_sets[code_post del]$ to disable pretty printing of sets in value.
*}

definition code_post_set :: bool
where pretty_sets [code_post, simp]: "code_post_set = True"

definition collapse_RBT_set :: "'a set_rbt \<Rightarrow> 'a :: corder set \<Rightarrow> 'a set"
where "collapse_RBT_set r M = set (RBT_Set2.keys r) \<union> M"

lemma RBT_set_collapse_RBT_set [code_post]:
  fixes r :: "'a :: corder set_rbt"
  assumes "code_post \<Longrightarrow> is_corder TYPE('a)" and code_post_set
  shows "RBT_set r = collapse_RBT_set r {}"
using assms
by(clarsimp simp add: code_post_def is_corder_def RBT_set_def member_conv_keys collapse_RBT_set_def)

lemma collapse_RBT_set_Branch [code_post]: 
  "collapse_RBT_set (Mapping_RBT (Branch c l x v r)) M =
   collapse_RBT_set (Mapping_RBT l) (insert x (collapse_RBT_set (Mapping_RBT r) M))"
unfolding collapse_RBT_set_def
by(auto simp add: is_corder_def set_keys_Mapping_RBT)

lemma collapse_RBT_set_Empty [code_post]: 
  "collapse_RBT_set (Mapping_RBT rbt.Empty) M = M"
by(auto simp add: collapse_RBT_set_def set_keys_Mapping_RBT)

definition collapse_DList_set :: "'a :: ceq set_dlist \<Rightarrow> 'a set"
where "collapse_DList_set dxs = set (DList_Set.list_of_dlist dxs)"

lemma DList_set_collapse_DList_set [code_post]:
  fixes dxs :: "'a :: ceq set_dlist"
  assumes "code_post \<Longrightarrow> is_ceq TYPE('a)" and code_post_set
  shows "DList_set dxs = collapse_DList_set dxs"
using assms
by(clarsimp simp add: code_post_def DList_set_def is_ceq_def collapse_DList_set_def Collect_member)

lemma collapse_DList_set_empty [code_post]: "collapse_DList_set (Abs_dlist []) = {}"
by(simp add: collapse_DList_set_def Abs_dlist_inverse)

lemma collapse_DList_set_Cons [code_post]: 
  "collapse_DList_set (Abs_dlist (x # xs)) = insert x (collapse_DList_set (Abs_dlist xs))"
by(simp add: collapse_DList_set_def set_list_of_dlist_Abs_dlist)

lemma Set_Monad_code_post [code_post]:
  assumes code_post_set
  shows "Set_Monad [] = {}"
  and "Set_Monad (x#xs) = insert x (Set_Monad xs)"
by simp_all

end
