theory Stores
  imports Memory
begin

section \<open>Calldata\<close>

datatype 'v call_data =
  is_Value: Value (vt: "'v")
  | is_Array: Array (ar: "'v call_data list")

fun c_to_s where
  "c_to_s (Value v) = adata.Value v"
| "c_to_s (Array xs) = adata.Array (map c_to_s xs)"

fun s_to_c where
  "s_to_c (adata.Value v) = Value v"
| "s_to_c (adata.Array xs) = Array (map s_to_c xs)"

lemma stoc_ctos:
  "s_to_c (c_to_s a) = a"
  by (induction a,auto simp add: map_idI)

lemma eq_iff_stoc:
  "a = b \<longleftrightarrow> s_to_c a = s_to_c b"
proof (induction a arbitrary: b)
  case (Value x)
  then show ?case
    by (metis c_to_s.simps(1,2) s_to_c.elims adata.disc(1,2))
next
  case (Array xs)
  show ?case
    apply simp using Array
    by (metis call_data.disc(3,4) call_data.sel(2) list.inj_map_strong
        s_to_c.elims s_to_c.simps(2))
qed

function (sequential) T where
  "T (adata.Value v) (Value v') = (v = v')"
 |"T (adata.Array xs) (Array xs') = list_all2 T xs xs'"
 |"T _ _ = False"
  by pat_completeness auto
termination T
  apply (relation "measure (\<lambda>(a,b). size a)")
  apply simp
  apply auto
  by (meson less_irrefl_nat not_less_eq nth_mem size_list_estimation)

lemma T_eq_stoc:
  "T x y = (s_to_c x = y)"
proof (induction x arbitrary: y)
  case (Value x)
  then show ?case
    using T.elims(1) by auto
next
  case (Array xs)
  then show ?case
  proof (cases y)
    case (Value x1)
    then show ?thesis
      by (simp add: Array)
  next
    case _: (Array ys)
    then show ?thesis using Array set_listall[where ?f=s_to_c and ?R = T, of xs ys]
      by simp
  qed
qed
  
lemma q: "Quotient (=) s_to_c c_to_s T"
proof (rule QuotientI)
  show "\<And>a. s_to_c (c_to_s a) = a" using stoc_ctos by blast
next
  show "\<And>a. c_to_s a = c_to_s a" by simp
next
  show "\<And>r s. (r = s) = (r = r \<and> s = s \<and> s_to_c r = s_to_c s)" using eq_iff_stoc by blast
next
  show "T = (\<lambda>x y. x = x \<and> s_to_c x = y)" using T_eq_stoc by auto
qed

setup_lifting q

code_datatype call_data.Value call_data.Array

lift_definition "write" :: "'v call_data \<Rightarrow> 'v memory \<Rightarrow> nat \<times> 'v memory" is Memory.write .
lift_definition clookup :: "'v::vtype list \<Rightarrow> 'v call_data \<Rightarrow> 'v call_data option" is Memory.alookup .

context includes lifting_syntax begin

lemma Value_transfer[transfer_rule]: "(R ===> (pcr_call_data R)) adata.Value call_data.Value"
  apply (auto simp: rel_fun_def pcr_call_data_def relcompp_apply)
  by (meson T.simps(1) adata.rel_inject(1))

lemma Array_transfer[transfer_rule]: "((list_all2 (pcr_call_data R)) ===> (pcr_call_data R)) adata.Array call_data.Array"
  apply (auto simp: rel_fun_def pcr_call_data_def relcompp_apply)
proof -
  fix x y
  assume "list_all2 (rel_adata R OO T) x y"
  then show "\<exists>b. rel_adata R (adata.Array x) b \<and> T b (call_data.Array y)"
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case
      by (metis T_eq_stoc list.ctr_transfer(1) list.map_disc_iff s_to_c.simps(2) adata.rel_inject(2))
  next
    case (Cons x xs y ys)
    then obtain b where *: "rel_adata R (adata.Array xs) b \<and> T b (call_data.Array ys)" by blast
    then obtain ys' where ys_def: "b = adata.Array ys'"
      by (metis T.simps(4) adata.exhaust_sel)

    from ys_def have "rel_adata R (adata.Array (x # xs)) (adata.Array (c_to_s y # ys'))"
      by (metis Cons.hyps(1) T_eq_stoc * stoc_ctos eq_iff_stoc list.rel_intros(2) relcompp.cases adata.rel_inject(2))
    moreover from ys_def have "T (adata.Array (c_to_s y # ys')) (call_data.Array (y # ys))"
      using T_eq_stoc * stoc_ctos by auto
    ultimately show ?case by blast
  qed
qed

lemma fold_map_transfer[transfer_rule]: "((A ===> B ===> rel_prod C B) ===> list_all2 A ===> B ===> rel_prod (list_all2 C) B) fold_map fold_map"
  apply (auto simp: rel_fun_def pcr_call_data_def relcompp_apply)
proof -
  fix x y xa ya xb yb
  assume "list_all2 A xa ya"
and "\<forall>xa ya. A xa ya \<longrightarrow> (\<forall>xb yb. B xb yb \<longrightarrow> rel_prod C B (x xa xb) (y ya yb))"
    and "B xb yb"
  then show "rel_prod (list_all2 C) B (fold_map x xa xb) (fold_map y ya yb)"
  proof (induction arbitrary: xb yb rule: list_all2_induct)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x' xs y' ys)
    obtain x0 y0 xs0 y0' where 1: "x x' xb = (x0, y0)" and 2: "(fold_map x xs y0) = (xs0, y0')" and 3: "(fold_map x (x' # xs) xb) = (x0 # xs0, y0')" by fastforce
    obtain x1 y1 xs1 y1' where 4: "y y' yb = (x1, y1)" and 5: "(fold_map y ys y1) = (xs1, y1')" and 6: "(fold_map y (y' # ys) yb) = (x1 # xs1, y1')" by fastforce

    from Cons have "rel_prod (list_all2 C) B (fold_map x xs y0) (fold_map y ys y1)"
      using \<open>x x' xb = (x0, y0)\<close> \<open>y y' yb = (x1, y1)\<close> by force
    then have "(list_all2 C) xs0 xs1"
      and "B y0' y1'" using 2 5 by simp+
    moreover have "C x0 x1"
      using Cons.hyps(1) Cons.prems(1,2) 1 4 by fastforce
    then have "(list_all2 C) (x0 # xs0) (x1 # xs1)"
      by (simp add: \<open>list_all2 C xs0 xs1\<close>)
    ultimately show ?case using 3 6 by simp
  qed
qed

lemma eq_transfer[transfer_rule]: "(rel_option (pcr_call_data (=)) ===> (rel_option (pcr_call_data (=)) ===> (=))) (=) (=)"
  apply (auto simp: rel_fun_def pcr_call_data_def relcompp_apply)
  apply (metis T_eq_stoc eq_OO option.rel_cases option.sel rel_option_None1 adata.rel_eq)
  by (metis T_eq_stoc eq_iff_stoc eq_OO option.rel_eq option.rel_sel adata.rel_eq)

lemma nth_safe_transfer[transfer_rule]: "(list_all2 ((pcr_call_data (=))) ===> ((=)) ===> rel_option (pcr_call_data (=))) nth_safe nth_safe"
  apply (auto simp: rel_fun_def pcr_call_data_def relcompp_apply)
  apply (simp add: eq_OO list_all2_conv_all_nth adata.rel_eq)
  by (simp add: nth_safe_def)

end

lemma write_length_append[simp,code]: "write (call_data.Value x) m = length_append m (mdata.Value x)"
  apply transfer
  by simp

lemma write_fold_map_length_append[simp,code]:
  "write (call_data.Array ds) m = (let (ns, m')
    = fold_map write ds m in (length_append m' (mdata.Array ns)))"
  apply transfer
  by auto

lemma clookup[simp,code]:
  "clookup [] s = Some s"
  apply (transfer)
  by simp

lemma clookup2[simp,code]:
  "clookup (i # is) (call_data.Array xs) = vtype_class.to_nat i \<bind> ($) xs \<bind> clookup is"
  apply transfer
  by simp

lemma clookup_none[simp,code]:
 "clookup (v # va) (call_data.Value vb) = None"
  apply transfer by simp

lemma write_length_inc: "length (snd (write cd m0)) > length m0"
  apply transfer using write_length_inc by blast

corollary write_loc:
  assumes "write cd m0 = (l, m)"
  shows "s_union_fs (loc m) (loc m0) (arange m l)"
  using assms apply transfer using write_loc by blast

section \<open>Storage\<close>

datatype 'v storage_data =
  is_Value: Value (vt:'v)
| is_Array: Array (ar: "'v storage_data list")
| is_Map: Map (mp: "'v \<Rightarrow> 'v storage_data")

abbreviation storage_check where "storage_check sd vf af mf \<equiv> case_storage_data vf af mf sd"

section \<open>Storage Lookup\<close>

text \<open>
  slookup is sd navigates storage sd according to the index sequence is.
\<close>
fun slookup :: "'v::vtype list \<Rightarrow> 'v storage_data \<Rightarrow> 'v storage_data option" where
  "slookup [] s = Some s"
| "slookup (i # is) (storage_data.Array xs) = to_nat i \<bind> ($) xs \<bind> slookup is"
| "slookup (i # is) (storage_data.Map f) = slookup is (f i)"
| "slookup _ _ = None"

section \<open>Storage Update\<close>

fun updateStore :: "('v::vtype) list \<Rightarrow> ('v storage_data \<Rightarrow> 'v storage_data) \<Rightarrow> 'v storage_data \<Rightarrow> 'v storage_data option" where
  "updateStore [] f v = Some (f v)"
| "updateStore (i # is) f (storage_data.Array xs) =
    to_nat i
    \<bind> (\<lambda>i. xs $ i \<bind> updateStore is f \<bind> list_update_safe xs i \<bind> Some \<circ> storage_data.Array)"
| "updateStore (i # is) f (Map m) = updateStore is f (m i) \<bind> Some \<circ> storage_data.Map \<circ> fun_upd m i"
| "updateStore _ _ _ = None"

subsection \<open>Copy from Calldata to Memory\<close>

fun copy_calldata_memory :: "'v call_data \<Rightarrow> location \<Rightarrow> 'v memory \<Rightarrow> (location \<times> 'v mdata \<times> 'v memory)" where
  "copy_calldata_memory (call_data.Value x) p m = (p, mdata.Value x, m)"
| "copy_calldata_memory (call_data.Array ds) p m =
      (let (ns, m') = fold_map write ds m in (p, mdata.Array ns, m'))"

subsection \<open>Copy from Calldata to Storage\<close>

fun copy_calldata_storage :: "'v call_data \<Rightarrow> 'v storage_data" where
  "copy_calldata_storage (call_data.Value v) = storage_data.Value v"
| "copy_calldata_storage (call_data.Array xs) = storage_data.Array (map copy_calldata_storage xs)"

subsection \<open>Copy from Storage to Memory\<close>

(*
  Note: In Solidity assigning a storage array to a memory array results
  in a new array added at the end and the pointer adapted.
*)

fun convert2 :: "'v storage_data \<Rightarrow> 'v adata option" where
  "convert2 (storage_data.Value x) = Some (adata.Value x)"
| "convert2 (storage_data.Array ds) = those (map convert2 ds) \<bind> Some \<circ> adata.Array"
| "convert2 _ = None"

fun convert :: "'v storage_data \<Rightarrow> 'v call_data option" where
  "convert (storage_data.Value x) = Some (call_data.Value x)"
| "convert (storage_data.Array ds) = those (map convert ds) \<bind> Some \<circ> call_data.Array"
| "convert _ = None"

definition copy_storage_memory :: "'v storage_data \<Rightarrow> location \<Rightarrow> 'v memory \<Rightarrow> (location \<times> 'v mdata \<times> 'v memory) option" where
  "copy_storage_memory sd p m =
    do {
      cd \<leftarrow> convert sd;
      Some (copy_calldata_memory cd p m)
    }"

global_interpretation storage_data: data storage_data.Value storage_data.Array
  defines copy_memory_storage_safe = storage_data.read_safe
      and copy_memory_storage = storage_data.read
      and range_storage_safe = storage_data.range_safe
      and range_storage = storage_data.range
  .

subsection \<open>Data type\<close>

record 'v pointer =
  Location :: String.literal
  Offset :: "'v list"

datatype 'v kdata =
  Storage "'v pointer option" |
  Memory (memloc: location) |
  Calldata "'v pointer option" |
  Value (vt: "'v")

end