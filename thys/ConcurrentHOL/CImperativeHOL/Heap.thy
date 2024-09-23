(*<*)
theory Heap
imports
  Ix
  "ConcurrentHOL.ConcurrentHOL"
begin

(*>*)
section\<open> A polymorphic heap\label{sec:CImperativeHOL-heap} \<close>

text\<open>

We model a heap as a partial map from opaque addresses to structured objects.
 \<^item> we use this extra structure to handle buffered writes (see \S\ref{sec:tso})
 \<^item> allocation is non-deterministic and partial
 \<^item> supports explicit deallocation

Limitations:
 \<^item> does not support polymorphic sum types such as \<^typ>\<open>'a + 'b\<close> and \<^typ>\<open>'a option\<close> or products or lists
 \<^item> the class of representable types is too small to represent processes

Source materials:
 \<^item> \<^file>\<open>$ISABELLE_HOME/src/HOL/Imperative_HOL/Heap.thy\<close>
  \<^item> that model of heaps includes a \<open>lim\<close> field to support deterministic allocation
  \<^item> it uses distinct heaps for arrays and references

\<close>

setup \<open>Sign.mandatory_path "heap"\<close>

type_synonym addr = nat \<comment>\<open> untyped heap addresses \<close>

datatype rep \<comment>\<open> the concrete representation of heap values \<close>
  = Addr nat heap.addr \<comment>\<open> metadata paired with an address \<close>
  | Val nat

datatype "write" = Write heap.addr nat heap.rep

type_synonym t = "heap.addr \<rightharpoonup> heap.rep list" \<comment>\<open> partial map from addresses to structured encoded values \<close>

abbreviation empty :: "heap.t" where
  "empty \<equiv> Map.empty"

primrec apply_write :: "heap.write \<Rightarrow> heap.t \<Rightarrow> heap.t" where
  "apply_write (heap.Write addr i x) s = s(addr \<mapsto> (the (s addr))[i := x])"

(* the free tyvar warning is the same as for \<open>countable\<close> *)
class rep = \<comment>\<open> the class of representable types \<close>
  assumes ex_inj: "\<exists>to_heap_rep :: 'a \<Rightarrow> heap.rep. inj to_heap_rep"

setup \<open>Sign.mandatory_path "rep"\<close>

lemma countable_classI[intro!]:
  shows "OFCLASS('a::countable, heap.rep_class)"
by intro_classes (simp add: inj_on_def exI[where x="heap.Val \<circ> to_nat"])

definition to :: "'a::heap.rep \<Rightarrow> heap.rep" where
  "to = (SOME f. inj f)"

definition "from" :: "heap.rep \<Rightarrow> 'a::heap.rep" where
  "from = inv (heap.rep.to :: 'a \<Rightarrow> heap.rep)"

lemmas inj_to[simp] = someI_ex[OF heap.ex_inj, folded heap.rep.to_def]

lemma inj_on_to[simp, intro]: "inj_on heap.rep.to S"
using heap.rep.inj_to by (auto simp: inj_on_def)

lemma surj_from[simp]: "surj heap.rep.from"
unfolding heap.rep.from_def by (simp add: inj_imp_surj_inv)

lemma to_split[simp]: "heap.rep.to x = heap.rep.to y \<longleftrightarrow> x = y"
using injD[OF heap.rep.inj_to] by auto

lemma from_to[simp]:
  shows "heap.rep.from (heap.rep.to x) = x"
by (simp add: heap.rep.from_def)

instance unit :: heap.rep ..

instance bool :: heap.rep ..

instance nat :: heap.rep ..

instance int :: heap.rep ..

instance char :: heap.rep ..

instance String.literal :: heap.rep ..

instance typerep :: heap.rep ..

setup \<open>Sign.parent_path\<close>

text\<open>

User-facing heap types typically carry more information than an
(untyped) address, such as (phantom) typing and a representation
invariant that guarantees the soundness of the encoding (for the given
value at the given address only). We abstract over that here and provide
some generic operations.

Notes:
 \<^item> intuitively \<open>addr_of\<close> should be surjective but we do not enforce this
 \<^item> we use sets here but these are not very flexible: all refs must have the same type
  \<^item> this means some intutive facts involving \<open>UNIV\<close> cannot be stated

\<close>

class addr_of =
  fixes addr_of :: "'a \<Rightarrow> heap.addr"
  fixes rep_val_inv :: "'a \<Rightarrow> heap.rep list pred"

definition obj_at :: "heap.rep list pred \<Rightarrow> heap.addr \<Rightarrow> heap.t pred" where
  "obj_at P r s = (case s r of None \<Rightarrow> False | Some v \<Rightarrow> P v)"

abbreviation (input) present :: "'a::heap.addr_of \<Rightarrow> heap.t pred" where
  "present r \<equiv> heap.obj_at \<langle>True\<rangle> (heap.addr_of r)"

abbreviation (input) rep_inv :: "'a::heap.addr_of \<Rightarrow> heap.t pred" where
  "rep_inv r \<equiv> heap.obj_at (heap.rep_val_inv r) (heap.addr_of r)"

abbreviation (input) rep_inv_set :: "'a::heap.addr_of \<Rightarrow> heap.t set" where
  "rep_inv_set r \<equiv> Collect (heap.rep_inv r)"

\<comment>\<open> allows arbitrary transitions provided the \<open>rep_inv\<close> of \<open>r\<close> is respected \<close>
abbreviation (input) rep_inv_rel :: "'a::heap.addr_of \<Rightarrow> heap.t rel" where
  "rep_inv_rel r \<equiv> heap.rep_inv_set r \<times> heap.rep_inv_set r"

\<comment>\<open> totality models the idea that all dereferences are ``valid'' but only some are reasonable \<close>
definition get :: "'a::heap.addr_of \<Rightarrow> heap.t \<Rightarrow> 'v::heap.rep list" where
  "get r s = map heap.rep.from (the (s (heap.addr_of r)))"

definition set :: "'a::heap.addr_of \<Rightarrow> 'v::heap.rep list \<Rightarrow> heap.t \<Rightarrow> heap.t" where
  "set r v s = s(heap.addr_of r \<mapsto> map heap.rep.to v)"

definition dealloc :: "'a::heap.addr_of \<Rightarrow> heap.t \<Rightarrow> heap.t" where
  "dealloc r s = s |` {heap.addr_of r}"

\<comment>\<open> allows no changes to \<open>rs\<close>, asserts the \<open>rep_inv\<close> of \<open>rs\<close> is valid, arbitrary changes to \<open>-rs\<close> \<close>
definition Id_on :: "'a::heap.addr_of set \<Rightarrow> heap.t rel" (\<open>heap.Id\<^bsub>_\<^esub>\<close>) where
  "heap.Id\<^bsub>rs\<^esub> = (\<Inter>r\<in>rs. heap.rep_inv_rel r \<inter> Id\<^bsub>\<lambda>s. s (heap.addr_of r)\<^esub>)"

\<comment>\<open> allows arbitrary changes to \<open>rs\<close> provided the \<open>rep_inv\<close> of \<open>rs\<close> is respected.
    requires addresses in \<open>-heap.addr_of ` rs\<close> to be unchanged \<close>
definition modifies :: "'a::heap.addr_of set \<Rightarrow> heap.t rel" (\<open>heap.modifies\<^bsub>_\<^esub>\<close>) where
  "heap.modifies\<^bsub>rs\<^esub> = (\<Inter>r\<in>rs. heap.rep_inv_rel r) \<inter> {(s, s'). \<forall>r\<in>-heap.addr_of ` rs. s r = s' r}"

setup \<open>Sign.mandatory_path "get"\<close>

lemma cong:
  assumes "s (heap.addr_of r) = s' (heap.addr_of r')"
  shows "heap.get r s = heap.get r' s'"
by (simp add: assms heap.get_def)

lemma Id_on_proj_cong:
  assumes "(s, s') \<in> heap.Id\<^bsub>{r}\<^esub>"
  shows "heap.get r s = heap.get r s'"
using assms by (simp add: heap.Id_on_def heap.get_def)

lemma fun_upd:
  shows "heap.get r (fun_upd s a (Some w))
      = (if heap.addr_of r = a then map heap.rep.from w else heap.get r s)"
by (simp add: heap.get_def)

lemma set_eq:
  shows "heap.get r (heap.set r v s) = v"
by (simp add: heap.get_def heap.set_def comp_def)

lemma set_neq:
  assumes "heap.addr_of r \<noteq> heap.addr_of r'"
  shows "heap.get r (heap.set r' v s) = heap.get r s"
by (simp add: heap.get_def heap.set_def assms)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "set"\<close>

lemma cong:
  assumes "heap.addr_of r = heap.addr_of r'"
  assumes "v = v'"
  assumes "\<And>r'. r' \<noteq> heap.addr_of r \<Longrightarrow> s r' = s' r'"
  shows "heap.set r v s = heap.set r' v' s'"
by (simp add: assms heap.set_def fun_eq_iff)

lemma empty:
  shows "heap.set r v (heap.empty) = [heap.addr_of r \<mapsto> map heap.rep.to v]"
by (simp add: heap.set_def)

lemma fun_upd:
  shows "heap.set r v (fun_upd s a w) = (fun_upd s a w)(heap.addr_of r \<mapsto> map heap.rep.to v)"
by (simp add: heap.set_def)

lemma same:
  shows "heap.set r v (heap.set r w s) = heap.set r v s"
by (simp add: heap.set_def)

lemma twist:
  assumes "heap.addr_of r \<noteq> heap.addr_of r'"
  shows "heap.set r v (heap.set r' w s) = heap.set r' w (heap.set r v s)"
using assms by (simp add: heap.set_def fun_eq_iff)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "obj_at"\<close>

lemma cong[cong]:
  fixes P :: "heap.rep list pred"
  assumes "\<And>v. s r = Some v \<Longrightarrow> P v = P' v"
  assumes "r = r'"
  assumes "s r = s' r'"
  shows "heap.obj_at P r s \<longleftrightarrow> heap.obj_at P' r' s'"
using assms by (simp add: heap.obj_at_def cong: option.case_cong)

lemma split:
  shows "Q (heap.obj_at P r s) \<longleftrightarrow> (s r = None \<longrightarrow> Q False) \<and> (\<forall>v. s r = Some v \<longrightarrow> Q (P v))"
by (simp add: heap.obj_at_def split: option.splits)

lemma split_asm:
  shows "Q (heap.obj_at P r s) \<longleftrightarrow> \<not> ((s r = None \<and> \<not>Q False) \<or> (\<exists>v. s r = Some v \<and> \<not> Q (P v)))"
by (simp add: heap.obj_at_def split: option.splits)

lemmas splits = heap.obj_at.split heap.obj_at.split_asm

lemma empty:
  shows "\<not>heap.obj_at P r heap.empty"
by (simp add: heap.obj_at_def)

lemma set:
  shows "heap.obj_at P r (heap.set r' v s)
    \<longleftrightarrow> (r = heap.addr_of r' \<and> P (map heap.rep.to v)) \<or> (r \<noteq> heap.addr_of r' \<and> heap.obj_at P r s)"
by (simp add: comp_def heap.set_def split: heap.obj_at.split)

lemma fun_upd:
  shows "heap.obj_at P r (fun_upd s a (Some w)) = (if r = a then P w else heap.obj_at P r s)"
by (simp split: heap.obj_at.split)

setup \<open>Sign.parent_path\<close>

lemmas simps = \<comment>\<open> objective: reduce manifest heaps \<close>
  heap.get.set_eq
  heap.get.fun_upd
  heap.set.empty
  heap.set.same
  heap.set.fun_upd
  heap.obj_at.empty
  heap.obj_at.fun_upd

setup \<open>Sign.mandatory_path "Id_on"\<close>

lemma empty[simp]:
  shows "heap.Id\<^bsub>{}\<^esub> = UNIV"
by (simp add: heap.Id_on_def)

lemma sup:
  shows "heap.Id\<^bsub>X \<union> Y\<^esub> = heap.Id\<^bsub>X\<^esub> \<inter> heap.Id\<^bsub>Y\<^esub>"
unfolding heap.Id_on_def by blast

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "modifies"\<close>

lemma empty[simp]:
  shows "heap.modifies\<^bsub>{}\<^esub> = Id"
by (auto simp: heap.modifies_def)

lemma rep_inv_rel_le:
  shows "heap.modifies\<^bsub>rs\<^esub> \<subseteq> (\<Inter>r\<in>rs. heap.rep_inv_rel r)"
by (simp add: heap.modifies_def)

lemma rep_inv:
  assumes "(s, s') \<in> heap.modifies\<^bsub>{a}\<^esub>"
  shows "heap.rep_inv a s"
    and "heap.rep_inv a s'"
using assms by (simp_all add: heap.modifies_def split: heap.obj_at.split)

lemma Id_conv:
  shows "(s, s) \<in> heap.modifies\<^bsub>rs\<^esub> \<longleftrightarrow> (\<forall>r\<in>rs. (s, s) \<in> heap.rep_inv_rel r)"
by (simp add: heap.modifies_def)

lemma eqI:
  assumes "(s, s') \<in> heap.modifies\<^bsub>rs\<^esub>"
  assumes "\<And>r. \<lbrakk>r \<in> rs; heap.rep_inv r s; heap.rep_inv r s'\<rbrakk> \<Longrightarrow> s (heap.addr_of r) = s' (heap.addr_of r)"
  shows "s = s'"
using assms by (simp add: heap.modifies_def) blast

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "stable.heap"\<close>

lemma Id_on_frame_cong:
  assumes "\<And>s s'. (\<And>r. r \<in> rs \<Longrightarrow> heap.rep_inv r s \<and> heap.rep_inv r s' \<and> s (heap.addr_of r) = s' (heap.addr_of r)) \<Longrightarrow> P s \<longleftrightarrow> P' s'"
  shows "stable heap.Id\<^bsub>rs\<^esub> P \<longleftrightarrow> stable heap.Id\<^bsub>rs\<^esub> P'"
using assms by (auto 10 0 simp: stable_def monotone_def heap.Id_on_def)

lemma Id_on_frameI:
  assumes "\<And>s s'. (\<And>r. r \<in> rs \<Longrightarrow> heap.rep_inv r s \<and> heap.rep_inv r s' \<and> s (heap.addr_of r) = s' (heap.addr_of r)) \<Longrightarrow> P s \<longleftrightarrow> P s'"
  shows "stable heap.Id\<^bsub>rs\<^esub> P"
using assms by (auto simp: stable_def monotone_def heap.Id_on_def)

lemma Id_on_rep_invI[stable.intro]:
  assumes "r \<in> rs"
  shows "stable heap.Id\<^bsub>rs\<^esub> (heap.rep_inv r)"
using assms by (blast intro: stable.heap.Id_on_frameI)

setup \<open>Sign.parent_path\<close>


subsection\<open> References\label{sec:CImperativeHOL-heap-refs} \<close>

datatype 'a ref = Ref (addr_of: heap.addr)

instantiation ref :: (heap.rep) heap.addr_of
begin

definition addr_of_ref :: "'a ref \<Rightarrow> heap.addr" where
  "addr_of_ref = ref.addr_of"

definition rep_val_inv_ref :: "'a ref \<Rightarrow> heap.rep list pred" where
  "rep_val_inv_ref r vs \<longleftrightarrow> (case vs of [v] \<Rightarrow> heap.rep.to (heap.rep.from v :: 'a) = v | _\<Rightarrow> False)"

instance ..

end

instance ref :: (heap.rep) heap.rep
by standard (simp add: inj_on_def ref.expand exI[where x="heap.Addr 0 \<circ> ref.addr_of"])

setup \<open>Sign.mandatory_path "Ref"\<close>

definition get :: "'a::heap.rep ref \<Rightarrow> heap.t \<Rightarrow> 'a" where
  "get r s = hd (heap.get r s)"

definition set :: "'a::heap.rep ref \<Rightarrow> 'a \<Rightarrow> heap.t \<Rightarrow> heap.t" where
  "set r v s = heap.set r [v] s"

definition alloc :: "'a \<Rightarrow> heap.t \<Rightarrow> ('a::heap.rep ref \<times> heap.t) set" where
  "alloc v s = {(r, Ref.set r v s) |r. \<not>heap.present r s}"

lemma addr_of:
  shows "heap.addr_of (Ref r) = r"
by (simp add: addr_of_ref_def)

setup \<open>Sign.mandatory_path "get"\<close>

lemma fun_upd:
  shows "Ref.get r (fun_upd s a (Some [w]))
      = (if heap.addr_of r = a then heap.rep.from w else Ref.get r s)"
by (simp add: Ref.get_def heap.simps)

lemma set_eq:
  shows "Ref.get r (Ref.set r v s) = v"
by (simp add: Ref.get_def Ref.set_def heap.simps)

lemma set_neq:
  fixes r :: "'a::heap.rep ref"
  fixes r' :: "'b::heap.rep ref"
  assumes "addr_of r \<noteq> addr_of r'"
  shows "Ref.get r (Ref.set r' v s) = Ref.get r s"
using assms by (simp add: Ref.get_def Ref.set_def addr_of_ref_def heap.get.set_neq)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "set"\<close>

lemma empty:
  shows "Ref.set r v (heap.empty) = [heap.addr_of r \<mapsto> [heap.rep.to v]]"
by (simp add: Ref.set_def heap.simps)

lemma fun_upd:
  shows "Ref.set r v (fun_upd s a w) = (fun_upd s a w)(heap.addr_of r \<mapsto> [heap.rep.to v])"
by (simp add: Ref.set_def heap.simps)

lemma same:
  shows "Ref.set r v (Ref.set r w s) = Ref.set r v s"
by (simp add: Ref.set_def heap.set_def)

lemma obj_at_conv:
  fixes a :: "heap.addr"
  fixes r :: "'a::heap.rep ref"
  fixes v :: "'a"
  fixes P :: "heap.rep list pred"
  shows "heap.obj_at P a (Ref.set r v s) \<longleftrightarrow> (a = heap.addr_of r \<and> P [heap.rep.to v])
                                           \<or> (a \<noteq> heap.addr_of r \<and> heap.obj_at P a s)"
by (simp add: Ref.set_def heap.set_def split: heap.obj_at.split)

setup \<open>Sign.parent_path\<close>

lemmas simps[simp] =
  Ref.addr_of
  Ref.get.set_eq
  Ref.get.set_neq
  Ref.get.fun_upd
  Ref.set.same
  Ref.set.empty
  Ref.set.fun_upd
  Ref.set.obj_at_conv

setup \<open>Sign.parent_path\<close>


subsection\<open> Arrays\label{sec:CImperativeHOL-heap-arrays} \<close>


subsubsection\<open> Code generation constants: one-dimensional arrays \<close>

text\<open>

We ask that targets of the code generator provide implementations of one-dimensional arrays
and the associated operations.

Notes:
 \<^item> user-facing arrays make use of \<^class>\<open>Ix\<close>
 \<^item> due to the lack of bounds there is no \<open>rep_val_inv\<close>

\<close>

datatype 'a one_dim_array = Array (addr_of: heap.addr)

instantiation one_dim_array :: (type) heap.addr_of
begin

definition addr_of_one_dim_array :: "'a one_dim_array \<Rightarrow> heap.addr" where
  "addr_of_one_dim_array = addr_of"

definition rep_val_inv_one_dim_array :: "'a one_dim_array \<Rightarrow> heap.rep list pred" where
[simp]: "rep_val_inv_one_dim_array a vs \<longleftrightarrow> True"

instance ..

end

setup \<open>Sign.mandatory_path "ODArray"\<close>

definition get :: "'a::heap.rep one_dim_array \<Rightarrow> nat \<Rightarrow> heap.t \<Rightarrow> 'a" where
  "get a i s = heap.get a s ! i"

definition set :: "'a::heap.rep one_dim_array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> heap.t \<Rightarrow> heap.t" where
  "set a i v s = heap.set a ((heap.get a s)[i:=v]) s"

definition alloc :: "'a list \<Rightarrow> heap.t \<Rightarrow> ('a::heap.rep one_dim_array \<times> heap.t) set" where
  "alloc av s = {(a, heap.set a av s) |a. \<not>heap.present a s}"

definition list_for :: "'a::heap.rep one_dim_array \<Rightarrow> heap.t \<Rightarrow> 'a list" where
  "list_for a = heap.get a"

setup \<open>Sign.mandatory_path "get"\<close>

lemma weak_cong:
  assumes "i = i'"
  assumes "a = a'"
  assumes "s (heap.addr_of a) = s' (heap.addr_of a')"
  shows "ODArray.get a i s = ODArray.get a' i' s'"
using assms by (simp add: ODArray.get_def cong: heap.get.cong)

lemma weak_Id_on_proj_cong:
  assumes "i = i'"
  assumes "a = a'"
  assumes "(s, s') \<in> heap.Id\<^bsub>{a'}\<^esub>"
  shows "ODArray.get a i s = ODArray.get a' i' s'"
using assms by (simp add: ODArray.get_def cong: heap.get.Id_on_proj_cong)

lemma set_eq:
  assumes "i < length (the (s (heap.addr_of a)))"
  shows "ODArray.get a i (ODArray.set a i v s) = v"
using assms by (simp add: ODArray.get_def ODArray.set_def heap.get.set_eq) (simp add: heap.get_def)

lemma set_neq:
  assumes "i \<noteq> j"
  shows "ODArray.get a i (ODArray.set a j v s) = ODArray.get a i s"
using assms by (simp add: ODArray.get_def ODArray.set_def heap.get.set_eq)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsubsection\<open> User-facing arrays \<close>

datatype ('i, 'a) array = Array (bounds: "('i \<times> 'i)") (arr: "'a one_dim_array")

hide_const (open) bounds arr

instantiation array :: (Ix, heap.rep) heap.addr_of
begin

definition addr_of_array :: "('a, 'b) array \<Rightarrow> heap.addr" where
  "addr_of_array = addr_of \<circ> array.arr"

definition rep_val_inv_array :: "('a, 'b) array \<Rightarrow> heap.rep list pred" where
  "rep_val_inv_array a vs \<longleftrightarrow>
      length vs = length (Ix.interval (array.bounds a))
    \<and> (\<forall>v\<in>set vs. heap.rep.to (heap.rep.from v :: 'b) = v)"

instance ..

end

instance array :: (countable, type) heap.rep
by standard
   (rule exI[where x="\<lambda>a. heap.Addr (to_nat (array.bounds a)) (addr_of (array.arr a))"],
         rule injI, simp add: array.expand one_dim_array.expand)

setup \<open>Sign.mandatory_path "Array"\<close>

abbreviation (input) square :: "('i::Ix \<times> 'i, 'a) array \<Rightarrow> bool" where
  "square a \<equiv> Ix.square (array.bounds a)"

abbreviation (input) index :: "('i::Ix, 'a) array \<Rightarrow> 'i \<Rightarrow> nat" where
  "index a \<equiv> Ix.index (array.bounds a)"

abbreviation (input) interval :: "('i::Ix, 'a) array \<Rightarrow> 'i list" where
  "interval a \<equiv> Ix.interval (array.bounds a)"

definition get :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> 'i \<Rightarrow> heap.t \<Rightarrow> 'a" where
  "get a i = ODArray.get (array.arr a) (Array.index a i)"

definition set :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> heap.t \<Rightarrow> heap.t" where
  "set a i v = ODArray.set (array.arr a) (Array.index a i) v"

definition list_for :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> heap.t \<Rightarrow> 'a list" where
  "list_for a = ODArray.list_for (array.arr a)"

\<comment>\<open> can coerce any indexing regime into any other provided the contents fit \<close>
definition coerce :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> ('j \<times> 'j) \<Rightarrow> ('j::Ix, 'a::heap.rep) array option" where
  "coerce a b = (if length (Array.interval a) = length (Ix.interval b)
                 then Some (Array b (array.arr a))
                 else None)"

definition Id_on :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> 'i set \<Rightarrow> heap.t rel" (\<open>Array.Id\<^bsub>_, _\<^esub>\<close>) where
  "Array.Id\<^bsub>a, is\<^esub> = heap.rep_inv_rel a \<inter> {(s, s'). \<forall>i\<in>is. Array.get a i s = Array.get a i s'}"

definition modifies :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> 'i set \<Rightarrow> heap.t rel" (\<open>Array.modifies\<^bsub>_, _\<^esub>\<close>) where
  "Array.modifies\<^bsub>a, is\<^esub>
    = heap.modifies\<^bsub>{a}\<^esub> \<inter> {(s, s'). \<forall>i\<in>set (Array.interval a) - is. Array.get a i s = Array.get a i s'}"

lemma simps[simp]:
  shows "heap.addr_of (array.arr a) = heap.addr_of a"
    and "heap.addr_of \<circ> array.arr = heap.addr_of"
by (simp_all add: addr_of_array_def addr_of_one_dim_array_def)

setup \<open>Sign.mandatory_path "get"\<close>

lemma set_eq:
  assumes "heap.rep_inv a s"
  assumes "i \<in> set (Array.interval a)"
  shows "Array.get a i (Array.set a i v s) = v"
using assms
by (simp add: Array.get_def Array.set_def ODArray.get.set_eq index_length rep_val_inv_array_def
       split: heap.obj_at.split_asm)

lemma set_neq:
  assumes "i \<in> set (Array.interval a)"
  assumes "j \<in> set (Array.interval a)"
  assumes "i \<noteq> j"
  shows "Array.get a j (Array.set a i v s) = Array.get a j s"
using assms by (simp add: Array.get_def Array.set_def ODArray.get.set_neq index_eq_conv)

lemma Id_on_proj_cong:
  assumes "a = a'"
  assumes "i = i'"
  assumes "(s, s') \<in> Array.Id\<^bsub>a', {i'}\<^esub>"
  assumes "i' \<in> set (Array.interval a)"
  shows "Array.get a i s = Array.get a' i' s'"
using assms by (simp add: Array.get_def Array.Id_on_def)

lemma weak_cong:
  assumes "a = a'"
  assumes "i = i'"
  assumes "s (heap.addr_of a) = s' (heap.addr_of a')"
  shows "Array.get a i s = Array.get a' i' s'"
using assms unfolding Array.get_def by (simp cong: ODArray.get.weak_cong)

lemma weak_Id_on_proj_cong:
  assumes "i = i'"
  assumes "a = a'"
  assumes "(s, s') \<in> heap.Id\<^bsub>{a'}\<^esub>"
  shows "Array.get a i s = Array.get a' i' s'"
using assms unfolding Array.get_def
by (simp add: heap.Id_on_def  ODArray.get.weak_Id_on_proj_cong split: heap.obj_at.splits)

lemma ext:
  assumes "heap.rep_inv a s"
  assumes "heap.rep_inv a s'"
  assumes "\<forall>i\<in>set (Ix_class.interval (array.bounds a)). Array.get a i s = Array.get a i s'"
  shows "s (heap.addr_of a) = s' (heap.addr_of a)"
using assms
by (simp add: Array.get_def ODArray.get_def heap.get_def rep_val_inv_array_def
       split: heap.obj_at.splits)
   (rule nth_equalityI, simp, metis index_forE nth_map nth_mem)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "set"\<close>

lemma cong_deref:
  assumes "a = a'"
  assumes "i = i'"
  assumes "v = v'"
  assumes "s r = s' r'"
  assumes "r = r'"
  shows "Array.set a i v s r = Array.set a' i' v' s' r'"
using assms by (clarsimp simp: Array.set_def ODArray.set_def heap.set_def heap.get_def)

lemma same:
  shows "Array.set a i v (Array.set a i v' s) = Array.set a i v s"
by (simp add: Array.set_def ODArray.set_def heap.simps)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "coerce"\<close>

lemma ex_bij_betw:
  fixes a :: "('i::Ix, 'a::heap.rep) array"
  fixes b :: "'j::Ix \<times> 'j"
  assumes "Array.coerce a b = Some a'"
  obtains f where "map f (Array.interval a) = Ix.interval b"
using assms unfolding Array.coerce_def by (metis interval map_map map_nth not_None_eq)

lemma ex_bij_betw2:
  fixes a :: "('i::Ix, 'a::heap.rep) array"
  fixes b :: "'j::Ix \<times> 'j"
  assumes "Array.coerce a b = Some a'"
  obtains f where "map f (Ix.interval b) = Array.interval a"
using assms by (metis Array.coerce_def Array.coerce.ex_bij_betw array.sel(1) option.distinct(1))

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "rep_inv"\<close>

lemma set:
  assumes "heap.rep_inv a s"
  shows "heap.rep_inv a (Array.set a i v s)"
using assms
by (simp add: Array.set_def ODArray.set_def rep_val_inv_array_def heap.set_def heap.get_def
       split: heap.obj_at.splits)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "modifies"\<close>

lemma heap_modifies_le:
  shows "Array.modifies\<^bsub>a, is\<^esub> \<subseteq> heap.modifies\<^bsub>{a}\<^esub>"
by (simp add: Array.modifies_def)

lemma heap_rep_inv_rel_le:
  shows "Array.modifies\<^bsub>a, is\<^esub> \<subseteq> heap.rep_inv_rel a"
using heap.modifies.rep_inv_rel_le[where rs="{a}"] by (auto simp: Array.modifies_def)

lemma empty:
  shows "Array.modifies\<^bsub>a, {}\<^esub> = Id \<inter> heap.rep_inv_rel a" (is "?lhs = ?rhs")
by (auto simp: Array.modifies_def heap.modifies.Id_conv heap.modifies.rep_inv
         elim: heap.modifies.eqI Array.get.ext)

lemma mono:
  assumes "is \<subseteq> js"
  shows "Array.modifies\<^bsub>a, is\<^esub> \<subseteq> Array.modifies\<^bsub>a, js\<^esub>"
using assms by (auto simp: Array.modifies_def)

lemma INTER:
  shows "Array.modifies\<^bsub>a, \<Inter>x\<in>X. f x\<^esub> = (\<Inter>x\<in>X. Array.modifies\<^bsub>a, f x\<^esub>) \<inter> heap.modifies\<^bsub>{a}\<^esub>"
by (auto simp: Array.modifies_def)

lemma Inter:
  shows "Array.modifies\<^bsub>a, \<Inter>X\<^esub> = (\<Inter>x\<in>X. Array.modifies\<^bsub>a, x\<^esub>) \<inter> heap.modifies\<^bsub>{a}\<^esub>"
by (auto simp: Array.modifies_def)

lemma inter:
  shows "Array.modifies\<^bsub>a, is\<^esub> \<inter> Array.modifies\<^bsub>a, js\<^esub> = Array.modifies\<^bsub>a, is \<inter> js\<^esub>"
by (auto simp: Array.modifies_def)

lemma UNION_subseteq:
  shows "(\<Union>x\<in>X. Array.modifies\<^bsub>a, I x\<^esub>) \<subseteq> Array.modifies\<^bsub>a, (\<Union>x\<in>X. I x)\<^esub>"
by (simp add: Array.modifies.mono Sup_upper UN_least)

lemma union_subseteq:
  shows "Array.modifies\<^bsub>a, is\<^esub> \<union> Array.modifies\<^bsub>a, js\<^esub> \<subseteq> Array.modifies\<^bsub>a, is \<union> js\<^esub>"
by (simp add: Array.modifies.mono)

lemma Diag_subseteq:
  assumes "\<And>s. P s \<Longrightarrow> heap.rep_inv a s"
  shows "Diag P \<subseteq> Array.modifies\<^bsub>a, is\<^esub>"
using assms by (auto simp: Array.modifies_def heap.modifies_def Diag_def)

lemma get:
  assumes "(s, s') \<in> Array.modifies\<^bsub>a, is\<^esub>"
  assumes "i \<in> set (Array.interval a) - is"
  shows "Array.get a i s' = Array.get a i s"
using assms by (simp add: Array.modifies_def)

lemma set:
  assumes "heap.rep_inv a s"
  shows "(s, Array.set a i v s) \<in> heap.modifies\<^bsub>{a}\<^esub>"
using assms
by (simp add: heap.modifies_def Array.set_def ODArray.set_def heap.set_def heap.get_def rep_val_inv_array_def 
       split: heap.obj_at.splits)

lemma Array_set:
  assumes "heap.rep_inv a s"
  assumes "i \<in> set (Array.interval a) \<inter> is"
  shows "(s, Array.set a i v s) \<in> Array.modifies\<^bsub>a, is\<^esub>"
using assms
by (auto simp: Array.modifies_def Array.rep_inv.set Array.modifies.set
        intro: Array.get.set_neq[symmetric])

lemma Array_set_conv:
  assumes "i \<in> set (Array.interval a) \<inter> is"
  shows "(s, Array.set a i v s) \<in> Array.modifies\<^bsub>a, is\<^esub> \<longleftrightarrow> heap.rep_inv a s" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
   using heap.modifies.rep_inv_rel_le[of "{a}", simplified] by (auto simp: Array.modifies_def)
  from assms show "?rhs \<Longrightarrow> ?lhs"
    by (simp add: Array.modifies.Array_set)
qed

setup \<open>Sign.parent_path\<close>

lemmas simps' =
  Array.rep_inv.set
  Array.get.set_eq

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "heap.Id_on.Array"\<close>

lemma Id_on_le:
  shows "heap.Id\<^bsub>{a}\<^esub> \<subseteq> Array.Id\<^bsub>a, is\<^esub>"
by (auto simp: Array.Id_on_def heap.Id_on_def Array.get_def ODArray.get_def heap.get_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "Array.Id_on"\<close>

lemma empty:
  shows "Array.Id\<^bsub>a, {}\<^esub> = heap.rep_inv_rel a"
by (simp add: Array.Id_on_def)

lemma mono:
  assumes "is \<subseteq> js"
  shows "Array.Id\<^bsub>a, js\<^esub> \<subseteq> Array.Id\<^bsub>a, is\<^esub>"
using assms by (auto simp: Array.Id_on_def)

lemma insert:
  shows "Array.Id\<^bsub>a, insert i is\<^esub> = Array.Id\<^bsub>a, {i}\<^esub> \<inter> Array.Id\<^bsub>a, is\<^esub>"
by (fastforce simp: Array.Id_on_def)

lemma union:
  shows "Array.Id\<^bsub>a, is \<union> js\<^esub> = Array.Id\<^bsub>a, is\<^esub> \<inter> Array.Id\<^bsub>a, js\<^esub>"
by (fastforce simp: Array.Id_on_def)

lemma rep_inv_rel:
  shows "Array.Id\<^bsub>a, is\<^esub> \<subseteq> heap.rep_inv_rel a"
by (simp add: Array.Id_on_def)

lemma eq_heap_Id_on:
  assumes "set (Array.interval a) \<subseteq> is"
  shows "Array.Id\<^bsub>a, is\<^esub> = heap.Id\<^bsub>{a}\<^esub>"
by (rule antisym[OF _ heap.Id_on.Array.Id_on_le])
   (use assms in \<open>force simp: Array.Id_on_def heap.Id_on_def elim: Array.get.ext\<close>)

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Stability\label{sec:CImperativeHOL-heap-stability} \<close>

setup \<open>Sign.mandatory_path "stable.heap.Id_on.Array"\<close>

lemma get[stable.intro]:
  assumes "a \<in> as"
  shows "stable heap.Id\<^bsub>as\<^esub> (\<lambda>s. P (Array.get a i s))"
using assms by (auto simp: stable_def monotone_def heap.Id_on_def cong: Array.get.weak_cong)

lemma get_chain: \<comment>\<open> difficult to apply \<close>
  assumes "\<And>v. stable heap.Id\<^bsub>as\<^esub> (P v)"
  assumes "a \<in> as"
  shows "stable heap.Id\<^bsub>as\<^esub> (\<lambda>s. P (Array.get a i s) s)"
using assms by (auto simp: stable_def monotone_def heap.Id_on_def cong: Array.get.weak_cong)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "stable.Array.Id_on.Array"\<close>

lemma get[stable.intro]:
  assumes "i \<in> is"
  shows "stable Array.Id\<^bsub>a, is\<^esub> (\<lambda>s. P (Array.get a i s))"
using assms by (auto simp: stable_def monotone_def Array.Id_on_def)

lemma get_chain: \<comment>\<open> difficult to apply \<close>
  assumes "\<And>v. stable Array.Id\<^bsub>a, is\<^esub> (P v)"
  assumes "i \<in> is"
  shows "stable Array.Id\<^bsub>a, is\<^esub> (\<lambda>s. P (Array.get a i s) s)"
using assms by (auto simp: stable_def monotone_def Array.Id_on_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "stable.heap.Array.Id_on.heap"\<close>

lemma rep_inv[stable.intro]:
  shows "stable Array.Id\<^bsub>a, is\<^esub> (heap.rep_inv a)"
by (simp add: stable_def monotone_def Array.Id_on_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "stable.heap.Array.modifies.heap"\<close>

lemma rep_inv[stable.intro]:
  shows "stable Array.modifies\<^bsub>a, is\<^esub> (heap.rep_inv a)"
by (simp add: stable_def monotone_def Array.modifies_def heap.modifies_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "stable.heap.Array.modifies.Array"\<close>

lemma get[stable.intro]:
  assumes "i \<in> set (Array.interval a) - is"
  shows "stable Array.modifies\<^bsub>a, is\<^esub> (\<lambda>s. P (Array.get a i s))"
using assms by (simp add: stable_def monotone_def Array.modifies_def)

lemma get_chain: \<comment>\<open> difficult to apply \<close>
  assumes "\<And>v. stable Array.modifies\<^bsub>a, is\<^esub> (P v)"
  assumes "i \<in> set (Array.interval a) - is"
  shows "stable Array.modifies\<^bsub>a, is\<^esub> (\<lambda>s. P (Array.get a i s) s)"
using assms by (simp add: stable_def monotone_def Array.modifies_def)

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
