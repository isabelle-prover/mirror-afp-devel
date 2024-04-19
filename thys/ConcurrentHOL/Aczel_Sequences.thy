(*<*)
theory Aczel_Sequences
imports
  HOL_Basis
begin

(*>*)
section\<open> Terminated Aczel sequences\label{sec:aczel_sequences} \<close>

text\<open>

We model a \<^emph>\<open>behavior\<close> of a system as a non-empty finite or infinite sequence of the form
\<open>s\<^sub>0 -a\<^sub>1\<rightarrow> s\<^sub>1 -a\<^sub>2\<rightarrow> \<dots> (\<rightarrow> v)?\<close> where \<open>s\<^sub>i\<close> is a state, \<open>a\<^sub>i\<close> an agent and \<open>v\<close> a return value for
finite sequences (see \S\ref{sec:tls}).  A \<^emph>\<open>trace\<close> is a finite sequence
\<open>s\<^sub>0 -a\<^sub>1\<rightarrow> s\<^sub>1 -a\<^sub>2\<rightarrow> \<dots> -a\<^sub>n\<rightarrow> s\<^sub>n \<rightarrow> v\<close> for \<open>n \<ge> 0\<close> with optional return value \<open>v\<close> (see
\S\ref{sec:safety_logic}). States, agents and return values are of arbitrary type.

\<close>


subsection\<open> Traces\label{sec:aczel_sequences-traces} \<close>

setup \<open>Sign.mandatory_path "trace"\<close>

datatype (aset: 'a, sset: 's, vset: 'v) t =
  T (init: 's) (rest: "('a \<times> 's) list") ("term": "'v option")
for
  map: map
  pred: pred
  rel: rel

declare trace.t.map_id0[simp]
declare trace.t.map_id0[unfolded id_def, simp]
declare trace.t.map_sel[simp]
declare trace.t.set_map[simp]
declare trace.t.map_comp[unfolded o_def, simp]
declare trace.t.set[simp del]

instance trace.t :: (countable, countable, countable) countable by countable_datatype

lemma split_all[no_atp]: \<comment>\<open> imitate the setup for \<^typ>\<open>'a \<times> 'b\<close> without the automation \<close>
  shows "(\<And>x. PROP P x) \<equiv> (\<And>s xs v. PROP P (trace.T s xs v))"
proof
  show "PROP P (trace.T s xs v)" if "\<And>x. PROP P x" for s xs v by (rule that)
next
  fix x
  assume "\<And>s xs v. PROP P (trace.T s xs v)"
  from \<open>PROP P (trace.T (trace.init x) (trace.rest x) (trace.term x))\<close> show "PROP P x" by simp
qed

lemma split_All[no_atp]:
  shows "(\<forall>x. P x) \<longleftrightarrow> (\<forall>s xs v. P (trace.T s xs v))" (is "?lhs \<longleftrightarrow> ?rhs")
proof (intro iffI allI)
  show "P x" if ?rhs for x using that by (cases x) simp_all
qed simp

lemma split_Ex[no_atp]:
  shows "(\<exists>x. P x) \<longleftrightarrow> (\<exists>s xs v. P (trace.T s xs v))" (is "?lhs \<longleftrightarrow> ?rhs")
proof (intro iffI allI; elim exE)
  show "\<exists>s xs v. P (trace.T s xs v)" if "P x" for x using that by (cases x) fast
qed auto


subsection\<open> Combinators on traces\label{sec:aczel_sequences-traces-combinators} \<close>

definition final' :: "'s \<Rightarrow> ('a \<times> 's) list \<Rightarrow> 's" where
  "final' s xs = last (s # map snd xs)"

abbreviation (input) final :: "('a, 's, 'v) trace.t \<Rightarrow> 's" where
  "final \<sigma> \<equiv> trace.final' (trace.init \<sigma>) (trace.rest \<sigma>)"

definition continue :: "('a, 's, 'v) trace.t \<Rightarrow> ('a \<times> 's) list \<times> 'v option \<Rightarrow> ('a, 's, 'v) trace.t" (infixl \<open>@-\<^sub>S\<close> 64) where
  "\<sigma> @-\<^sub>S xsv = (case trace.term \<sigma> of None \<Rightarrow> trace.T (trace.init \<sigma>) (trace.rest \<sigma> @ fst xsv) (snd xsv) | Some v \<Rightarrow> \<sigma>)"

definition tl :: "('a, 's, 'v) trace.t \<rightharpoonup> ('a, 's, 'v) trace.t" where
  "tl \<sigma> = (case trace.rest \<sigma> of [] \<Rightarrow> None | x # xs \<Rightarrow> Some (trace.T (snd x) xs (trace.term \<sigma>)))"

definition dropn :: "nat \<Rightarrow> ('a, 's, 'v) trace.t \<rightharpoonup> ('a, 's, 'v) trace.t" where
  "dropn = (^^) trace.tl"

definition take :: "nat \<Rightarrow> ('a, 's, 'v) trace.t \<Rightarrow> ('a, 's, 'v) trace.t" where
  "take i \<sigma> = (if i \<le> length (trace.rest \<sigma>) then trace.T (trace.init \<sigma>) (List.take i (trace.rest \<sigma>)) None else \<sigma>)"

type_synonym ('a, 's) transitions = "('a \<times> 's \<times> 's) list"

primrec transitions' :: "'s \<Rightarrow> ('a \<times> 's) list \<Rightarrow> ('a, 's) trace.transitions" where
  "transitions' s [] = []"
| "transitions' s (x # xs) = (fst x, s, snd x) # transitions' (snd x) xs"

abbreviation (input) transitions :: "('a, 's, 'v) trace.t \<Rightarrow> ('a, 's) trace.transitions" where
  "transitions \<sigma> \<equiv> trace.transitions' (trace.init \<sigma>) (trace.rest \<sigma>)"

setup \<open>Sign.mandatory_path "final'"\<close>

lemma simps[simp]:
  shows "trace.final' s [] = s"
    and "trace.final' s (x # xs) = trace.final' (snd x) xs"
    and "trace.final' s (xs @ ys) = trace.final' (trace.final' s xs) ys"
    and idle: "snd ` set xs \<subseteq> {s} \<Longrightarrow> trace.final' s xs = s"
    and "snd ` set xs \<subseteq> {s} \<Longrightarrow> trace.final' s (xs @ ys) = trace.final' s ys"
    and "snd ` set ys \<subseteq> {trace.final' s xs} \<Longrightarrow> trace.final' s (xs @ ys) = trace.final' s xs"
by (simp_all add: trace.final'_def last_map image_subset_iff split: if_split_asm)

lemma map:
  shows "trace.final' (sf s) (map (map_prod af sf) xs) = sf (trace.final' s xs)"
by (simp add: trace.final'_def last_map)

lemma replicate:
  shows "trace.final' s (replicate i as) = (if i = 0 then s else snd as)"
by (simp add: trace.final'_def)

lemma map_idle:
  assumes "(\<lambda>x. sf (snd x)) ` set xs \<subseteq> {sf s}"
  shows "sf (trace.final' s xs) = sf s"
using assms by (induct xs arbitrary: s) simp_all

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tl"\<close>

lemma simps[simp]:
  shows "trace.tl (trace.T s [] v) = None"
    and "trace.tl (trace.T s (x # xs) v) = Some (trace.T (snd x) xs v)"
by (simp_all add: trace.tl_def)

setup \<open>Sign.parent_path\<close>

lemma dropn_alt_def:
  shows "trace.dropn i \<sigma>
       = (case drop i ((undefined, trace.init \<sigma>) # trace.rest \<sigma>) of
           [] \<Rightarrow> None
         | x # xs \<Rightarrow> Some (trace.T (snd x) xs (trace.term \<sigma>)))"
proof(induct i arbitrary: \<sigma>)
  case 0 show ?case
    by (simp add: trace.dropn_def)
next
  case (Suc i \<sigma>) then show ?case
    by (cases \<sigma>; cases "trace.rest \<sigma>"; simp add: trace.dropn_def drop_Cons' split: list.split)
qed

setup \<open>Sign.mandatory_path "dropn"\<close>

lemma simps[simp]:
  shows 0: "trace.dropn 0 = Some"
    and Suc: "trace.dropn (Suc i) \<sigma> = Option.bind (trace.tl \<sigma>) (trace.dropn i)"
    and dropn: "Option.bind (trace.dropn i \<sigma>) (trace.dropn j) = trace.dropn (i + j) \<sigma>"
by (simp_all add: trace.dropn_def pfunpow_add)

lemma Suc_right:
  shows "trace.dropn (Suc i) \<sigma> = Option.bind (trace.dropn i \<sigma>) trace.tl"
by (simp add: trace.dropn_def pfunpow_Suc_right del: pfunpow.simps)

lemma eq_none_length_conv:
  shows "trace.dropn i \<sigma> = None \<longleftrightarrow> length (trace.rest \<sigma>) < i"
by (auto simp: trace.dropn_alt_def split: list.split)

lemma eq_Some_length_conv:
  shows "(\<exists>\<sigma>'. trace.dropn i \<sigma> = Some \<sigma>') \<longleftrightarrow> i \<le> length (trace.rest \<sigma>)"
by (auto simp: trace.dropn_alt_def dest: drop_eq_Cons_lengthD split: list.split)

lemma eq_Some_lengthD:
  assumes "trace.dropn i \<sigma> = Some \<sigma>'"
  shows "i \<le> length (trace.rest \<sigma>)"
using assms trace.dropn.eq_Some_length_conv by blast

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "take"\<close>

lemma sel:
  shows "trace.init (trace.take i \<sigma>) = trace.init \<sigma>"
    and "trace.rest (trace.take i \<sigma>) = List.take i (trace.rest \<sigma>)"
    and "trace.term (trace.take i \<sigma>) = (if i \<le> length (trace.rest \<sigma>) then None else trace.term \<sigma>)"
by (simp_all add: trace.take_def)

lemma 0:
  shows "trace.take 0 \<sigma> = trace.T (trace.init \<sigma>) [] None"
by (simp add: trace.take_def)

lemma Nil:
  shows "trace.take i (trace.T s [] None) = trace.T s [] None"
by (simp add: trace.take_def)

lemmas simps[simp] =
  trace.take.sel
  "trace.take.0"
  trace.take.Nil

lemma map:
  shows "trace.take i (trace.map af sf vf \<sigma>) = trace.map af sf vf (trace.take i \<sigma>)"
by (simp add: trace.take_def take_map)

lemma append:
  shows "trace.take i (trace.T s (xs @ ys) v) = trace.T s (List.take i (xs @ ys)) (if length (xs @ ys) < i then v else None)"
by (simp add: trace.take_def)

lemma take:
  shows "trace.take i (trace.take j \<sigma>) = trace.take (min i j) \<sigma>"
by (simp add: min_le_iff_disj trace.take_def)

lemma continue:
  shows "trace.take i (\<sigma> @-\<^sub>S xsv)
       = trace.take i \<sigma> @-\<^sub>S (List.take (i - length (trace.rest \<sigma>)) (fst xsv),
                            if i \<le> length (trace.rest \<sigma>) + length (fst xsv) then None else snd xsv)"
by (simp add: trace.continue_def trace.take_def split: option.split)

lemma all_iff:
  shows "trace.take i \<sigma> = \<sigma> \<longleftrightarrow> (case trace.term \<sigma> of None \<Rightarrow> length (trace.rest \<sigma>) | Some _ \<Rightarrow> Suc (length (trace.rest \<sigma>))) \<le> i" (is ?thesis1)
    and "\<sigma> = trace.take i \<sigma> \<longleftrightarrow> (case trace.term \<sigma> of None \<Rightarrow> length (trace.rest \<sigma>) | Some _ \<Rightarrow> Suc (length (trace.rest \<sigma>))) \<le> i" (is ?thesis2)
proof -
  show ?thesis1 by (cases \<sigma>) (simp add: trace.take_def split: option.split)
  then show ?thesis2
    by (rule eq_commute_conv)
qed

lemmas all = iffD2[OF trace.take.all_iff(1)]

lemma Ex_all:
  shows "\<sigma> = trace.take (Suc (length (trace.rest \<sigma>))) \<sigma>"
by (simp add: trace.take_def)

lemma replicate:
  shows "trace.take i (trace.T s (replicate j as) v)
      = trace.T s (replicate (min i j) as) (if i \<le> j then None else v)"
by (simp add: trace.take_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "continue"\<close>

lemma sel[simp]:
  shows "trace.init (\<sigma> @-\<^sub>S xs) = trace.init \<sigma>"
    and "trace.rest (\<sigma> @-\<^sub>S xsv) = (case trace.term \<sigma> of None \<Rightarrow> trace.rest \<sigma> @ fst xsv | Some v \<Rightarrow> trace.rest \<sigma>)"
    and "trace.term (\<sigma> @-\<^sub>S xsv) = (case trace.term \<sigma> of None \<Rightarrow> snd xsv | Some v \<Rightarrow> trace.term \<sigma>)"
by (simp_all add: trace.continue_def split: option.split)

lemma simps[simp]:
  shows "trace.T s xs None @-\<^sub>S ysv = trace.T s (xs @ fst ysv) (snd ysv)"
    and "trace.T s xs (Some v) @-\<^sub>S ysv = trace.T s xs (Some v)"
    and "\<sigma> @-\<^sub>S ([], None) = \<sigma>"
by (simp_all add: trace.continue_def trace.t.expand split: option.split)

lemma Nil:
  shows "\<sigma> @-\<^sub>S ([], trace.term \<sigma>) = \<sigma>"
    and "trace.T (trace.init \<sigma>) [] None @-\<^sub>S (trace.rest \<sigma>, trace.term \<sigma>) = \<sigma>"
by (cases \<sigma>) (simp_all add: trace.continue_def split: option.split)

lemma map:
  shows "trace.map af sf vf (\<sigma> @-\<^sub>S xsv) = trace.map af sf vf \<sigma> @-\<^sub>S map_prod (map (map_prod af sf)) (map_option vf) xsv"
by (simp add: trace.continue_def split: option.split)

lemma eq_trace_conv:
  shows "\<sigma> @-\<^sub>S xsv = trace.T s xs v \<longleftrightarrow> trace.init \<sigma> = s \<and> (case trace.term \<sigma> of None \<Rightarrow> trace.rest \<sigma> @ fst xsv = xs \<and> v = snd xsv | Some v' \<Rightarrow> trace.rest \<sigma> = xs \<and> v = Some v')"
    and "trace.T s xs v = \<sigma> @-\<^sub>S xsv \<longleftrightarrow> trace.init \<sigma> = s \<and> (case trace.term \<sigma> of None \<Rightarrow> trace.rest \<sigma> @ fst xsv = xs \<and> v = snd xsv | Some v' \<Rightarrow> trace.rest \<sigma> = xs \<and> v = Some v')"
by (case_tac [!] \<sigma>) (auto simp: trace.continue_def split: option.split)

lemma self_conv:
  shows "(\<sigma> = \<sigma> @-\<^sub>S xsv) \<longleftrightarrow> (case trace.term \<sigma> of None \<Rightarrow> xsv = ([], None) | Some _ \<Rightarrow> True)"
    and "(\<sigma> @-\<^sub>S xsv = \<sigma>) \<longleftrightarrow> (case trace.term \<sigma> of None \<Rightarrow> xsv = ([], None) | Some _ \<Rightarrow> True)"
by (cases \<sigma>; cases xsv; fastforce split: option.splits)+

lemma same_eq:
  shows "(\<sigma> @-\<^sub>S xsv = \<sigma> @-\<^sub>S ysv) \<longleftrightarrow> (case trace.term \<sigma> of None \<Rightarrow> xsv = ysv | Some _ \<Rightarrow> True)"
by (fastforce simp: trace.continue_def prod.expand split: option.split)

lemma continue:
  shows "\<sigma> @-\<^sub>S xsv @-\<^sub>S ysv = \<sigma> @-\<^sub>S (case snd xsv of None \<Rightarrow> (fst xsv @ fst ysv, snd ysv) | Some _ \<Rightarrow> xsv)"
by (simp add: trace.continue_def split: option.split)

lemma take_drop_id:
  shows "trace.take i \<sigma> @-\<^sub>S case_option ([], None) (\<lambda>\<sigma>'. (trace.rest \<sigma>', trace.term \<sigma>')) (trace.dropn i \<sigma>) = \<sigma>"
by (cases \<sigma>)
   (clarsimp simp: trace.take_def trace.dropn_alt_def split: list.split;
    metis append_take_drop_id list.sel(3) tl_drop)

setup \<open>Sign.parent_path\<close>


paragraph\<open> Prefix ordering \<close>

instantiation trace.t :: (type, type, type) order
begin

definition less_eq_t :: "('a, 's, 'v) trace.t relp" where
  "less_eq_t \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<longleftrightarrow> (\<exists>xsv. \<sigma>\<^sub>2 = \<sigma>\<^sub>1 @-\<^sub>S xsv)"

definition less_t :: "('a, 's, 'v) trace.t relp" where
  "less_t \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<longleftrightarrow> \<sigma>\<^sub>1 \<le> \<sigma>\<^sub>2 \<and> \<sigma>\<^sub>1 \<noteq> \<sigma>\<^sub>2"

instance
by standard
   (auto simp: less_eq_t_def less_t_def trace.continue.self_conv trace.continue.continue trace.continue.same_eq
        split: option.splits)

end

lemma less_eqE[consumes 1, case_names prefix maximal]:
  assumes "\<sigma>\<^sub>1 \<le> \<sigma>\<^sub>2"
  assumes "\<lbrakk>trace.term \<sigma>\<^sub>1 = None; trace.init \<sigma>\<^sub>1 = trace.init \<sigma>\<^sub>2; prefix (trace.rest \<sigma>\<^sub>1) (trace.rest \<sigma>\<^sub>2)\<rbrakk> \<Longrightarrow> P"
  assumes "\<And>v. \<lbrakk>trace.term \<sigma>\<^sub>1 = Some v; \<sigma>\<^sub>1 = \<sigma>\<^sub>2\<rbrakk> \<Longrightarrow> P"
  shows P
using assms by (cases "trace.term \<sigma>\<^sub>1") (auto simp: trace.less_eq_t_def trace.continue.self_conv)

lemmas less_eq_extE[consumes 1, case_names prefix maximal]
  = trace.less_eqE[of "trace.T s\<^sub>1 xs\<^sub>1 v\<^sub>1" "trace.T s\<^sub>2 xs\<^sub>2 v\<^sub>2", simplified, simplified conj_explode]
    for s\<^sub>1 xs\<^sub>1 v\<^sub>1 s\<^sub>2 xs\<^sub>2 v\<^sub>2

lemma less_eq_self_continue:
  shows "\<sigma> \<le> \<sigma> @-\<^sub>S xsv"
using trace.less_eq_t_def by blast

lemma less_eq_same_append_conv:
  shows "trace.T s xs v \<le> trace.T s' (xs @ ys) v' \<longleftrightarrow> s = s' \<and> (\<forall>v''. v = Some v'' \<longrightarrow> ys = [] \<and> v = v')"
by (auto simp: trace.less_eq_t_def trace.continue.eq_trace_conv split: option.split)

lemma less_same_append_conv:
  shows "trace.T s xs v < trace.T s' (xs @ ys) v' \<longleftrightarrow> s = s' \<and> v = None \<and> (ys \<noteq> [] \<or> (\<exists>v''. v' = Some v''))"
by (cases v) (auto simp: trace.less_t_def trace.less_eq_same_append_conv)

lemma less_eq_Some[simp]:
  shows "trace.T s xs (Some v) \<le> \<sigma> \<longleftrightarrow> trace.init \<sigma> = s \<and> trace.rest \<sigma> = xs \<and> trace.term \<sigma> = Some v"
by (cases \<sigma>) (simp add: trace.less_eq_t_def)

lemma less_eq_None:
  shows "\<sigma> \<le> trace.T s xs None \<longleftrightarrow> trace.init \<sigma> = s \<and> prefix (trace.rest \<sigma>) xs \<and> trace.term \<sigma> = None"
    and "trace.T s xs None \<le> \<sigma> \<longleftrightarrow> trace.init \<sigma> = s \<and> prefix xs (trace.rest \<sigma>)"
by (case_tac [!] \<sigma>) (auto simp: trace.less_eq_same_append_conv elim!: trace.less_eqE prefixE)

lemma less:
  shows "trace.T s xs v < \<sigma> \<longleftrightarrow> trace.init \<sigma> = s \<and> (\<exists>ys. trace.rest \<sigma> = xs @ ys \<and> (trace.term \<sigma> = None \<longrightarrow> ys \<noteq> [])) \<and> v = None"
    and "\<sigma> < trace.T s xs v  \<longleftrightarrow> trace.init \<sigma> = s \<and> (\<exists>ys. xs = trace.rest \<sigma> @ ys \<and> (v = None \<longrightarrow> ys \<noteq> [])) \<and> trace.term \<sigma> = None"
by (case_tac [!] \<sigma>)
   (auto simp: trace.less_t_def trace.less_eq_t_def trace.continue.eq_trace_conv split: option.split_asm)

lemma less_eq_take[iff]:
  shows "trace.take i \<sigma> \<le> \<sigma>"
by (simp add: trace.take_def take_is_prefix trace.less_eq_None)

lemma less_eq_takeE:
  assumes "\<sigma>\<^sub>1 \<le> \<sigma>\<^sub>2"
  obtains i where "\<sigma>\<^sub>1 = trace.take i \<sigma>\<^sub>2"
using assms
by (cases \<sigma>\<^sub>1)
   (auto simp: trace.take_def
        elim!: trace.less_eqE prefixE
         dest: meta_spec[where x="length (trace.rest \<sigma>\<^sub>1)"]
                  meta_spec[where x="Suc (length (trace.rest \<sigma>\<^sub>1))"])

lemma less_eq_take_def:
  shows "\<sigma>\<^sub>1 \<le> \<sigma>\<^sub>2 \<longleftrightarrow> (\<exists>i. \<sigma>\<^sub>1 = trace.take i \<sigma>\<^sub>2)"
by (blast elim: trace.less_eq_takeE)

lemma less_take_less_eq:
  assumes "\<sigma> < trace.take (Suc i) \<sigma>'"
  shows "\<sigma> \<le> trace.take i \<sigma>'"
using assms
by (clarsimp simp: trace.less_t_def trace.less_eq_take_def trace.take.take) (metis le_SucE min_def)

lemma wfP_less:
  shows "wfP ((<) :: (_, _, _) trace.t relp)"
unfolding wfP_def
proof(rule wf_subset[rotated])
  let ?r = "inv_image ({(None, Some v) |v. True} <*lex*> {(x, y). strict_prefix x y}) (\<lambda>\<sigma>. (trace.term \<sigma>, trace.rest \<sigma>))"
  show "wf ?r"
    using wfP_def wfP_strict_prefix wf_def by fastforce
  show "{(x, y). x < y} \<subseteq> ?r"
    by (auto simp: trace.less_t_def trace.less_eq_take_def trace.take.all_iff split: option.splits)
qed

lemma less_eq_same_cases:
  fixes ys :: "(_, _, _) trace.t"
  assumes "xs\<^sub>1 \<le> ys"
  assumes "xs\<^sub>2 \<le> ys"
  shows "xs\<^sub>1 \<le> xs\<^sub>2 \<or> xs\<^sub>2 \<le> xs\<^sub>1"
using assms
by (clarsimp simp: trace.less_eq_take_def trace.take.take) (metis min.absorb_iff1 nle_le)

setup \<open>Sign.mandatory_path "take"\<close>

lemma mono:
  assumes "\<sigma>\<^sub>1 \<le> \<sigma>\<^sub>2"
  assumes "i \<le> j"
  shows "trace.take i \<sigma>\<^sub>1 \<le> trace.take j \<sigma>\<^sub>2"
using assms
by (clarsimp simp: trace.less_eq_take_def trace.take.take) (metis min.assoc min.commute min_def)


setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map"\<close>

lemmas map = trace.t.map_comp[unfolded comp_def]

lemma monotone:
  shows "mono (trace.map af sf vf)"
by (rule monoI) (fastforce simp: trace.less_eq_take_def trace.take.map)

lemmas strengthen[strg] = st_monotone[OF trace.map.monotone]
lemmas mono = monoD[OF trace.map.monotone]

lemma monotone_less:
  shows "monotone (<) (<) (trace.map af sf vf)"
by (rule monotoneI)
   (auto simp: trace.less_t_def trace.map.mono[OF order.strict_implies_order] trace.split_all
        elim!: trace.less_eqE prefixE)

lemma less_eqR:
  assumes "\<sigma>\<^sub>1 \<le> trace.map af sf vf \<sigma>\<^sub>2"
  obtains \<sigma>\<^sub>2' where "\<sigma>\<^sub>2' \<le> \<sigma>\<^sub>2" and "\<sigma>\<^sub>1 = trace.map af sf vf \<sigma>\<^sub>2'"
using assms by (fastforce simp: trace.less_eq_take_def trace.take.map)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

lemmas eq = trace.t.rel_eq

lemmas mono = trace.t.rel_mono_strong[of ar sr vr \<sigma>\<^sub>1 \<sigma>\<^sub>2 ar' sr' vr'] for ar sr vr \<sigma>\<^sub>1 \<sigma>\<^sub>2 ar' sr' vr'

lemma strengthen[strg]:
  assumes "st_ord F ar ar'"
  assumes "st_ord F sr sr'"
  assumes "st_ord F vr vr'"
  shows "st_ord F (trace.rel ar sr vr \<sigma>\<^sub>1 \<sigma>\<^sub>2) (trace.rel ar' sr' vr' \<sigma>\<^sub>1 \<sigma>\<^sub>2)"
using assms by (cases F) (auto intro!: le_boolI elim: trace.rel.mono)

lemma length_rest:
  assumes "trace.rel ar sr vr \<sigma>\<^sub>1 \<sigma>\<^sub>2"
  shows "length (trace.rest \<sigma>\<^sub>1)
       = length (trace.rest \<sigma>\<^sub>2) \<and> (\<forall>i<length (trace.rest \<sigma>\<^sub>1). rel_prod ar sr (trace.rest \<sigma>\<^sub>1 ! i) (trace.rest \<sigma>\<^sub>2 ! i))"
by (rule rel_funE[OF trace.t.sel_transfer(2) assms]) (simp add: list_all2_conv_all_nth)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "take"\<close>

lemma rel:
  assumes "trace.rel ar sr vr \<sigma>\<^sub>1 \<sigma>\<^sub>2"
  shows "trace.rel ar sr vr (trace.take i \<sigma>\<^sub>1) (trace.take i \<sigma>\<^sub>2)"
using assms
by (auto simp: trace.take_def trace.t.rel_sel trace.rel.length_rest
         elim: rel_funE[OF trace.t.sel_transfer(1)])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "transitions'"\<close>

lemma prefix_conv:
  shows "prefix (trace.transitions' s xs) (trace.transitions' s ys) \<longleftrightarrow> prefix xs ys"
proof(induct xs arbitrary: s ys)
  case (Cons x xs s ys) then show ?case by (cases ys) auto
qed simp

lemma monotone:
  shows "monotone prefix prefix (trace.transitions' s)"
by (rule monotoneI) (simp add: trace.transitions'.prefix_conv)

lemma append:
  shows "trace.transitions' s (xs @ ys) = trace.transitions' s xs @ trace.transitions' (trace.final' s xs) ys"
by (induct xs arbitrary: s ys) simp_all

lemma eq_Nil_conv:
  shows "trace.transitions' s xs = [] \<longleftrightarrow> xs = []"
    and "[] = trace.transitions' s xs \<longleftrightarrow> xs = []"
by (case_tac [!] xs) simp_all

lemma eq_Cons_conv:
  shows "trace.transitions' s xs = y # ys \<longleftrightarrow> (\<exists>a s' xs'. xs = (a, s') # xs' \<and> y = (a, s, s') \<and> ys = trace.transitions' s' xs')"
    and "y # ys = trace.transitions' s xs \<longleftrightarrow> (\<exists>a s' xs'. xs = (a, s') # xs' \<and> y = (a, s, s') \<and> ys = trace.transitions' s' xs')"
by (case_tac [!] xs) auto

lemma inj_conv:
  shows "trace.transitions' s xs = trace.transitions' s ys \<longleftrightarrow> xs = ys"
by (induct xs arbitrary: s ys) (auto simp: trace.transitions'.eq_Nil_conv trace.transitions'.eq_Cons_conv)

lemma continue:
  shows "trace.transitions (\<sigma> @-\<^sub>S xsv)
       = trace.transitions \<sigma> @ (case trace.term \<sigma> of None \<Rightarrow> trace.transitions' (trace.final \<sigma>) (fst xsv) | Some v \<Rightarrow> [])"
by (simp add: trace.transitions'.append last_map trace.final'_def split: option.splits)

lemma idle_conv:
  shows "set (trace.transitions' s xs) \<subseteq> UNIV \<times> Id \<longleftrightarrow> snd ` set xs \<subseteq> {s}"
by (induct xs arbitrary: s) (simp; fast)+

lemma map:
  shows "trace.transitions' (sf s) (map (map_prod af sf) xs)
       = map (map_prod af (map_prod sf sf)) (trace.transitions' s xs)"
by (induct xs arbitrary: s) simp_all

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "transitions"\<close>

lemma monotone:
  shows "monotone (\<le>) prefix trace.transitions"
by (rule monotoneI) (metis prefix_order.eq_iff trace.less_eqE trace.transitions'.prefix_conv)

lemmas mono = monotoneD[OF trace.transitions.monotone]

lemma subseq:
 assumes "\<sigma> \<le> \<sigma>'"
 shows "subseq (trace.transitions \<sigma>) (trace.transitions \<sigma>')"
by (rule prefix_imp_subseq[OF trace.transitions.mono[OF assms]])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

type_synonym ('a, 's) steps = "('a \<times> 's \<times> 's) set"

setup \<open>Sign.mandatory_path "trace"\<close>

definition steps' :: "'s \<Rightarrow> ('a \<times> 's) list \<Rightarrow> ('a, 's) steps" where
  "steps' s xs = set (trace.transitions' s xs) - UNIV \<times> Id"

abbreviation (input) steps :: "('a, 's, 'v) trace.t \<Rightarrow> ('a, 's) steps" where
  "steps \<sigma> \<equiv> trace.steps' (trace.init \<sigma>) (trace.rest \<sigma>)"

setup \<open>Sign.mandatory_path "steps'"\<close>

lemma simps[simp]:
  shows "trace.steps' s [] = {}"
    and "trace.steps' s ((a, s) # xs) = trace.steps' s xs"
    and "s \<noteq> snd x \<Longrightarrow> trace.steps' s (x # xs) = insert (fst x, s, snd x) (trace.steps' (snd x) xs)"
    and "(a, s', s') \<notin> trace.steps' s xs"
    and "snd ` set xs \<subseteq> {s} \<Longrightarrow> trace.steps' s xs = {}"
    and "trace.steps' s [x] = (if s = snd x then {} else {(fst x, s, snd x)})"
by (simp_all add: trace.steps'_def insert_Diff_if trace.transitions'.idle_conv)

lemma Cons_eq_if:
  shows "trace.steps' s (x # xs)
      = (if s = snd x then trace.steps' s xs else insert (fst x, s, snd x) (trace.steps' (snd x) xs))"
by (auto simp: trace.steps'_def)

lemma stuttering:
  shows "trace.steps' s xs \<subseteq> r \<union> A \<times> Id \<longleftrightarrow> trace.steps' s xs \<subseteq> r"
    and "trace.steps' s xs \<subseteq> A \<times> Id \<union> r \<longleftrightarrow> trace.steps' s xs \<subseteq> r"
by (auto simp: trace.steps'_def)

lemma empty_conv[simp]:
  shows "trace.steps' s xs = {} \<longleftrightarrow> snd ` set xs \<subseteq> {s}" (is ?thesis1)
    and "{} = trace.steps' s xs \<longleftrightarrow> snd ` set xs \<subseteq> {s}" (is ?thesis2)
proof -
  show ?thesis1 by (simp add: trace.steps'_def trace.transitions'.idle_conv)
  then show ?thesis2
    by (rule eq_commute_conv)
qed

lemma append:
  shows "trace.steps' s (xs @ ys)
       = trace.steps' s xs \<union> trace.steps' (trace.final' s xs) ys"
by (simp add: trace.steps'_def trace.transitions'.append Un_Diff)

lemma map:
  shows "trace.steps' (sf s) (map (map_prod af sf) xs) = map_prod af (map_prod sf sf) ` trace.steps' s xs - UNIV \<times> Id"
    and "trace.steps' s (map (map_prod af id) xs) = map_prod af id ` trace.steps' s xs - UNIV \<times> Id"
by (force simp: trace.steps'_def trace.transitions'.map trace.transitions'.map[where sf=id, simplified])+

lemma memberD:
  assumes "(a, s, s') \<in> trace.steps' s\<^sub>0 xs"
  shows "(a, s') \<in> set xs"
using assms by (induct xs arbitrary: s\<^sub>0) (auto simp: trace.steps'.Cons_eq_if split: if_split_asm)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "steps"\<close>

lemma monotone:
  shows "mono trace.steps"
by (simp add: monoI trace.steps'_def Diff_mono set_subseq[OF trace.transitions.subseq])

lemmas mono = monoD[OF trace.steps.monotone]
lemmas strengthen[strg] = st_monotone[OF trace.steps.monotone]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "aset"\<close>

lemma simps:
  shows "trace.aset (trace.T s xs v) = fst ` set xs"
by (force simp: trace.t.set)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "sset"\<close>

lemma simps:
  shows "trace.sset (trace.T s xs v) = insert s (snd ` set xs)"
by (fastforce simp: trace.t.set image_iff)

lemma dropn_le:
  assumes "trace.dropn i \<sigma> = Some \<sigma>'"
  shows "trace.sset \<sigma>' \<subseteq> trace.sset \<sigma>"
using assms
by (cases \<sigma>; cases \<sigma>')
   (fastforce simp: trace.dropn_alt_def trace.sset.simps image_iff
             split: list.split_asm
              dest: arg_cong[where f=set] in_set_dropD)

lemma take_le:
  shows "trace.sset (trace.take i \<sigma>) \<subseteq> trace.sset \<sigma>"
by (cases \<sigma>) (auto simp: trace.take_def trace.sset.simps dest: in_set_takeD)

lemma mono:
  shows "mono trace.sset"
by (rule monoI, unfold trace.less_eq_take_def)
   (blast dest: subsetD[OF trace.sset.take_le])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Behaviors\label{sec:aczel_sequences-behaviors} \<close>

setup \<open>Sign.mandatory_path "behavior"\<close>

datatype (aset: 'a, sset: 's, vset: 'v) t =
  B (init: 's) (rest: "('a \<times> 's, 'v) tllist")
for
  map: map

definition "term" :: "('a, 's, 'v) behavior.t \<Rightarrow> 'v option" where
  "term \<omega> = (if tfinite (behavior.rest \<omega>) then Some (terminal (behavior.rest \<omega>)) else None)"

declare behavior.t.map_id0[simp]
declare behavior.t.map_id0[unfolded id_def, simp]
declare behavior.t.map_sel[simp]
declare behavior.t.set_map[simp]
declare behavior.t.map_comp[unfolded o_def, simp]
declare behavior.t.set[simp del]

lemma split_all[no_atp]: \<comment>\<open> imitate the setup for \<^typ>\<open>'a \<times> 'b\<close> without the automation \<close>
  shows "(\<And>x. PROP P x) \<equiv> (\<And>s xs. PROP P (behavior.B s xs))"
proof
  show "PROP P (behavior.B s xs)" if "\<And>x. PROP P x" for s xs by (rule that)
next
  fix x
  assume "\<And>s xs. PROP P (behavior.B s xs)"
  from \<open>PROP P (behavior.B (behavior.init x) (behavior.rest x))\<close> show "PROP P x" by simp
qed

lemma split_All[no_atp]:
  shows "(\<forall>x. P x) \<longleftrightarrow> (\<forall>s xs. P (behavior.B s xs))" (is "?lhs \<longleftrightarrow> ?rhs")
proof (intro iffI allI)
  fix x assume ?rhs then show "P x" by (cases x) simp_all
qed simp

lemma split_Ex[no_atp]:
  shows "(\<exists>x. P x) \<longleftrightarrow> (\<exists>s xs. P (behavior.B s xs))" (is "?lhs \<longleftrightarrow> ?rhs")
proof (intro iffI allI; elim exE)
  fix x assume "P x" then show "\<exists>s xs. P (behavior.B s xs)" by (cases x) fast
qed auto


subsection\<open> Combinators on behaviors\label{sec:aczel_sequences-behaviors-combinators} \<close>

definition continue :: "('a, 's, 'v) trace.t \<Rightarrow> ('a \<times> 's, 'v) tllist \<Rightarrow> ('a, 's, 'v) behavior.t" (infix \<open>@-\<^sub>B\<close> 64) where
  "\<sigma> @-\<^sub>B xs = behavior.B (trace.init \<sigma>) (tshift2 (trace.rest \<sigma>, trace.term \<sigma>) xs)"

definition tl :: "('a, 's, 'v) behavior.t \<rightharpoonup> ('a, 's, 'v) behavior.t" where
  "tl \<omega> = (case behavior.rest \<omega> of TNil v \<Rightarrow> None | TCons x xs \<Rightarrow> Some (behavior.B (snd x) xs))"

definition dropn :: "nat \<Rightarrow> ('a, 's, 'v) behavior.t \<rightharpoonup> ('a, 's, 'v) behavior.t" where
  "dropn = (^^) behavior.tl"

definition take :: "nat \<Rightarrow> ('a, 's, 'v) behavior.t \<Rightarrow> ('a, 's, 'v) trace.t" where
  "take i \<omega> = uncurry (trace.T (behavior.init \<omega>)) (ttake i (behavior.rest \<omega>))"

setup \<open>Sign.mandatory_path "continue"\<close>

lemma simps:
  shows "trace.T s xs None @-\<^sub>B ys = behavior.B s (tshift xs ys)"
    and "trace.T s xs (Some v) @-\<^sub>B ys = behavior.B s (tshift xs (TNil v))"
    and "trace.T s (x # xs) w @-\<^sub>B ys = behavior.B s (TCons x (tshift2 (xs, w) ys))"
by (simp_all add: behavior.continue_def)

lemma sel[simp]:
  shows init: "behavior.init (\<sigma> @-\<^sub>B xs) = trace.init \<sigma>"
    and rest: "behavior.rest (\<sigma> @-\<^sub>B xs) = tshift2 (trace.rest \<sigma>, trace.term \<sigma>) xs"
by (simp_all add: behavior.continue_def)

lemma term_None:
  assumes "trace.term \<sigma> = None"
  shows "\<sigma> @-\<^sub>B xs = behavior.B (trace.init \<sigma>) (tshift (trace.rest \<sigma>) xs)"
by (simp add: assms behavior.continue_def)

lemma term_Some:
  assumes "trace.term \<sigma> = Some v"
  shows "\<sigma> @-\<^sub>B xs = behavior.B (trace.init \<sigma>) (tshift (trace.rest \<sigma>) (TNil v))"
by (simp add: assms behavior.continue_def)

lemma tshift2:
  shows "\<sigma> @-\<^sub>B tshift2 xsv ys = (\<sigma> @-\<^sub>S xsv) @-\<^sub>B ys"
by (simp add: behavior.continue_def tshift2_def tshift_append split: option.split)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tl"\<close>

lemma TNil:
  shows "behavior.tl (behavior.B s (TNil v)) = None"
by (simp add: behavior.tl_def)

lemma TCons:
  shows "behavior.tl (behavior.B s (TCons x xs)) = Some (behavior.B (snd x) xs)"
by (simp add: behavior.tl_def)

lemma eq_None_conv:
  shows "behavior.tl \<omega> = None \<longleftrightarrow> is_TNil (behavior.rest \<omega>)"
by (simp add: behavior.tl_def split: tllist.split)

lemma continue_Cons:
  shows "behavior.tl (trace.T s (x # xs) v @-\<^sub>B ys) = Some (trace.T (snd x) xs v @-\<^sub>B ys)"
by (simp add: behavior.tl_def behavior.continue_def)

lemmas simps[simp] =
  behavior.tl.TNil
  behavior.tl.TCons
  behavior.tl.eq_None_conv
  behavior.tl.continue_Cons

lemma tfiniteD:
  assumes "behavior.tl \<omega> = Some \<omega>'"
  shows "tfinite (behavior.rest \<omega>') \<longleftrightarrow> tfinite (behavior.rest \<omega>)"
using assms by (auto simp: behavior.tl_def split: tllist.splits)

setup \<open>Sign.parent_path\<close>

lemma dropn_alt_def:
  shows "behavior.dropn i \<omega>
       = (case tdropn i (TCons (undefined, behavior.init \<omega>) (behavior.rest \<omega>)) of
           TNil _ \<Rightarrow> None
         | TCons x xs \<Rightarrow> Some (behavior.B (snd x) xs))"
proof(induct i arbitrary: \<omega>)
  case 0 show ?case by (simp add: behavior.dropn_def)
next
  case (Suc i \<omega>) then show ?case
    by (cases \<omega>; cases "behavior.rest \<omega>"; cases i;
        simp add: behavior.dropn_def tdropn_eq_TNil_conv tdropn_tlength split: tllist.splits)
qed

setup \<open>Sign.mandatory_path "dropn"\<close>

lemma simps[simp]:
  shows 0: "behavior.dropn 0 \<omega> = Some \<omega>"
    and TNil: "behavior.dropn i (behavior.B s (TNil v)) = (case i of 0 \<Rightarrow> Some (behavior.B s (TNil v)) | _ \<Rightarrow> None)"
by (simp_all add: behavior.dropn_def split: nat.splits)

lemma TCons:
  shows "behavior.dropn i (behavior.B s (TCons x xs))
      = (case i of 0 \<Rightarrow> Some (behavior.B s (TCons x xs)) | Suc j \<Rightarrow> behavior.dropn j (behavior.B (snd x) xs))"
by (simp add: behavior.dropn_def split: nat.splits)

lemma Suc:
  shows "behavior.dropn (Suc i) \<omega> = Option.bind (behavior.tl \<omega>) (behavior.dropn i)"
by (simp_all add: behavior.dropn_def)

lemma bind_tl_commute:
  shows "behavior.tl \<omega> \<bind> behavior.dropn i = behavior.dropn i \<omega> \<bind> behavior.tl"
by (simp add: behavior.dropn_def pfunpow_swap1)

lemma Suc_right:
  shows "behavior.dropn (Suc i) \<omega> = Option.bind (behavior.dropn i \<omega>) behavior.tl"
by (simp add: behavior.dropn_def pfunpow_Suc_right del: pfunpow.simps)

lemma dropn:
  shows "Option.bind (behavior.dropn i \<omega>) (behavior.dropn j) = behavior.dropn (i + j) \<omega>"
by (simp add: behavior.dropn_def pfunpow_add)

lemma add:
  shows "behavior.dropn (i + j) = (\<lambda>\<omega>. Option.bind (behavior.dropn i \<omega>) (behavior.dropn j))"
by (simp add: fun_eq_iff behavior.dropn.dropn)

lemma tfiniteD:
  assumes "behavior.dropn i \<omega> = Some \<omega>'"
  shows "tfinite (behavior.rest \<omega>') \<longleftrightarrow> tfinite (behavior.rest \<omega>)"
using assms
by (induct i arbitrary: \<omega>')
   (auto simp: behavior.dropn.Suc_right behavior.tl.tfiniteD split: bind_split_asm)

lemma shorterD:
  assumes "behavior.dropn i \<omega> = Some \<omega>'"
  assumes "j \<le> i"
  shows "\<exists>\<omega>''. behavior.dropn j \<omega> = Some \<omega>''"
using assms(1) le_Suc_ex[OF assms(2)]
by (clarsimp simp flip: behavior.dropn.dropn split: Option.bind_split_asm)

lemma eq_None_tlength_conv:
  shows "behavior.dropn i \<omega> = None \<longleftrightarrow> tlength (behavior.rest \<omega>) < enat i"
proof(induct i arbitrary: \<omega>)
  case 0 show ?case by (simp add: enat_0)
next
  case (Suc i) then show ?case
    by (cases \<omega>; cases "behavior.rest \<omega>"; simp add: behavior.dropn.Suc enat_0_iff flip: eSuc_enat)
qed

lemma eq_Some_tlength_conv:
  shows "(\<exists>\<omega>'. behavior.dropn i \<omega> = Some \<omega>') \<longleftrightarrow> enat i \<le> tlength (behavior.rest \<omega>)"
by (metis behavior.dropn.eq_None_tlength_conv leD leI not_None_eq2)

lemma eq_Some_tlengthD:
  assumes "behavior.dropn i \<omega> = Some \<omega>'"
  shows "enat i \<le> tlength (behavior.rest \<omega>)"
using assms behavior.dropn.eq_Some_tlength_conv by blast

lemma tlength_eq_SomeD:
  assumes "enat i \<le> tlength (behavior.rest \<omega>)"
  shows "\<exists>\<omega>'. behavior.dropn i \<omega> = Some \<omega>'"
using assms behavior.dropn.eq_Some_tlength_conv by blast

lemma eq_Some_tdropnD:
  assumes "behavior.dropn i \<omega> = Some \<omega>'"
  shows "tdropn i (behavior.rest \<omega>) = behavior.rest \<omega>'"
using assms
proof(induct i arbitrary: \<omega>)
  case (Suc i) then show ?case
    by (cases \<omega>; cases "behavior.rest \<omega>"; fastforce simp: behavior.dropn.Suc)
qed simp

lemma continue_shorter:
  assumes "i \<le> length (trace.rest \<sigma>)"
  shows "behavior.dropn i (\<sigma> @-\<^sub>B xs) = Option.bind (trace.dropn i \<sigma>) (\<lambda>\<sigma>'. Some (\<sigma>' @-\<^sub>B xs))"
using assms
proof(induct i arbitrary: \<sigma>)
  case (Suc i \<sigma>) from Suc.prems show ?case
    by (cases \<sigma>; cases "trace.rest \<sigma>")
       (simp_all add: behavior.dropn.Suc flip: Suc.hyps)
qed simp

lemma continue_Some:
  assumes "length (trace.rest \<sigma>) < i"
  assumes "trace.term \<sigma> = Some v"
  shows "behavior.dropn i (\<sigma> @-\<^sub>B xs) = None"
using assms by (simp add: behavior.dropn.eq_None_tlength_conv tlength_tshift2 tlength_tshift)

lemma continue_None:
  assumes "length (trace.rest \<sigma>) < i"
  assumes "trace.term \<sigma> = None"
  shows "behavior.dropn i (\<sigma> @-\<^sub>B xs)
       = (case tdropn (i - Suc (length (trace.rest \<sigma>))) xs of
           TNil _ \<Rightarrow> None
         | TCons y ys \<Rightarrow> Some (behavior.B (snd y) ys))"
using assms by (cases i) (auto simp: behavior.dropn_alt_def tdropn_tshift)

lemma continue:
  shows "behavior.dropn i (\<sigma> @-\<^sub>B xs)
       = (if i \<le> length (trace.rest \<sigma>)
            then Option.bind (trace.dropn i \<sigma>) (\<lambda>\<sigma>'. Some (\<sigma>' @-\<^sub>B xs))
            else if trace.term \<sigma> = None
                 then case tdropn (i - Suc (length (trace.rest \<sigma>))) xs of
                        TNil _ \<Rightarrow> None
                      | TCons y ys \<Rightarrow> Some (behavior.B (snd y) ys)
                 else None)"
by (clarsimp simp: behavior.dropn.continue_None behavior.dropn.continue_Some
                   behavior.dropn.continue_shorter)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "trace.take.behavior"\<close>

lemma take:
  shows "trace.take i (behavior.take j \<omega>) = behavior.take (min i j) \<omega>"
by (simp add: behavior.take_def trace.take_def split_def
              ttake_eq_None_conv ttake_flat length_ttake take_fst_ttake
       split: enat.split split_min)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "behavior"\<close>

setup \<open>Sign.mandatory_path "take"\<close>

lemma simps[simp]:
  shows 0: "behavior.take 0 \<omega> = trace.T (behavior.init \<omega>) [] None"
    and Suc_TNil: "behavior.take (Suc i) (behavior.B s (TNil v)) = trace.T s [] (Some v)"
by (simp_all add: behavior.take_def)

lemma sel[simp]:
  shows "trace.init (behavior.take i \<omega>) = behavior.init \<omega>"
    and "trace.rest (behavior.take i \<omega>) = fst (ttake i (behavior.rest \<omega>))"
    and "trace.term (behavior.take i \<omega>) = snd (ttake i (behavior.rest \<omega>))"
by (simp_all add: behavior.take_def split_def)

lemma monotone:
  shows "mono (\<lambda>i. behavior.take i \<omega>)"
by (rule monoI) (fastforce simp: trace.less_eq_take_def trace.take.behavior.take min_def)

lemmas mono = monoD[OF behavior.take.monotone]

lemma map:
  shows "behavior.take i (behavior.map af sf vf \<omega>) = trace.map af sf vf (behavior.take i \<omega>)"
by (induct i arbitrary: \<omega>) (simp_all add: behavior.take_def split_def ttake_tmap split: tllist.split)

lemma continue:
  shows "behavior.take i (\<sigma> @-\<^sub>B \<omega>) = trace.take i \<sigma> @-\<^sub>S ttake (i - length (trace.rest \<sigma>)) \<omega>"
by (cases \<sigma>)
   (auto simp: behavior.take_def split_def trace.take_def ttake_tshift2 ttake_TNil
        split: option.split nat.split)

lemma all_continue:
  assumes "tlength (behavior.rest \<omega>) < enat i"
  shows "behavior.take i \<omega> @-\<^sub>S xsv = behavior.take i \<omega>"
using assms
by (auto simp: behavior.take_def split_def trace.continue_def ttake_eq_None_conv
        split: option.split)

lemma continue_same:
  shows "behavior.take i (behavior.take i \<omega> @-\<^sub>B xsv) = behavior.take i \<omega>"
by (auto simp: behavior.take_def split_def ttake_tshift2 length_ttake
               ttake_eq_None_conv ttake_eq_Nil_conv ttake_eq_Some_conv ttake_TNil
        split: enat.split nat.split option.split)

lemma treplicate:
  shows "behavior.take i (behavior.B s (treplicate j as v))
       = trace.T s (List.replicate (min i j) as) (if j < i then Some v else None)"
by (simp add: behavior.take_def)

lemma trepeat:
  shows "behavior.take i (behavior.B s (trepeat as)) = trace.T s (List.replicate i as) None"
by (simp add: behavior.take_def ttake_trepeat)

lemma tshift:
  shows "behavior.take i (behavior.B s (tshift xs ys)) = trace.take i (trace.T s xs None) @-\<^sub>S ttake (i - length xs) ys"
by (simp add: behavior.take_def trace.take_def ttake_tshift split_def)

lemma length:
  shows "length (trace.rest (behavior.take j \<omega>))
       = (case tlength (behavior.rest \<omega>) of enat i \<Rightarrow> min i j | \<infinity> \<Rightarrow> j)"
by (auto simp: length_ttake split: enat.split)

lemma add:
  shows "behavior.take (i + j) \<omega>
       = behavior.take i \<omega> @-\<^sub>S (case behavior.dropn i \<omega> of Some \<omega>' \<Rightarrow> ttake j (behavior.rest \<omega>'))"
by (auto simp: behavior.take_def split_def ttake_add Let_def behavior.dropn.eq_Some_tdropnD
               behavior.dropn.eq_None_tlength_conv
         dest: iffD1[OF ttake_eq_None_conv(1)]
        split: option.split)

lemma term_Some_conv:
  shows "trace.term (behavior.take j \<omega>) = Some v
    \<longleftrightarrow> (tlength (behavior.rest \<omega>) < enat j \<and> Some v = behavior.term \<omega>)"
by (auto simp: behavior.term_def ttake_eq_Some_conv tfinite_tlength_conv)

lemma dropn:
  assumes "behavior.dropn i \<omega> = Some \<omega>'"
  shows "behavior.take j \<omega>' = the (trace.dropn i (behavior.take (i + j) \<omega>))"
using assms
proof(induct i arbitrary: j \<omega> \<omega>')
  case (Suc i j \<omega>) then show ?case
    by (cases \<omega>; cases "behavior.rest \<omega>"; cases i)
       (auto simp: behavior.dropn.Suc behavior.take_def split_def)
qed simp

lemma continue_id:
  assumes "tlength (behavior.rest \<omega>) < enat i"
  shows "behavior.take i \<omega> @-\<^sub>B xs = \<omega>"
using assms by (simp add: behavior.continue_def tshift2_ttake_shorter)

lemma flat:
  assumes "tlength (behavior.rest \<omega>) < enat i"
  assumes "i \<le> j"
  shows "behavior.take i \<omega> = behavior.take j \<omega>"
using assms by (simp add: behavior.take_def ttake_flat)

lemma eqI:
  assumes "\<And>i. behavior.take i \<omega>\<^sub>1 = behavior.take i \<omega>\<^sub>2"
  shows "\<omega>\<^sub>1 = \<omega>\<^sub>2"
using assms
by (cases \<omega>\<^sub>1; cases \<omega>\<^sub>2; simp add: behavior.take_def case_prod_beta prod_eq_iff ttake_eq_imp_eq)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "continue"\<close>

lemma take_drop_shorter:
  assumes "i \<le> j"
  shows "behavior.take i \<omega> @-\<^sub>S apfst (drop i) (ttake j (behavior.rest \<omega>)) = behavior.take j \<omega>"
using assms
by (simp add: trace.continue_def behavior.take.flat ttake_eq_None_conv ttake_eq_Some_conv trace.t.expand
        flip: take_fst_ttake[where i=i and j=j, simplified min_absorb1[OF assms]]
       split: option.split)

lemma take_drop_id:
  shows "behavior.take i \<omega> @-\<^sub>B behavior.rest (the (behavior.dropn i \<omega>)) = \<omega>"
by (cases "tlength (behavior.rest \<omega>) < enat i")
   (simp add: behavior.take.continue_id,
    simp add: behavior.continue_def tshift2_ttake_tdropn_id behavior.dropn.tlength_eq_SomeD
        flip: behavior.dropn.eq_Some_tdropnD)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "aset"\<close>

lemma simps:
  shows "behavior.aset (behavior.B s xs) = fst ` tset xs"
by (force simp: behavior.t.set)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "sset"\<close>

lemma simps:
  shows "behavior.sset (behavior.B s xs) = insert s (snd ` tset xs)"
by (fastforce simp: behavior.t.set image_iff)

lemma dropn_le:
  assumes "behavior.dropn i \<omega> = Some \<omega>'"
  shows "behavior.sset \<omega>' \<subseteq> behavior.sset \<omega>"
using assms
by (cases \<omega>; cases \<omega>')
   (fastforce simp: behavior.dropn_alt_def behavior.sset.simps image_iff
             split: tllist.split_asm
              dest: arg_cong[where f=tset] in_tset_tdropnD)

lemma take_le:
  shows "trace.sset (behavior.take i \<omega>) \<subseteq> behavior.sset \<omega>"
by (cases \<omega>)
   (auto simp: behavior.take_def behavior.sset.simps trace.sset.simps split_def
         dest: in_set_ttakeD)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "trace.dropn.behavior"\<close>

lemma take:
  shows "trace.dropn i (behavior.take j \<omega>)
       = (if i \<le> j then Option.bind (behavior.dropn i \<omega>) (\<lambda>\<omega>'. Some (behavior.take (j - i) \<omega>'))
                    else None)"
proof(cases "i \<le> j")
  case False then show ?thesis
    by (clarsimp simp: trace.dropn.eq_none_length_conv length_ttake split: enat.split) linarith
next
  case True then show ?thesis
  proof(induct j arbitrary: i \<omega>)
    case (Suc j i \<omega>) then show ?case
      by (cases \<omega>; cases i)
         (auto simp: behavior.dropn.Suc behavior.take_def split_def behavior.split_all
              split: tllist.splits)
  qed simp
qed

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
