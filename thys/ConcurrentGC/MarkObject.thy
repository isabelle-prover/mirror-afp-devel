(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory MarkObject
imports
  Handshakes
begin

(*>*)
subsection{* Object colours, reference validity, worklist validity *}

text{*

We adopt the classical tricolour scheme for object colours due to
\citet{DBLP:journals/cacm/DijkstraLMSS78}, but tweak it somewhat in
the presence of worklists and TSO. Intuitively:.
\begin{description}
\item[White] potential garbage, not yet reached
\item[Grey] reached, presumed live, a source of possible new references (work)
\item[Black] reached, presumed live, not a source of new references
\end{description}

In this particular setting we use the following interpretation:
\begin{description}
\item[White:] not marked
\item[Grey:] on a worklist
\item[Black:] marked and not on a worklist
\end{description}

Note that this allows the colours to overlap: an object being marked
may be white (on the heap) and in @{const "ghost_honorary_grey"} for
some process, i.e. grey.

*}

abbreviation marked :: "'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "marked r s \<equiv> obj_at (\<lambda>obj. obj_mark obj = sys_fM s) r s"

abbreviation white :: "'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "white r s \<equiv> obj_at (\<lambda>obj. obj_mark obj = (\<not>sys_fM s)) r s"

definition WL :: "'mut process_name \<Rightarrow> ('field, 'mut, 'ref) lsts \<Rightarrow> 'ref set" where
  "WL p \<equiv> \<lambda>s. W (s p) \<union> ghost_honorary_grey (s p)"

definition grey :: "'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "grey r \<equiv> EXS p. \<langle>r\<rangle> in WL p"

definition black :: "'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "black r \<equiv> marked r and not grey r"

text{*

We show that if a mutator can load a reference into its roots (its
working set of references), then there is an object in the heap at
that reference.

In this particular collector, we can think of grey references and
pending TSO heap mutations as extra mutator roots; in particular the
GC holds no roots itself but marks everything reachable from its
worklist, and so we need to know these objects exist. By the strong
tricolour invariant (\S\ref{sec:strong-tricolour-invariant}), black
objects point to black or grey objects, and so we do not need to treat
these specially.

*}

abbreviation write_refs :: "('field, 'ref) mem_write_action \<Rightarrow> 'ref set" where
  "write_refs w \<equiv> case w of mw_Mutate r f r' \<Rightarrow> {r} \<union> Option.set_option r' | _ \<Rightarrow> {}"

definition (in mut_m) tso_write_refs :: "('field, 'mut, 'ref) lsts \<Rightarrow> 'ref set" where
  "tso_write_refs \<equiv> \<lambda>s. \<Union>w \<in> set (sys_mem_write_buffers (mutator m) s). write_refs w"

definition (in mut_m) reachable :: "'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "reachable y \<equiv> EXS x. \<langle>x\<rangle> in (mut_roots union mut_ghost_honorary_root union tso_write_refs)
                    and x reaches y"

definition grey_reachable :: "'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "grey_reachable y \<equiv> EXS g. grey g and g reaches y"

definition valid_refs_inv :: "('field, 'mut, 'ref) lsts_pred" where
 "valid_refs_inv \<equiv> ALLS x. ((EXS m. mut_m.reachable m x) or grey_reachable x) imp valid_ref x"

text{*

\label{def:valid_W_inv}

The worklists track the grey objects. The following invariant asserts
that grey objects are marked on the heap except for a few steps near
the end of @{const "mark_object_fn"}, the processes' worklists and
@{const "ghost_honorary_grey"}s are disjoint, and that pending marks
are sensible.

The safety of the collector does not to depend on disjointness; we
include it as proof that the single-threading of grey objects in the
implementation is sound.

*}

definition valid_W_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "valid_W_inv \<equiv> ALLS p q r.
    (r in_W p or (sys_mem_lock neq \<langle>Some p\<rangle> and r in_ghost_honorary_grey p) imp marked r)
  and (\<langle>p \<noteq> q\<rangle> imp not (\<langle>r\<rangle> in WL p and \<langle>r\<rangle> in WL q))
  and (not (r in_ghost_honorary_grey p and r in_W q))
  and (empty sys_ghost_honorary_grey)
  and (ALLS fl. tso_pending_write p (mw_Mark r fl)
       imp ( \<langle>fl\<rangle> eq sys_fM
             and r in_ghost_honorary_grey p
             and tso_locked_by p
             and white r
             and tso_pending_mark p eq \<langle>[mw_Mark r fl]\<rangle> ))"

(*<*)

lemma obj_at_mark_dequeue[simp]:
  "obj_at P r (s(sys := s sys\<lparr> heap := (sys_heap s)(r' := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r')), mem_write_buffers := wb' \<rparr>))
\<longleftrightarrow> (r = r' \<longrightarrow> obj_at (\<lambda>obj. (P (obj\<lparr> obj_mark := fl \<rparr>))) r s) \<and> (r \<noteq> r' \<longrightarrow> obj_at P r s)"
by (clarsimp split: obj_at_splits)

lemma marked_not_white:
  "white r s \<Longrightarrow> \<not>marked r s"
by (clarsimp split: obj_at_splits)

lemma valid_ref_valid_null_ref_simps[simp]:
  "valid_ref r (s(sys := do_write_action w (s sys)\<lparr>mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>)) \<longleftrightarrow> valid_ref r s"
  "valid_null_ref r' (s(sys := do_write_action w (s sys)\<lparr>mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>)) \<longleftrightarrow> valid_null_ref r' s"
  "valid_null_ref r' (s(mutator m := mut_s', sys := (s sys)\<lparr> heap := (heap (s sys))(r'' \<mapsto> obj) \<rparr>)) \<longleftrightarrow> valid_null_ref r' s \<or> r' = Some r''"
by (auto simp: do_write_action_def valid_null_ref_def
        split: mem_write_action.splits obj_at_splits option.splits)

text{* points to, reaches, reachable mut, reachable grey *}

lemma reaches_fields:
  assumes "(x reaches y) s'"
  assumes "\<forall>r. (Option.set_option (sys_heap s' r) \<bind> ran \<circ> obj_fields) = (Option.set_option (sys_heap s r) \<bind> ran \<circ> obj_fields)"
  shows "(x reaches y) s"
using assms
proof induct
  case (step y z)
  then have "(y points_to z) s"
    by (cases "sys_heap s y")
       (auto simp: ran_def obj_at_def split: option.splits dest!: spec[where x=y])
  with step show ?case by (blast intro: rtranclp.intros(2))
qed simp

lemma reaches_eq_imp:
  "eq_imp (\<lambda>r s. Option.set_option (sys_heap s r) \<bind> ran \<circ> obj_fields)
          (x reaches y)"
by (auto simp: eq_imp_def elim: reaches_fields)

lemmas reaches_fun_upd[simp] = eq_imp_fun_upd[OF reaches_eq_imp, simplified eq_imp_simps, rule_format]

lemma (in mut_m) reachable_eq_imp:
  "eq_imp (\<lambda>r'. mut_roots \<otimes> mut_ghost_honorary_root \<otimes> (\<lambda>s. Option.set_option (sys_heap s r') \<bind> ran \<circ> obj_fields) \<otimes> tso_pending_mutate (mutator m))
          (reachable r)"
apply (clarsimp simp: eq_imp_def reachable_def tso_write_refs_def ex_disj_distrib)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>r'. (\<exists>w\<in>set (sys_mem_write_buffers (mutator m) s). r' \<in> write_refs w) \<longleftrightarrow> (\<exists>w\<in>set (sys_mem_write_buffers (mutator m) s'). r' \<in> write_refs w)")
 apply (subgoal_tac "\<forall>x. (x reaches r) s \<longleftrightarrow> (x reaches r) s'")
  apply clarsimp
 apply (auto simp: reaches_fields)[1]
apply (drule arg_cong[where f=set])
apply (clarsimp simp: set_eq_iff)
apply (rule iffI)
 apply clarsimp
 apply (rename_tac s s' r' w)
 apply (drule_tac x=w in spec)
 apply (rule_tac x=w in bexI)
  apply clarsimp
 apply (case_tac w, simp_all)
apply clarsimp
apply (rename_tac s s' r' w)
apply (drule_tac x=w in spec)
apply (rule_tac x=w in bexI)
 apply clarsimp
apply (case_tac w, simp_all)
done

lemmas reachable_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.reachable_eq_imp, simplified eq_imp_simps, rule_format]

lemma reachableI[intro]:
  "x \<in> mut_m.mut_roots m s \<Longrightarrow> mut_m.reachable m x s"
  "x \<in> mut_m.tso_write_refs m s \<Longrightarrow> mut_m.reachable m x s"
by (auto simp: mut_m.reachable_def)

lemma reachableE:
  "\<lbrakk> (x points_to y) s; mut_m.reachable m x s \<rbrakk> \<Longrightarrow> mut_m.reachable m y s"
by (auto simp: mut_m.reachable_def
         elim: rtranclp.intros(2))

lemma (in mut_m) reachable_induct[consumes 1, case_names root ghost_honorary_root tso_root reaches]:
  assumes r: "reachable y s"
  assumes root: "\<And>x. \<lbrakk> x \<in> mut_roots s \<rbrakk> \<Longrightarrow> P x"
  assumes ghost_honorary_root: "\<And>x. \<lbrakk> x \<in> mut_ghost_honorary_root s \<rbrakk> \<Longrightarrow> P x"
  assumes tso_root: "\<And>x. \<lbrakk> x \<in> tso_write_refs s \<rbrakk> \<Longrightarrow> P x"
  assumes reaches: "\<And>x y. \<lbrakk> reachable x s; (x points_to y) s; P x \<rbrakk> \<Longrightarrow> P y"
  shows "P y"
using r unfolding reachable_def
proof(clarify)
  fix x
  assume xy: "(x reaches y) s" and xr: "x \<in> mut_roots s \<union> mut_ghost_honorary_root s \<union> tso_write_refs s"
  then show "P y"
  proof induct
    case base with root ghost_honorary_root tso_root show ?case by blast
  next
    case (step y z) with reaches show ?case
      unfolding reachable_def by blast
  qed
qed

lemma (in mut_m) mut_reachableE[consumes 1, case_names mut_root tso_write_refs]:
  "\<lbrakk> reachable y s;
     \<And>x. \<lbrakk> (x reaches y) s; x \<in> mut_roots s \<rbrakk> \<Longrightarrow> Q;
     \<And>x. \<lbrakk> (x reaches y) s; x \<in> mut_ghost_honorary_root s \<rbrakk> \<Longrightarrow> Q;
     \<And>x. \<lbrakk> (x reaches y) s; x \<in> tso_write_refs s \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (auto simp: reachable_def)

lemma grey_reachable_eq_imp:
  "eq_imp (\<lambda>r'. (\<lambda>s. \<Union>p. WL p s) \<otimes> (\<lambda>s. Option.set_option (sys_heap s r') \<bind> ran \<circ> obj_fields))
          (grey_reachable r)"
by (auto simp: eq_imp_def grey_reachable_def grey_def set_eq_iff reaches_fields)

lemmas grey_reachable_fun_upd[simp] = eq_imp_fun_upd[OF grey_reachable_eq_imp, simplified eq_imp_simps, rule_format]

lemma grey_reachableI[intro]:
  "grey g s \<Longrightarrow> grey_reachable g s"
by (auto simp: grey_reachable_def)

lemma grey_reachableE:
  "\<lbrakk> (g points_to y) s; grey_reachable g s \<rbrakk> \<Longrightarrow> grey_reachable y s"
by (auto simp: grey_reachable_def
         elim: rtranclp.intros(2))

text{* colours and work lists *}

lemma black_eq_imp:
  "eq_imp (\<lambda>_::unit. (\<lambda>s. r \<in> (\<Union>p. WL p s)) \<otimes> sys_fM \<otimes> (\<lambda>s. Option.map_option obj_mark (sys_heap s r)))
          (black r)"
by (auto simp add: eq_imp_def black_def grey_def obj_at_def split: option.splits)

lemma white_eq_imp:
  "eq_imp (\<lambda>_::unit. sys_fM \<otimes> (\<lambda>s. Option.map_option obj_mark (sys_heap s r)))
          (white r)"
by (auto simp add: eq_imp_def obj_at_def split: option.splits)

lemma grey_eq_imp:
  "eq_imp (\<lambda>_::unit. (\<lambda>s. r \<in> (\<Union>p. WL p s)))
          (grey r)"
by (auto simp add: eq_imp_def grey_def)

lemmas black_fun_upd[simp] = eq_imp_fun_upd[OF black_eq_imp, simplified eq_imp_simps, rule_format]
lemmas grey_fun_upd[simp] = eq_imp_fun_upd[OF grey_eq_imp, simplified eq_imp_simps, rule_format]
lemmas white_fun_upd[simp] = eq_imp_fun_upd[OF white_eq_imp, simplified eq_imp_simps, rule_format]

(* This demonstrates the overlap in colours *)
lemma colours_distinct[dest]:
  "black r s \<Longrightarrow> \<not>grey r s"
  "black r s \<Longrightarrow> \<not>white r s"
  "grey r s  \<Longrightarrow> \<not>black r s"
  "white r s \<Longrightarrow> \<not>black r s"
by (auto simp: black_def split: obj_at_splits)

lemma marked_imp_black_or_grey:
  "marked r s \<Longrightarrow> black r s \<or> grey r s"
  "\<not> white r s \<Longrightarrow> \<not> valid_ref r s \<or> black r s \<or> grey r s"
by (auto simp: black_def grey_def split: obj_at_splits)

lemma blackD[dest]:
  "black r s \<Longrightarrow> marked r s"
  "black r s \<Longrightarrow> r \<notin> WL p s"
by (simp_all add: black_def grey_def)

text{* valid refs inv *}

lemma valid_refs_inv_eq_imp:
  "eq_imp (\<lambda>(m', r'). (\<lambda>s. roots (s (mutator m'))) \<otimes> (\<lambda>s. ghost_honorary_root (s (mutator m'))) \<otimes> (\<lambda>s. Option.map_option obj_fields (sys_heap s r')) \<otimes> tso_pending_mutate (mutator m') \<otimes> (\<lambda>s. \<Union>p. WL p s))
          valid_refs_inv"
apply (clarsimp simp: eq_imp_def valid_refs_inv_def grey_reachable_def all_conj_distrib)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>r. valid_ref r s \<longleftrightarrow> valid_ref r s'")
 apply (subgoal_tac "\<forall>x. Option.set_option (sys_heap s x) \<bind> ran \<circ> obj_fields = Option.set_option (sys_heap s' x) \<bind> ran \<circ> obj_fields")
  apply (subst eq_impD[OF mut_m.reachable_eq_imp])
   defer
   apply (subst eq_impD[OF grey_eq_imp])
    defer
    apply (subst eq_impD[OF reaches_eq_imp])
     defer
     apply force
    apply clarsimp
    apply (rename_tac x)
    apply (drule_tac x=x in spec)
    apply (clarsimp simp: set_eq_iff ran_def)
    apply (case_tac "sys_heap s x", simp_all)[1]
    apply (metis (hide_lams, no_types) elem_set not_Some_eq option.inject map_option_eq_Some)
   apply (clarsimp split: obj_at_splits)
   apply (rule conjI)
    apply (metis map_option_is_None)
   apply (metis map_option_eq_Some)
  apply clarsimp
 apply clarsimp
apply clarsimp
done

lemmas valid_refs_inv_fun_upd[simp] = eq_imp_fun_upd[OF valid_refs_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma valid_refs_invD[elim]:
  "\<lbrakk> x \<in> mut_m.mut_roots m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> x \<in> mut_m.mut_roots m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s y = Some obj"
  "\<lbrakk> x \<in> mut_m.tso_write_refs m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> x \<in> mut_m.tso_write_refs m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s y = Some obj"
  "\<lbrakk> w \<in> set (sys_mem_write_buffers (mutator m) s); x \<in> write_refs w; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> w \<in> set (sys_mem_write_buffers (mutator m) s); x \<in> write_refs w; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s y = Some obj"
  "\<lbrakk> grey x s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> mut_m.reachable m x s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref x s"
  "\<lbrakk> mut_m.reachable m x s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s x = Some obj"
  "\<lbrakk> x \<in> mut_m.mut_ghost_honorary_root m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> x \<in> mut_m.mut_ghost_honorary_root m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s y = Some obj"
by (fastforce simp: valid_refs_inv_def grey_reachable_def mut_m.reachable_def mut_m.tso_write_refs_def
             split: obj_at_splits)+

lemma valid_refs_invD2[elim]:
  "\<lbrakk> mut_m.reachable m x s;  valid_refs_inv s; (x reaches y) s \<rbrakk> \<Longrightarrow> valid_ref y s"
apply (clarsimp simp: valid_refs_inv_def mut_m.reachable_def)
apply (frule (1) rtranclp_trans)
apply auto
done

lemma valid_refs_invD3:
  "\<lbrakk> sys_mem_write_buffers (mutator m) s = mw_Mutate r f opt_r' # ws; (r reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
apply (clarsimp simp: valid_refs_inv_def mut_m.reachable_def mut_m.tso_write_refs_def)
apply (fastforce dest: spec[where x=y] spec[where x=m])
done

text{* WL *}

lemma WLI[intro]:
  "r \<in> W (s p) \<Longrightarrow> r \<in> WL p s"
  "r \<in> ghost_honorary_grey (s p) \<Longrightarrow> r \<in> WL p s"
by (simp_all add: WL_def)

lemma WL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (ghost_honorary_grey (s p), W (s p)))
          (WL p)"
by (clarsimp simp: eq_imp_def WL_def)

lemmas WL_fun_upd[simp] = eq_imp_fun_upd[OF WL_eq_imp, simplified eq_imp_simps, rule_format]

lemma greyI[intro]:
  "r \<in> ghost_honorary_grey (s p) \<Longrightarrow> grey r s"
  "r \<in> W (s p) \<Longrightarrow> grey r s"
  "r \<in> WL p s \<Longrightarrow> grey r s"
by (case_tac [!] p) (auto simp: grey_def WL_def)

text{* @{const "valid_W_inv"} *}

lemma valid_W_inv_eq_imp:
  "eq_imp (\<lambda>(p, r). (\<lambda>s. W (s p)) \<otimes> (\<lambda>s. ghost_honorary_grey (s p)) \<otimes> sys_fM \<otimes> (\<lambda>s. Option.map_option obj_mark (sys_heap s r)) \<otimes> sys_mem_lock \<otimes> tso_pending_mark p)
          valid_W_inv"
apply (clarsimp simp: eq_imp_def valid_W_inv_def fun_eq_iff all_conj_distrib)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>p. WL p s = WL p s'")
 apply (subgoal_tac "\<forall>x. obj_at (\<lambda>obj. obj_mark obj = sys_fM s') x s \<longleftrightarrow> obj_at (\<lambda>obj. obj_mark obj = sys_fM s') x s'")
  apply (subgoal_tac "\<forall>x. obj_at (\<lambda>obj. obj_mark obj = (\<not>sys_fM s')) x s \<longleftrightarrow> obj_at (\<lambda>obj. obj_mark obj = (\<not>sys_fM s')) x s'")
   apply (subgoal_tac "\<forall>x xa xb. mw_Mark xa xb \<in> set (sys_mem_write_buffers x s) \<longleftrightarrow> mw_Mark xa xb \<in> set (sys_mem_write_buffers x s')")
    apply simp
   apply clarsimp
   apply (rename_tac x xa xb)
   apply (drule_tac x=x in spec, drule arg_cong[where f=set], fastforce)
  apply (clarsimp split: obj_at_splits)
  apply (rename_tac x)
  apply ( (drule_tac x=x in spec)+ )[1]
  apply (case_tac "sys_heap s x", simp_all)
   apply (case_tac "sys_heap s' x", auto)[1]
 apply (clarsimp split: obj_at_splits)
 apply (rename_tac x)
 apply (drule_tac x=x in spec)
 apply (case_tac "sys_heap s x", simp_all)
 apply (case_tac "sys_heap s' x", simp_all)
apply (simp add: WL_def)
done

lemmas valid_W_inv_fun_upd[simp] = eq_imp_fun_upd[OF valid_W_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma valid_W_invD[dest]:
  "\<lbrakk> r \<in> W (s p); valid_W_inv s \<rbrakk> \<Longrightarrow> marked r s"
  "\<lbrakk> r \<in> W (s p); valid_W_inv s \<rbrakk> \<Longrightarrow> valid_ref r s"
  "\<lbrakk> r \<in> WL p s;  valid_W_inv s; p \<noteq> q \<rbrakk> \<Longrightarrow> r \<notin> WL q s"
  "\<lbrakk> r \<in> W (s p); valid_W_inv s; p \<noteq> q \<rbrakk> \<Longrightarrow> r \<notin> WL q s"
  "\<lbrakk> r \<in> W (s p); valid_W_inv s \<rbrakk> \<Longrightarrow> r \<notin> ghost_honorary_grey (s q)"
  "\<lbrakk> r \<in> ghost_honorary_grey (s p); valid_W_inv s \<rbrakk> \<Longrightarrow> r \<notin> W (s q)"
  "\<lbrakk> r \<in> ghost_honorary_grey (s p); valid_W_inv s; p \<noteq> q \<rbrakk> \<Longrightarrow> r \<notin> WL q s"
by (auto simp: valid_W_inv_def WL_def split: obj_at_splits)

(* FIXME horrible but effective (?) *)
lemma valid_W_invD2[dest]:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mark r fl # ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = []"
  "\<lbrakk> mw_Mark r fl \<in> set (sys_mem_write_buffers p s); valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark (sys_mem_write_buffers p s) = [mw_Mark r fl]"
by (clarsimp simp: valid_W_inv_def dest!: spec[where x=p], blast)+

lemma valid_W_invD3[elim]:
  "\<lbrakk> mw_Mark r fl \<in> set (sys_mem_write_buffers p s); valid_W_inv s \<rbrakk> \<Longrightarrow> r \<in> ghost_honorary_grey (s p)"
  "\<lbrakk> r \<in> ghost_honorary_grey (s p); sys_mem_lock s \<noteq> Some p; valid_W_inv s \<rbrakk> \<Longrightarrow> marked r s"
  "\<lbrakk> r \<in> ghost_honorary_grey (s p); sys_mem_lock s \<noteq> Some p; valid_W_inv s \<rbrakk> \<Longrightarrow> valid_ref r s"
apply (simp_all add: valid_W_inv_def)
apply (clarsimp split: obj_at_splits)
apply blast
done

lemma valid_W_invD4:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mutate r' f r'' # ws; mw_Mark r fl \<in> set ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = [mw_Mark r fl]"
  "\<lbrakk> sys_mem_write_buffers p s = mw_fA fl' # ws; mw_Mark r fl \<in> set ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = [mw_Mark r fl]"
  "\<lbrakk> sys_mem_write_buffers p s = mw_fM fl' # ws; mw_Mark r fl \<in> set ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = [mw_Mark r fl]"
  "\<lbrakk> sys_mem_write_buffers p s = mw_Phase ph # ws; mw_Mark r fl \<in> set ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = [mw_Mark r fl]"
by (clarsimp simp: valid_W_inv_def dest!: spec[where x=p], blast)+

lemma valid_W_iff[iff]:
  "valid_W_inv s \<Longrightarrow> sys_ghost_honorary_grey s = {}"
by (simp add: valid_W_inv_def)

lemma valid_W_inv_no_mark_writes_invD:
  "\<lbrakk> sys_mem_lock s \<noteq> Some p; valid_W_inv s \<rbrakk>
     \<Longrightarrow> tso_pending p is_mw_Mark s = []"
by (auto intro!: filter_False)

lemma valid_W_inv_sys_read[simp]:
  "\<lbrakk> sys_mem_lock s \<noteq> Some p; valid_W_inv s \<rbrakk>
     \<Longrightarrow> sys_read p (mr_Mark r) (s sys) = mv_Mark (Option.map_option obj_mark (sys_heap s r))"
using assms
apply (clarsimp simp: sys_read_def fold_writes_def)
apply (rule fold_invariant[where P="\<lambda>fr. Option.map_option obj_mark (heap (fr (s sys)) r) = Option.map_option obj_mark (sys_heap s r)"
                             and Q="\<lambda>w. \<forall>r fl. w \<noteq> mw_Mark r fl"])
  apply (auto simp: Option.map_option_case do_write_action_def filter_empty_conv
             split: mem_write_action.splits option.splits)
done

(*>*)
subsection{* Mark Object *}

text{*

Local invariants for @{const "mark_object_fn"}. Invoking this code in
phases where @{const "sys_fM"} is constant marks the reference in
@{const "ref"}. When @{const "sys_fM"} could vary this code is not
called. The two cases are distinguished by @{term "p_ph_enabled"}.

Each use needs to provide extra facts to justify validity of
references, etc.  We do not include a post-condition for @{const
"mark_object_fn"} here as it is different at each call site.

*}

locale mark_object =
  fixes p :: "'mut process_name"
  fixes l :: "location"
  fixes p_ph_enabled :: "('field, 'mut, 'ref) lsts_pred"
  assumes p_ph_enabled_eq_imp: "eq_imp (\<lambda>(_::unit) s. s p) p_ph_enabled"
begin

abbreviation (input) "p_cas_mark s \<equiv> cas_mark (s p)"
abbreviation (input) "p_mark s \<equiv> mark (s p)"
abbreviation (input) "p_fM s \<equiv> fM (s p)"
abbreviation (input) "p_ghost_handshake_phase s \<equiv> ghost_handshake_phase (s p)"
abbreviation (input) "p_ghost_honorary_grey s \<equiv> ghost_honorary_grey (s p)"
abbreviation (input) "p_ghost_handshake_in_sync s \<equiv> ghost_handshake_in_sync (s p)"
abbreviation (input) "p_phase s \<equiv> phase (s p)"
abbreviation (input) "p_ref s \<equiv> ref (s p)"
abbreviation (input) "p_the_ref \<equiv> the \<circ> p_ref"
abbreviation (input) "p_W s \<equiv> W (s p)"

abbreviation at_p :: "location \<Rightarrow> ('field, 'mut, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'ref) gc_pred" where
  "at_p l' P \<equiv> at p (l @ l') imp LSTP P"

abbreviation (input) "p_en_cond P \<equiv> p_ph_enabled imp P"

abbreviation (input) "p_valid_ref \<equiv> not null p_ref and valid_ref \<triangleright> p_the_ref"
abbreviation (input) "p_tso_no_pending_mark \<equiv> list_null (tso_pending_mark p)"
abbreviation (input) "p_tso_no_pending_mutate \<equiv> list_null (tso_pending_mutate p)"

abbreviation (input)
  "p_valid_W_inv \<equiv> ((p_cas_mark neq p_mark or p_tso_no_pending_mark) imp marked \<triangleright> p_the_ref)
                and (tso_pending_mark p in (\<lambda>s. {[], [mw_Mark (p_the_ref s) (p_fM s)]}) )"

abbreviation (input)
  "p_mark_inv \<equiv> not null p_mark
            and ((\<lambda>s. obj_at (\<lambda>obj. Some (obj_mark obj) = p_mark s) (p_the_ref s) s)
              or marked \<triangleright> p_the_ref)"

abbreviation (input)
  "p_cas_mark_inv \<equiv> (\<lambda>s. obj_at (\<lambda>obj. Some (obj_mark obj) = p_cas_mark s) (p_the_ref s) s)"

abbreviation (input) "p_valid_fM \<equiv> p_fM eq sys_fM"

abbreviation (input)
  "p_ghg_eq_ref \<equiv> p_ghost_honorary_grey eq pred_singleton (the \<circ> p_ref)"
abbreviation (input)
  "p_ghg_inv \<equiv> If p_cas_mark eq p_mark Then p_ghg_eq_ref Else empty p_ghost_honorary_grey"

definition mark_object_invL :: "('field, 'mut, 'ref) gc_pred" where
  "mark_object_invL \<equiv>
      at_p ''_mo_null''        \<langle>True\<rangle>
  and at_p ''_mo_mark''        (p_valid_ref)
  and at_p ''_mo_fM''          (p_valid_ref and p_en_cond (p_mark_inv))
  and at_p ''_mo_mtest''       (p_valid_ref and p_en_cond (p_mark_inv and p_valid_fM))
  and at_p ''_mo_phase''       (p_valid_ref and p_mark neq Some \<circ> p_fM and p_en_cond (p_mark_inv and p_valid_fM))
  and at_p ''_mo_ptest''       (p_valid_ref and p_mark neq Some \<circ> p_fM and p_en_cond (p_mark_inv and p_valid_fM))

  and at_p ''_mo_co_lock''     (p_valid_ref and p_mark_inv and p_valid_fM and p_mark neq Some \<circ> p_fM and p_tso_no_pending_mark)
  and at_p ''_mo_co_cmark''    (p_valid_ref and p_mark_inv and p_valid_fM and p_mark neq Some \<circ> p_fM and p_tso_no_pending_mark)
  and at_p ''_mo_co_ctest''    (p_valid_ref and p_mark_inv and p_valid_fM and p_mark neq Some \<circ> p_fM and p_cas_mark_inv and p_tso_no_pending_mark)
  and at_p ''_mo_co_mark''     (p_cas_mark eq p_mark and p_valid_ref and p_valid_fM and white \<triangleright> p_the_ref and p_tso_no_pending_mark)
  and at_p ''_mo_co_unlock''   (p_ghg_inv and p_valid_ref and p_valid_fM and p_valid_W_inv)
  and at_p ''_mo_co_won''      (p_ghg_inv and p_valid_ref and p_valid_fM and marked \<triangleright> p_the_ref and p_tso_no_pending_mutate)
  and at_p ''_mo_co_W''        (p_ghg_eq_ref and p_valid_ref and p_valid_fM and marked \<triangleright> p_the_ref and p_tso_no_pending_mutate)"
(*<*)

lemma mark_object_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s p, s\<down> p, sys_heap s\<down>, sys_fM s\<down>, sys_mem_write_buffers p s\<down>))
          mark_object_invL"
apply (clarsimp simp: eq_imp_def)
apply (rename_tac s s')
apply (cut_tac s="s\<down>" and s'="s'\<down>" in eq_impD[OF p_ph_enabled_eq_imp], simp)
apply (clarsimp simp: mark_object_invL_def obj_at_def
                cong: option.case_cong)
done

lemmas mark_object_invL_niE[nie] =
  iffD1[OF mark_object_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]
(*>*)

end (* locale mark_object *)

text{*

The uses of @{const "mark_object_fn"} in the GC and during the root
marking are straightforward.

*}
(* FIXME we'd like:

sublocale mut < get_roots: mark_object "mutator mut" "''hs_get_roots_loop''" .

but this doesn't seem to get promoted to the top-level, so we can't
use it in the other process locales.

This interpretation promotes the [inv] attribute to the top-level.

*)
interpretation gc_mark: mark_object "gc" "''mark_loop''" "\<langle>True\<rangle>"
  by standard (simp add: eq_imp_def)

lemmas gc_mark_mark_object_invL_def2[inv] = gc_mark.mark_object_invL_def[simplified]

interpretation mut_get_roots: mark_object "mutator m" "''hs_get_roots_loop''" "\<langle>True\<rangle>" for m
  by standard (simp add: eq_imp_def)

lemmas mut_get_roots_mark_object_invL_def2[inv] = mut_get_roots.mark_object_invL_def[simplified]

text{*

The most interesting cases are the two asynchronous uses of @{const
"mark_object_fn"} in the mutators: we need something that holds even
before we read the phase. In particular we need to avoid interference
by an @{const "fM"} flip.

*}

interpretation mut_store_del: mark_object "mutator m" "''store_del''" "mut_m.mut_ghost_handshake_phase m neq \<langle>hp_Idle\<rangle>" for m
  by standard (simp add: eq_imp_def)

lemmas mut_store_del_mark_object_invL_def2[inv] = mut_store_del.mark_object_invL_def[simplified]

interpretation mut_store_ins: mark_object "mutator m" "''store_ins''"  "mut_m.mut_ghost_handshake_phase m neq \<langle>hp_Idle\<rangle>" for m
  by standard (simp add: eq_imp_def)

lemmas mut_store_ins_mark_object_invL_def2[inv] = mut_store_ins.mark_object_invL_def[simplified]

(* **************************************** *)

text{*

Local invariant for the mutator's uses of @{term "mark_object"}.

*}

definition "mut_hs_get_roots_loop_locs \<equiv>
  prefixed ''hs_get_roots_loop''"
local_setup {* Cimp.locset @{thm "mut_hs_get_roots_loop_locs_def"} *}

definition "mut_hs_get_roots_loop_mo_locs \<equiv>
  prefixed ''hs_get_roots_loop_mo'' \<union> {''hs_get_roots_loop_done''}"
local_setup {* Cimp.locset @{thm "mut_hs_get_roots_loop_mo_locs_def"} *}

abbreviation "mut_async_mark_object_prefixes \<equiv> { ''store_del'', ''store_ins'' }"

definition "mut_hs_not_hp_Idle_locs \<equiv>
  \<Union>pref\<in>mut_async_mark_object_prefixes.
  \<Union>l\<in>{''mo_co_lock'', ''mo_co_cmark'', ''mo_co_ctest'', ''mo_co_mark'', ''mo_co_unlock'', ''mo_co_won'', ''mo_co_W''}. {pref @ ''_'' @ l}"
local_setup {* Cimp.locset @{thm "mut_hs_not_hp_Idle_locs_def"} *}

definition "mut_async_mo_ptest_locs \<equiv>
  \<Union>pref\<in>mut_async_mark_object_prefixes. {pref @ ''_mo_ptest''}"
local_setup {* Cimp.locset @{thm "mut_async_mo_ptest_locs_def"} *}

definition "mut_mo_ptest_locs \<equiv>
  \<Union>pref\<in>mut_async_mark_object_prefixes. {pref @ ''_mo_ptest''}"
local_setup {* Cimp.locset @{thm "mut_mo_ptest_locs_def"} *}

definition "mut_mo_valid_ref_locs \<equiv>
  prefixed ''store_del'' \<union> prefixed ''store_ins'' \<union> { ''deref_del'', ''lop_store_ins''}"
local_setup {* Cimp.locset @{thm "mut_mo_valid_ref_locs_def"} *}
(*<*)

lemma mut_hs_get_roots_loop_locs_subseteq_hs_get_roots:
  "mut_hs_get_roots_loop_locs \<subseteq> prefixed ''hs_get_roots_''"
by (auto simp: mut_hs_get_roots_loop_locs_def intro: append_prefixeqD)

lemma mut_m_ghost_handshake_phase_not_hp_Idle:
  "\<lbrakk> atS (mutator m) mut_hs_get_roots_loop_locs s; mut_m.handshake_invL m s; handshake_phase_inv s\<down> \<rbrakk>
     \<Longrightarrow> ghost_handshake_phase (s\<down> (mutator m)) \<noteq> hp_Idle"
unfolding mut_m.handshake_invL_def
apply (elim conjE)
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule mp, erule atS_mono[OF _ mut_hs_get_roots_loop_locs_subseteq_hs_get_roots])
apply (clarsimp simp: hp_step_rel_def)
done

(*>*)
text{*

This local invariant for the mutators illustrates the handshake
structure: we can rely on the insertion barrier earlier than on the
deletion barrier. Both need to be installed before @{text "get_roots"}
to ensure we preserve the strong tricolour invariant. All black
objects at that point are allocated: we need to know that the
insertion barrier is installed to preserve it. This limits when @{text
"fA"} can be set.

It is interesting to contrast the two barriers. Intuitively a mutator
can locally guarantee that it, in the relevant phases, will insert
only marked references. Less often can it be sure that the reference
it is overwriting is marked. We also need to consider writes pending
in TSO buffers.

*}

definition ghost_honorary_grey_empty_locs :: "location set" where
  "ghost_honorary_grey_empty_locs \<equiv>
     - (\<Union>pref\<in>{ ''mark_loop'', ''hs_get_roots_loop'', ''store_del'', ''store_ins'' }.
        \<Union>l\<in>{ ''mo_co_unlock'', ''mo_co_won'', ''mo_co_W'' }. {pref @ ''_'' @ l})"
local_setup {* Cimp.locset @{thm "ghost_honorary_grey_empty_locs_def"} *}

definition (in mut_m) mark_object_invL :: "('field, 'mut, 'ref) gc_pred" where
[inv]: "mark_object_invL \<equiv>
      atS_mut mut_hs_get_roots_loop_locs    (mut_refs subseteq mut_roots and (ALLS r. \<langle>r\<rangle> in mut_roots diff mut_refs imp marked r))
  and atS_mut mut_hs_get_roots_loop_mo_locs (not null mut_ref and mut_the_ref in mut_roots)
  and at_mut ''hs_get_roots_loop_done''     (marked \<triangleright> mut_the_ref)
  and at_mut ''hs_get_roots_loop_mo_ptest'' (mut_phase neq \<langle>ph_Idle\<rangle>)
  and at_mut ''hs_get_roots_done''          (ALLS r. \<langle>r\<rangle> in mut_roots imp marked r)

  and atS_mut mut_mo_valid_ref_locs         ( (not null mut_new_ref imp mut_the_new_ref in mut_roots)
                                          and (mut_tmp_ref in mut_roots) )
  and at_mut ''store_del_mo_null''          (not null mut_ref imp mut_the_ref in mut_ghost_honorary_root)
  and atS_mut (prefixed ''store_del'' - {''store_del_mo_null''}) (mut_the_ref in mut_ghost_honorary_root)
  and atS_mut (prefixed ''store_ins'')      (mut_ref eq mut_new_ref)

  and atS_mut (suffixed ''_mo_ptest'')      (mut_phase neq \<langle>ph_Idle\<rangle> imp mut_ghost_handshake_phase neq \<langle>hp_Idle\<rangle>)
  and atS_mut mut_hs_not_hp_Idle_locs       (mut_ghost_handshake_phase neq \<langle>hp_Idle\<rangle>)

  and atS_mut mut_mo_ptest_locs             (mut_phase eq \<langle>ph_Idle\<rangle> imp (mut_ghost_handshake_phase in \<langle>{hp_Idle, hp_IdleInit}\<rangle>
                                                                          or (mut_ghost_handshake_phase eq \<langle>hp_IdleMarkSweep\<rangle>
                                                                                and sys_phase eq \<langle>ph_Idle\<rangle>)))

  and atS_mut ghost_honorary_grey_empty_locs (empty mut_ghost_honorary_grey)

(* insertion barrier *)
  and at_mut ''store_ins''                  ( (mut_ghost_handshake_phase in \<langle>{hp_InitMark, hp_Mark}\<rangle>
                                            or (mut_ghost_handshake_phase eq \<langle>hp_IdleMarkSweep\<rangle> and sys_phase neq \<langle>ph_Idle\<rangle>))
                                           and not null mut_new_ref
                                           imp marked \<triangleright> mut_the_new_ref )
(* deletion barrier *)
  and atS_mut (prefixed ''store_del_mo'' \<union> {''lop_store_ins''})
                                            ( (mut_ghost_handshake_phase eq \<langle>hp_Mark\<rangle>
                                            or (mut_ghost_handshake_phase eq \<langle>hp_IdleMarkSweep\<rangle> and sys_phase neq \<langle>ph_Idle\<rangle>))
                                          and (\<lambda>s. \<forall>opt_r'. \<not>tso_pending_write (mutator m) (mw_Mutate (mut_tmp_ref s) (mut_field s) opt_r') s)
                                          imp (\<lambda>s. obj_at_field_on_heap (\<lambda>r. mut_ref s = Some r \<or> marked r s) (mut_tmp_ref s) (mut_field s) s))

  and at_mut ''lop_store_ins''              ( (mut_ghost_handshake_phase eq \<langle>hp_Mark\<rangle>
                                            or (mut_ghost_handshake_phase eq \<langle>hp_IdleMarkSweep\<rangle> and sys_phase neq \<langle>ph_Idle\<rangle>))
                                          and not null mut_ref
                                          imp marked \<triangleright> mut_the_ref )
  and atS_mut (prefixed ''store_ins'')
                                            ( (mut_ghost_handshake_phase eq \<langle>hp_Mark\<rangle>
                                            or (mut_ghost_handshake_phase eq \<langle>hp_IdleMarkSweep\<rangle> and sys_phase neq \<langle>ph_Idle\<rangle>))
                                          and (\<lambda>s. \<forall>opt_r'. \<not>tso_pending_write (mutator m) (mw_Mutate (mut_tmp_ref s) (mut_field s) opt_r') s)
                                          imp (\<lambda>s. obj_at_field_on_heap (\<lambda>r'. marked r' s) (mut_tmp_ref s) (mut_field s) s) )"
(*<*)

lemma get_roots_get_work_subseteq_ghost_honorary_grey_empty_locs:
  "hs_get_roots_locs \<union> hs_get_work_locs \<subseteq> ghost_honorary_grey_empty_locs"
by (auto simp: hs_get_roots_locs_def hs_get_work_locs_def ghost_honorary_grey_empty_locs_def)

lemma (in mut_m) mark_object_invL_eq_imp:
  "eq_imp (\<lambda>r s. (AT s (mutator m), s\<down> (mutator m), sys_heap s\<down> r, sys_fM s\<down>, sys_phase s\<down>, tso_pending_mutate (mutator m) s\<down>))
          mark_object_invL"
apply (clarsimp simp: eq_imp_def mark_object_invL_def fun_eq_iff[symmetric] obj_at_field_on_heap_def
                cong: option.case_cong)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>r. marked r s\<down> \<longleftrightarrow> marked r s'\<down>")
 apply (subgoal_tac "\<forall>r. valid_null_ref r s\<down> \<longleftrightarrow> valid_null_ref r s'\<down>")
  apply (subgoal_tac "\<forall>r f opt_r'. mw_Mutate r f opt_r' \<notin> set (sys_mem_write_buffers (mutator m) s\<down>) \<longleftrightarrow> mw_Mutate r f opt_r' \<notin> set (sys_mem_write_buffers (mutator m) s'\<down>)")
   apply (clarsimp cong: option.case_cong)
  apply (drule arg_cong[where f=set])
  apply auto[1]
 apply (clarsimp simp: obj_at_def valid_null_ref_def split: option.splits)
apply (clarsimp simp: obj_at_def valid_null_ref_def split: option.splits)
done

lemmas mut_m_mark_object_invL_niE[nie] =
  iffD1[OF mut_m.mark_object_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in mut_m) mark_object_invL[intro]:
  "\<lbrace> handshake_invL and mark_object_invL
      and mut_get_roots.mark_object_invL m
      and mut_store_del.mark_object_invL m
      and mut_store_ins.mark_object_invL m
      and LSTP (phase_rel_inv and handshake_phase_inv and phase_rel_inv and tso_writes_inv and valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> mark_object_invL \<rbrace>"
apply vcg_jackhammer

(* store_ins_mo_ptest *)
apply (elim disjE, simp_all)[1]

(* store_ins_mo_ptest *)
apply (drule handshake_phase_invD)
apply (drule phase_rel_invD)
apply (clarsimp simp: phase_rel_def)
apply (rename_tac s s' y)
apply (case_tac "sys_ghost_handshake_phase s\<down>", simp_all add: hp_step_rel_def)[1]
apply (elim disjE, auto)[1]
apply (elim disjE, auto)[1]
apply (elim disjE, auto)[1]
apply (elim disjE, auto)[1]
apply (elim disjE, auto)[1]

apply auto[1]
apply auto[1]
apply auto[1]

apply (drule handshake_phase_invD)
apply (drule phase_rel_invD)
apply (clarsimp simp: phase_rel_def)
apply (rename_tac s s' y)
apply (case_tac "sys_ghost_handshake_phase s\<down>", simp_all add: hp_step_rel_def)[1]
    apply auto[1]
   apply (elim disjE, auto)[1]
  apply (elim disjE, auto)[1]
 apply (elim disjE, auto)[1]
apply (elim disjE, auto)[1]

apply auto[1]

apply (auto dest: obj_at_field_on_heap_no_pending_writes)[1]

(* hs get roots loop done *)
apply force

(* hs get roots loop mo phase *)
apply (drule handshake_phase_invD)
apply (drule phase_rel_invD)
apply (clarsimp simp: phase_rel_def hp_step_rel_def)

(* hs get roots loop choose ref *)
apply blast

done

lemma (in mut_m') mut_mark_object_invL[intro]:
  "\<lbrace> mark_object_invL \<rbrace> mutator m'"
apply vcg_nihe
apply vcg_ni
 apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
 apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
done

lemma (in mut_m) mut_store_ins_mark_object_invL[intro]:
  "\<lbrace> mut_store_ins.mark_object_invL m and mark_object_invL and handshake_invL and tso_lock_invL
       and LSTP (handshake_phase_inv and valid_W_inv and tso_writes_inv and valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> mut_store_ins.mark_object_invL m \<rbrace>"
apply vcg_jackhammer
apply (auto dest: valid_refs_invD valid_W_inv_no_mark_writes_invD
           split: obj_at_splits)
done

lemma mut_m_not_idle_no_fM_writeD:
  "\<lbrakk> sys_mem_write_buffers p s = mw_fM fl # ws; ghost_handshake_phase (s (mutator m)) \<noteq> hp_Idle; fM_rel_inv s; handshake_phase_inv s; tso_writes_inv s; p \<noteq> sys \<rbrakk>
     \<Longrightarrow> False"
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule fM_rel_invD)
apply (fastforce simp: hp_step_rel_def fM_rel_def filter_empty_conv p_not_sys)
done

lemma (in sys) mut_store_ins_mark_object_invL[intro]:
  notes mut_m.mark_object_invL_def[inv]
  notes mut_m.tso_lock_invL_def[inv]
  notes mut_m_not_idle_no_fM_writeD[where m=m, dest!]
  notes map_option.compositionality[simp] o_def[simp]
  shows
  "\<lbrace> mut_m.tso_lock_invL m and mut_m.mark_object_invL m and mut_store_ins.mark_object_invL m
       and LSTP (fM_rel_inv and handshake_phase_inv and valid_W_inv and tso_writes_inv) \<rbrace>
     sys
   \<lbrace> mut_store_ins.mark_object_invL m \<rbrace>"
apply (vcg_ni simp: not_blocked_def)
  apply (fastforce simp: do_write_action_def
            split: mem_write_action.splits obj_at_splits)+   (* slow *)
done

lemma (in sys) mut_get_roots_mark_object_invL[intro]:
  notes mut_m.handshake_invL_def[inv]
  notes mut_m.tso_lock_invL_def[inv]
  notes map_option.compositionality[simp] o_def[simp]
  shows
  "\<lbrace> mut_m.tso_lock_invL m and mut_m.handshake_invL m and mut_get_roots.mark_object_invL m
       and LSTP (fM_rel_inv and handshake_phase_inv and valid_W_inv and tso_writes_inv) \<rbrace>
     sys
   \<lbrace> mut_get_roots.mark_object_invL m \<rbrace>"
apply (vcg_ni simp: not_blocked_def p_not_sys
             dest!: mut_m.handshake_phase_invD[where m=m])
apply (fastforce simp: do_write_action_def fM_rel_inv_def fM_rel_def hp_step_rel_def
                split: mem_write_action.splits if_splits obj_at_splits)+   (* slow *)
done

lemma (in sys) mut_store_del_mark_object_invL[intro]:
  notes mut_m.mark_object_invL_def[inv]
  notes mut_m.tso_lock_invL_def[inv]
  notes mut_m_not_idle_no_fM_writeD[where m=m, dest!]
  notes map_option.compositionality[simp] o_def[simp]
  shows
  "\<lbrace> mut_m.tso_lock_invL m and mut_m.mark_object_invL m and mut_store_del.mark_object_invL m
       and LSTP (fM_rel_inv and handshake_phase_inv and valid_W_inv and tso_writes_inv) \<rbrace>
     sys
   \<lbrace> mut_store_del.mark_object_invL m \<rbrace>"
apply (vcg_ni simp: not_blocked_def)
apply (fastforce simp: do_write_action_def
            split: mem_write_action.splits obj_at_splits)+   (* slow *)
done

lemma (in mut_m) mut_store_del_mark_object_invL[intro]:
  "\<lbrace> mut_store_del.mark_object_invL m and mark_object_invL and handshake_invL and tso_lock_invL
       and LSTP (handshake_phase_inv and valid_W_inv and tso_writes_inv and valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> mut_store_del.mark_object_invL m \<rbrace>"
apply vcg_jackhammer
apply (auto dest: valid_refs_invD valid_W_inv_no_mark_writes_invD split: obj_at_splits)
done

lemma (in mut_m) mut_get_roots_mark_object_invL[intro]:
  "\<lbrace> mut_get_roots.mark_object_invL m and mark_object_invL and handshake_invL and tso_lock_invL
       and LSTP (handshake_phase_inv and valid_W_inv and tso_writes_inv and valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> mut_get_roots.mark_object_invL m \<rbrace>"
apply vcg_jackhammer
apply (auto dest: valid_W_inv_no_mark_writes_invD split: obj_at_splits)
done

lemma (in mut_m') mut_get_roots_mark_object_invL[intro]:
  "\<lbrace> mut_get_roots.mark_object_invL m \<rbrace> mutator m'"
apply vcg_nihe
apply vcg_ni
done

lemma (in mut_m') mut_store_ins_mark_object_invL[intro]:
  "\<lbrace> mut_store_ins.mark_object_invL m \<rbrace> mutator m'"
apply vcg_nihe
apply vcg_ni
done

lemma (in mut_m') mut_store_del_mark_object_invL[intro]:
  "\<lbrace> mut_store_del.mark_object_invL m \<rbrace> mutator m'"
apply vcg_nihe
apply vcg_ni
done

lemma (in gc) mut_get_roots_mark_object_invL[intro]:
  notes mut_m.handshake_invL_def[inv]
  shows "\<lbrace> handshake_invL and mut_m.handshake_invL m and mut_get_roots.mark_object_invL m \<rbrace> gc \<lbrace> mut_get_roots.mark_object_invL m \<rbrace>"
apply vcg_nihe
apply vcg_ni
done

(*>*)
text{*

The GC's use of @{const "mark_object_fn"} is correct.

When we take grey @{const "tmp_ref"} to black, all of the objects it
points to are marked, ergo the new black does not point to white, and
so we preserve the strong tricolour invariant.

*}

definition (in gc) obj_fields_marked_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "obj_fields_marked_inv \<equiv>
     ALLS f. \<langle>f\<rangle> in (- gc_field_set) imp (\<lambda>s. obj_at_field_on_heap (\<lambda>r. marked r s) (gc_tmp_ref s) f s)"
(*<*)

lemma (in gc) obj_fields_marked_inv_eq_imp:
  "eq_imp (\<lambda>_::unit. gc_field_set \<otimes> gc_tmp_ref \<otimes> sys_heap \<otimes> sys_fM \<otimes> tso_pending_mutate gc)
          obj_fields_marked_inv"
by (clarsimp simp: eq_imp_def obj_fields_marked_inv_def obj_at_field_on_heap_def obj_at_def
             cong: option.case_cong)

lemmas gc_obj_fields_marked_inv_fun_upd[simp] = eq_imp_fun_upd[OF gc.obj_fields_marked_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma (in gc) obj_fields_marked_inv_UNIV[iff]:
  "obj_fields_marked_inv (s(gc := (s gc)\<lparr> field_set := UNIV \<rparr>))"
by (simp_all add: obj_fields_marked_inv_def)

lemma (in gc) obj_fields_marked_inv_mark_field_done[iff]:
  "\<lbrakk> obj_at_field_on_heap (\<lambda>r. marked r s) (gc_tmp_ref s) (gc_field s) s; obj_fields_marked_inv s \<rbrakk>
     \<Longrightarrow> obj_fields_marked_inv (s(gc := (s gc)\<lparr>field_set := gc_field_set s - {gc_field s}\<rparr>))"
by (force simp: obj_fields_marked_inv_def obj_at_field_on_heap_def split: option.splits obj_at_splits)
(*>*)
text{**}

definition obj_fields_marked_locs :: "location set" where
  "obj_fields_marked_locs \<equiv>
     { ''mark_loop_mark_object_loop'', ''mark_loop_mark_choose_field'', ''mark_loop_mark_deref'', ''mark_loop_mark_field_done'', ''mark_loop_blacken'' }
   \<union> prefixed ''mark_loop_mo''"
local_setup {* Cimp.locset @{thm "obj_fields_marked_locs_def"} *}

definition (in gc) obj_fields_marked_invL :: "('field, 'mut, 'ref) gc_pred" where
[inv]: "obj_fields_marked_invL \<equiv>
      atS_gc obj_fields_marked_locs       (obj_fields_marked_inv and gc_tmp_ref in gc_W)
  and atS_gc (prefixed ''mark_loop_mo'' \<union> { ''mark_loop_mark_field_done'' })
                                          (\<lambda>s. obj_at_field_on_heap (\<lambda>r. gc_ref s = Some r \<or> marked r s) (gc_tmp_ref s) (gc_field s) s)
  and atS_gc (prefixed ''mark_loop_mo'')  (ALLS y. not null gc_ref and (\<lambda>s. ((gc_the_ref s) reaches y) s) imp valid_ref y)
  and at_gc ''mark_loop_fields''          (gc_tmp_ref in gc_W)
  and at_gc ''mark_loop_mark_field_done'' (not null gc_ref imp marked \<triangleright> gc_the_ref)
  and at_gc ''mark_loop_blacken''         (empty gc_field_set)
  and atS_gc ghost_honorary_grey_empty_locs (empty gc_ghost_honorary_grey)"
(*<*)

lemma (in gc) obj_fields_marked_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) (s :: ('field, 'mut, 'ref) gc_pred_state). (AT s gc, s\<down> gc, sys_heap s\<down>, sys_fM s\<down>, sys_W s\<down>, tso_pending_mutate gc s\<down>))
          obj_fields_marked_invL"
by (clarsimp simp: eq_imp_def inv obj_at_def obj_fields_marked_inv_def obj_at_field_on_heap_def
             cong: option.case_cong)

lemmas gc_obj_fields_marked_invL_niE[nie] =
  iffD1[OF gc.obj_fields_marked_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in gc) gc_mark_mark_object_invL[intro]:
  "\<lbrace> fM_fA_invL and gc_mark.mark_object_invL and obj_fields_marked_invL and tso_lock_invL
        and LSTP valid_W_inv \<rbrace>
     gc
   \<lbrace> gc_mark.mark_object_invL \<rbrace>"
apply vcg_jackhammer
apply (auto dest: valid_W_inv_no_mark_writes_invD split: obj_at_splits)
done

lemma (in gc) obj_fields_marked_invL[intro]:
  "\<lbrace> fM_fA_invL and phase_invL and obj_fields_marked_invL and gc_mark.mark_object_invL
       and LSTP (tso_writes_inv and valid_W_inv and valid_refs_inv) \<rbrace>
     gc
   \<lbrace> obj_fields_marked_invL \<rbrace>"
apply vcg_jackhammer

(* mark_loop_mark_field_done *)
apply (rule obj_fields_marked_inv_mark_field_done, auto)[1]

(* mark_loop_mark_deref *)
apply (rename_tac s s')
apply (subgoal_tac "grey (gc_tmp_ref s\<down>) s\<down>") (* FIXME rule *)
 apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
 apply (frule valid_refs_invD, fastforce, fastforce)
 apply (rule conjI)
  apply (clarsimp split: obj_at_splits)
 apply clarsimp
 apply (rename_tac x)
 apply (subgoal_tac "(gc_tmp_ref s\<down> reaches x) s\<down>")
  apply (erule valid_refs_invD, fastforce, fastforce)
 apply (fastforce elim: converse_rtranclp_into_rtranclp[rotated]
                  simp: ran_def split: obj_at_splits)
apply blast
done

lemma (in mut_m) gc_obj_fields_marked_invL[intro]:
  notes gc.obj_fields_marked_invL_def[inv]
  notes gc.handshake_invL_def[inv]
  shows "\<lbrace> handshake_invL and gc.handshake_invL and gc.obj_fields_marked_invL and LSTP (tso_writes_inv and valid_refs_inv) \<rbrace>
           mutator m
         \<lbrace> gc.obj_fields_marked_invL \<rbrace>"
apply vcg_nihe
apply vcg_ni
(* FIXME rules *)
 apply (clarsimp simp: gc.obj_fields_marked_inv_def)
 apply (rename_tac s s' ra x)
 apply (drule_tac x=x in spec)
 apply clarsimp
 apply (erule obj_at_field_on_heapE)
  apply (subgoal_tac "grey (gc_tmp_ref s\<down>) s\<down>")
   apply (drule_tac y="gc_tmp_ref s\<down>" in valid_refs_invD(7), simp+)
   apply (clarsimp split: obj_at_splits)
  apply (erule greyI)
 apply (clarsimp split: obj_at_splits)
apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
apply vcg_ni+
done

lemma (in mut_m) gc_mark_mark_object_invL[intro]:
  "\<lbrace> gc_mark.mark_object_invL \<rbrace> mutator m"
apply vcg_nihe
apply vcg_ni
done

lemma (in sys) gc_mark_mark_object_invL[intro]:
  notes gc.tso_lock_invL_def[inv]
  notes gc.phase_invL_def[inv]
  notes gc.fM_fA_invL_def[inv]
  notes gc.handshake_invL_def[inv]
  notes map_option.compositionality[simp] o_def[simp]
  shows
  "\<lbrace> gc.fM_fA_invL and gc.handshake_invL and gc.phase_invL and gc_mark.mark_object_invL and gc.tso_lock_invL
       and LSTP (handshake_phase_inv and phase_rel_inv and valid_W_inv and tso_writes_inv) \<rbrace>
     sys
   \<lbrace> gc_mark.mark_object_invL \<rbrace>"
apply vcg_ni
apply (force dest!: valid_W_invD2
              simp: do_write_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys
             split: mem_write_action.splits if_splits)+   (* slow *)
done

(*>*)
(*<*)

end
(*>*)
