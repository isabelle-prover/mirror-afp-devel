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

theory Handshakes
imports
  TSO
begin

(*>*)
subsection{* Handshake phases *}

text{*

The mutators can be at most one step behind the garbage collector (and
system). If any mutator is behind then the GC is stalled on a pending
handshake. Unfortunately this is a complicated by needing to consider
the handshake type due to @{text "get_work"}. This relation is very
precise.

*}

definition hp_step_rel :: "(bool \<times> handshake_type \<times> handshake_phase \<times> handshake_phase) set" where
  "hp_step_rel \<equiv>
  { True }  \<times> ({ (ht_NOOP, hp, hp) |hp. hp \<in> {hp_Idle, hp_IdleInit, hp_InitMark, hp_Mark} }
            \<union> { (ht_GetRoots, hp_IdleMarkSweep, hp_IdleMarkSweep)
              , (ht_GetWork,  hp_IdleMarkSweep, hp_IdleMarkSweep) })
\<union> { False } \<times> { (ht_NOOP,     hp_Idle,          hp_IdleMarkSweep)
              , (ht_NOOP,     hp_IdleInit,      hp_Idle)
              , (ht_NOOP,     hp_InitMark,      hp_IdleInit)
              , (ht_NOOP,     hp_Mark,          hp_InitMark)
              , (ht_GetRoots, hp_IdleMarkSweep, hp_Mark)
              , (ht_GetWork,  hp_IdleMarkSweep, hp_IdleMarkSweep) }"

definition handshake_phase_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "handshake_phase_inv \<equiv> ALLS m.
      (sys_ghost_handshake_in_sync m \<otimes> sys_handshake_type
        \<otimes> sys_ghost_handshake_phase \<otimes> mut_m.mut_ghost_handshake_phase m) in \<langle>hp_step_rel\<rangle>
  and (sys_handshake_pending m imp not sys_ghost_handshake_in_sync m)"
(*<*)

(* Sanity *)
lemma handshake_step_inv:
  "hp' = handshake_step hp \<Longrightarrow> \<exists>in' ht. (in', ht, hp', hp) \<in> hp_step_rel"
by (cases hp) (auto simp: hp_step_rel_def)

(* Sanity *)
lemma handshake_step_invD:
  "(False, ht, hp', hp) \<in> hp_step_rel \<Longrightarrow> hp' = hp_step ht hp"
by (cases ht) (auto simp: hp_step_rel_def)

lemma (in mut_m) handshake_phase_invD:
  "handshake_phase_inv s \<Longrightarrow> (sys_ghost_handshake_in_sync m s, sys_handshake_type s, sys_ghost_handshake_phase s, mut_ghost_handshake_phase s) \<in> hp_step_rel
                          \<and> (sys_handshake_pending m s \<longrightarrow> \<not>sys_ghost_handshake_in_sync m s)"
by (simp add: handshake_phase_inv_def)

lemma handshake_in_syncD:
  "\<lbrakk> All (ghost_handshake_in_sync (s sys)); handshake_phase_inv s \<rbrakk>
     \<Longrightarrow> \<forall>m'. mut_m.mut_ghost_handshake_phase m' s = sys_ghost_handshake_phase s"
by clarsimp (auto simp: hp_step_rel_def dest!: mut_m.handshake_phase_invD)

lemma (in sys) handshake_phase_inv[intro]:
  "\<lbrace> LSTP handshake_phase_inv \<rbrace> sys"
by (vcg_jackhammer simp: handshake_phase_inv_def)

(*>*)
text{*

Connect @{const "sys_ghost_handshake_phase"} with locations in the GC.

*}

definition "hp_Idle_locs \<equiv>
  (prefixed ''idle_noop'' - { ''idle_noop_mfence'', ''idle_noop_init_type'' })
\<union> { ''idle_read_fM'', ''idle_invert_fM'', ''idle_write_fM'', ''idle_flip_noop_mfence'', ''idle_flip_noop_init_type'' }"
local_setup {* Cimp.locset @{thm "hp_Idle_locs_def"} *}

definition "hp_IdleInit_locs \<equiv>
    (prefixed ''idle_flip_noop'' - { ''idle_flip_noop_mfence'', ''idle_flip_noop_init_type'' })
  \<union> { ''idle_phase_init'', ''init_noop_mfence'', ''init_noop_init_type'' }"
local_setup {* Cimp.locset @{thm "hp_IdleInit_locs_def"} *}

definition "hp_InitMark_locs \<equiv>
  (prefixed ''init_noop'' - { ''init_noop_mfence'', ''init_noop_init_type'' })
\<union> { ''init_phase_mark'', ''mark_read_fM'', ''mark_write_fA'', ''mark_noop_mfence'', ''mark_noop_init_type'' }"
local_setup {* Cimp.locset @{thm "hp_InitMark_locs_def"} *}

definition "hp_IdleMarkSweep_locs \<equiv>
     { ''idle_noop_mfence'', ''idle_noop_init_type'', ''mark_end'' }
  \<union>  sweep_locs
  \<union> (mark_loop_locs - { ''mark_loop_get_roots_init_type'' })"
local_setup {* Cimp.locset @{thm "hp_IdleMarkSweep_locs_def"} *}

definition "hp_Mark_locs \<equiv>
    (prefixed ''mark_noop'' - { ''mark_noop_mfence'', ''mark_noop_init_type'' })
  \<union> { ''mark_loop_get_roots_init_type'' }"
local_setup {* Cimp.locset @{thm "hp_Mark_locs_def"} *}

abbreviation
  "hs_noop_prefixes \<equiv> {''idle_noop'', ''idle_flip_noop'', ''init_noop'', ''mark_noop'' }"

definition "hs_noop_locs \<equiv>
  \<Union>l \<in> hs_noop_prefixes. prefixed l - (suffixed ''_noop_mfence'' \<union> suffixed ''_noop_init_type'')"
local_setup {* Cimp.locset @{thm "hs_noop_locs_def"} *}

definition "hs_get_roots_locs \<equiv>
  prefixed ''mark_loop_get_roots'' - {''mark_loop_get_roots_init_type''}"
local_setup {* Cimp.locset @{thm "hs_get_roots_locs_def"} *}

definition "hs_get_work_locs \<equiv>
  prefixed ''mark_loop_get_work'' - {''mark_loop_get_work_init_type''}"
local_setup {* Cimp.locset @{thm "hs_get_work_locs_def"} *}

abbreviation "hs_prefixes \<equiv>
  hs_noop_prefixes \<union> { ''mark_loop_get_roots'', ''mark_loop_get_work'' }"

definition "hs_init_loop_locs \<equiv> \<Union>l \<in> hs_prefixes. prefixed (l @ ''_init_loop'')"
local_setup {* Cimp.locset @{thm "hs_init_loop_locs_def"} *}

definition "hs_done_loop_locs \<equiv> \<Union>l \<in> hs_prefixes. prefixed (l @ ''_done_loop'')"
local_setup {* Cimp.locset @{thm "hs_done_loop_locs_def"} *}

definition "hs_done_locs \<equiv> \<Union>l \<in> hs_prefixes. prefixed (l @ ''_done'')"
local_setup {* Cimp.locset @{thm "hs_done_locs_def"} *}

definition "hs_none_pending_locs \<equiv> - (hs_init_loop_locs \<union> hs_done_locs)"
local_setup {* Cimp.locset @{thm "hs_none_pending_locs_def"} *}

definition "hs_in_sync_locs \<equiv>
  (- ( (\<Union>l \<in> hs_prefixes. prefixed (l @ ''_init'')) \<union> hs_done_locs ))
  \<union> (\<Union>l \<in> hs_prefixes. {l @ ''_init_type''})"
local_setup {* Cimp.locset @{thm "hs_in_sync_locs_def"} *}

definition "hs_out_of_sync_locs \<equiv>
  \<Union>l \<in> hs_prefixes. {l @ ''_init_muts''}"
local_setup {* Cimp.locset @{thm "hs_out_of_sync_locs_def"} *}

definition "hs_mut_in_muts_locs \<equiv>
  \<Union>l \<in> hs_prefixes. {l @ ''_init_loop_set_pending'', l @ ''_init_loop_done''}"
local_setup {* Cimp.locset @{thm "hs_mut_in_muts_locs_def"} *}

definition "hs_init_loop_done_locs \<equiv>
  \<Union>l \<in> hs_prefixes. {l @ ''_init_loop_done''}"
local_setup {* Cimp.locset @{thm "hs_init_loop_done_locs_def"} *}

definition "hs_init_loop_not_done_locs \<equiv>
  hs_init_loop_locs - (\<Union>l \<in> hs_prefixes. {l @ ''_init_loop_done''})"
local_setup {* Cimp.locset @{thm "hs_init_loop_not_done_locs_def"} *}

definition (in gc) handshake_invL :: "('field, 'mut, 'ref) gc_pred" where
[inv]: "handshake_invL \<equiv>
      atS_gc hs_noop_locs         (sys_handshake_type eq \<langle>ht_NOOP\<rangle>)
  and atS_gc hs_get_roots_locs    (sys_handshake_type eq \<langle>ht_GetRoots\<rangle>)
  and atS_gc hs_get_work_locs     (sys_handshake_type eq \<langle>ht_GetWork\<rangle>)

  and atS_gc hs_mut_in_muts_locs      (gc_mut in gc_muts)
  and atS_gc hs_init_loop_locs        (ALLS m. not \<langle>m\<rangle> in gc_muts imp sys_handshake_pending m
                                                                  or sys_ghost_handshake_in_sync m)
  and atS_gc hs_init_loop_not_done_locs (ALLS m.   \<langle>m\<rangle> in gc_muts imp not sys_handshake_pending m
                                                                 and not sys_ghost_handshake_in_sync m)
  and atS_gc hs_init_loop_done_locs     ( (sys_handshake_pending \<triangleright> gc_mut
                                        or sys_ghost_handshake_in_sync \<triangleright> gc_mut)
                                      and (ALLS m. \<langle>m\<rangle> in gc_muts and \<langle>m\<rangle> neq gc_mut
                                                                 imp not sys_handshake_pending m
                                                                 and not sys_ghost_handshake_in_sync m) )

  and atS_gc hs_done_locs       (ALLS m. sys_handshake_pending m or sys_ghost_handshake_in_sync m)
  and atS_gc hs_done_loop_locs  (ALLS m. not \<langle>m\<rangle> in gc_muts imp not sys_handshake_pending m)
  and atS_gc hs_none_pending_locs (ALLS m. not sys_handshake_pending m)
  and atS_gc hs_in_sync_locs      (ALLS m. sys_ghost_handshake_in_sync m)
  and atS_gc hs_out_of_sync_locs  (ALLS m. not sys_handshake_pending m
                                       and not sys_ghost_handshake_in_sync m)

  and atS_gc hp_Idle_locs          (sys_ghost_handshake_phase eq \<langle>hp_Idle\<rangle>)
  and atS_gc hp_IdleInit_locs      (sys_ghost_handshake_phase eq \<langle>hp_IdleInit\<rangle>)
  and atS_gc hp_InitMark_locs      (sys_ghost_handshake_phase eq \<langle>hp_InitMark\<rangle>)
  and atS_gc hp_IdleMarkSweep_locs (sys_ghost_handshake_phase eq \<langle>hp_IdleMarkSweep\<rangle>)
  and atS_gc hp_Mark_locs          (sys_ghost_handshake_phase eq \<langle>hp_Mark\<rangle>)"
(*<*)

lemma hs_get_roots_locs_subseteq_hp_IdleMarkSweep_locs:
  "hs_get_roots_locs \<subseteq> hp_IdleMarkSweep_locs"
by (auto simp: hs_get_roots_locs_def hp_IdleMarkSweep_locs_def mark_loop_locs_def
        intro: append_prefixeqD)

lemma hs_get_work_locs_subseteq_hp_IdleMarkSweep_locs:
  "hs_get_work_locs \<subseteq> hp_IdleMarkSweep_locs"
apply (simp add: hs_get_work_locs_def hp_IdleMarkSweep_locs_def mark_loop_locs_def)
apply clarsimp
apply (drule mp)
 apply (auto intro: append_prefixeqD)[1]
apply auto
done

lemma gc_handshake_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s gc, s\<down> gc, sys_ghost_handshake_phase s\<down>, handshake_pending (s\<down> sys), ghost_handshake_in_sync (s\<down> sys), sys_handshake_type s\<down>))
          gc.handshake_invL"
by (simp add: gc.handshake_invL_def eq_imp_def)

lemmas gc_handshake_invL_niE[nie] =
  iffD1[OF gc_handshake_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in gc) handshake_invL[intro]:
  "\<lbrace> handshake_invL \<rbrace> gc"
by vcg_jackhammer_ff

lemma (in sys) gc_handshake_invL[intro]:
  notes gc.handshake_invL_def[inv]
  shows "\<lbrace> gc.handshake_invL \<rbrace> sys"
by vcg_ni

lemma (in gc) handshake_phase_inv[intro]:
  "\<lbrace> handshake_invL and LSTP handshake_phase_inv \<rbrace> gc \<lbrace> LSTP handshake_phase_inv \<rbrace>"
by (vcg_jackhammer_ff simp: handshake_phase_inv_def hp_step_rel_def)

(*>*)
text{*

Local handshake phase invariant for the mutators.

*}

definition "mut_no_pending_mutates_locs \<equiv>
    (prefixed ''hs_noop'' - { ''hs_noop'', ''hs_noop_mfence'' })
  \<union> (prefixed ''hs_get_roots'' - { ''hs_get_roots'', ''hs_get_roots_mfence'' })
  \<union> (prefixed ''hs_get_work'' - { ''hs_get_work'', ''hs_get_work_mfence'' })"
local_setup {* Cimp.locset @{thm "mut_no_pending_mutates_locs_def"} *}

definition (in mut_m) handshake_invL :: "('field, 'mut, 'ref) gc_pred" where
[inv]: "handshake_invL \<equiv>
     atS_mut (prefixed ''hs_noop_'')      (sys_handshake_type eq \<langle>ht_NOOP\<rangle> and sys_handshake_pending m)
 and atS_mut (prefixed ''hs_get_roots_'') (sys_handshake_type eq \<langle>ht_GetRoots\<rangle> and sys_handshake_pending m)
 and atS_mut (prefixed ''hs_get_work_'')  (sys_handshake_type eq \<langle>ht_GetWork\<rangle> and sys_handshake_pending m)
 and atS_mut mut_no_pending_mutates_locs  (list_null (tso_pending_mutate (mutator m)))"
(*<*)

lemma (in mut_m) handshake_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s (mutator m), s\<down> (mutator m), sys_handshake_type s\<down>, handshake_pending (s\<down> sys), mem_write_buffers (s\<down> sys) (mutator m)))
          handshake_invL"
by (simp add: eq_imp_def handshake_invL_def)

lemmas mut_m_handshake_invL_niE[nie] =
  iffD1[OF mut_m.handshake_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in mut_m) handshake_invL[intro]:
  "\<lbrace> handshake_invL \<rbrace> mutator m"
by vcg_jackhammer

lemma (in mut_m') handshake_invL[intro]:
  "\<lbrace> handshake_invL \<rbrace> mutator m'"
apply vcg_nihe
apply vcg_ni+
done

lemma (in gc) mut_handshake_invL[intro]:
  notes mut_m.handshake_invL_def[inv]
  shows "\<lbrace> handshake_invL and mut_m.handshake_invL m \<rbrace> gc \<lbrace> mut_m.handshake_invL m \<rbrace>"
apply vcg_nihe
apply vcg_ni+
done

lemma (in sys) mut_handshake_invL[intro]:
  notes mut_m.handshake_invL_def[inv]
  shows "\<lbrace> mut_m.handshake_invL m \<rbrace> sys"
by (vcg_ni split: if_splits)

lemma (in mut_m) gc_handshake_invL[intro]:
  notes gc.handshake_invL_def[inv]
  shows "\<lbrace> handshake_invL and gc.handshake_invL \<rbrace> mutator m \<lbrace> gc.handshake_invL \<rbrace>"
apply vcg_nihe
apply vcg_ni+
done

lemma (in mut_m) handshake_phase_inv[intro]:
  "\<lbrace> handshake_invL and LSTP handshake_phase_inv \<rbrace> mutator m \<lbrace> LSTP handshake_phase_inv \<rbrace>"
apply (vcg_jackhammer simp: handshake_phase_inv_def)
apply (auto simp: hp_step_rel_def)
done

(*>*)
text{*

Relate @{const "sys_ghost_handshake_phase"}, @{const "gc_phase"},
@{const "sys_phase"} and writes to the phase in the GC's TSO buffer.

The first relation treats the case when the GC's TSO buffer does not
contain any writes to the phase.

The second relation exhibits the data race on the phase variable: we
need to precisely track the possible states of the GC's TSO buffer.

*}

definition handshake_phase_rel :: "handshake_phase \<Rightarrow> bool \<Rightarrow> gc_phase \<Rightarrow> bool" where
  "handshake_phase_rel hp in_sync ph \<equiv>
     case hp of
       hp_Idle          \<Rightarrow> ph = ph_Idle
     | hp_IdleInit      \<Rightarrow> ph = ph_Idle \<or> (in_sync \<and> ph = ph_Init)
     | hp_InitMark      \<Rightarrow> ph = ph_Init \<or> (in_sync \<and> ph = ph_Mark)
     | hp_Mark          \<Rightarrow> ph = ph_Mark
     | hp_IdleMarkSweep \<Rightarrow> ph = ph_Mark \<or> (in_sync \<and> ph \<in> { ph_Idle, ph_Sweep })"

definition phase_rel :: "(bool \<times> handshake_phase \<times> gc_phase \<times> gc_phase \<times> ('field, 'ref) mem_write_action list) set" where
  "phase_rel \<equiv>
      { (in_sync, hp, ph, ph, []) |in_sync hp ph. handshake_phase_rel hp in_sync ph }
    \<union> ({True} \<times> { (hp_IdleInit, ph_Init, ph_Idle, [mw_Phase ph_Init]),
                  (hp_InitMark, ph_Mark, ph_Init, [mw_Phase ph_Mark]),
                  (hp_IdleMarkSweep, ph_Sweep, ph_Mark, [mw_Phase ph_Sweep]),
                  (hp_IdleMarkSweep, ph_Idle, ph_Mark, [mw_Phase ph_Sweep, mw_Phase ph_Idle]),
                  (hp_IdleMarkSweep, ph_Idle, ph_Sweep, [mw_Phase ph_Idle]) })"

definition phase_rel_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "phase_rel_inv \<equiv> (ALLS m. sys_ghost_handshake_in_sync m) \<otimes> sys_ghost_handshake_phase \<otimes> gc_phase \<otimes> sys_phase \<otimes> tso_pending_phase gc in \<langle>phase_rel\<rangle>"
(*<*)

simps_of_case handshake_phase_rel_simps[simp]: handshake_phase_rel_def (splits: handshake_phase.split)

lemma phase_rel_invD:
  "phase_rel_inv s \<Longrightarrow> (\<forall>m. sys_ghost_handshake_in_sync m s, sys_ghost_handshake_phase s, gc_phase s, sys_phase s, tso_pending_phase gc s) \<in> phase_rel"
using assms by (simp add: phase_rel_inv_def)

lemma phases_rel_Id[iff]:
  "(\<forall>m. sys_ghost_handshake_in_sync m s, sys_ghost_handshake_phase s, gc_phase s, sys_phase s, tso_pending_phase gc s) \<in> phase_rel
     \<Longrightarrow> (\<forall>ph. mw_Phase ph \<notin> set (sys_mem_write_buffers gc s)) \<longleftrightarrow> sys_phase s = gc_phase s"
by (auto simp: phase_rel_def filter_empty_conv filter_eq_Cons_iff)

(*>*)
text{*

Tie the garbage collector's control location to the value of @{const
"gc_phase"}.

*}

definition no_pending_phase_locs :: "location set" where
  "no_pending_phase_locs \<equiv>
       (idle_locs - { ''idle_noop_mfence'' })
     \<union> (init_locs - { ''init_noop_mfence'' })
     \<union> (mark_locs - { ''mark_read_fM'', ''mark_write_fA'', ''mark_noop_mfence'' })"
local_setup {* Cimp.locset @{thm "no_pending_phase_locs_def"} *}

definition (in gc) phase_invL :: "('field, 'mut, 'ref) gc_pred" where
[inv]: "phase_invL \<equiv>
      atS_gc idle_locs             (gc_phase eq \<langle>ph_Idle\<rangle>)
  and atS_gc init_locs             (gc_phase eq \<langle>ph_Init\<rangle>)
  and atS_gc mark_locs             (gc_phase eq \<langle>ph_Mark\<rangle>)
  and atS_gc sweep_locs            (gc_phase eq \<langle>ph_Sweep\<rangle>)
  and atS_gc no_pending_phase_locs (list_null (tso_pending_phase gc))"
(*<*)

lemma (in gc) phase_invL_eq_imp:
  "eq_imp (\<lambda>r (s :: ('field, 'mut, 'ref) gc_pred_state). (AT s gc, s\<down> gc, tso_pending_phase gc s\<down>))
          phase_invL"
by (clarsimp simp: eq_imp_def inv)

lemmas gc_phase_invL_niE[nie] =
  iffD1[OF gc.phase_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in gc) phase_invL[intro]:
  "\<lbrace> phase_invL and LSTP phase_rel_inv \<rbrace> gc \<lbrace> phase_invL \<rbrace>"
by (vcg_jackhammer dest!: phase_rel_invD simp: phase_rel_def)

lemma (in sys) gc_phase_invL[intro]:
  notes gc.phase_invL_def[inv]
  shows "\<lbrace> gc.phase_invL and LSTP tso_writes_inv \<rbrace> sys \<lbrace> gc.phase_invL \<rbrace>"
by (vcg_ni split: if_splits)

lemma (in mut_m) gc_phase_invL[intro]:
  notes gc.phase_invL_def[inv]
  shows "\<lbrace> gc.phase_invL \<rbrace> mutator m"
by vcg_nihe

lemma (in gc) phase_rel_inv[intro]:
  notes phase_rel_inv_def[inv]
  shows "\<lbrace> handshake_invL and phase_invL and LSTP phase_rel_inv \<rbrace> gc \<lbrace> LSTP phase_rel_inv \<rbrace>"
by (vcg_jackhammer_ff dest!: phase_rel_invD simp: phase_rel_def)

lemma (in sys) phase_rel_inv[intro]:
  notes gc.phase_invL_def[inv] phase_rel_inv_def[inv]
  shows "\<lbrace> LSTP (phase_rel_inv and tso_writes_inv) \<rbrace> sys \<lbrace> LSTP phase_rel_inv \<rbrace>"
apply vcg_jackhammer
apply (simp add: phase_rel_def p_not_sys split: if_splits)
apply (elim disjE)
    apply (auto split: if_splits)
done

lemma (in mut_m) phase_rel_inv[intro]:
  "\<lbrace> handshake_invL and LSTP (handshake_phase_inv and phase_rel_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP phase_rel_inv \<rbrace>"
apply (vcg_jackhammer simp: phase_rel_inv_def)
apply (auto dest!: handshake_phase_invD
             simp: handshake_phase_rel_def phase_rel_def hp_step_rel_def
            split: handshake_phase.splits) (* takes long *)
done

(*>*)

(* **************************************** *)

text{*

Validity of @{const "sys_fM"} wrt @{const "gc_fM"} and the handshake
phase. Effectively we use @{const "gc_fM"} as ghost state. We also
include the TSO lock to rule out the GC having any pending marks
during the @{const "hp_Idle"} handshake phase.

*}

definition fM_rel :: "(bool \<times> handshake_phase \<times> gc_mark \<times> gc_mark \<times> ('field, 'ref) mem_write_action list \<times> bool) set" where
  "fM_rel =
      { (in_sync, hp, fM, fM, [], l) |fM hp in_sync l. hp = hp_Idle \<longrightarrow> \<not>in_sync }
    \<union> { (in_sync, hp_Idle, fM, fM', [], l) |fM fM' in_sync l. in_sync }
    \<union> { (in_sync, hp_Idle, \<not>fM, fM, [mw_fM (\<not>fM)], False) |fM in_sync. in_sync }"

definition fM_rel_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "fM_rel_inv \<equiv> (ALLS m. sys_ghost_handshake_in_sync m) \<otimes> sys_ghost_handshake_phase \<otimes> gc_fM \<otimes> sys_fM \<otimes> tso_pending_fM gc \<otimes> (sys_mem_lock eq \<langle>Some gc\<rangle>) in \<langle>fM_rel\<rangle>"

definition fA_rel :: "(bool \<times> handshake_phase \<times> gc_mark \<times> gc_mark \<times> ('field, 'ref) mem_write_action list) set" where
  "fA_rel =
      { (in_sync, hp_Idle,          fA,  fM, []) |fA fM in_sync. \<not>in_sync \<longrightarrow> fA = fM }
    \<union> { (in_sync, hp_IdleInit,      fA, \<not>fA, []) |fA in_sync. True }
    \<union> { (in_sync, hp_InitMark,      fA, \<not>fA, [mw_fA (\<not>fA)]) |fA in_sync. in_sync }
    \<union> { (in_sync, hp_InitMark,      fA,  fM, []) |fA fM in_sync. \<not>in_sync \<longrightarrow> fA \<noteq> fM }
    \<union> { (in_sync, hp_Mark,          fA,  fA, []) |fA in_sync. True }
    \<union> { (in_sync, hp_IdleMarkSweep, fA,  fA, []) |fA in_sync. True }"

definition fA_rel_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "fA_rel_inv \<equiv> (ALLS m. sys_ghost_handshake_in_sync m) \<otimes> sys_ghost_handshake_phase \<otimes> sys_fA \<otimes> gc_fM \<otimes> tso_pending_fA gc in \<langle>fA_rel\<rangle>"

definition fM_eq_locs :: "location set" where
  "fM_eq_locs \<equiv> (- { ''idle_write_fM'', ''idle_flip_noop_mfence'' })"
local_setup (in -) {* Cimp.locset @{thm "fM_eq_locs_def"} *}

definition fM_tso_empty_locs :: "location set" where
  "fM_tso_empty_locs \<equiv> (- { ''idle_flip_noop_mfence'' })"
local_setup (in -) {* Cimp.locset @{thm "fM_tso_empty_locs_def"} *}

definition fA_tso_empty_locs :: "location set" where
  "fA_tso_empty_locs \<equiv> (- { ''mark_noop_mfence'' })"
local_setup (in -) {* Cimp.locset @{thm "fA_tso_empty_locs_def"} *}

definition fA_eq_locs :: "location set" where
  "fA_eq_locs \<equiv> { ''idle_read_fM'', ''idle_invert_fM'' }
              \<union> prefixed ''idle_noop''
              \<union> (mark_locs - { ''mark_read_fM'', ''mark_write_fA'', ''mark_noop_mfence'' })
              \<union> sweep_locs"
local_setup {* Cimp.locset @{thm "fA_eq_locs_def"} *}

definition fA_neq_locs :: "location set" where
  "fA_neq_locs \<equiv> { ''idle_phase_init'', ''idle_write_fM'', ''mark_read_fM'', ''mark_write_fA'' }
               \<union> prefixed ''idle_flip_noop''
               \<union> init_locs"
local_setup {* Cimp.locset @{thm "fA_neq_locs_def"} *}

definition (in gc) fM_fA_invL :: "('field, 'mut, 'ref) gc_pred" where
[inv]: "fM_fA_invL \<equiv>
      atS_gc fM_eq_locs                    (sys_fM  eq gc_fM)
  and at_gc ''idle_write_fM''              (sys_fM neq gc_fM)
  and at_gc ''idle_flip_noop_mfence''      (sys_fM neq gc_fM imp (not list_null (tso_pending_fM gc)))
  and atS_gc fM_tso_empty_locs             (list_null (tso_pending_fM gc))

  and atS_gc fA_eq_locs                    (sys_fA  eq gc_fM)
  and atS_gc fA_neq_locs                   (sys_fA neq gc_fM)
  and at_gc ''mark_noop_mfence''           (sys_fA neq gc_fM imp (not list_null (tso_pending_fA gc)))
  and atS_gc fA_tso_empty_locs             (list_null (tso_pending_fA gc))"
(*<*)

lemmas fM_rel_invD = iffD1[OF fun_cong[OF fM_rel_inv_def[simplified atomize_eq]]]

lemma do_write_action_fM[simp]:
  "\<lbrakk> sys_mem_write_buffers p s = w # ws; tso_writes_inv s; handshake_phase_inv s; fM_rel_inv s;
     ghost_handshake_phase (s (mutator m)) \<noteq> hp_Idle \<or> (sys_ghost_handshake_phase s = hp_IdleMarkSweep \<and> All (ghost_handshake_in_sync (s sys)));
     p \<noteq> sys \<rbrakk>
     \<Longrightarrow> fM (do_write_action w (s sys)) = fM (s sys)"
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (clarsimp simp: do_write_action_def p_not_sys
               split: mem_write_action.splits)
apply (simp add: hp_step_rel_def)
apply (elim disjE, auto simp: fM_rel_inv_def fM_rel_def)
done

lemmas fA_rel_invD = iffD1[OF fun_cong[OF fA_rel_inv_def[simplified atomize_eq]]]

lemma gc_fM_fA_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s gc, s\<down> gc, sys_fA s\<down>, sys_fM s\<down>, sys_mem_write_buffers gc s\<down>))
          gc.fM_fA_invL"
by (simp add: gc.fM_fA_invL_def eq_imp_def)

lemmas gc_fM_fA_invL_niE[nie] =
  iffD1[OF gc_fM_fA_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in gc) fM_fA_invL[intro]:
  "\<lbrace> fM_fA_invL \<rbrace> gc"
by vcg_jackhammer

lemma (in gc) fM_rel_inv[intro]:
  "\<lbrace> fM_fA_invL and handshake_invL and tso_lock_invL and LSTP fM_rel_inv \<rbrace>
     gc
   \<lbrace> LSTP fM_rel_inv \<rbrace>"
by (vcg_jackhammer simp: fM_rel_inv_def fM_rel_def)

lemma (in gc) fA_rel_inv[intro]:
  "\<lbrace> fM_fA_invL and handshake_invL and LSTP fA_rel_inv \<rbrace>
     gc
   \<lbrace> LSTP fA_rel_inv \<rbrace>"
apply (vcg_jackhammer simp: fA_rel_inv_def)
apply (auto simp: fA_rel_def)
done (* FIXME weird *)

lemma (in mut_m) gc_fM_fA_invL[intro]:
  notes gc.fM_fA_invL_def[inv]
  shows "\<lbrace> gc.fM_fA_invL \<rbrace> mutator m"
by vcg_nihe

lemma (in mut_m) fM_rel_inv[intro]:
  "\<lbrace> LSTP fM_rel_inv \<rbrace> mutator m"
apply (vcg_jackhammer simp: fM_rel_inv_def fM_rel_def)
apply ((elim disjE, auto split: if_splits)[1])+
done (* FIXME trivial but eta reduction plays merry hell *)

lemma (in mut_m) fA_rel_inv[intro]:
  "\<lbrace> LSTP fA_rel_inv \<rbrace> mutator m"
apply (vcg_jackhammer simp: fA_rel_inv_def)
apply ((simp add: fA_rel_def, elim disjE, auto split: if_splits)[1])+
done

lemma fA_neq_locs_diff_fA_tso_empty_locs[simp]:
  "fA_neq_locs - fA_tso_empty_locs = {}"
by (simp add: fA_neq_locs_def fA_tso_empty_locs_def loc)

lemma (in sys) gc_fM_fA_invL[intro]:
  notes gc.fM_fA_invL_def[inv]
  shows
  "\<lbrace> gc.fM_fA_invL and LSTP (fA_rel_inv and fM_rel_inv and tso_writes_inv) \<rbrace>
     sys
   \<lbrace> gc.fM_fA_invL \<rbrace>"
apply (vcg_ni simp: p_not_sys)

apply (erule disjE)
 apply (clarsimp simp: fM_rel_inv_def fM_rel_def split: if_splits)
apply (clarsimp simp: fM_rel_inv_def fM_rel_def filter_empty_conv)

apply (erule disjE)
 apply clarsimp
apply clarsimp

apply (rule conjI)
 apply (clarsimp simp: fM_rel_inv_def fM_rel_def split: if_splits)
apply (clarsimp simp: fM_rel_inv_def fM_rel_def split: if_splits)

apply (clarsimp split: if_splits)

apply (erule disjE)
 apply (clarsimp simp: fA_rel_inv_def fA_rel_def)
apply clarsimp

apply (erule disjE)
 apply (clarsimp simp: fA_rel_inv_def fA_rel_def fM_rel_inv_def fM_rel_def)
 apply (drule (1) atS_dests(3), fastforce simp: atS_simps)
apply clarsimp

apply (rule conjI)
 apply (clarsimp simp: fA_rel_inv_def fA_rel_def split: if_splits)
apply clarsimp

apply (clarsimp split: if_splits)
done

lemma (in sys) fM_rel_inv[intro]:
  "\<lbrace> LSTP (fM_rel_inv and tso_writes_inv) \<rbrace> sys \<lbrace> LSTP fM_rel_inv \<rbrace>"
apply (vcg_ni simp: p_not_sys)
apply (fastforce simp: do_write_action_def fM_rel_inv_def fM_rel_def
                split: mem_write_action.splits)
done

lemma (in sys) fA_rel_inv[intro]:
  "\<lbrace> LSTP (fA_rel_inv and tso_writes_inv) \<rbrace> sys \<lbrace> LSTP fA_rel_inv \<rbrace>"
apply (vcg_ni simp: p_not_sys)
apply (fastforce simp: do_write_action_def fA_rel_inv_def fA_rel_def
                split: mem_write_action.splits)
done

lemma mut_m_get_roots_no_fM_write:
  "\<lbrakk> atS (mutator m) (prefixed ''hs_get_roots_'') s; mut_m.handshake_invL m s; handshake_phase_inv s\<down>; fM_rel_inv s\<down>; tso_writes_inv s\<down>; p \<noteq> sys \<rbrakk>
     \<Longrightarrow> \<not>sys_mem_write_buffers p s\<down> = mw_fM fl # ws"
unfolding mut_m.handshake_invL_def
apply (elim conjE)
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule fM_rel_invD)
apply (fastforce simp: hp_step_rel_def fM_rel_def loc filter_empty_conv p_not_sys)
done

lemma mut_m_get_roots_no_phase_write:
  "\<lbrakk> atS (mutator m) (prefixed ''hs_get_roots_'') s; mut_m.handshake_invL m s; handshake_phase_inv s\<down>; phase_rel_inv s\<down>; tso_writes_inv s\<down>; p \<noteq> sys \<rbrakk>
     \<Longrightarrow> \<not>sys_mem_write_buffers p s\<down> = mw_Phase ph # ws"
unfolding mut_m.handshake_invL_def
apply (elim conjE)
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule phase_rel_invD)
apply (fastforce simp: hp_step_rel_def phase_rel_def loc filter_empty_conv p_not_sys)
done

lemma mut_m_not_idle_no_fM_write:
  "\<lbrakk> ghost_handshake_phase (s (mutator m)) \<noteq> hp_Idle; fM_rel_inv s; handshake_phase_inv s; tso_writes_inv s; p \<noteq> sys \<rbrakk>
     \<Longrightarrow> \<not>sys_mem_write_buffers p s = mw_fM fl # ws"
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule fM_rel_invD)
apply (fastforce simp: hp_step_rel_def fM_rel_def filter_empty_conv p_not_sys)
done

lemma (in mut_m) mut_ghost_handshake_phase_idle:
  "\<lbrakk> mut_ghost_handshake_phase s = hp_Idle; handshake_phase_inv s; phase_rel_inv s \<rbrakk>
     \<Longrightarrow> sys_phase s = ph_Idle"
by (auto dest!: phase_rel_invD handshake_phase_invD
          simp: phase_rel_def hp_step_rel_def)
(*>*)
(*<*)

end
(*>*)
