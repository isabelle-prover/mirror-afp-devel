(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section \<open>EPIC Level 1 Example instantiation of locale\<close>
text\<open>In this theory we instantiate the locale @{text "dataplane0"} and thus show that its
assumptions are satisfiable. In particular, this involves the assumptions concerning the network.
We also instantiate the locale @{text "epic_l1_defs"}.\<close>
theory EPIC_L1_SA_Example
  imports
    "EPIC_L1_SA"
begin

(*  
   A
  / \
 B   C
  \ /
   D
   |
   E
  / \
 F   G
*)

text\<open>The network topology that we define is the same as in the paper.\<close>

abbreviation nA :: as where "nA \<equiv> 3"
abbreviation nB :: as where "nB \<equiv> 4"
abbreviation nC :: as where "nC \<equiv> 5"
abbreviation nD :: as where "nD \<equiv> 6"
abbreviation nE :: as where "nE \<equiv> 7"
abbreviation nF :: as where "nF \<equiv> 8"
abbreviation nG :: as where "nG \<equiv> 9"

abbreviation bad :: "as set" where "bad \<equiv> {nF}"

text\<open>We assume a complete graph, in which interfaces contain the name of the adjacent AS\<close>
fun tgtas :: "as \<Rightarrow> ifs \<Rightarrow> as option" where
  "tgtas a i = Some i"
fun tgtif :: "as \<Rightarrow> ifs \<Rightarrow> ifs option" where
  "tgtif a i = Some a"

subsection\<open>Left segment\<close>
abbreviation hiAl :: "ahi" where "hiAl \<equiv> \<lparr>UpIF = None, DownIF = Some nB, ASID = nA\<rparr>"
abbreviation hiBl :: "ahi" where "hiBl \<equiv> \<lparr>UpIF = Some nA, DownIF = Some nD, ASID = nB\<rparr>"
abbreviation hiDl :: "ahi" where "hiDl \<equiv> \<lparr>UpIF = Some nB, DownIF = Some nE, ASID = nD\<rparr>"
abbreviation hiEl :: "ahi" where "hiEl \<equiv> \<lparr>UpIF = Some nD, DownIF = Some nF, ASID = nE\<rparr>"
abbreviation hiFl :: "ahi" where "hiFl \<equiv> \<lparr>UpIF = Some nE, DownIF = None, ASID = nF\<rparr>"

subsection\<open>Right segment\<close>
abbreviation hiAr :: "ahi" where "hiAr \<equiv> \<lparr>UpIF = None, DownIF = Some nB, ASID = nA\<rparr>"
abbreviation hiBr :: "ahi" where "hiBr \<equiv> \<lparr>UpIF = Some nA, DownIF = Some nD, ASID = nB\<rparr>"
abbreviation hiDr :: "ahi" where "hiDr \<equiv> \<lparr>UpIF = Some nB, DownIF = Some nE, ASID = nD\<rparr>"
abbreviation hiEr :: "ahi" where "hiEr \<equiv> \<lparr>UpIF = Some nD, DownIF = Some nG, ASID = nE\<rparr>"
abbreviation hiGr :: "ahi" where "hiGr \<equiv> \<lparr>UpIF = Some nE, DownIF = None, ASID = nG\<rparr>"

abbreviation hfF_attr_E :: "ahi set" where "hfF_attr_E \<equiv> {hi . ASID hi = nF \<and> UpIF hi = Some nE}"
abbreviation hfF_attr :: "ahi set" where "hfF_attr \<equiv> {hi . ASID hi = nF}"

abbreviation leftpath :: "ahi list" where 
  "leftpath \<equiv> [hiFl, hiEl, hiDl, hiBl, hiAl]"
abbreviation rightpath :: "ahi list" where 
  "rightpath \<equiv> [hiGr, hiEr, hiDr, hiBr, hiAr]"
abbreviation rightsegment where "rightsegment \<equiv> (Num 0, rightpath)"

abbreviation leftpath_wormholed :: "ahi list set" where 
  "leftpath_wormholed \<equiv> 
    { xs@[hf, hiEl, hiDl, hiBl, hiAl] | hf xs . hf \<in> hfF_attr_E \<and> set xs \<subseteq> hfF_attr}"

definition leftsegment_wormholed :: "(msgterm \<times> ahi list) set" where 
  "leftsegment_wormholed = { (Num 0, leftpath) | leftpath . leftpath \<in> leftpath_wormholed}"

definition attr_segment :: "(msgterm \<times> ahi list) set" where 
  "attr_segment = { (ainfo, path) | ainfo path . set path \<subseteq> hfF_attr}"

definition auth_seg0 :: "(msgterm \<times> ahi list) set" where 
  "auth_seg0 = leftsegment_wormholed \<union> {rightsegment} \<union> attr_segment"

lemma tgtasif_inv:
    "\<lbrakk>tgtas u i = Some v; tgtif u i = Some j\<rbrakk> \<Longrightarrow> tgtas v j = Some u"
    "\<lbrakk>tgtas u i = Some v; tgtif u i = Some j\<rbrakk> \<Longrightarrow> tgtif v j = Some i"
  by simp+

locale no_assumptions_left 
begin

sublocale d0: network_model bad auth_seg0 tgtas tgtif
  apply unfold_locales
  done

lemma attr_ifs_valid: "\<lbrakk>ASID y = nF; set ys \<subseteq> hfF_attr\<rbrakk> \<Longrightarrow> d0.ifs_valid (Some y) ys nxt"
  by(induction ys arbitrary: y)
    (auto simp add: auth_seg0_def leftsegment_wormholed_def attr_segment_def TW.holds_split_tail 
                    TW.holds.simps list.case_eq_if)

lemma attr_ifs_valid': "\<lbrakk>set ys \<subseteq> hfF_attr; pre = None\<rbrakk> \<Longrightarrow> d0.ifs_valid pre ys nxt"
  by(induction ys nxt rule: TW.holds.induct)
    (auto simp add: auth_seg0_def leftsegment_wormholed_def attr_segment_def TW.holds_split_tail 
                    TW.holds.simps list.case_eq_if dest: attr_ifs_valid)

lemma leftpath_ifs_valid: "\<lbrakk>pre = None; ASID hf = nF; UpIF hf = Some nE; set xs \<subseteq> hfF_attr\<rbrakk>
    \<Longrightarrow> d0.ifs_valid pre (xs @ [hf, hiEl, hiDl, hiBl, hiAl]) nxt"
  by(auto simp add: TW.holds_append auth_seg0_def leftsegment_wormholed_def attr_segment_def 
                    TW.holds_split_tail TW.holds.simps list.case_eq_if intro!: attr_ifs_valid')force+

lemma ASM_if_valid: "\<lbrakk>(info, l) \<in> auth_seg0; pre = None\<rbrakk> \<Longrightarrow> d0.ifs_valid pre l nxt"
  by(auto simp add: auth_seg0_def leftsegment_wormholed_def attr_segment_def TW.holds_split_tail 
                    TW.holds.simps intro: attr_ifs_valid' leftpath_ifs_valid)

(*move to parametrized model?*)
lemma rooted_app[simp]: "d0.rooted (xs@y#ys) \<longleftrightarrow> d0.rooted (y#ys)"
  by(induction xs arbitrary: y ys, auto)
    (metis Nil_is_append_conv d0.rooted.simps(2) d0.terminated.cases)+

lemma ASM_rooted: "(info, l) \<in> auth_seg0 \<Longrightarrow> d0.rooted l" 
  apply(induction l)
  apply(auto 3 4 simp add: auth_seg0_def leftsegment_wormholed_def attr_segment_def TW.holds_split_tail)
  subgoal for x xs
    by(cases xs, auto)
  done

lemma ASM_terminated: "(info, l) \<in> auth_seg0 \<Longrightarrow> d0.terminated l"
  apply(auto simp add: auth_seg0_def leftsegment_wormholed_def TW.holds_split_tail attr_segment_def)
  subgoal for hf xs
    by(induction xs, auto)
  by(induction l, auto)

lemma ASM_empty: "(info, []) \<in> auth_seg0" 
  by(auto simp add: auth_seg0_def leftsegment_wormholed_def attr_segment_def)

lemma ASM_singleton: "\<lbrakk>ASID hf \<in> bad\<rbrakk> \<Longrightarrow> (info, [hf]) \<in> auth_seg0" 
  by(auto simp add: auth_seg0_def leftsegment_wormholed_def attr_segment_def)

lemma ASM_extension: 
  "\<lbrakk>(info, hf2#ys) \<in> auth_seg0; ASID hf2 \<in> bad; ASID hf1 \<in> bad\<rbrakk> 
\<Longrightarrow> (info, hf1#hf2#ys) \<in> auth_seg0" 
  by(auto simp add: auth_seg0_def leftsegment_wormholed_def TW.holds_split_tail attr_segment_def)

lemma ASM_modify: "\<lbrakk>(info, hf#ys) \<in> auth_seg0; ASID hf = a;
      ASID hf' = a; UpIF hf' = UpIF hf; a \<in> bad\<rbrakk> \<Longrightarrow> (info, hf'#ys) \<in> auth_seg0"
  apply(auto simp add: auth_seg0_def leftsegment_wormholed_def attr_segment_def)
  subgoal for y hfa l
    by(induction l, auto)
  subgoal for y hfa l
    by(induction l, auto)
  done

lemma rightpath_no_nF: "\<lbrakk>ASID hf = nF; zs @ hf # ys = rightpath\<rbrakk> \<Longrightarrow> False"
apply(cases ys rule: rev_cases, auto)
subgoal for ys' apply(cases ys' rule: rev_cases, auto)
 subgoal for ys'' apply(cases ys'' rule: rev_cases, auto)
  subgoal for ys''' apply(cases ys''' rule: rev_cases, auto)
   subgoal for ys''' by(cases ys''' rule: rev_cases, auto)
   done
  done
 done
done

lemma ASM_cutoff_leftpath:
"\<lbrakk>ASID hf = nF; 
\<forall>hfa. UpIF hfa = Some nE \<longrightarrow> ASID hfa = nF \<longrightarrow> (\<forall>xs. hf # ys = xs @ [hfa, hiEl, hiDr, hiBr, hiAr] \<longrightarrow> 
\<not> set xs \<subseteq> hfF_attr); x \<in> set ys; info = Num 0;
        zs @ hf # ys = xs @ [hfa, hiEl, hiDr, hiBr, hiAr]; ASID hfa = nF; UpIF hfa = Some nE; set xs \<subseteq> hfF_attr\<rbrakk>
       \<Longrightarrow> ASID x = nF"
apply(cases ys rule: rev_cases, simp)
subgoal for ys' b
 apply(cases ys' rule: rev_cases, simp)
 subgoal for ys'' c
  apply(cases ys'' rule: rev_cases, simp)
  subgoal for ys''' d
   apply(cases ys'' rule: rev_cases, simp)
   subgoal for ys''' e
    apply(cases ys''' rule: rev_cases, simp)
    subgoal for ys'''' f
     apply(cases ys'''' rule: rev_cases, simp)
     by auto blast+
    done
   done
  done
 done
done

lemma ASM_cutoff: "\<lbrakk>(info, zs@hf#ys) \<in> auth_seg0; ASID hf \<in> bad\<rbrakk> \<Longrightarrow> (info, hf#ys) \<in> auth_seg0"
  apply(simp add: auth_seg0_def, auto dest: rightpath_no_nF)
  by(auto simp add: leftsegment_wormholed_def TW.holds_split_tail attr_segment_def intro: ASM_cutoff_leftpath)

sublocale network_assums_direct_instance: network_assums_direct bad tgtas tgtif auth_seg0
  apply unfold_locales
  using ASM_if_valid ASM_rooted ASM_terminated ASM_empty ASM_singleton ASM_extension ASM_modify ASM_cutoff
  by simp_all

definition no_oracle :: "msgterm \<Rightarrow> nat \<Rightarrow> bool" where 
  "no_oracle ainfo uinfo = True"

sublocale e1: epic_l1_defs bad tgtas tgtif auth_seg0 no_oracle
  by unfold_locales

declare e1.upd_uinfo_def[simp]
declare TWu.holds_takeW_is_identity[simp]
thm TWu.holds_takeW_is_identity
declare e1.auth_restrict_def [simp]
declare no_oracle_def [simp]
declare e1.upd_pkt_def [simp]

subsection\<open>Executability\<close>
subsubsection\<open>Honest sender's packet forwarding\<close>

abbreviation ainfo where "ainfo \<equiv> Num 0"
abbreviation uinfo :: nat where "uinfo \<equiv> 1"
abbreviation \<sigma>A where "\<sigma>A \<equiv> Mac[macKey nA] (L [ainfo, \<epsilon>, AS nB])"
abbreviation \<sigma>B where "\<sigma>B \<equiv> Mac[macKey nB] (L [ainfo, AS nA, AS nD, Hash \<sigma>A])"
abbreviation \<sigma>D where "\<sigma>D \<equiv> Mac[macKey nD] (L [ainfo, AS nB, AS nE, Hash \<sigma>B])"
abbreviation \<sigma>E where "\<sigma>E \<equiv> Mac[macKey nE] (L [ainfo, AS nD, AS nF, Hash \<sigma>D])"
abbreviation \<sigma>F where "\<sigma>F \<equiv> Mac[macKey nF] (L [ainfo, AS nE, \<epsilon>, Hash \<sigma>E])"

definition hfAl where "hfAl \<equiv> \<lparr>AHI = hiAl, UHI = Hash \<sigma>A, HVF = Mac[\<sigma>A] \<langle>ainfo, Num uinfo\<rangle>\<rparr>"
definition hfBl where "hfBl \<equiv> \<lparr>AHI = hiBl, UHI = Hash \<sigma>B, HVF = Mac[\<sigma>B] \<langle>ainfo, Num uinfo\<rangle>\<rparr>"
definition hfDl where "hfDl \<equiv> \<lparr>AHI = hiDl, UHI = Hash \<sigma>D, HVF = Mac[\<sigma>D] \<langle>ainfo, Num uinfo\<rangle>\<rparr>"
definition hfEl where "hfEl \<equiv> \<lparr>AHI = hiEl, UHI = Hash \<sigma>E, HVF = Mac[\<sigma>E] \<langle>ainfo, Num uinfo\<rangle>\<rparr>"
definition hfFl where "hfFl \<equiv> \<lparr>AHI = hiFl, UHI = Hash \<sigma>F, HVF = Mac[\<sigma>F] \<langle>ainfo, Num uinfo\<rangle>\<rparr>"

lemmas hfl_defs = hfAl_def hfBl_def hfDl_def hfEl_def hfFl_def

lemma "e1.hf_valid ainfo uinfo hfAl None"
  by (simp add: e1.hf_valid_invert hfAl_def)
lemma "e1.hf_valid ainfo uinfo hfBl (Some hfAl)"
  apply (auto simp add: e1.hf_valid_invert hfAl_def hfBl_def)
  using d0.ASIF.simps by blast+

lemma "e1.hf_valid ainfo uinfo hfFl (Some hfEl)"
  apply (auto intro!: exI simp add: e1.hf_valid_invert hfl_defs)
  using d0.ASIF.simps by blast+

abbreviation forwardingpath where
  "forwardingpath \<equiv> [hfFl, hfEl, hfDl, hfBl, hfAl]"

definition pkt0 where "pkt0 \<equiv> \<lparr>
                AInfo = ainfo,
                UInfo = uinfo,
                past = [],
                future = forwardingpath,
                history = []
              \<rparr>"
definition pkt1 where "pkt1 \<equiv> \<lparr>
                AInfo = ainfo,
                UInfo = uinfo,
                past = [hfFl],
                future = [hfEl, hfDl, hfBl, hfAl],
                history = [hiFl]
              \<rparr>"
definition pkt2 where "pkt2 \<equiv> \<lparr>
                AInfo = ainfo,
                UInfo = uinfo,
                past = [hfEl, hfFl],
                future = [hfDl, hfBl, hfAl],
                history = [hiEl, hiFl]
              \<rparr>"
definition pkt3 where "pkt3 \<equiv> \<lparr>
                AInfo = ainfo,
                UInfo = uinfo,
                past = [hfDl, hfEl, hfFl],
                future = [hfBl, hfAl],
                history = [hiDl, hiEl, hiFl]
              \<rparr>"
definition pkt4 where "pkt4 \<equiv> \<lparr>
                AInfo = ainfo,
                UInfo = uinfo,
                past = [hfBl, hfDl, hfEl, hfFl],
                future = [hfAl],
                history = [hiBl, hiDl, hiEl, hiFl]
              \<rparr>"
definition pkt5 where "pkt5 \<equiv> \<lparr>
                AInfo = ainfo,
                UInfo = uinfo,
                past = [hfAl, hfBl, hfDl, hfEl, hfFl],
                future = [],
                history = [hiAl, hiBl, hiDl, hiEl, hiFl]
              \<rparr>"

(*s0 -- dispatch -- s1 -- send -- s2 -- recv -- s3 ... s9 -- deliver -- s10*)
definition s0 where "s0 \<equiv> e1.dp2_init"
definition s1 where "s1 \<equiv> s0\<lparr>loc2 := (loc2 s0)(nF := {pkt0})\<rparr>"
definition s2 where 
  "s2 \<equiv> s1\<lparr>chan2 := (chan2 s1)((nF, nE, nE, nF) := chan2 s1 (nF, nE, nE, nF) \<union> {pkt1})\<rparr>"
definition s3 where "s3 \<equiv> s2\<lparr>loc2 := (loc2 s2)(nE := {pkt1})\<rparr>"
definition s4 where 
  "s4 \<equiv> s3\<lparr>chan2 := (chan2 s3)((nE, nD, nD, nE) := chan2 s3 (nE, nD, nD, nE) \<union> {pkt2})\<rparr>"
definition s5 where "s5 \<equiv> s4\<lparr>loc2 := (loc2 s4)(nD := {pkt2})\<rparr>"
definition s6 where 
  "s6 \<equiv> s5\<lparr>chan2 := (chan2 s5)((nD, nB, nB, nD) := chan2 s5 (nD, nB, nB, nD) \<union> {pkt3})\<rparr>"
definition s7 where "s7 \<equiv> s6\<lparr>loc2 := (loc2 s6)(nB := {pkt3})\<rparr>"
definition s8 where 
  "s8 \<equiv> s7\<lparr>chan2 := (chan2 s7)((nB, nA, nA, nB) := chan2 s7 (nB, nA, nA, nB) \<union> {pkt4})\<rparr>"
definition s9 where "s9 \<equiv> s8\<lparr>loc2 := (loc2 s8)(nA := {pkt4})\<rparr>"
definition s10 where "s10 \<equiv> s9\<lparr>loc2 := (loc2 s9)(nA := {pkt4, pkt5})\<rparr>"

lemmas forwading_states = 
  s0_def s1_def s2_def s3_def s4_def s5_def s6_def s7_def s8_def s9_def s10_def 

lemma forwardingpath_valid: "e1.hfs_valid_None ainfo uinfo forwardingpath"
  by(auto simp add: TWu.holds_split_tail hfl_defs)

lemma forwardingpath_auth: "pfragment ainfo forwardingpath (e1.auth_seg2 uinfo)"
  apply(auto simp add: e1.auth_seg2_def pfragment_def)
  using forwardingpath_valid
  by(auto intro!: exI[of _ "[]"] simp add: e1.hfs_valid_prefix_generic_def auth_seg0_def leftsegment_wormholed_def hfl_defs)

lemma reach_s0: "reach e1.dp2 s0" by(auto simp add: s0_def e1.dp2_def)

lemma s0_s1: "e1.dp2: s0 \<midarrow>evt_dispatch_int2 nF pkt0\<rightarrow> s1"
  using forwardingpath_auth 
  by(auto dest!: e1.dp2_dispatch_int_also_works_for_honest[where ?m = pkt0])
    (auto simp add: e1.dp2_def e1.dp2_defs e1.dp2_msgs forwading_states pkt0_def e1.dp2_init_def)

lemma s1_s2: "e1.dp2: s1 \<midarrow>evt_send2 nF nE pkt0\<rightarrow> s2"
  by (auto simp add: e1.dp2_def forwading_states e1.dp2_defs e1.dp2_msgs pkt0_def pkt1_def)
     (auto simp add: hfl_defs)

lemma s2_s3: "e1.dp2: s2 \<midarrow>evt_recv2 nE nF pkt1\<rightarrow> s3"
  by (auto simp add: e1.dp2_def forwading_states e1.dp2_defs e1.dp2_msgs pkt0_def pkt1_def)
     (auto simp add: hfl_defs)

lemma s3_s4: "e1.dp2: s3 \<midarrow>evt_send2 nE nD pkt1\<rightarrow> s4"
  by (auto simp add: e1.dp2_def forwading_states e1.dp2_defs e1.dp2_msgs pkt1_def pkt2_def)
     (auto simp add: hfl_defs)

lemma s4_s5: "e1.dp2: s4 \<midarrow>evt_recv2 nD nE pkt2\<rightarrow> s5"
  by (auto simp add: e1.dp2_def forwading_states e1.dp2_defs e1.dp2_msgs pkt1_def pkt2_def)
     (auto simp add: hfl_defs)

lemma s5_s6: "e1.dp2: s5 \<midarrow>evt_send2 nD nB pkt2\<rightarrow> s6"
  by (auto simp add: e1.dp2_def forwading_states e1.dp2_defs e1.dp2_msgs pkt3_def pkt2_def)
     (auto simp add: hfl_defs)

lemma s6_s7: "e1.dp2: s6 \<midarrow>evt_recv2 nB nD pkt3\<rightarrow> s7"
  by (auto simp add: e1.dp2_def forwading_states e1.dp2_defs e1.dp2_msgs pkt3_def pkt2_def)
     (auto simp add: hfl_defs)

lemma s7_s8: "e1.dp2: s7 \<midarrow>evt_send2 nB nA pkt3\<rightarrow> s8"
  by (auto simp add: e1.dp2_def forwading_states e1.dp2_defs e1.dp2_msgs pkt4_def pkt3_def)
     (auto simp add: hfl_defs)

lemma s8_s9: "e1.dp2: s8 \<midarrow>evt_recv2 nA nB pkt4\<rightarrow> s9"
  by (auto simp add: e1.dp2_def forwading_states e1.dp2_defs e1.dp2_msgs pkt4_def pkt3_def)
     (auto simp add: hfl_defs)

lemma s9_s10: "e1.dp2: s9 \<midarrow>evt_deliver2 nA pkt4\<rightarrow> s10"
  by (auto simp add: e1.dp2_def forwading_states e1.dp2_defs e1.dp2_msgs pkt5_def pkt4_def)
     (auto simp add: hfl_defs)

text\<open>The state in which the packet is received is reachable\<close>
lemma executability: "reach e1.dp2 s10"
  using reach_s0 s0_s1 s1_s2 s2_s3 s3_s4 s4_s5 s5_s6 s6_s7 s7_s8 s8_s9 s9_s10 
  by(auto elim!: reach_trans)

subsubsection\<open>Attacker event executability\<close>
text\<open>We also show that the attacker event can be executed.\<close>

definition pkt_attr where "pkt_attr \<equiv> \<lparr>
                AInfo = ainfo,
                UInfo = uinfo,
                past = [],
                future = [hfEl],
                history = []
              \<rparr>"

definition s_attr where 
  "s_attr \<equiv> s0\<lparr>chan2 := (chan2 s0)((nF, nE, nE, nF) := chan2 s0 (nF, nE, nE, nF) \<union> {pkt_attr})\<rparr>"

lemma ik_hfs_in_ik: "t \<in> e1.ik_hfs \<Longrightarrow> t \<in> synth (analz (e1.ik_dyn s))"
  by(auto simp add: e1.ik_dyn_def e1.ik_def)

lemma hvf_e_auth: "HVF hfEl \<in> e1.ik_hfs"
  apply(auto simp add: e1.ik_hfs_def e1.auth_seg2_def
               intro!: exI[of _ hfEl] exI[of _ "[hfFl, hfEl, hfDl, hfBl, hfAl]"] exI[of _ ainfo])
  using e1.hfs_valid_prefix_generic_def no_assumptions_left.forwardingpath_valid
  by(auto intro!: exI[of _ uinfo] simp add: auth_seg0_def leftsegment_wormholed_def hfl_defs)

lemma uhi_e_auth: "UHI hfEl \<in> e1.ik_hfs"
  apply(auto simp add: e1.ik_hfs_def e1.auth_seg2_def
               intro!: exI[of _ hfEl] exI[of _ "[hfFl, hfEl, hfDl, hfBl, hfAl]"] exI[of _ ainfo])
  using e1.hfs_valid_prefix_generic_def no_assumptions_left.forwardingpath_valid
  by(auto simp add: e1.auth_seg2_def auth_seg0_def leftsegment_wormholed_def hfl_defs)

text\<open>The attacker can also execute her event.\<close>
lemma attr_executability: "reach e1.dp2 s_attr"
proof- 
  have "e1.dp2: s0 \<midarrow>evt_dispatch_ext2 nF nE pkt_attr\<rightarrow> s_attr"
    apply (auto simp add: forwading_states e1.dp2_defs e1.dp2_msgs pkt_attr_def e1.ik_hfs_def e1.terms_pkt_def)
    using hvf_e_auth uhi_e_auth 
    by(auto dest: ik_hfs_in_ik simp add: s_attr_def s0_def e1.dp2_init_def pkt_attr_def)
  then show ?thesis using reach_s0 by auto
qed

end
end
