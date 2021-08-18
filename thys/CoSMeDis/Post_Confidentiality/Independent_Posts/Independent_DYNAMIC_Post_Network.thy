theory Independent_DYNAMIC_Post_Network
  imports
    "Independent_DYNAMIC_Post_ISSUER"
    "Independent_Post_RECEIVER"
    "../../API_Network"
    "BD_Security_Compositional.Composing_Security_Network"
begin

subsubsection \<open>Confidentiality for the N-ary composition\<close>

type_synonym ttrans = "(state, act, out) trans"
type_synonym obs = Post_Observation_Setup_ISSUER.obs
type_synonym "value" = "Post.value + Post_RECEIVER.value"

lemma value_cases:
fixes v :: "value"
obtains (PVal) pst where "v = Inl (Post.PVal pst)"
      | (PValS) aid pst where "v = Inl (Post.PValS aid pst)"
      | (OVal) ov where "v = Inl (Post.OVal ov)"
      | (PValR) pst where "v = Inr (Post_RECEIVER.PValR pst)"
proof (cases v)
  case (Inl vl) then show thesis using PVal PValS OVal by (cases vl rule: Post.value.exhaust) auto next
  case (Inr vr) then show thesis using PValR by (cases vr rule: Post_RECEIVER.value.exhaust) auto
qed

locale Post_Network = Network
+ fixes UIDs :: "apiID \<Rightarrow> userID set"
  and AID :: "apiID" and PID :: "postID"
  assumes AID_in_AIDs: "AID \<in> AIDs"
begin

sublocale Iss: Post "UIDs AID" PID .

abbreviation \<phi> :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool"
where "\<phi> aid trn \<equiv> (if aid = AID then Iss.\<phi> trn else Post_RECEIVER.\<phi> PID AID trn)"

abbreviation f :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> value"
where "f aid trn \<equiv> (if aid = AID then Inl (Iss.f trn) else Inr (Post_RECEIVER.f PID AID trn))"

abbreviation \<gamma> :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool"
where "\<gamma> aid trn \<equiv> (if aid = AID then Iss.\<gamma> trn else Strong_ObservationSetup_RECEIVER.\<gamma> (UIDs aid) trn)"

abbreviation g :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> obs"
where "g aid trn \<equiv> (if aid = AID then Iss.g trn else Strong_ObservationSetup_RECEIVER.g PID AID trn)"

abbreviation T :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool"
where "T aid trn \<equiv> (if aid = AID then Iss.T trn else Post_RECEIVER.T (UIDs aid) PID AID trn)"

abbreviation B :: "apiID \<Rightarrow> value list \<Rightarrow> value list \<Rightarrow> bool"
where "B aid vl vl1 \<equiv>
  (if aid = AID then list_all isl vl \<and> list_all isl vl1 \<and> Iss.B (map projl vl) (map projl vl1)
   else list_all (Not o isl) vl \<and> list_all (Not o isl) vl1 \<and> Post_RECEIVER.B (map projr vl) (map projr vl1))"

fun comOfV :: "apiID \<Rightarrow> value \<Rightarrow> com" where
  "comOfV aid (Inl (Post.PValS aid' pst)) = (if aid' \<noteq> aid then Send else Internal)"
| "comOfV aid (Inl (Post.PVal pst)) = Internal"
| "comOfV aid (Inl (Post.OVal ov)) = Internal"
| "comOfV aid (Inr v) = Recv"

fun tgtNodeOfV :: "apiID \<Rightarrow> value \<Rightarrow> apiID" where
  "tgtNodeOfV aid (Inl (Post.PValS aid' pst)) = aid'"
| "tgtNodeOfV aid (Inl (Post.PVal pst)) = undefined"
| "tgtNodeOfV aid (Inl (Post.OVal ov)) = undefined"
| "tgtNodeOfV aid (Inr v) = AID"

definition syncV :: "apiID \<Rightarrow> value \<Rightarrow> apiID \<Rightarrow> value \<Rightarrow> bool" where
  "syncV aid1 v1 aid2 v2 =
    (\<exists>pst. aid1 = AID \<and> v1 = Inl (Post.PValS aid2 pst) \<and> v2 = Inr (Post_RECEIVER.PValR pst))"

lemma syncVI: "syncV AID (Inl (Post.PValS aid' pst)) aid' (Inr (Post_RECEIVER.PValR pst))"
unfolding syncV_def by auto

lemma syncVE:
assumes "syncV aid1 v1 aid2 v2"
obtains pst where "aid1 = AID" "v1 = Inl (Post.PValS aid2 pst)" "v2 = Inr (Post_RECEIVER.PValR pst)"
using assms unfolding syncV_def by auto

fun getTgtV where
  "getTgtV (Inl (Post.PValS aid pst)) = Inr (Post_RECEIVER.PValR pst)"
| "getTgtV v = v"

lemma comOfV_AID:
  "comOfV AID v = Send \<longleftrightarrow> isl v \<and> Iss.isPValS (projl v) \<and> Iss.tgtAPI (projl v) \<noteq> AID"
  "comOfV AID v = Recv \<longleftrightarrow> Not (isl v)"
by (cases v rule: value_cases; auto)+

lemmas \<phi>_defs = Post_RECEIVER.\<phi>_def2 Iss.\<phi>_def3

sublocale Net: BD_Security_TS_Network_getTgtV
where istate = "\<lambda>_. istate" and validTrans = validTrans and srcOf = "\<lambda>_. srcOf" and tgtOf = "\<lambda>_. tgtOf"
  and nodes = AIDs and comOf = comOf and tgtNodeOf = tgtNodeOf
  and sync = sync and \<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
  and comOfV = comOfV and tgtNodeOfV = tgtNodeOfV and syncV = syncV
  and comOfO = comOfO and tgtNodeOfO = tgtNodeOfO and syncO = syncO (*and cmpO = cmpO*)
  and source = AID and getTgtV = getTgtV
using AID_in_AIDs proof (unfold_locales, goal_cases)
  case (1 nid trn) then show ?case using Iss.validTrans_isCOMact_open[of trn] by (cases trn rule: Iss.\<phi>.cases) (auto simp: \<phi>_defs split: prod.splits) next
  case (2 nid trn) then show ?case using Iss.validTrans_isCOMact_open[of trn] by (cases trn rule: Iss.\<phi>.cases) (auto simp: \<phi>_defs split: prod.splits) next
  case (3 nid trn)
    interpret Sink: Post_RECEIVER "UIDs nid" PID AID .
    show ?case using 3 by (cases "(nid,trn)" rule: tgtNodeOf.cases) (auto split: prod.splits)
next
  case (4 nid trn)
    interpret Sink: Post_RECEIVER "UIDs nid" PID AID .
    show ?case using 4 by (cases "(nid,trn)" rule: tgtNodeOf.cases) (auto split: prod.splits)
next
  case (5 nid1 trn1 nid2 trn2)
    interpret Sink1: Post_RECEIVER "UIDs nid1" PID AID .
    interpret Sink2: Post_RECEIVER "UIDs nid2" PID AID .
    show ?case using 5 by (elim sync_cases) (auto intro: syncVI)
next
  case (6 nid1 trn1 nid2 trn2)
    interpret Sink1: Post_RECEIVER "UIDs nid1" PID AID .
    interpret Sink2: Post_RECEIVER "UIDs nid2" PID AID .
    show ?case using 6 by (elim sync_cases) auto
next
  case (7 nid1 trn1 nid2 trn2)
    interpret Sink1: Post_RECEIVER "UIDs nid1" PID AID .
    interpret Sink2: Post_RECEIVER "UIDs nid2" PID AID .
    show ?case using 7(2,4,6-10)
      using Iss.validTrans_isCOMact_open[OF 7(2)] Iss.validTrans_isCOMact_open[OF 7(4)]
      by (elim sync_cases) (auto split: prod.splits, auto simp: sendPost_def)
next
  case (8 nid1 trn1 nid2 trn2)
    interpret Sink1: Post_RECEIVER "UIDs nid1" PID AID .
    interpret Sink2: Post_RECEIVER "UIDs nid2" PID AID .
    show ?case using 8(2,4,6-10,11,12,13)
      apply (elim syncO_cases; cases trn1; cases trn2)
          apply (auto simp: Iss.g_simps Strong_ObservationSetup_RECEIVER.g_simps split: prod.splits)
      apply (auto simp: sendPost_def split: prod.splits elim: syncVE)[]
      done
next
  case (9 nid trn)
    then show ?case
      by (cases "(nid,trn)" rule: tgtNodeOf.cases)
         (auto simp: Strong_ObservationSetup_RECEIVER.\<gamma>.simps)
next
  case (10 nid trn) then show ?case by (cases trn) (auto simp: \<phi>_defs)
next
  case (11 vSrc nid vn) then show ?case by (cases vSrc rule: value_cases) (auto simp: syncV_def)
next
  case (12 vSrc nid vn) then show ?case by (cases vSrc rule: value_cases) (auto simp: syncV_def)
qed

lemma list_all_Not_isl_projectSrcV: "list_all (Not o isl) (Net.projectSrcV aid vlSrc)"
proof (induction vlSrc)
  case (Cons vSrc vlSrc') then show ?case by (cases vSrc rule: value_cases) auto
qed auto

context
fixes AID' :: apiID
assumes AID': "AID' \<in> AIDs - {AID}"
begin

interpretation Recv: Post_RECEIVER "UIDs AID'" PID AID by unfold_locales

lemma Iss_BC_BO_tgtAPI:
shows "(Iss.BC vl vl1 \<longrightarrow> map Iss.tgtAPI (filter Iss.isPValS vl) =
                          map Iss.tgtAPI (filter Iss.isPValS vl1)) \<and>
       (Iss.BO vl vl1 \<longrightarrow> map Iss.tgtAPI (filter Iss.isPValS vl) =
                          map Iss.tgtAPI (filter Iss.isPValS vl1))"
by (induction rule: Iss.BC_BO.induct) auto

lemma Iss_B_Recv_B_aux:
assumes "list_all isl vl"
and "list_all isl vl1"
and "map Iss.tgtAPI (filter Iss.isPValS (map projl vl)) =
     map Iss.tgtAPI (filter Iss.isPValS (map projl vl1))"
shows "length (map projr (Net.projectSrcV AID' vl)) = length (map projr (Net.projectSrcV AID' vl1))"
using assms proof (induction vl vl1 rule: list22_induct)
  case (ConsCons v vl v1 vl1)
    consider (SendSend) aid pst pst1 where "v = Inl (Iss.PValS aid pst)" "v1 = Inl (Iss.PValS aid pst1)"
           | (Internal) "comOfV AID v = Internal" "\<not>Iss.isPValS (projl v)"
           | (Internal1) "comOfV AID v1 = Internal" "\<not>Iss.isPValS (projl v1)"
      using ConsCons(4-6) by (cases v rule: value_cases; cases v1 rule: value_cases) auto
    then show ?case proof cases
      case (SendSend) then show ?thesis using ConsCons.IH(1) ConsCons.prems by auto
    next
      case (Internal) then show ?thesis using ConsCons.IH(2)[of "v1 # vl1"] ConsCons.prems by auto
    next
      case (Internal1) then show ?thesis using ConsCons.IH(3)[of "v # vl"] ConsCons.prems by auto
    qed
qed (auto simp: comOfV_AID)

lemma Iss_B_Recv_B:
assumes "B AID vl vl1"
shows "Recv.B (map projr (Net.projectSrcV AID' vl)) (map projr (Net.projectSrcV AID' vl1))"
using assms Iss_B_Recv_B_aux Iss_BC_BO_tgtAPI by (auto simp: Iss.B_def Recv.B_def)

end

lemma map_projl_Inl: "map (projl o Inl) vl = vl"
by (induction vl) auto

lemma these_map_Inl_projl: "list_all isl vl \<Longrightarrow> these (map (Some o Inl o projl) vl) = vl"
by (induction vl) auto

lemma map_projr_Inr: "map (projr o Inr) vl = vl"
by (induction vl) auto

lemma these_map_Inr_projr: "list_all (Not o isl) vl \<Longrightarrow> these (map (Some o Inr o projr) vl) = vl"
by (induction vl) auto

sublocale BD_Security_TS_Network_Preserve_Source_Security_getTgtV
where istate = "\<lambda>_. istate" and validTrans = validTrans and srcOf = "\<lambda>_. srcOf" and tgtOf = "\<lambda>_. tgtOf"
  and nodes = AIDs and comOf = comOf and tgtNodeOf = tgtNodeOf
  and sync = sync and \<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
  and comOfV = comOfV and tgtNodeOfV = tgtNodeOfV and syncV = syncV
  and comOfO = comOfO and tgtNodeOfO = tgtNodeOfO and syncO = syncO (*and cmpO = cmpO*)
  and source = AID and getTgtV = getTgtV
proof (unfold_locales, goal_cases)
  case 1 show ?case using AID_in_AIDs .
next
  case 2
    interpret Iss': BD_Security_TS_Trans
      istate System_Specification.validTrans srcOf tgtOf Iss.\<phi> Iss.f Iss.\<gamma> Iss.g Iss.T Iss.B
      istate System_Specification.validTrans srcOf tgtOf Iss.\<phi> "\<lambda>trn. Inl (Iss.f trn)" Iss.\<gamma> Iss.g Iss.T "B AID"
      id id Some "Some o Inl"
    proof (unfold_locales, goal_cases)
      case (11 vl' vl1' tr) then show ?case
        by (intro exI[of _ "map projl vl1'"]) (auto simp: map_projl_Inl these_map_Inl_projl)
    qed auto
    show ?case using Iss.secure Iss'.translate_secure by auto
next
  case (3 aid tr vl' vl1)
    then show ?case
      using Iss_B_Recv_B[of aid "(Net.lV AID tr)" vl1] list_all_Not_isl_projectSrcV
      by auto
qed

theorem secure: "secure"
proof (intro preserve_source_secure ballI)
  fix aid
  assume aid: "aid \<in> AIDs - {AID}"
  interpret Node: Post_RECEIVER "UIDs aid" PID AID .
  interpret Node': BD_Security_TS_Trans
    istate System_Specification.validTrans srcOf tgtOf Node.\<phi> Node.f Node.\<gamma> Node.g Node.T Node.B
    istate System_Specification.validTrans srcOf tgtOf Node.\<phi> "\<lambda>trn. Inr (Node.f trn)" Node.\<gamma> Node.g Node.T "B aid"
    id id Some "Some o Inr"
  proof (unfold_locales, goal_cases)
    case (11 vl' vl1' tr) then show ?case using aid
      by (intro exI[of _ "map projr vl1'"]) (auto simp: map_projr_Inr these_map_Inr_projr)
  qed auto
  show "Net.lsecure aid"
    using aid Node.Post_secure Node'.translate_secure by auto
qed

end  (* context Post_Network *)

end
