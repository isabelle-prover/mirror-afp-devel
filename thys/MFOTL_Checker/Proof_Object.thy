(*<*)
theory Proof_Object
  imports Formula Partition
begin
(*>*)

section \<open>Proof Objects\<close>

datatype (dead 'n, dead 'd) sproof = STT nat 
  | SPred nat 'n "('n, 'd) Formula.trm list"
  | SEq_Const nat 'n 'd
  | SNeg "('n, 'd) vproof" 
  | SOrL "('n, 'd) sproof" 
  | SOrR "('n, 'd) sproof" 
  | SAnd "('n, 'd) sproof" "('n, 'd) sproof"
  | SImpL "('n, 'd) vproof" 
  | SImpR "('n, 'd) sproof"
  | SIffSS "('n, 'd) sproof" "('n, 'd) sproof" 
  | SIffVV "('n, 'd) vproof" "('n, 'd) vproof" 
  | SExists 'n 'd "('n, 'd) sproof"
  | SForall 'n "('d, ('n, 'd) sproof) part" 
  | SPrev "('n, 'd) sproof"
  | SNext "('n, 'd) sproof"
  | SOnce nat "('n, 'd) sproof"
  | SEventually nat "('n, 'd) sproof" 
  | SHistorically nat nat "('n, 'd) sproof list" 
  | SHistoricallyOut nat
  | SAlways nat nat "('n, 'd) sproof list"
  | SSince "('n, 'd) sproof" "('n, 'd) sproof list" 
  | SUntil "('n, 'd) sproof list" "('n, 'd) sproof" 
  and ('n, 'd) vproof = VFF nat 
  | VPred nat 'n "('n, 'd) Formula.trm list"
  | VEq_Const nat 'n 'd
  | VNeg "('n, 'd) sproof" 
  | VOr "('n, 'd) vproof" "('n, 'd) vproof"
  | VAndL "('n, 'd) vproof" 
  | VAndR "('n, 'd) vproof" 
  | VImp "('n, 'd) sproof" "('n, 'd) vproof" 
  | VIffSV "('n, 'd) sproof" "('n, 'd) vproof" 
  | VIffVS "('n, 'd) vproof" "('n, 'd) sproof" 
  | VExists 'n "('d, ('n, 'd) vproof) part" 
  | VForall 'n 'd "('n, 'd) vproof"
  | VPrev "('n, 'd) vproof"
  | VPrevZ
  | VPrevOutL nat 
  | VPrevOutR nat
  | VNext "('n, 'd) vproof" 
  | VNextOutL nat 
  | VNextOutR nat 
  | VOnceOut nat 
  | VOnce nat nat "('n, 'd) vproof list" 
  | VEventually nat nat "('n, 'd) vproof list"
  | VHistorically nat "('n, 'd) vproof" 
  | VAlways nat "('n, 'd) vproof"
  | VSinceOut nat
  | VSince nat "('n, 'd) vproof" "('n, 'd) vproof list" 
  | VSinceInf nat nat "('n, 'd) vproof list" 
  | VUntil nat "('n, 'd) vproof list" "('n, 'd) vproof"
  | VUntilInf nat nat "('n, 'd) vproof list"

type_synonym ('n, 'd) "proof" = "('n, 'd) sproof + ('n, 'd) vproof"

type_synonym ('n, 'd) expl = "('d, ('n, 'd) proof, 'n) pdt"

fun s_at :: "('n, 'd) sproof \<Rightarrow> nat" and 
  v_at :: "('n, 'd) vproof \<Rightarrow> nat" where
  "s_at (STT i) = i"
| "s_at (SPred i _ _) = i"
| "s_at (SEq_Const i _ _) = i"
| "s_at (SNeg vp) = v_at vp"
| "s_at (SOrL sp1) = s_at sp1"
| "s_at (SOrR sp2) = s_at sp2"
| "s_at (SAnd sp1 _) = s_at sp1"
| "s_at (SImpL vp1) = v_at vp1"
| "s_at (SImpR sp2) = s_at sp2"
| "s_at (SIffSS sp1 _) = s_at sp1"
| "s_at (SIffVV vp1 _) = v_at vp1"
| "s_at (SExists _ _ sp) = s_at sp"
| "s_at (SForall _ part) = s_at (part_hd part)"
| "s_at (SPrev sp) = s_at sp + 1"
| "s_at (SNext sp) = s_at sp - 1"
| "s_at (SOnce i _) = i"
| "s_at (SEventually i _) = i"
| "s_at (SHistorically i _ _) = i"
| "s_at (SHistoricallyOut i) = i"
| "s_at (SAlways i _ _) = i"
| "s_at (SSince sp2 sp1s) = (case sp1s of [] \<Rightarrow> s_at sp2 | _ \<Rightarrow> s_at (last sp1s))"
| "s_at (SUntil sp1s sp2) = (case sp1s of [] \<Rightarrow> s_at sp2 | sp1 # _ \<Rightarrow> s_at sp1)"
| "v_at (VFF i) = i"
| "v_at (VPred i _ _) = i"
| "v_at (VEq_Const i _ _) = i"
| "v_at (VNeg sp) = s_at sp"
| "v_at (VOr vp1 _) = v_at vp1"
| "v_at (VAndL vp1) = v_at vp1"
| "v_at (VAndR vp2) = v_at vp2"
| "v_at (VImp sp1 _) = s_at sp1"
| "v_at (VIffSV sp1 _) = s_at sp1"
| "v_at (VIffVS vp1 _) = v_at vp1"
| "v_at (VExists _ part) = v_at (part_hd part)"
| "v_at (VForall _ _ vp1) = v_at vp1"
| "v_at (VPrev vp) = v_at vp + 1"
| "v_at (VPrevZ) = 0"
| "v_at (VPrevOutL i) = i"
| "v_at (VPrevOutR i) = i"
| "v_at (VNext vp) = v_at vp - 1"
| "v_at (VNextOutL i) = i"
| "v_at (VNextOutR i) = i"
| "v_at (VOnceOut i) = i"
| "v_at (VOnce i _ _) = i"
| "v_at (VEventually i _ _) = i"
| "v_at (VHistorically i _) = i"
| "v_at (VAlways i _) = i"
| "v_at (VSinceOut i) = i"
| "v_at (VSince i _ _) = i"
| "v_at (VSinceInf i _ _) = i"
| "v_at (VUntil i _ _) = i"
| "v_at (VUntilInf i _ _) = i"

definition p_at :: "('n, 'd) proof \<Rightarrow> nat" where "p_at p = case_sum s_at v_at p" 

(*<*)
end
(*>*)
