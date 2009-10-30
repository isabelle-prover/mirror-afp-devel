(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

(*<*)
theory LFPFusion
imports HOLCF
begin
(*>*)

section{* Least-fixed-point fusion *}

text{*\label{sec:lfp-fusion}*}

text{* We make use of @{text "lfp-fusion"} as stated by
\citet{FokkingaMeijer:1991} (later re-packaged as
\citet*{barbed-wire:1991}, which cites earlier statements of this
lemma). The earliest reference I have is \citet[p215]{Stoy:1977}, and
the following proof is close to his third variant. This lemma forms a
cornerstone for the program transformation system PATH of
\citet{Tullsen:PhDThesis}.

*}

lemma lfp_fusion:
  assumes fgh: "g oo f = h oo g"
      and strictg: "g\<cdot>\<bottom> = \<bottom>"
  shows "g\<cdot>(fix\<cdot>f) = fix\<cdot>h"
proof-
  let ?P = "\<lambda>xy. g\<cdot>(cfst\<cdot>xy) = csnd\<cdot>xy"
  let ?F = "\<Lambda> xy. \<langle>f\<cdot>(cfst\<cdot>xy), h\<cdot>(csnd\<cdot>xy)\<rangle>"
  have "?P (fix\<cdot>?F)"
  proof(induct rule: fix_ind)
    case 2 with strictg show ?case by simp
    case (3 x)
    hence "g\<cdot>(cfst\<cdot>x) = csnd\<cdot>x" .
    hence "h\<cdot>(g\<cdot>(cfst\<cdot>x)) = h\<cdot>(csnd\<cdot>x)" by simp
    with fgh have "g\<cdot>(f\<cdot>(cfst\<cdot>x)) = h\<cdot>(csnd\<cdot>x)"
      using cfcomp2[where f="g" and g="f", symmetric] by simp
    thus ?case by simp
  qed simp
  thus ?thesis
    using fix_cprod[where F="?F"] by (simp add: eta_cfun)
qed

text {* Some may find the pointed version easier to read. *}

lemma lfp_fusion_pointed:
  assumes Cfg: "\<And>f. C\<cdot>(F\<cdot>f) = G\<cdot>(C\<cdot>f)"
      and strictC: "C\<cdot>\<bottom> = \<bottom>"
  shows "C\<cdot>(fix\<cdot>F) = fix\<cdot>G"
  using lfp_fusion[where f=F and g=C and h=G] prems by (simp add: cfcomp1)

(*<*)
end
(*>*)
