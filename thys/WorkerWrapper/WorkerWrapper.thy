(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009, Peter Gammie, peteg42 at gmail.com, commenced December 2007.
 * License: BSD
 *)

(*<*)
theory WorkerWrapper
imports HOLCF
begin
(*>*)

section{* Gill/Hutton's worker/wrapper transformation. *}

text{* Firstly, the \emph{rolling rule} as proved in
\citet{GillHutton:2009}. The theorem dates from the 1970s at the
latest -- see \citet[p210]{Stoy:1977} and \citet{Plotkin:1983}. *}

lemma rolling_rule_ltr: "fix\<cdot>(g oo f) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
proof -
  have "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    by blast -- {* reflexivity *}
  hence "g\<cdot>((f oo g)\<cdot>(fix\<cdot>(f oo g))) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    using fix_eq[where F="f oo g"] by simp -- {* computation *}
  hence "(g oo f)\<cdot>(g\<cdot>(fix\<cdot>(f oo g))) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    by simp -- {* re-associate @{term "op oo"} *}
  thus "fix\<cdot>(g oo f) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    using fix_least_less by blast -- {* induction *}
qed

lemma rolling_rule_rtl: "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> fix\<cdot>(g oo f)"
proof -
  have "fix\<cdot>(f oo g) \<sqsubseteq> f\<cdot>(fix\<cdot>(g oo f))" by (rule rolling_rule_ltr)
  hence "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> g\<cdot>(f\<cdot>(fix\<cdot>(g oo f)))"
    by (rule monofun_cfun_arg) -- {* g is monotonic *}
  thus "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> fix\<cdot>(g oo f)"
    using fix_eq[where F="g oo f"] by simp -- {* computation *}
qed

lemma rolling_rule: "fix\<cdot>(g oo f) = g\<cdot>(fix\<cdot>(f oo g))"
  by (rule antisym_less[OF rolling_rule_ltr rolling_rule_rtl])

text{* Secondly we review the basic worker/wrapper lemmas that justify
the transformation. There is a battery of them of varying strengths of
hypothesis. The proofs in \citet{GillHutton:2009} are sound. *}

lemma worker_wrapper_id:
  assumes wrap_unwrap: "wrap oo unwrap = ID"
      and comp_body: "computation = fix\<cdot>body"
  shows "computation = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
proof -
  from comp_body have "computation = fix\<cdot>(ID oo body)"
    by simp
  also from wrap_unwrap have "\<dots> = fix\<cdot>(wrap oo unwrap oo body)"
    by (simp add: assoc_oo)
  also have "\<dots> = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
    using rolling_rule[where f="unwrap oo body" and g="wrap"]
    by (simp add: assoc_oo)
  finally show ?thesis .
qed

lemma worker_wrapper_body:
  assumes wrap_unwrap: "wrap oo unwrap oo body = body"
      and comp_body: "computation = fix\<cdot>body"
  shows "computation = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
proof -
  from comp_body have "computation = fix\<cdot>(wrap oo unwrap oo body)"
    using wrap_unwrap by (simp add: assoc_oo wrap_unwrap)
  also have "\<dots> = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
    using rolling_rule[where f="unwrap oo body" and g="wrap"] by (simp add: assoc_oo)
  finally show ?thesis .
qed

lemma worker_wrapper_fix:
  assumes wrap_unwrap: "fix\<cdot>(wrap oo unwrap oo body) = fix\<cdot>body"
      and comp_body: "computation = fix\<cdot>body"
  shows "computation = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
proof -
  from comp_body have "computation = fix\<cdot>(wrap oo unwrap oo body)"
    using wrap_unwrap by (simp add: assoc_oo wrap_unwrap)
  also have "\<dots> = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
    using rolling_rule[where f="unwrap oo body" and g="wrap"] by (simp add: assoc_oo)
  finally show ?thesis .
qed

text{* Gill and Hutton's @{text "worker_wrapper_fusion"} rule is
intended to allow the transformation of @{term "(unwrap oo wrap)\<cdot>R"}
to @{term "R"} in recursive contexts, where @{term "R"} is meant to be
a self-call. Unfortunately while their proof is sound, their use of
this rule is not; see \S\ref{sec:ww-counterexample} for a counter
example. *}

lemma worker_wrapper_fusion:
  assumes wrap_unwrap: "wrap oo unwrap = ID"
      and work: "work = fix\<cdot>(unwrap oo body oo wrap)"
  shows "(unwrap oo wrap)\<cdot>work = work" (is "?lhs = ?rhs")
proof -
  have "?lhs = (unwrap oo wrap)\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
    using work by simp
  also have "\<dots> = (unwrap oo wrap)\<cdot>(fix\<cdot>(unwrap oo body oo wrap oo unwrap oo wrap))"
    using wrap_unwrap by (simp add: assoc_oo)
  also have "\<dots> = fix\<cdot>(unwrap oo wrap oo unwrap oo body oo wrap)"
    using rolling_rule[where f="unwrap oo body oo wrap" and g="unwrap oo wrap"]
    by (simp add: assoc_oo)
  also have "\<dots> = fix\<cdot>(unwrap oo body oo wrap)"
    using wrap_unwrap by (simp add: assoc_oo)
  finally show ?thesis using work by simp
qed

(*<*)
end
(*>*)
