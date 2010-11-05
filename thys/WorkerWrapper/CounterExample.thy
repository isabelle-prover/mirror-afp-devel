(*<*)
theory CounterExample

imports HOLCF WorkerWrapper

begin
(*>*)

subsection{* Unwrap needs to be strict *}

text{* \label{sec:unwrap-strict}

If @{term "unwrap"} is lazy, then it is possible that the fusion rule
proposed by Gill and Hutton does not preserve termination. To show
this we take a small artificial example. The type @{term "A"} is not
important, but we need access to a non-bottom inhabitant. The target
type @{term "B"} is the lift of @{term "A"}. *}

domain A = A
domain B = B (lazy "A")

text{* The functions @{term "wrap"} and @{term "unwrap"} are
routine. Note that @{term "wrap"} is (necessarily) strict but @{term
"unwrap"} is lazy. *}

fixrec wrap :: "B \<rightarrow> A" where
  "wrap\<cdot>(B\<cdot>a) = a"

(*<*)
lemma wrap_strict[simp]: "wrap\<cdot>\<bottom> = \<bottom>"
by fixrec_simp
(*>*)

fixrec unwrap :: "A \<rightarrow> B" where
  "unwrap = B"

lemma wrap_unwrap_ID: "wrap oo unwrap = ID"
  by (rule ext_cfun) simp

text{* Any function that uses the recursion parameter @{term "r"}
lazily will do. *}

fixrec body :: "A \<rightarrow> A" where
  "body\<cdot>r = A"

text{* The wrinkle is that the transformed worker can be strict in the
recursion parameter @{term "r"}, as @{term "unwrap"} always lifts
it. *}

fixrec body' :: "B \<rightarrow> B" where
  "body'\<cdot>(B\<cdot>a) = B\<cdot>A"

(*<*)
lemma body'_strict[simp]: "body'\<cdot>\<bottom> = \<bottom>"
by fixrec_simp
(*>*)

lemma "unwrap oo body oo wrap = body' oo unwrap oo wrap"
  by (rule ext_cfun) simp

lemma "fix\<cdot>(unwrap oo body oo wrap) = B\<cdot>A"
  by (subst fix_eq) simp

lemma "fix\<cdot>body' = \<bottom>"
  by (simp add: fix_strict)

lemma "\<not> fix\<cdot>(unwrap oo body oo wrap) \<sqsubseteq> fix\<cdot>body'"
  by (subst fix_eq) (simp add: fix_strict)

text{* This trick works whenever @{term "unwrap"} is lazy, so we need
to assume that it is strict. In that case we can show fusion is
totally correct, see \S\ref{sec:ww-fixed}. *}

subsection{* Fold/unfold does not preserve termination *}

text{*
\label{sec:ww-counterexample}

The above example shows that fusion requires a strict @{term "unwrap"}
but does not explain how this requirement slipped past Gill and
Hutton, where all the explicitly-presented proofs are correct. This
section shows a slippery example of where the Burstall/Darlington
fold/unfold framework \citep{BurstallDarlington:1977} can lead us
astray. It follows the reconstruction of that framework by
\citet{Tullsen:PhDThesis}.

Consider the following two domains, where we wish to replace recursion
at type $X$ with recursion at type $Y$ that contains extra junk,
represented by @{term "JY"}.

*}

domain X = KX
domain Y = KY | JY

text{* There isn't too much choice about how to embed @{typ "X"} into
@{typ "Y"}, but establishing the worker/wrapper condition will require
strictness. *}

definition x2y :: "X \<rightarrow> Y" where
  "x2y \<equiv> \<Lambda> x. case x of KX \<Rightarrow> KY"

(*<*)
lemma x2y_strict[simp]: "x2y\<cdot>\<bottom> = \<bottom>"
  unfolding x2y_def by simp
(*>*)

text {* Conversely we do have a choice about what @{term "JY"} in
@{typ "Y"} should map to in @{typ "X"}, as it is not in the image of
@{term "x2y"}. The example hinges on mapping it to @{term "KX"}. *}

definition y2x :: "Y \<rightarrow> X" where
  "y2x \<equiv> \<Lambda> x. case x of KY \<Rightarrow> KX | JY \<Rightarrow> KX"

(*<*)
lemma y2x_strict[simp]: "y2x\<cdot>\<bottom> = \<bottom>"
  unfolding y2x_def by simp
(*>*)

(*<*)
lemma [simp]: "y2x\<cdot>(x2y\<cdot>x) = x"
  unfolding x2y_def y2x_def by (cases x) simp_all

lemma [simp]: "x2y\<cdot>(y2x\<cdot>x) = (case x of KY \<Rightarrow> KY | JY \<Rightarrow> KY)"
  unfolding x2y_def y2x_def by (cases x) simp_all
(*>*)

text{* Next we lift our mappings to functions, and establish the
requisite identity for worker/wrapper to apply. *}

types
  C = "X \<rightarrow> X"
  D = "Y \<rightarrow> Y"

definition dc_wrap :: "D \<rightarrow> C" where
  "dc_wrap \<equiv> \<Lambda> f. y2x oo f oo x2y"

definition dc_unwrap :: "C \<rightarrow> D" where
  "dc_unwrap \<equiv> \<Lambda> f. x2y oo f oo y2x"

lemma dc_wrap_strict[simp]: "dc_wrap\<cdot>\<bottom> = \<bottom>"
  unfolding dc_wrap_def by (rule ext_cfun) simp

lemma dc_unwrap_strict[simp]: "dc_unwrap\<cdot>\<bottom> = \<bottom>"
(*<*)
  unfolding dc_unwrap_def by (rule ext_cfun) simp
(*>*)

lemma dc_wrap_dc_unwrap_ID: "dc_wrap oo dc_unwrap = ID"
(*<*)
  unfolding dc_wrap_def dc_unwrap_def by (rule ext_cfun)+ simp
(*>*)

text {* The particular candidate for worker/wrapper transformaiton is
the recursive identity function at type @{typ "C"}. *}

definition idC_body :: "C \<rightarrow> C" where
  "idC_body \<equiv> \<Lambda> r. ID"

text {* Applying the worker/wrapper transformation yields the
following term: *}

definition work_body :: "D \<rightarrow> D" where
  "work_body \<equiv> dc_unwrap oo idC_body oo dc_wrap"

definition work :: "D" where
  "work = fix\<cdot>work_body"

(*<*)
lemma [simp]: "work\<cdot>KY = KY"
  unfolding idC_body_def work_def work_body_def dc_unwrap_def
  by (subst fix_eq) simp
(*>*)

definition idww :: "C" where
  "idww = dc_wrap\<cdot>work"

lemma idww: "idww = fix\<cdot>idC_body"
  unfolding idww_def work_def work_body_def
  using worker_wrapper_id[OF dc_wrap_dc_unwrap_ID]
  by simp

text{* Critically, we can exploit the definition of @{term "y2x"} by
transforming the body of the worker into a function that uses
recursion: *}

definition dbody' :: "D \<rightarrow> D" where
  "dbody' \<equiv> \<Lambda> r x. case x of KY \<Rightarrow> KY | JY \<Rightarrow> r\<cdot>JY"

text{* To simulate the fold/unfold framework, we now consider @{term
"work"} as an explicitly recursive definition:

@{term "work = (dc_unwrap oo idC_body oo dc_wrap)\<cdot>work"}

Imagine we want to do the following rewrite:

@{term "work = (dbody' oo dc_unwrap oo dc_wrap)\<cdot>work"}

which follows by brute-force extensionality.

Then we want to apply fusion to get:

@{term "worker = dbody'\<cdot>worker"}

which is where the wheels fall off, as we show below.

To make this work we appeal to the reconstruction of
Burstall/Darlington fold/unfold by \citet[\S3.1.1]{Tullsen:PhDThesis}:
the fold rule only preserves partial correctness.

*}

lemma "fix\<cdot>dbody' \<sqsubseteq> work"
proof(rule fix_least)
  have "work = (dc_unwrap oo idC_body oo dc_wrap)\<cdot>work"
    (*<*)
    unfolding work_def work_body_def
    by (subst fix_eq) simp
    (*>*)
  also have "... = (dbody' oo dc_unwrap oo dc_wrap)\<cdot>work"
    (*<*)
    unfolding dbody'_def idC_body_def dc_wrap_def dc_unwrap_def
    by (rule ext_cfun) simp
    (*>*)
  also have "... = dbody'\<cdot>work"
    (*<*) unfolding work_def work_body_def (*>*)
    using worker_wrapper_fusion[OF dc_wrap_dc_unwrap_ID] by simp
  finally show "dbody'\<cdot>work = work" by simp
qed

text{* Without the wrap/unwrap protective armour, @{term "dbody'"} does
not terminate as often as @{term "work"} does. In general we might get
some lesser-defined object, if the domains are not flat. *}

lemma "\<not> work \<sqsubseteq> fix\<cdot>dbody'"
proof -
  have "fix\<cdot>dbody'\<cdot>JY = \<bottom>"
    (*<*) unfolding dbody'_def by (rule fix_ind) simp_all (*>*)
  moreover
  have "work\<cdot>JY = KY"
    (*<*)
    unfolding idC_body_def work_def work_body_def dc_unwrap_def
    by (subst fix_eq) simp_all
    (*>*)
  ultimately
  show ?thesis
    apply (simp add: cfun_below_iff)
    apply (rule exI[where x="JY"])
    apply simp
    done
qed

text {* The new definition is still equivalent to the old one in the
original context, though. This shows that the introduction of
divergence can be masked. *}

lemma "dc_wrap\<cdot>work = dc_wrap\<cdot>(fix\<cdot>dbody')"
  unfolding dbody'_def work_def dc_wrap_def
  apply (rule ext_cfun)
  apply (subst fix_eq)
  apply (simp add: idC_body_def work_body_def dc_unwrap_def)
  apply (subst fix_eq)
  apply (case_tac "x")
  apply (simp_all add: x2y_def y2x_def)
  done

text{* As we will see in the following sections, all uses of fusion by
\citet{GillHutton:2009} are actually sound. *}

(*<*)
end
(*>*)
