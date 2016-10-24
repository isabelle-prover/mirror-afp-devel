(*<*)
theory Nitpick
imports
  Choice_Functions
begin

(*>*)

text\<open>

 Nitpick: find counterexamples to IRC + bilateral/unilateral
  substitutes does not imply their SARP.

  \citet[\S6.3]{AygunSonmez:2012-WP}: can nitpick find these
  counterexamples? -- what are these? want to show that unilateral
  substitutes + lad does not imply irc, and moreover the COP can fail
  to yield an allocation. See top of \S\ref{sec:cop-rh}.

  demonstrate Theorem~11 does not hold without LAD. See MwC p925,
  bottom left.

\<close>

(*
converse of lad_on_substitutes_on_irc_on:

lemma
  assumes "f_range_on A f"
  assumes "substitutes_on A f"
  assumes "irc_on A f"
  shows "lad_on A f"
oops
(*
nitpick
Nitpick found a counterexample for card 'a = 3:

  Free variables:
    A = {a\<^sub>1, a\<^sub>2, a\<^sub>3}
    f = (\<lambda>x. _)({} := {}, {a\<^sub>1} := {a\<^sub>1}, {a\<^sub>1, a\<^sub>2} := {a\<^sub>2}, {a\<^sub>1, a\<^sub>2, a\<^sub>3} := {a\<^sub>2}, {a\<^sub>1, a\<^sub>3} := {a\<^sub>1, a\<^sub>3}, {a\<^sub>2} := {a\<^sub>2}, {a\<^sub>2, a\<^sub>3} := {a\<^sub>2}, {a\<^sub>3} := {a\<^sub>3})
  Skolem constants:
    ??.lad_on.B = {a\<^sub>1, a\<^sub>2, a\<^sub>3}
    ??.lad_on.C = {a\<^sub>1, a\<^sub>3}
*)
*)

context Contracts
begin

text\<open>

Apropos HatfieldMilgrom without IRC:

We run out of steam on the following two lemmas, which are the
remaining requirements for stability.

FIXME nitpick's counterexamples are interesting (I think). Considering
the properties separately yields two trivial examples, whereas the one
presented in the literature is relatively complex.

\<close>

lemma
  assumes "stable_pair_on ds XD_XH"
  shows "individually_rational_on ds (match XD_XH)"
oops
(*
nitpick
Nitpick found a counterexample for card 'd = 1, card 'h = 1, and card 'x = 2:

  Free variables:
    Ch = (\<lambda>x. _)(h\<^sub>1 := (\<lambda>x. _)({} := {}, {x\<^sub>1} := {}, {x\<^sub>1, x\<^sub>2} := {x\<^sub>1}, {x\<^sub>2} := {}))
    Pd = (\<lambda>x. _)(d\<^sub>1 := {(x\<^sub>1, x\<^sub>1), (x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>2)})
    XD_XH = ({x\<^sub>1}, {x\<^sub>1, x\<^sub>2})
    Xd = (\<lambda>x. _)(x\<^sub>1 := d\<^sub>1, x\<^sub>2 := d\<^sub>1)
    Xh = (\<lambda>x. _)(x\<^sub>1 := h\<^sub>1, x\<^sub>2 := h\<^sub>1)
    ds = {d\<^sub>1}
*)

lemma
  assumes "stable_pair_on ds XD_XH"
  shows "stable_no_blocking (match XD_XH)"
oops
(*
nitpick
Nitpick found a counterexample for card 'd = 2, card 'h = 2, and card 'x = 1:

  Free variables:
    Ch = (\<lambda>x. _)(h\<^sub>1 := (\<lambda>x. _)({} := {}, {x\<^sub>1} := {}), h\<^sub>2 := (\<lambda>x. _)({} := {}, {x\<^sub>1} := {x\<^sub>1}))
    Pd = (\<lambda>x. _)(d\<^sub>1 := {}, d\<^sub>2 := {(x\<^sub>1, x\<^sub>1)})
    XD_XH = ({x\<^sub>1}, {})
    Xd = (\<lambda>x. _)(x\<^sub>1 := d\<^sub>2)
    Xh = (\<lambda>x. _)(x\<^sub>1 := h\<^sub>2)
    ds = {}
  Skolem constants:
    ??.stable_no_blocking_on.X'' = {x\<^sub>1}
    ??.stable_no_blocking_on.h = h\<^sub>2
*)

text\<open>

\citet{HatfieldMilgrom:2005} also claim that the converse holds:

\<close>

lemma
  assumes "stable_on ds X"
  obtains XD_XH where "stable_pair_on ds XD_XH" and "X = match XD_XH"
oops
(*
nitpick
Nitpick found a counterexample for card 'd = 1, card 'h = 1, and card 'x = 2:

  Free variables:
    Ch = (\<lambda>x. _)(h\<^sub>1 := (\<lambda>x. _)({} := {}, {x\<^sub>1} := {}, {x\<^sub>1, x\<^sub>2} := {x\<^sub>2}, {x\<^sub>2} := {}))
    Pd = (\<lambda>x. _)(d\<^sub>1 := {(x\<^sub>1, x\<^sub>1), (x\<^sub>2, x\<^sub>1), (x\<^sub>2, x\<^sub>2)})
    X = {}
    Xd = (\<lambda>x. _)(x\<^sub>1 := d\<^sub>1, x\<^sub>2 := d\<^sub>1)
    Xh = (\<lambda>x. _)(x\<^sub>1 := h\<^sub>1, x\<^sub>2 := h\<^sub>1)
    ds = {d\<^sub>1}
    thesis = False

FIXME nitpick's example is opaque. We want to know that no XD, XH
work. I guess we're not going to get much help with that. See below
for what I did: prove that no XD, XH work.

irc fails here.

*)



context ContractsWithSubstitutesAndLAD
begin

lemma (in ContractsWithSubstitutesAndIRC) Theorem_9_counterexample:
  assumes "stable_on ds Y"
  assumes "stable_on ds Z"
  shows "card (Ch h Y) = card (Ch h Z)"
oops
(*
nitpick[timeout=12000, card 'c=1]
Nitpick found a counterexample for card 'a = 3, card 'b = 2, and card 'c = 1:

  Free variables:
    Ch = (\<lambda>x. _)(c\<^sub>1 := (\<lambda>x. _)({} := {}, {a\<^sub>1} := {a\<^sub>1}, {a\<^sub>1, a\<^sub>2} := {a\<^sub>1}, {a\<^sub>1, a\<^sub>2, a\<^sub>3} := {a\<^sub>1}, {a\<^sub>1, a\<^sub>3} := {a\<^sub>1}, {a\<^sub>2} := {a\<^sub>2}, {a\<^sub>2, a\<^sub>3} := {a\<^sub>2, a\<^sub>3}, {a\<^sub>3} := {a\<^sub>3}))
    Pd = (\<lambda>x. _)(b\<^sub>1 := {(a\<^sub>1, a\<^sub>1), (a\<^sub>1, a\<^sub>2), (a\<^sub>2, a\<^sub>2)}, b\<^sub>2 := {(a\<^sub>3, a\<^sub>3)})
    Xd = (\<lambda>x. _)(a\<^sub>1 := b\<^sub>1, a\<^sub>2 := b\<^sub>1, a\<^sub>3 := b\<^sub>2)
    Xh = (\<lambda>x. _)(a\<^sub>1 := c\<^sub>1, a\<^sub>2 := c\<^sub>1, a\<^sub>3 := c\<^sub>1)
    Y = {a\<^sub>1}
    Z = {a\<^sub>2, a\<^sub>3}
    ds = {b\<^sub>1, b\<^sub>2}
    h = c\<^sub>1
*)

end

(* COP *)

locale ContractsWithBilateralSubstitutes = Contracts +
  assumes Ch_bilateral_substitutes: "\<forall>h. bilateral_substitutes (Ch h)"

(*
begin

FIXME the game here is to get nitpick to produce a suitable
counterexample (and not mechanize theirs).

theorem Theorem_1:
  shows "stable_on ds (CH (fp_cop_F ds))"
oops
(*
nitpick

Nitpick found a counterexample for card 'd = 2, card 'h = 2, and card 'x = 2:

  Free variables:
    Ch = (\<lambda>x. _)(h\<^sub>1 := (\<lambda>x. _)({} := {}, {x\<^sub>1} := {}, {x\<^sub>1, x\<^sub>2} := {}, {x\<^sub>2} := {x\<^sub>2}), h\<^sub>2 := (\<lambda>x. _)({} := {}, {x\<^sub>1} := {}, {x\<^sub>1, x\<^sub>2} := {}, {x\<^sub>2} := {}))
    Pd = (\<lambda>x. _)(d\<^sub>1 := {(x\<^sub>2, x\<^sub>2)}, d\<^sub>2 := {(x\<^sub>1, x\<^sub>1)})
    Xd = (\<lambda>x. _)(x\<^sub>1 := d\<^sub>2, x\<^sub>2 := d\<^sub>1)
    Xh = (\<lambda>x. _)(x\<^sub>1 := h\<^sub>1, x\<^sub>2 := h\<^sub>1)
    ds = {d\<^sub>1, d\<^sub>2}
  Skolem constants:
    ??.Ball.x = x\<^sub>1
    ??.Ball.x = x\<^sub>1
    ??.stable_no_blocking_on.X'' = {x\<^sub>2}
    ??.stable_no_blocking_on.h = h\<^sub>1
*)

end
*)

text\<open>

\label{sec:cop-opposition-of-interests}

FIXME

Lemma~1: opposition of interests, but not symmetric. Their proof
depends on hospital preferences. As we don't have these use revealed
preference instead. They say it works for general preferences; nitpick
disagrees, though it probably does work if there is an underlying linear
order. See Sonmez et al. They don't prove this one though.

The ordering for dpref follow the Isabelle convention: larger
on the right. Note weakly.

\<close>

context Contracts
begin

definition dpref :: "'x set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "dpref X Y = (\<forall>x\<in>X. \<exists>y\<in>Y. (x, y) \<in> Pd (Xd x))"

lemmas %invisible dprefI = iffD2[OF dpref_def, rule_format]

lemma Lemma_1:
  assumes "stable_on ds Y"
  assumes "stable_on ds Z"
  assumes "dpref Z Y"
  assumes "x \<in> Ch h Z"
  shows "x \<in> Ch h (Y \<union> Z)"
oops
(*
nitpick
Nitpick found a counterexample for card 'd = 1, card 'h = 1, and card 'x = 2:

  Free variables:
    Ch = (\<lambda>x. _)(h\<^sub>1 := (\<lambda>x. _)({} := {}, {x\<^sub>1} := {x\<^sub>1}, {x\<^sub>1, x\<^sub>2} := {}, {x\<^sub>2} := {x\<^sub>2}))
    Pd = (\<lambda>x. _)(d\<^sub>1 := {(x\<^sub>1, x\<^sub>1), (x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>2)})
    Xd = (\<lambda>x. _)(x\<^sub>1 := d\<^sub>1, x\<^sub>2 := d\<^sub>1)
    Xh = (\<lambda>x. _)(x\<^sub>1 := h\<^sub>1, x\<^sub>2 := h\<^sub>1)
    Y = {x\<^sub>2}
    Z = {x\<^sub>1}
    ds = {d\<^sub>1}
    h = h\<^sub>1
    x = x\<^sub>1
*)

(*<*)

end
(*>*)
