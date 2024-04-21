(*<*)
theory Programs
imports
  Refinement
begin

(*>*)
section\<open> A programming language\label{sec:programs} \<close>

text\<open>

The \<^typ>\<open>('a, 's, 'v) spec\<close> lattice of
\S\ref{sec:safety_logic-logic} is adequate for logic but is deficient
as a programming language. In particular we wish to interpret the
parallel composition as intersection
(\S\ref{sec:constructions-parallel_composition}) which requires
processes to contain enough interference opportunities. Similarly we
want the customary ``laws of programming''
\<^citep>\<open>"HoareEtAl:1987"\<close> to hold without side
conditions.

These points are discussed at some length by
\<^citet>\<open>\<open>\S3.2\<close> in "Zwiers:1989"\<close> and also
\<^citet>\<open>\<open>Lemma~6.7\<close> in "Foster:2020"\<close>.

Our \<open>('v, 's) prog\<close> lattice (\S\ref{sec:programs-prog})
therefore handles the common case of the familiar constructs for
sequential programming, and we lean on our \<^typ>\<open>('a, 's, 'v)
spec\<close> lattice for other constructions such as interleaving
parallel composition (\S\ref{sec:constructions-parallel_composition})
and local state (\S\ref{sec:local_state}). It allows arbitrary
interference by the environment before and after every program action.

\<close>


subsection\<open> The \<^emph>\<open>('s, 'v) prog\<close> lattice \label{sec:programs-prog} \<close>

text\<open>

According to \<^citet>\<open>\<open>\S2.1\<close> in "MuellerOlm:1997"\<close>, \<open>('s, 'v) prog\<close> is
a \<^emph>\<open>sub-lattice\<close> of \<^typ>\<open>('a, 's, 'v) spec\<close> as the corresponding \<^const>\<open>inf\<close> and \<^const>\<open>sup\<close>
operations coincide. However it is not a \<^emph>\<open>complete\<close> sub-lattice as \<^const>\<open>Sup\<close> in \<open>('s, 'v) prog\<close>
needs to account for the higher bottom of that lattice.

\<close>

typedef ('s, 'v) prog = "spec.interference.closed ({env} \<times> UNIV) :: (sequential, 's, 'v) spec set"
morphisms p2s Abs_t
by blast

hide_const (open) p2s

setup_lifting type_definition_prog

instantiation prog :: (type, type) complete_distrib_lattice
begin

lift_definition bot_prog :: "('s, 'v) prog" is "spec.interference.cl ({env} \<times> UNIV) \<bottom>" ..
lift_definition top_prog :: "('s, 'v) prog" is \<top> ..
lift_definition sup_prog :: "('s, 'v) prog \<Rightarrow> ('s, 'v) prog \<Rightarrow> ('s, 'v) prog" is sup ..
lift_definition inf_prog :: "('s, 'v) prog \<Rightarrow> ('s, 'v) prog \<Rightarrow> ('s, 'v) prog" is inf ..
lift_definition less_eq_prog :: "('s, 'v) prog \<Rightarrow> ('s, 'v) prog \<Rightarrow> bool" is less_eq .
lift_definition less_prog :: "('s, 'v) prog \<Rightarrow> ('s, 'v) prog \<Rightarrow> bool" is less .
lift_definition Inf_prog :: "('s, 'v) prog set \<Rightarrow> ('s, 'v) prog" is Inf ..
lift_definition Sup_prog :: "('s, 'v) prog set \<Rightarrow> ('s, 'v) prog" is "\<lambda>X. Sup X \<squnion> spec.interference.cl ({env} \<times> UNIV) \<bottom>" ..

instance
by standard (transfer; auto simp: Inf_lower InfI SupI le_supI1 spec.interference.least)+

end


subsection\<open> Morphisms to and from the \<^emph>\<open>(sequential, 's, 'v) spec\<close> lattice\label{sec:programs-morphisms} \<close>

text\<open>

We can readily convert a \<^typ>\<open>('s, 'v) prog\<close> into a
\<^typ>\<open>('a agent, 's, 'v) spec\<close>. More interestingly, on
\<^typ>\<open>('s, 'v) prog\<close> we have a Galois connection that
embeds specifications into programs. (This connection is termed a
\<^emph>\<open>Galois insertion\<close> by
\<^citet>\<open>"MeltonSchmidtStrecker:1985"\<close> as we also have
\<open>prog.s2p.p2s\<close>; Cousot says ``Galois retraction''.)

See also \S\ref{sec:programs-refinement-galois} and
\S\ref{sec:programs-ag-galois}.

\<close>

setup \<open>Sign.mandatory_path "spec.interference.closed"\<close>

lemmas p2s[iff] = prog.p2s

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.interference.cl"\<close>

lemmas p2s = spec.interference.closed_conv[OF spec.interference.closed.p2s, symmetric, of P for P]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.idle"\<close>

lemmas p2s_le[spec.idle_le]
  = spec.interference.le_closedE[OF spec.idle.interference.cl_le spec.interference.closed.p2s, of P for P]
lemmas p2s_minimal[iff] = order.trans[OF spec.idle.minimal_le spec.idle.p2s_le]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "prog"\<close>

lemma p2s_leI:
  assumes "prog.p2s c \<le> prog.p2s d"
  shows "c \<le> d"
by (simp add: assms less_eq_prog.rep_eq)

setup \<open>Sign.mandatory_path "p2s"\<close>

named_theorems simps \<open>simp rules for \<^const>\<open>p2s\<close>\<close>

lemmas bot = bot_prog.rep_eq
lemmas top = top_prog.rep_eq
lemmas inf = inf_prog.rep_eq
lemmas sup = sup_prog.rep_eq
lemmas Inf = Inf_prog.rep_eq
lemmas Sup = Sup_prog.rep_eq

lemma Sup_not_empty:
  assumes "X \<noteq> {}"
  shows "prog.p2s (\<Squnion>X) = \<Squnion>(prog.p2s ` X)"
using assms by transfer (simp add: sup.absorb1 less_eq_Sup spec.interference.least)

lemma SUP_not_empty:
  assumes "X \<noteq> {}"
  shows " prog.p2s (\<Squnion>x\<in>X. f x) = (\<Squnion>x\<in>X. prog.p2s (f x))"
by (simp add: assms prog.p2s.Sup_not_empty[where X="f ` X", simplified image_image])


lemma monotone:
  shows "mono prog.p2s"
by (rule monoI) (transfer; simp)

lemmas strengthen[strg] = st_monotone[OF prog.p2s.monotone]
lemmas mono = monotoneD[OF prog.p2s.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF prog.p2s.monotone, simplified, of orda P for orda P]

lemma mcont: \<comment>\<open> Morally @{thm [source] galois.complete_lattice.mcont_lower} \<close>
  shows "mcont Sup (\<le>) Sup (\<le>) prog.p2s"
by (simp add: contI mcontI prog.p2s.Sup_not_empty)

lemmas mcont2mcont[cont_intro] = mcont2mcont[OF prog.p2s.mcont, of luba orda P for luba orda P]

lemmas Let_distrib = Let_distrib[where f=prog.p2s]

lemmas [prog.p2s.simps] =
  prog.p2s.bot
  prog.p2s.top
  prog.p2s.inf
  prog.p2s.sup
  prog.p2s.Inf
  prog.p2s.Sup_not_empty
  spec.interference.cl.p2s
  prog.p2s.Let_distrib

lemma interference_wind_bind:
  shows "spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. prog.p2s P) = prog.p2s P"
by (subst (1 2) spec.interference.closed_conv[OF prog.p2s])
   (simp add: spec.interference.cl_def spec.rel.wind_bind flip: spec.bind.bind)

setup \<open>Sign.parent_path\<close>

definition s2p :: "(sequential, 's, 'v) spec \<Rightarrow> ('s, 'v) prog" where \<comment>\<open> Morally the upper of a Galois connection \<close>
  "s2p P = \<Squnion>{c. prog.p2s c \<le> P}"

setup \<open>Sign.mandatory_path "s2p"\<close>

lemma bottom:
  shows "prog.s2p \<bottom> = \<bottom>"
by (simp add: prog.s2p_def bot.extremum_uniqueI less_eq_prog.rep_eq)

lemma top:
  shows "prog.s2p \<top> = \<top>"
by (simp add: prog.s2p_def)

lemma monotone:
  shows "mono prog.s2p"
by (fastforce simp: prog.s2p_def intro: monotoneI Sup_subset_mono)

lemmas strengthen[strg] = st_monotone[OF prog.s2p.monotone]
lemmas mono = monotoneD[OF prog.s2p.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF prog.s2p.monotone, simplified]

lemma p2s:
  shows "prog.s2p (prog.p2s P) = P"
by (auto simp: prog.s2p_def simp flip: less_eq_prog.rep_eq intro: Sup_eqI)

lemma Sup_le:
  shows "\<Squnion>(prog.s2p ` X) \<le> prog.s2p (\<Squnion>X)"
by (simp add: prog.s2p_def Collect_mono SUPE Sup_subset_mono Sup_upper2)

lemma sup_le:
  shows "prog.s2p x \<squnion> prog.s2p y \<le> prog.s2p (x \<squnion> y)"
using prog.s2p.Sup_le[where X="{x, y}"] by simp

lemma Inf:
  shows "prog.s2p (\<Sqinter>X) = \<Sqinter>(prog.s2p ` X)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (simp add: prog.s2p_def SupI Sup_le_iff le_Inf_iff)
  show "?rhs \<le> ?lhs"
    by (fastforce simp: prog.s2p_def prog.p2s.mono
                        Inf_Sup[where A="(\<lambda>x. {c. prog.p2s c \<le> x}) ` X", simplified image_image]
                        le_Inf_iff INF_lower2
                  elim: order.trans[rotated]
                 intro: Sup_subset_mono)
qed

lemma inf:
  shows "prog.s2p (x \<sqinter> y) = prog.s2p x \<sqinter> prog.s2p y"
using prog.s2p.Inf[where X="{x, y}"] by simp

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "p2s_s2p"\<close>

lemma galois: \<comment>\<open> the Galois connection \<close>
  shows "prog.p2s c \<le> S
     \<longleftrightarrow> c \<le> prog.s2p S \<and> spec.term.none (spec.rel ({env} \<times> UNIV) :: (_, _, unit) spec) \<le> S" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (metis order.trans prog.s2p.mono prog.s2p.p2s spec.interference.closed.p2s
              spec.term.none.interference.closed.rel_le)
  show "?rhs \<Longrightarrow> ?lhs"
    unfolding prog.s2p_def by transfer (force simp: spec.interference.cl.bot elim: order.trans)
qed

lemma le:
  shows "prog.p2s (prog.s2p S) \<le> spec.interference.cl ({env} \<times> UNIV) S"
by (metis bot_prog.rep_eq prog.p2s_s2p.galois prog.s2p.mono spec.interference.cl_bot_least
          spec.interference.expansive)

lemma insertion:
  fixes S :: "(sequential, 's, 'v) spec"
  assumes "S \<in> spec.interference.closed ({env} \<times> UNIV)"
  shows "prog.p2s (prog.s2p S) = S"
by (metis assms prog.p2s_cases prog.s2p.p2s)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Programming language constructs\label{sec:programs-language} \<close>

text\<open>

We lift the combinators directly from the \<^typ>\<open>('a,
's ,'v) spec\<close> lattice (\S\ref{sec:safety_logic}), but need to
interference-close primitive actions. Control flow is expressed via
HOL's \<open>if-then-else\<close> construct and other case combinators
where the scrutinee is a pure value. This means that the atomicity of a process is completely
determined by occurrences of \<open>prog.action\<close>.

\<close>

setup \<open>Sign.mandatory_path "prog"\<close>

lift_definition bind :: "('s, 'v) prog \<Rightarrow> ('v \<Rightarrow> ('s, 'w) prog) \<Rightarrow> ('s, 'w) prog" is
  spec.bind ..

adhoc_overloading
  Monad_Syntax.bind prog.bind

lift_definition action :: "('v \<times> 's \<times> 's) set \<Rightarrow> ('s, 'v) prog" is
  "\<lambda>F. spec.interference.cl ({env} \<times> UNIV) (spec.action (map_prod id (Pair self) ` F))" ..

abbreviation (input) det_action :: "('s \<Rightarrow> ('v \<times> 's)) \<Rightarrow> ('s, 'v) prog" where
  "det_action f \<equiv> prog.action {(v, s, s'). (v, s') = f s}"

definition return :: "'v \<Rightarrow> ('s, 'v) prog" where
  "return v = prog.action ({v} \<times> Id)"

definition guard :: "'s pred \<Rightarrow> ('s, unit) prog" where
  "guard g \<equiv> prog.action ({()} \<times> Diag g)"

abbreviation (input) read :: "('s \<Rightarrow> 'v) \<Rightarrow> ('s, 'v) prog" where
  "read F \<equiv> prog.action {(F s, s, s) |s. True}"

abbreviation (input) "write" :: "('s \<Rightarrow> 's) \<Rightarrow> ('s, unit) prog" where
  "write F \<equiv> prog.action {((), s, F s) |s. True}"

lift_definition Parallel :: "'a set \<Rightarrow> ('a \<Rightarrow> ('s, unit) prog) \<Rightarrow> ('s, unit) prog" is spec.Parallel
by (rule spec.interference.closed.Parallel)

lift_definition parallel :: "('s, unit) prog \<Rightarrow> ('s, unit) prog \<Rightarrow> ('s, unit) prog" is spec.parallel
by (simp add: spec.parallel_def spec.interference.closed.Parallel)

lift_definition vmap :: "('v \<Rightarrow> 'w) \<Rightarrow> ('s, 'v) prog \<Rightarrow> ('s, 'w) prog" is spec.vmap
by (rule subsetD[OF spec.interference.closed.antimono spec.interference.closed.map_sf_id, rotated])
   auto

adhoc_overloading
  Parallel prog.Parallel
adhoc_overloading
  parallel prog.parallel

lemma return_alt_def:
  shows "prog.return v = prog.read \<langle>v\<rangle>"
by (auto simp: prog.return_def intro: arg_cong[where f="prog.action"])

lemma parallel_alt_def:
  shows "prog.parallel P Q = prog.Parallel UNIV (\<lambda>a::bool. if a then P else Q)"
by transfer (simp add: spec.parallel_def)

lift_definition rel :: "'s rel \<Rightarrow> ('s, 'v) prog" is "\<lambda>r. spec.rel ({env} \<times> UNIV \<union> {self} \<times> r)"
by (simp add: spec.interference.closed.rel)

lift_definition steps :: "('s, 'v) prog \<Rightarrow> 's rel" is "\<lambda>P. spec.steps P `` {self}" .

lift_definition invmap :: "('s \<Rightarrow> 't) \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> ('t, 'w) prog \<Rightarrow> ('s, 'v) prog" is
  "spec.invmap id"
by (rule subsetD[OF spec.interference.closed.antimono spec.interference.closed.invmap, rotated])
   auto

abbreviation sinvmap ::"('s \<Rightarrow> 't) \<Rightarrow> ('t, 'v) prog \<Rightarrow> ('s, 'v) prog" where
  "sinvmap sf \<equiv> prog.invmap sf id"
abbreviation vinvmap ::"('v \<Rightarrow> 'w) \<Rightarrow> ('s, 'w) prog \<Rightarrow> ('s, 'v) prog" where
  "vinvmap vf \<equiv> prog.invmap id vf"

declare prog.bind_def[code del]
declare prog.action_def[code del]
declare prog.return_def[code del]
declare prog.Parallel_def[code del]
declare prog.parallel_def[code del]
declare prog.vmap_def[code del]
declare prog.rel_def[code del]
declare prog.steps_def[code del]
declare prog.invmap_def[code del]


subsubsection\<open> Laws of programming \label{sec:programs-laws} \<close>

setup \<open>Sign.mandatory_path "p2s"\<close>

lemma bind[prog.p2s.simps]:
  shows "prog.p2s (f \<bind> g) = prog.p2s f \<bind> (\<lambda>x. prog.p2s (g x))"
by transfer simp

lemmas action = prog.action.rep_eq

lemma return:
  shows "prog.p2s (prog.return v) = spec.interference.cl ({env} \<times> UNIV) (spec.return v)"
by (simp add: prog.return_def prog.p2s.action map_prod_image_Times Pair_image
        flip: spec.return_alt_def)

lemma guard:
  shows "prog.p2s (prog.guard g) = spec.interference.cl ({env} \<times> UNIV) (spec.guard g)"
by (simp add: prog.guard_def prog.p2s.action map_prod_image_Times Pair_image
        flip: spec.guard.alt_def[where A="{self}"])

lemmas Parallel[prog.p2s.simps] = prog.Parallel.rep_eq[simplified, of as Ps for as Ps, unfolded comp_def]
lemmas parallel[prog.p2s.simps] = prog.parallel.rep_eq
lemmas invmap[prog.p2s.simps] = prog.invmap.rep_eq
lemmas rel[prog.p2s.simps] = prog.rel.rep_eq

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "return"\<close>

lemma transfer[transfer_rule]:
  shows "rel_fun (=) cr_prog (\<lambda>v. spec.interference.cl ({env} \<times> UNIV) (spec.return v)) prog.return"
by (simp add: rel_funI cr_prog_def prog.p2s.return)

lemma cong:
  fixes F :: "('v \<times> 's \<times> 's) set"
  assumes "\<And>v s s'. (v, s, s') \<in> F \<Longrightarrow> s' = s"
  assumes "\<And>v s s' s''. v \<in> fst ` F \<Longrightarrow> (v, s, s) \<in> F"
  shows "prog.action F = (\<Squnion>(v, s, s')\<in>F. prog.return v)"
using assms
by transfer
   (subst spec.return.cong;
    fastforce simp: spec.interference.cl.action spec.interference.cl.return
                    spec.interference.cl.Sup spec.interference.cl.sup spec.interference.cl.idle
                    spec.interference.cl.bot image_image split_def
             intro: map_prod_imageI[where f=id, simplified])

lemma rel_le:
  shows "prog.return v \<le> prog.rel r"
by transfer (simp add: spec.interference.least spec.interference.closed.rel spec.return.rel_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma empty:
  shows "prog.action {} = \<bottom>"
by transfer
   (simp add: spec.action.empty spec.interference.cl.bot spec.interference.cl.idle
        flip: bot_fun_def spec.bind.botR)

lemma monotone:
  shows "mono (prog.action :: _ \<Rightarrow> ('s, 'v) prog)"
proof(transfer, rule monotoneI)
  show "spec.interference.cl ({env} \<times> UNIV) (spec.action (map_prod id (Pair self) ` F))
     \<le> spec.interference.cl ({env} \<times> UNIV) (spec.action (map_prod id (Pair self) ` F'))"
    if "F \<subseteq> F'" for F F' :: "('v \<times> 's \<times> 's) set"
    by (strengthen ord_to_strengthen(1)[OF \<open>F \<subseteq> F'\<close>]) simp
qed

lemmas strengthen[strg] = st_monotone[OF prog.action.monotone]
lemmas mono = monotoneD[OF prog.action.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF prog.action.monotone, simplified]

lemma Sup:
  shows "prog.action (\<Squnion>Fs) = (\<Squnion>F\<in>Fs. prog.action F)"
by transfer
   (simp add: spec.interference.cl.bot spec.interference.cl.Sup spec.interference.cl.sup
              spec.interference.cl.idle spec.interference.cl.action spec.action.Sup image_Union image_image
        flip: bot_fun_def spec.bind.botR)

lemmas sup = prog.action.Sup[where Fs="{F, G}" for F G, simplified]

lemma Inf_le:
  shows "prog.action (\<Sqinter>Fs) \<le> (\<Sqinter>F\<in>Fs. prog.action F)"
apply transfer
apply (strengthen ord_to_strengthen(1)[OF image_Inter_subseteq])
apply (strengthen ord_to_strengthen(1)[OF spec.action.Inf_le])
apply (strengthen ord_to_strengthen(1)[OF spec.interference.cl_Inf_le])
apply (blast intro: Inf_mono)
done

lemma inf_le:
  shows "prog.action (F \<sqinter> G) \<le> prog.action F \<sqinter> prog.action G"
using prog.action.Inf_le[where Fs="{F, G}"] by simp

lemma sinvmap_le: \<comment>\<open> a strict refinement \<close>
  shows "prog.p2s (prog.action (map_prod id (map_prod sf sf) -` F))
      \<le> spec.sinvmap sf (prog.p2s (prog.action F))"
by (force intro: order.trans[OF _ spec.interference.cl.mono[OF order.refl spec.action.invmap_le]]
                 spec.interference.cl.mono spec.action.mono
           simp: prog.p2s.action spec.invmap.interference.cl)

lemma return_const:
  fixes F :: "'s rel"
  fixes V :: "'v set"
  fixes W :: "'w set"
  assumes "V \<noteq> {}"
  assumes "W \<noteq> {}"
  shows "prog.action (V \<times> F) = prog.action (W \<times> F) \<then> (\<Squnion>v\<in>V. prog.return v)"
using assms(1)
by (simp add: prog.p2s.simps prog.p2s.action prog.p2s.return image_image
              map_prod_image_Times spec.action.return_const[OF assms]
              spec.bind.SUPR_not_empty spec.interference.cl.bind_return
              spec.interference.cl.return spec.interference.cl_Sup_not_empty
              spec.interference.closed.bind_relR
        flip: prog.p2s_inject)

lemma rel_le:
  assumes "\<And>v s s'. (v, s, s') \<in> F \<Longrightarrow> (s, s') \<in> r \<or> s = s'"
  shows "prog.action F \<le> prog.rel r"
by (auto intro: order.trans[OF spec.interference.cl.mono[OF order.refl
                                                            spec.action.rel_le[where r="{self} \<times> r \<union> {env} \<times> UNIV"]]]
          dest: assms
          simp: less_eq_prog.rep_eq prog.p2s.simps prog.p2s.action spec.interference.cl.rel ac_simps)

lemma invmap_le:
  shows "prog.action (map_prod vf (map_prod sf sf) -` F) \<le> prog.invmap sf vf (prog.action F)"
by transfer
   (force simp: spec.invmap.interference.cl
         intro: spec.interference.cl.mono
                spec.action.mono order.trans[OF _ spec.interference.cl.mono[OF order.refl spec.action.invmap_le]])

lemma action_le:
  shows "spec.action (map_prod id (Pair self) ` F) \<le> prog.p2s (prog.action F)"
by (simp add: prog.p2s.action spec.interference.expansive)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemmas if_distrL = if_distrib[where f="\<lambda>x. x \<bind> g" for g :: "_ \<Rightarrow> (_, _) prog"]

lemma mono:
  assumes "f \<le> f'"
  assumes "\<And>x. g x \<le> g' x"
  shows "prog.bind f g \<le> prog.bind f' g'"
using assms by transfer (simp add: spec.bind.mono)

lemma strengthen[strg]:
  assumes "st_ord F f f'"
  assumes "\<And>x. st_ord F (g x) (g' x)"
  shows "st_ord F (prog.bind f g) (prog.bind f' g')"
using assms by (cases F; clarsimp intro!: prog.bind.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) f"
  assumes "\<And>x. monotone orda (\<le>) (\<lambda>y. g y x)"
  shows "monotone orda (\<le>) (\<lambda>x. prog.bind (f x) (g x))"
using assms by transfer simp

text\<open> The monad laws hold unconditionally in the \<^typ>\<open>('s, 'v) prog\<close> lattice. \<close>

lemma bind:
  shows "f \<bind> g \<bind> h = prog.bind f (\<lambda>x. g x \<bind> h)"
by transfer (simp add: spec.bind.bind)

lemma return:
  shows returnL: "(\<bind>) (prog.return v) = (\<lambda>g :: 'v \<Rightarrow> ('s, 'w) prog. g v)" (is ?thesis1)
    and returnR: "f \<bind> prog.return = f" (is ?thesis2)
proof -
  have "prog.return v \<bind> g = g v" for g :: "'v \<Rightarrow> ('s, 'w) prog"
    by transfer
       (simp add: map_prod_image_Times Pair_image spec.action.read_agents
                  spec.interference.cl.return spec.bind.bind
                  spec.bind.returnL spec.idle_le prog.p2s_induct spec.interference.closed.bind_relL
            flip: spec.return_def)
  then show ?thesis1
    by (simp add: fun_eq_iff)
  show ?thesis2
    by transfer
       (simp add: map_prod_image_Times Pair_image spec.action.read_agents
            flip: spec.interference.cl.bindL spec.return_def spec.interference.closed_conv)
qed

lemma botL:
  shows "prog.bind \<bottom> = \<bottom>"
by (simp add: fun_eq_iff prog.p2s.simps spec.interference.cl.bot
        flip: prog.p2s_inject)

lemma botR_le:
  shows "prog.bind f \<langle>\<bottom>\<rangle> \<le> f" (is ?thesis1)
    and "prog.bind f \<bottom> \<le> f" (is ?thesis2)
proof -
  show ?thesis1
    by (metis bot.extremum dual_order.refl prog.bind.mono prog.bind.returnR)
  then show ?thesis2
    by (simp add: bot_fun_def)
qed

lemma
  fixes f :: "(_, _) prog"
  fixes f\<^sub>1 :: "(_, _) prog"
  shows supL: "(f\<^sub>1 \<squnion> f\<^sub>2) \<bind> g = (f\<^sub>1 \<bind> g) \<squnion> (f\<^sub>2 \<bind> g)"
    and supR: "f \<bind> (\<lambda>x. g\<^sub>1 x \<squnion> g\<^sub>2 x) = (f \<bind> g\<^sub>1) \<squnion> (f \<bind> g\<^sub>2)"
by (transfer; blast intro: spec.bind.supL spec.bind.supR)+

lemma SUPL:
  fixes X :: "_ set"
  fixes f :: "_ \<Rightarrow> (_, _) prog"
  shows "(\<Squnion>x\<in>X. f x) \<bind> g = (\<Squnion>x\<in>X. f x \<bind> g)"
by transfer
   (simp add: spec.interference.cl.bot spec.bind.supL spec.bind.bind spec.bind.SUPL
        flip: spec.bind.botR bot_fun_def)

lemma SUPR:
  fixes X :: "_ set"
  fixes f :: "(_, _) prog"
  shows "f \<bind> (\<lambda>v. \<Squnion>x\<in>X. g x v) = (\<Squnion>x\<in>X. f \<bind> g x) \<squnion> (f \<bind> \<bottom>)"
unfolding bot_fun_def
by transfer
   (simp add: spec.bind.supL spec.bind.supR spec.bind.bind spec.bind.SUPR ac_simps le_supI2
              spec.interference.closed.bind_rel_botR
              sup.absorb2 spec.interference.closed.bind spec.interference.least spec.bind.mono
        flip: spec.bind.botR)

lemma SupR:
  fixes X :: "_ set"
  fixes f :: "(_, _) prog"
  shows "f \<then> (\<Squnion>X) = (\<Squnion>x\<in>X. f \<then> x) \<squnion> (f \<bind> \<bottom>)"
by (simp add: prog.bind.SUPR[where g="\<lambda>x v. x", simplified])

lemma SUPR_not_empty:
  fixes f :: "(_, _) prog"
  assumes "X \<noteq> {}"
  shows "f \<bind> (\<lambda>v. \<Squnion>x\<in>X. g x v) = (\<Squnion>x\<in>X. f \<bind> g x)"
using iffD2[OF ex_in_conv assms]
by (subst trans[OF prog.bind.SUPR sup.absorb1]; force intro: SUPI prog.bind.mono)

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) f"
  assumes "\<And>v. mcont luba orda Sup (\<le>) (\<lambda>x. g x v)"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. prog.bind (f x) (g x))"
proof(rule ccpo.mcont2mcont'[OF complete_lattice_ccpo _ _ assms(1)])
  show "mcont Sup (\<le>) Sup (\<le>) (\<lambda>f. prog.bind f (g x))" for x
    by (intro mcontI contI monotoneI) (simp_all add: prog.bind.mono flip: prog.bind.SUPL)
  show "mcont luba orda Sup (\<le>) (\<lambda>x. prog.bind f (g x))" for f
    by (intro mcontI monotoneI contI)
       (simp_all add: mcont_monoD[OF assms(2)] prog.bind.mono
                flip: prog.bind.SUPR_not_empty contD[OF mcont_cont[OF assms(2)]])
qed

lemma inf_rel:
  shows "prog.rel r \<sqinter> (f \<bind> g) = prog.rel r \<sqinter> f \<bind> (\<lambda>x. prog.rel r \<sqinter> g x)"
    and "(f \<bind> g) \<sqinter> prog.rel r = prog.rel r \<sqinter> f \<bind> (\<lambda>x. prog.rel r \<sqinter> g x)"
by (transfer; simp add: spec.bind.inf_rel)+

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "guard"\<close>

lemma bot:
  shows "prog.guard \<bottom> = \<bottom>"
    and "prog.guard \<langle>False\<rangle> = \<bottom>"
by (simp_all add: prog.guard_def prog.action.empty)

lemma top:
  shows "prog.guard (\<top>::'a pred) = prog.return ()" (is ?thesis1)
    and "prog.guard (\<langle>True\<rangle>::'a pred) = prog.return ()" (is ?thesis2)
proof -
  show ?thesis1
    unfolding prog.guard_def prog.return_def by transfer (simp add: Id_def)
  then show ?thesis2
    by (simp add: top_fun_def)
qed

lemma return_le:
  shows "prog.guard g \<le> prog.return ()"
unfolding prog.guard_def Diag_def prog.return_def
by transfer (blast intro: spec.interference.cl.mono spec.action.mono)

lemma monotone:
  shows "mono (prog.guard :: 's pred \<Rightarrow> _)"
proof(rule monoI)
  show "prog.guard g \<le> prog.guard h" if "g \<le> h" for g h :: "'s pred"
    unfolding prog.guard_def
    by (strengthen ord_to_strengthen(1)[OF that]) (rule order.refl)
qed

lemmas strengthen[strg] = st_monotone[OF prog.guard.monotone]
lemmas mono = monotoneD[OF prog.guard.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF prog.guard.monotone, simplified]

lemma less: \<comment>\<open> Non-triviality \<close>
  assumes "g < g'"
  shows "prog.guard g < prog.guard g'"
proof(rule le_neq_trans)
  show "prog.guard g \<le> prog.guard g'"
    by (strengthen ord_to_strengthen(1)[OF order_less_imp_le[OF assms]]) simp
  from assms obtain s where "g' s" "\<not>g s" by (metis leD predicate1I)
  from \<open>\<not>g s\<close> have "\<not>\<lblot>trace.T s [] (Some ())\<rblot> \<le> prog.p2s (prog.guard g)"
    by (fastforce simp: trace.split_all prog.p2s.guard spec.guard_def spec.interference.cl.action
                        spec.singleton.le_conv spec.singleton.action_le_conv trace.steps'.step_conv
                  elim: spec.singleton.bind_le)
  moreover
  from \<open>g' s\<close> have "\<lblot>trace.T s [] (Some ())\<rblot> \<le> prog.p2s (prog.guard g')"
    by (force simp: prog.p2s.guard prog.p2s.action spec.guard_def
             intro: order.trans[OF _ spec.interference.expansive] spec.action.stutterI)
  ultimately show "prog.guard g \<noteq> prog.guard g'" by metis
qed

lemma "if":
  shows "(if b then t else e) = (prog.guard \<langle>b\<rangle> \<then> t) \<squnion> (prog.guard \<langle>\<not>b\<rangle> \<then> e)"
by (auto simp: prog.guard.bot prog.guard.top prog.bind.returnL prog.bind.botL)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "Parallel"\<close>

lemma bot:
  assumes "\<And>a. a \<in> bs \<Longrightarrow> Ps a = \<bottom>"
  assumes "as \<inter> bs \<noteq> {}"
  shows "prog.Parallel as Ps = prog.Parallel (as - bs) Ps \<bind> \<bottom>"
by (auto simp: assms(1)
               prog.p2s.simps spec.interference.cl.bot
               spec.interference.closed.bind_rel_unitR spec.interference.closed.Parallel
               spec.term.none.Parallel_some_agents[OF _ assms(2), where Ps'="\<langle>spec.rel ({env} \<times> UNIV)\<rangle>"]
               spec.Parallel.discard_interference[where as=as and bs="as \<inter> bs"]
     simp del: Int_iff
    simp flip: prog.p2s_inject spec.bind.botR spec.bind.bind
        intro: arg_cong[OF spec.Parallel.cong])

lemma mono:
  assumes "\<And>a. a \<in> as \<Longrightarrow> Ps a \<le> Ps' a"
  shows "prog.Parallel as Ps \<le> prog.Parallel as Ps'"
using assms by transfer (blast intro: spec.Parallel.mono)

lemma strengthen_Parallel[strg]:
  assumes "\<And>a. a \<in> as \<Longrightarrow> st_ord F (Ps a) (Ps' a)"
  shows "st_ord F (prog.Parallel as Ps) (prog.Parallel as Ps')"
using assms by (cases F) (auto simp: prog.Parallel.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "\<And>a. a \<in> as \<Longrightarrow> monotone orda (\<le>) (F a)"
  shows "monotone orda (\<le>) (\<lambda>f. prog.Parallel as (\<lambda>a. F a f))"
using assms by transfer (simp add: spec.Parallel.mono2mono)

lemma cong:
  assumes "as = as'"
  assumes "\<And>a. a \<in> as' \<Longrightarrow> Ps a = Ps' a"
  shows "prog.Parallel as Ps = prog.Parallel as' Ps'"
using assms by transfer (rule spec.Parallel.cong; simp)

lemma no_agents:
  shows "prog.Parallel {} Ps = prog.return ()"
by transfer
   (simp add: spec.Parallel.no_agents spec.interference.cl.return map_prod_image_Times Pair_image
              spec.action.read_agents)

lemma singleton_agents:
  shows "prog.Parallel {a} Ps = Ps a"
by transfer (rule spec.Parallel.singleton_agents)

lemma rename_UNIV:
  assumes "inj_on f as"
  shows "prog.Parallel as Ps
       = prog.Parallel UNIV (\<lambda>b. if b \<in> f ` as then Ps (inv_into as f b) else prog.return ())"
by (simp add: prog.p2s.simps if_distrib prog.p2s.return spec.interference.cl.return
              spec.Parallel.rename_UNIV[OF assms]
        flip: prog.p2s_inject
        cong: spec.Parallel.cong if_cong)

lemmas rename = spec.Parallel.rename[transferred]

lemma return:
  assumes "\<And>a. a \<in> bs \<Longrightarrow> Ps a = prog.return ()"
  shows "prog.Parallel as Ps = prog.Parallel (as - bs) Ps"
by (subst (1 2) prog.Parallel.rename_UNIV[where f=id, simplified])
   (auto intro: arg_cong[where f="prog.Parallel UNIV"]
          simp: assms fun_eq_iff f_inv_into_f[where f=id, simplified])

lemma unwind:
  assumes a: "f \<bind> g \<le> Ps a" \<comment>\<open> The selected process starts with action \<open>f\<close> \<close>
  assumes "a \<in> as"
  shows "f \<bind> (\<lambda>v. prog.Parallel as (Ps(a:=g v))) \<le> prog.Parallel as Ps"
using assms by transfer (simp add: spec.Parallel.unwind spec.interference.closed.bind_relL)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "parallel"\<close>

lemmas commute = spec.parallel.commute[transferred]
lemmas assoc = spec.parallel.assoc[transferred]
lemmas mono = spec.parallel.mono[transferred]

lemma strengthen[strg]:
  assumes "st_ord F P P'"
  assumes "st_ord F Q Q'"
  shows "st_ord F (prog.parallel P Q) (prog.parallel P' Q')"
using assms by (cases F; simp add: prog.parallel.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) F"
  assumes "monotone orda (\<le>) G"
  shows "monotone orda (\<le>) (\<lambda>f. prog.parallel (F f) (G f))"
using assms by (simp add: monotone_def prog.parallel.mono)

lemma bot:
  shows botL: "prog.parallel \<bottom> P = P \<bind> \<bottom>" (is ?thesis1)
    and botR: "prog.parallel P \<bottom> = P \<bind> \<bottom>" (is ?thesis2)
proof -
  show ?thesis1
    by (simp add: prog.parallel_alt_def prog.Parallel.bot[where bs="{True}", simplified]
                  prog.Parallel.singleton_agents
            cong: prog.Parallel.cong)
  then show ?thesis2
    by (simp add: prog.parallel.commute)
qed

lemma return:
  shows returnL: "prog.return () \<parallel> P = P" (is ?thesis1)
    and returnR: "P \<parallel> prog.return () = P" (is ?thesis2)
proof -
  show ?thesis1
    by (simp add: prog.parallel_alt_def prog.Parallel.return[where bs="{True}", simplified]
                  prog.Parallel.singleton_agents)
  then show ?thesis2
    by (simp add: prog.parallel.commute)
qed

lemma Sup_not_empty:
  fixes X :: "(_, unit) prog set"
  assumes "X \<noteq> {}"
  shows SupL_not_empty: "\<Squnion>X \<parallel> Q = (\<Squnion>P\<in>X. P \<parallel> Q)" (is "?thesis1 Q")
    and SupR_not_empty: "P \<parallel> \<Squnion>X = (\<Squnion>Q\<in>X. P \<parallel> Q)" (is ?thesis2)
proof -
  from assms show "?thesis1 Q" for Q
    by (simp add: prog.p2s.parallel prog.p2s.Sup_not_empty[OF assms] image_image
                  spec.parallel.Sup prog.p2s.SUP_not_empty
            flip: prog.p2s_inject)
  then show ?thesis2
    by (simp add: prog.parallel.commute)
qed

lemma sup:
  fixes P :: "(_, unit) prog"
  shows supL: "P \<squnion> Q \<parallel> R = (P \<parallel> R) \<squnion> (Q \<parallel> R)"
    and supR: "P \<parallel> Q \<squnion> R = (P \<parallel> Q) \<squnion> (P \<parallel> R)"
using prog.parallel.SupL_not_empty[where X="{P, Q}"] prog.parallel.SupR_not_empty[where X="{Q, R}"] by simp_all

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  assumes "mcont luba orda Sup (\<le>) Q"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. prog.parallel (P x) (Q x))"
proof(rule ccpo.mcont2mcont'[OF complete_lattice_ccpo _ _ assms(1)])
  show "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. prog.parallel y (Q x))" for x
    by (intro mcontI contI monotoneI) (simp_all add: prog.parallel.mono prog.parallel.SupL_not_empty)
  show "mcont luba orda Sup (\<le>) (\<lambda>x. prog.parallel y (Q x))" for y
    by (simp add: mcontI monotoneI contI mcont_monoD[OF assms(2)]
                  spec.parallel.mono mcont_contD[OF assms(2)] prog.parallel.SupR_not_empty image_image)
qed

lemma unwindL:
  fixes f :: "('s, 'v) prog"
  assumes a: "f \<bind> g \<le> P" \<comment>\<open> The selected process starts with action \<open>f\<close> \<close>
  shows "f \<bind> (\<lambda>v. g v \<parallel> Q) \<le> P \<parallel> Q"
unfolding prog.parallel_alt_def
by (strengthen ord_to_strengthen[OF prog.Parallel.unwind[where a=True]])
   (auto simp: prog.Parallel.mono prog.bind.mono intro: assms)

lemma unwindR:
  fixes f :: "('s, 'v) prog"
  assumes a: "f \<bind> g \<le> Q" \<comment>\<open> The selected process starts with action \<open>f\<close> \<close>
  shows "f \<bind> (\<lambda>v. P \<parallel> g v) \<le> P \<parallel> Q"
by (subst (1 2) prog.parallel.commute) (rule prog.parallel.unwindL[OF assms])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma parallel_le:
  fixes P :: "(_, _) prog"
  shows "P \<then> Q \<le> P \<parallel> Q"
by (strengthen ord_to_strengthen[OF prog.parallel.unwindL[where g=prog.return, simplified prog.bind.returnR, OF order.refl]])
   (simp add: prog.parallel.return)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma bot:
  shows "prog.invmap sf vf \<bottom> = (prog.rel (map_prod sf sf -` Id) :: (_, unit) prog) \<bind> \<bottom>"
by (auto simp: prog.p2s.simps spec.interference.cl.bot spec.rel.wind_bind_trailing
               spec.invmap.bind spec.invmap.rel spec.invmap.bot
    simp flip: prog.p2s_inject spec.bind.botR spec.bind.bind bot_fun_def
        intro: arg_cong[where f="\<lambda>r. spec.rel r \<bind> \<bottom>"])

lemma id:
  shows "prog.invmap id id P = P"
    and "prog.invmap (\<lambda>x. x) (\<lambda>x. x) P = P"
by (transfer; simp add: spec.invmap.id id_def)+

lemma comp:
  shows "prog.invmap sf vf (prog.invmap sg vg P) = prog.invmap (\<lambda>s. sg (sf s)) (\<lambda>s. vg (vf s)) P" (is "?thesis1 P")
    and "prog.invmap sf vf \<circ> prog.invmap sg vg = prog.invmap (sg \<circ> sf) (vg \<circ> vf)" (is "?thesis2")
proof -
  show "?thesis1 P" for P by transfer (simp add: spec.invmap.comp id_def)
  then show ?thesis2 by (simp add: comp_def)
qed

lemma monotone:
  shows "mono (prog.invmap sf vf)"
unfolding monotone_def by transfer (simp add: spec.invmap.mono)

lemmas strengthen[strg] = st_monotone[OF prog.invmap.monotone]
lemmas mono = monotoneD[OF prog.invmap.monotone]

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) t"
  shows "monotone orda (\<le>) (\<lambda>x. prog.invmap sf vf (t x))"
by (rule monotone2monotone[OF prog.invmap.monotone assms]) simp_all

lemma Sup:
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  shows "prog.invmap sf vf (\<Squnion>X) = \<Squnion>(prog.invmap sf vf ` X) \<squnion> prog.invmap sf vf \<bottom>"
by transfer
   (simp add: spec.invmap.bot spec.invmap.Sup spec.invmap.sup spec.invmap.bind spec.invmap.rel
              spec.interference.cl.bot map_prod_vimage_Times ac_simps
              sup.absorb2 spec.bind.mono[OF spec.rel.mono order.refl]
        flip: spec.bind.botR spec.bind.bind spec.rel.unwind_bind_trailing bot_fun_def inv_image_alt_def)

lemma Sup_not_empty:
  assumes "X \<noteq> {}"
  shows "prog.invmap sf vf (\<Squnion>X) = \<Squnion>(prog.invmap sf vf ` X)"
using iffD2[OF ex_in_conv assms]
by (clarsimp simp: prog.invmap.Sup sup.absorb1 SUPI prog.invmap.mono[OF bot_least])

lemma mcont:
  shows "mcont Sup (\<le>) Sup (\<le>) (prog.invmap sf vf)"
by (simp add: contI mcontI prog.invmap.monotone prog.invmap.Sup_not_empty)

lemmas mcont2mcont[cont_intro] = mcont2mcont[OF prog.invmap.mcont, of luba orda P for luba orda P]

lemma bind:
  shows "prog.invmap sf vf (f \<bind> g) = prog.sinvmap sf f \<bind> (\<lambda>v. prog.invmap sf vf (g v))"
by transfer (simp add: spec.invmap.bind)

lemma parallel:
  shows "prog.invmap sf vf (P \<parallel> Q) = prog.invmap sf vf P \<parallel> prog.invmap sf vf Q"
by transfer (simp add: spec.invmap.parallel)

lemma invmap_image_vimage_commute:
  shows "map_prod id (map_prod id sf) -` map_prod id (Pair self) ` F
       = map_prod id (Pair self) ` map_prod id sf -` F"
by (auto simp: map_prod_conv)

lemma action:
  shows "prog.invmap sf vf (prog.action F)
       = prog.rel (map_prod sf sf -` Id)
          \<bind> (\<lambda>_::unit. prog.action (map_prod id (map_prod sf sf) -` F)
            \<bind> (\<lambda>v. prog.rel (map_prod sf sf -` Id)
              \<bind> (\<lambda>_::unit. \<Squnion>v'\<in>vf -` {v}. prog.return v')))"
proof -
  have *: "{env} \<times> UNIV \<union> {self} \<times> map_prod sf sf -` Id
         = {env} \<times> UNIV \<union> UNIV \<times> map_prod sf sf -` Id" by auto
  show ?thesis
    by (simp add: ac_simps prog.p2s.simps prog.p2s.action
                  spec.interference.cl.action spec.invmap.bind spec.invmap.rel spec.invmap.action spec.invmap.return
                  spec.bind.bind spec.bind.return
                  prog.invmap.invmap_image_vimage_commute map_prod_vimage_Times *
            flip: prog.p2s_inject)
       (simp add: prog.p2s.Sup image_image prog.p2s.simps prog.p2s.return spec.interference.cl.return
                  spec.interference.cl.bot spec.bind.supR
                  spec.rel.wind_bind_leading spec.rel.wind_bind_trailing
            flip: spec.bind.botR spec.bind.SUPR spec.bind.bind)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "vmap"\<close>

lemma bot:
  shows "prog.vmap vf \<bottom> = \<bottom>"
by transfer
   (simp add: spec.interference.cl.bot spec.vmap.unit_rel
        flip: spec.term.none.map_gen[where vf="\<langle>()\<rangle>"])

lemma unitL:
  shows "f \<then> g = prog.vmap \<langle>()\<rangle> f \<then> g"
by transfer (metis spec.vmap.unitL)

lemma eq_return:
  shows "prog.vmap vf P = P \<bind> prog.return \<circ> vf" (is ?thesis1)
    and "prog.vmap vf P = P \<bind> (\<lambda>v. prog.return (vf v))" (is ?thesis2)
proof -
  show ?thesis1
    by transfer
       (simp add: comp_def spec.vmap.eq_return spec.interference.cl.return spec.interference.closed.bind_relR)
  then show ?thesis2
    by (simp add: comp_def)
qed

lemma action:
  shows "prog.vmap vf (prog.action F) = prog.action (map_prod vf id ` F)"
by transfer (simp add: spec.map.interference.cl_sf_id spec.map.surj_sf_action image_comp)

lemma return:
  shows "prog.vmap vf (prog.return v) = prog.return (vf v)"
by (simp add: prog.return_def prog.vmap.action map_prod_image_Times)

setup \<open>Sign.parent_path\<close>

interpretation kleene: kleene "prog.return ()" "\<lambda>x y. prog.bind x \<langle>y\<rangle>"
by standard
   (simp_all add: prog.bind.bind prog.bind.return prog.bind.botL prog.bind.supL prog.bind.supR)

interpretation rel: galois.complete_lattice_class prog.steps prog.rel
proof
  show "prog.steps P \<subseteq> r \<longleftrightarrow> P \<le> prog.rel r" for P :: "('a, 'b) prog" and r :: "'a rel"
    by transfer (auto simp flip: spec.rel.galois)
qed

setup \<open>Sign.mandatory_path "rel"\<close>

lemma empty:
  shows "prog.rel {} = \<Squnion>range prog.return"
by (simp add: prog.p2s.simps prog.p2s.return image_image
              spec.interference.cl.bot spec.interference.cl.return
              spec.term.closed.bind_all_return[OF spec.term.closed.rel] spec.term.all.rel
              sup.absorb1 spec.term.galois
        flip: prog.p2s_inject spec.bind.SUPR_not_empty)

lemmas monotone = prog.rel.monotone_upper
lemmas strengthen[strg] = st_monotone[OF prog.rel.monotone]
lemmas mono = monotoneD[OF prog.rel.monotone]

lemmas Inf = prog.rel.upper_Inf
lemmas inf = prog.rel.upper_inf

lemma reflcl:
  shows "prog.rel (r \<union> Id) = (prog.rel r :: ('s, 'v) prog)" (is ?thesis1)
    and "prog.rel (Id \<union> r) = (prog.rel r :: ('s, 'v) prog)" (is ?thesis2)
proof -
  show ?thesis1
    by transfer
       (subst (2) spec.rel.reflcl[where A=UNIV, symmetric];
        auto intro: arg_cong[where f="spec.rel"])
  then show ?thesis2
    by (simp add: ac_simps)
qed

lemma minus_Id:
  shows "prog.rel (r - Id) = prog.rel r"
by (metis Un_Diff_cancel2 prog.rel.reflcl(1))

lemma Id:
  shows "prog.rel Id = \<Squnion>range prog.return"
by (simp add: prog.rel.reflcl(1)[where r="{}", simplified] prog.rel.empty)

lemma unfoldL:
  fixes r :: "'s rel"
  assumes "Id \<subseteq> r"
  shows "prog.rel r = prog.action ({()} \<times> r) \<then> prog.rel r"
proof -
  have *: "spec.rel ({env} \<times> UNIV)
             \<bind> (\<lambda>v::unit. spec.action (map_prod id (Pair self) ` ({()} \<times> r))
             \<bind> (\<lambda>v::unit. spec.rel ({env} \<times> UNIV \<union> {self} \<times> r)))
         = spec.rel ({env} \<times> UNIV \<union> {self} \<times> r)" (is "?lhs = ?rhs")
    if "Id \<subseteq> r"
   for r :: "'s rel"
  proof(rule antisym)
    let ?r' = "{env} \<times> UNIV \<union> {self} \<times> r"
    have "?lhs \<le> spec.rel ?r' \<bind> (\<lambda>_::unit. spec.rel ?r' \<bind> (\<lambda>_::unit. spec.rel ?r'))"
      by (fastforce intro: spec.bind.mono spec.rel.mono spec.action.mono
                           order.trans[OF _ spec.rel.monomorphic_act_le]
                     simp: spec.rel.act_def)
    also have "\<dots> = ?rhs"
      by (simp add: spec.rel.wind_bind)
    finally show "?lhs \<le> ?rhs" .
    from that show "?rhs \<le> ?lhs"
      apply -
      apply (rule order.trans[OF _
              spec.bind.mono[OF spec.return.rel_le
                spec.bind.mono[OF spec.action.mono[where x="{()} \<times> {self} \<times> Id"] order.refl]]])
       apply (subst spec.return.cong; simp add: image_image spec.bind.supL spec.bind.supR spec.bind.returnL spec.idle_le)
      apply (fastforce simp: map_prod_image_Times)
      done
  qed
  from assms show ?thesis
    by transfer (simp add: * spec.interference.cl.action spec.bind.bind spec.rel.wind_bind_leading)
qed

lemma wind_bind: \<comment>\<open> arbitrary interstitial return type \<close>
  shows "prog.rel r \<then> prog.rel r = prog.rel r"
by transfer (simp add: spec.rel.wind_bind)

lemma wind_bind_leading: \<comment>\<open> arbitrary interstitial return type \<close>
  assumes "r' \<subseteq> r"
  shows "prog.rel r' \<then> prog.rel r = prog.rel r"
using assms by transfer (subst spec.rel.wind_bind_leading; blast)

lemma wind_bind_trailing: \<comment>\<open> arbitrary interstitial return type \<close>
  assumes "r' \<subseteq> r"
  shows "prog.rel r \<then> prog.rel r' = prog.rel r" (is "?lhs = ?rhs")
using assms by transfer (subst spec.rel.wind_bind_trailing; blast)

text\<open> Interstitial unit, for unfolding \<close>

lemmas unwind_bind = prog.rel.wind_bind[where 'c=unit, symmetric]
lemmas unwind_bind_leading = prog.rel.wind_bind_leading[where 'c=unit, symmetric]
lemmas unwind_bind_trailing = prog.rel.wind_bind_trailing[where 'c=unit, symmetric]

lemma mono_conv:
  shows "prog.rel r = prog.kleene.star (prog.action ({()} \<times> r\<^sup>=))" (is "?lhs = ?rhs")
proof(rule antisym)
  have "spec.kleene.star (spec.rel.act ({env} \<times> UNIV \<union> {self} \<times> r)) \<le> prog.p2s ?rhs"
  proof(induct rule: spec.kleene.star.fixp_induct[case_names adm bot step])
    case (step R) show ?case
    proof(induct rule: le_supI[case_names act_step ret])
      case act_step
      have *: "spec.rel.act ({env} \<times> UNIV \<union> {self} \<times> r) \<le> prog.p2s (prog.action ({()} \<times> r\<^sup>=))"
        by (auto simp: spec.rel.act_alt_def Times_Un_distrib2 spec.action.sup
                       prog.p2s.sup prog.p2s.return spec.interference.cl.return prog.action.sup map_prod_conv
            simp flip: prog.return_def
                intro: spec.action.mono le_supI2 spec.action.rel_le spec.return.rel_le
                       le_supI1[OF order.trans[OF spec.action.mono prog.action.action_le]])
      show ?case
        apply (subst prog.kleene.star.simps)
        apply (strengthen ord_to_strengthen(1)[OF step])
        apply (simp add: prog.p2s.simps le_supI1[OF spec.bind.mono[OF * order.refl]])
        done
    next
      case ret show ?case
        by (simp add: order.trans[OF _ prog.p2s.mono[OF prog.kleene.epsilon_star_le]]
                      prog.p2s.return spec.interference.expansive)
    qed
  qed simp_all
  then show "?lhs \<le> ?rhs"
    by (simp add: prog.p2s_leI prog.p2s.simps spec.rel.monomorphic_conv)
  show "?rhs \<le> ?lhs"
  proof(induct rule: prog.kleene.star.fixp_induct[case_names adm bot step])
    case (step R) show ?case
      apply (strengthen ord_to_strengthen(1)[OF step])
      apply (simp add: prog.return.rel_le)
      apply (subst (2) prog.rel.unwind_bind)
      apply (auto intro: prog.bind.mono prog.action.rel_le)
      done
  qed simp_all
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma inf_rel:
  assumes "refl r"
  shows "prog.action F \<sqinter> prog.rel r = prog.action (F \<inter> UNIV \<times> r)" (is ?thesis1)
    and "prog.rel r \<sqinter> prog.action F = prog.action (F \<inter> UNIV \<times> r)" (is ?thesis2)
proof -
  from assms have "refl (({env} \<times> UNIV \<union> {self} \<times> r) `` {a})" for a
    by (fastforce dest: reflD intro: reflI)
  then show ?thesis1
    by transfer (simp add: spec.interference.cl.inf_rel spec.action.inf_rel; rule arg_cong; blast)
  then show ?thesis2
    by (rule inf_commute_conv)
qed

lemma inf_rel_reflcl:
  shows "prog.action F \<sqinter> prog.rel r = prog.action (F \<inter> UNIV \<times> r\<^sup>=)"
    and "prog.rel r \<sqinter> prog.action F = prog.action (F \<inter> UNIV \<times> r\<^sup>=)"
by (simp_all add: refl_on_def prog.rel.reflcl ac_simps flip: prog.action.inf_rel)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "return"\<close>

lemma not_bot:
  shows "prog.return v \<noteq> (\<bottom> :: ('s, 'v) prog)"
using prog.guard.less[where g="\<bottom>::'s pred" and g'=top]
by (force dest: arg_cong[where f="prog.vmap (\<lambda>_::'v. ())"]
          simp: prog.vmap.return prog.vmap.bot fun_eq_iff prog.guard.bot prog.guard.top
     simp flip: top.not_eq_extremum)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma return:
  shows "prog.invmap sf vf (prog.return v)
       = prog.rel (map_prod sf sf -` Id) \<bind> (\<lambda>_::unit. \<Squnion>v'\<in>vf -` {v}. prog.return v')"
apply (simp add: prog.return_def prog.invmap.action map_prod_vimage_Times)
apply (simp add: prog.action.return_const[where V="{v}" and W="{()}"] prog.bind.bind prog.bind.return)
apply (subst prog.bind.bind[symmetric], subst prog.rel.unfoldL[symmetric];
       force simp: prog.rel.wind_bind simp flip: prog.bind.bind)
done

lemma split_vinvmap:
  fixes P :: "('s, 'v) prog"
  shows "prog.invmap sf vf P = prog.sinvmap sf P \<bind> (\<lambda>v. \<Squnion>v'\<in>vf -` {v}. prog.return v')"
proof -
  note sic_invmap = spec.interference.closed.invmap[where af=id and r="{env} \<times> UNIV",
                                                    simplified map_prod_vimage_Times, simplified]
  show ?thesis
    apply transfer
    apply (simp add: spec.bind.supR sup.absorb1 spec.interference.cl.bot bot_fun_def
                     spec.interference.closed.bind_relR sic_invmap spec.bind.mono
               flip: spec.bind.botR)
    apply (subst (1) spec.invmap.split_vinvmap)
    apply (subst (1) spec.interference.closed.bind_relR[symmetric], erule sic_invmap)
    apply (simp add: spec.bind.SUPR spec.bind.supR spec.interference.cl.return
              sup.absorb1 bot_fun_def spec.interference.closed.bind_relR sic_invmap spec.bind.mono)
    done
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Refinement for \<^emph>\<open>('s, 'v) prog\<close>\label{sec:programs-refinement} \<close>

text\<open>

We specialize the rules of \S\ref{sec:refinement-spec} to the
\<^typ>\<open>('s, 'v) prog\<close> lattice. Observe that, as
preconditions, postconditions and assumes are not interference closed,
we apply the \<^const>\<open>prog.p2s\<close> morphism and work in the more
capacious \<^typ>\<open>(sequential, 's, 'v) spec\<close>
lattice. This syntactic noise could be elided with another definition.

\<close>


subsubsection\<open> Introduction rules\label{sec:programs-refinement-intros} \<close>

text\<open>

Refinement is a way of showing inequalities and equalities between programs.

\<close>

setup \<open>Sign.mandatory_path "refinement.prog"\<close>

lemma leI:
  assumes "prog.p2s c \<le> \<lbrace>\<langle>True\<rangle>\<rbrace>, \<top> \<tturnstile> prog.p2s d, \<lbrace>\<lambda>_. \<langle>True\<rangle>\<rbrace>"
  shows "c \<le> d"
using assms by (simp add: refinement_def prog.p2s_leI)

lemma eqI:
  assumes "prog.p2s c \<le> \<lbrace>\<langle>True\<rangle>\<rbrace>, \<top> \<tturnstile> prog.p2s d, \<lbrace>\<lambda>_. \<langle>True\<rangle>\<rbrace>"
  assumes "prog.p2s d \<le> \<lbrace>\<langle>True\<rangle>\<rbrace>, \<top> \<tturnstile> prog.p2s c, \<lbrace>\<lambda>_. \<langle>True\<rangle>\<rbrace>"
  shows "c = d"
by (rule antisym; simp add: assms refinement.prog.leI)

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Galois considerations\label{sec:programs-refinement-galois} \<close>

text\<open>

Refinement quadruples \<open>\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>\<close> denote points in the \<^typ>\<open>('s, 'v) prog\<close> lattice
provided \<open>G\<close> is suitably interference closed.

\<close>

setup \<open>Sign.mandatory_path "refinement.prog"\<close>

lemma galois:
  assumes "spec.term.none (spec.rel ({env} \<times> UNIV) :: (_, _, unit) spec) \<le> G"
  shows "prog.p2s c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> \<longleftrightarrow> c \<le> prog.s2p (\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>)"
by (simp add: assms prog.p2s_s2p.galois refinement_def spec.next_imp.contains spec.term.none.post_le)

lemmas s2p_refinement = iffD1[OF refinement.prog.galois, rotated]

lemma p2s_s2p:
  assumes "spec.term.none (spec.rel ({env} \<times> UNIV) :: (_, _, unit) spec) \<le> G"
  shows "prog.p2s (prog.s2p (\<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>)) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
using assms by (simp add: refinement.prog.galois)

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Rules\label{sec:programs-refinement-rules} \<close>

setup \<open>Sign.mandatory_path "refinement.prog"\<close>

lemma bot[iff]:
  shows "prog.p2s \<bottom> \<le> \<lbrace>P\<rbrace>, A \<tturnstile> prog.p2s c', \<lbrace>Q\<rbrace>"
by (simp add: refinement.prog.galois spec.term.none.interference.closed.rel_le)

lemma sup_conv:
  shows "prog.p2s (c\<^sub>1 \<squnion> c\<^sub>2) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>
     \<longleftrightarrow> prog.p2s c\<^sub>1 \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace> \<and> prog.p2s c\<^sub>2 \<le> \<lbrace>P\<rbrace>, A \<tturnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: prog.p2s.simps)

lemmas sup = iffD2[OF refinement.prog.sup_conv, unfolded conj_explode]

lemma "if":
  assumes "i \<Longrightarrow> prog.p2s t \<le> \<lbrace>P\<rbrace>, A \<tturnstile> prog.p2s t', \<lbrace>Q\<rbrace>"
  assumes "\<not>i \<Longrightarrow> prog.p2s e \<le> \<lbrace>P'\<rbrace>, A \<tturnstile> prog.p2s e', \<lbrace>Q\<rbrace>"
  shows "prog.p2s (if i then t else e) \<le> \<lbrace>if i then P else P'\<rbrace>, A \<tturnstile> prog.p2s (if i then t' else e'), \<lbrace>Q\<rbrace>"
using assms by fastforce

lemmas if' = refinement.prog.if[where P=P and P'=P, simplified] for P

lemma case_option:
  assumes "opt = None \<Longrightarrow> prog.p2s none \<le> \<lbrace>P\<^sub>n\<rbrace>, A \<tturnstile> prog.p2s none', \<lbrace>Q\<rbrace>"
  assumes "\<And>v. opt = Some v \<Longrightarrow> prog.p2s (some v) \<le> \<lbrace>P\<^sub>s v\<rbrace>, A \<tturnstile> prog.p2s (some' v), \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_option none some opt) \<le> \<lbrace>case opt of None \<Rightarrow> P\<^sub>n | Some v \<Rightarrow> P\<^sub>s v\<rbrace>, A \<tturnstile> prog.p2s (case_option none' some' opt), \<lbrace>Q\<rbrace>"
using assms by (simp add: option.case_eq_if)

lemma case_sum:
  assumes "\<And>v. x = Inl v \<Longrightarrow> prog.p2s (left v) \<le> \<lbrace>P\<^sub>l v\<rbrace>, A \<tturnstile> prog.p2s (left' v), \<lbrace>Q\<rbrace>"
  assumes "\<And>v. x = Inr v \<Longrightarrow> prog.p2s (right v) \<le> \<lbrace>P\<^sub>r v\<rbrace>, A \<tturnstile> prog.p2s (right' v), \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_sum left right x) \<le> \<lbrace>case_sum P\<^sub>l P\<^sub>r x\<rbrace>, A \<tturnstile> prog.p2s (case_sum left' right' x), \<lbrace>Q\<rbrace>"
using assms by (simp add: sum.case_eq_if)

lemma case_list:
  assumes "x = [] \<Longrightarrow> prog.p2s nil \<le> \<lbrace>P\<^sub>n\<rbrace>, A \<tturnstile> prog.p2s nil', \<lbrace>Q\<rbrace>"
  assumes "\<And>v vs. x = v # vs \<Longrightarrow> prog.p2s (cons v vs) \<le> \<lbrace>P\<^sub>c v vs\<rbrace>, A \<tturnstile> prog.p2s (cons' v vs), \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_list nil cons x) \<le> \<lbrace>case_list P\<^sub>n P\<^sub>c x\<rbrace>, A \<tturnstile> prog.p2s (case_list nil' cons' x), \<lbrace>Q\<rbrace>"
using assms by (simp add: list.case_eq_if)

lemma action:
  fixes F :: "('v \<times> 's \<times> 's) set"
  assumes "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F; (self, s, s') \<in> spec.steps A \<or> s = s'\<rbrakk> \<Longrightarrow> Q v s'"
  assumes "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> (v, s, s') \<in> F'"
  assumes sP: "stable (spec.steps A `` {env}) P"
  assumes "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> stable (spec.steps A `` {env}) (Q v)"
  shows "prog.p2s (prog.action F) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> prog.p2s (prog.action F'), \<lbrace>Q\<rbrace>"
unfolding prog.p2s.action spec.interference.cl.action
apply (rule refinement.pre_a[OF _ spec.rel.upper_lower_expansive])
apply (rule refinement.spec.bind[rotated])
 apply (rule refinement.spec.rel_mono[OF order.refl];
        fastforce simp: spec.term.all.rel spec.steps.rel
                 intro: sP antimonoD[OF stable.antimono_rel, unfolded le_bool_def, rule_format, rotated])
apply (strengthen ord_to_strengthen(1)[OF inf_le2])
apply (strengthen ord_to_strengthen(1)[OF refinement.spec.bind.res.rel_le[OF order.refl]])
apply (rule refinement.spec.bind[rotated, where Q'="\<lambda>v s. Q v s \<and> stable (spec.steps A `` {env}) (Q v)"])
 apply (rule refinement.spec.action;
        fastforce simp: spec.initial_steps.term.all spec.initial_steps.rel
             intro: assms)
apply (rule refinement.gen_asm)
 apply (rule refinement.spec.bind[rotated])
  apply (rule refinement.spec.rel_mono[OF order.refl];
         fastforce simp: spec.steps.term.all spec.rel.lower_upper_lower
                   elim: antimonoD[OF stable.antimono_rel, unfolded le_bool_def, rule_format, rotated]
                   dest: subsetD[OF spec.steps.refinement.spec.bind.res_le])
 apply (rule refinement.spec.return)
apply (simp only: spec.idle_le)
done

lemma return:
  assumes sQ: "stable (spec.steps A `` {env}) (Q v)"
  shows "prog.p2s (prog.return v) \<le> \<lbrace>Q v\<rbrace>, A \<tturnstile> prog.p2s (prog.return v), \<lbrace>Q\<rbrace>"
unfolding prog.return_def using assms by (blast intro: refinement.prog.action)

lemma invmap_return:
  assumes sQ: "stable (spec.steps A `` {env}) (Q v)"
  assumes "vf v = v'"
  shows "prog.p2s (prog.return v) \<le> \<lbrace>Q v\<rbrace>, A \<tturnstile> prog.p2s (prog.invmap sf vf (prog.return v')), \<lbrace>Q\<rbrace>"
unfolding prog.invmap.return
by (strengthen ord_to_strengthen(2)[OF prog.return.rel_le])
   (simp add: assms(2) refinement.pre_g[OF refinement.prog.return[where Q=Q, OF sQ]]
              SUP_upper prog.bind.return prog.p2s.mono)

lemma bind_abstract:
  fixes f :: "('s, 'v) prog"
  fixes f' :: "('s, 'v') prog"
  fixes g :: "'v \<Rightarrow> ('s, 'w) prog"
  fixes g' :: "'v' \<Rightarrow> ('s, 'w) prog"
  fixes vf :: "'v \<Rightarrow> 'v'"
  assumes "\<And>v. prog.p2s (g v) \<le> \<lbrace>Q' (vf v)\<rbrace>, refinement.spec.bind.res (spec.pre P \<sqinter> spec.term.all A \<sqinter> prog.p2s f') A (vf v) \<tturnstile> prog.p2s (g' (vf v)), \<lbrace>Q\<rbrace>"
  assumes "prog.p2s f \<le> \<lbrace>P\<rbrace>, spec.term.all A \<tturnstile> spec.vinvmap vf (prog.p2s f'), \<lbrace>\<lambda>v. Q' (vf v)\<rbrace>"
  shows "prog.p2s (f \<bind> g) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> prog.p2s (f' \<bind> g'), \<lbrace>Q\<rbrace>"
by (simp add: prog.p2s.simps refinement.spec.bind_abstract[OF assms])

lemma bind:
  assumes "\<And>v. prog.p2s (g v) \<le> \<lbrace>Q' v\<rbrace>, refinement.spec.bind.res (spec.pre P \<sqinter> spec.term.all A \<sqinter> prog.p2s f') A v \<tturnstile> prog.p2s (g' v), \<lbrace>Q\<rbrace>"
  assumes "prog.p2s f \<le> \<lbrace>P\<rbrace>, spec.term.all A \<tturnstile> prog.p2s f', \<lbrace>Q'\<rbrace>"
  shows "prog.p2s (f \<bind> g) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> prog.p2s (f' \<bind> g'), \<lbrace>Q\<rbrace>"
by (simp add: prog.p2s.simps refinement.spec.bind[OF assms])

lemmas rev_bind = refinement.prog.bind[rotated]

lemma Parallel:
  fixes A :: "(sequential, 's, unit) spec"
  fixes Q :: "'a \<Rightarrow> 's pred"
  fixes Ps :: "'a \<Rightarrow> ('s, unit) prog"
  fixes Ps' :: "'a \<Rightarrow> ('s, unit) prog"
  assumes "\<And>a. a \<in> as \<Longrightarrow> prog.p2s (Ps a) \<le> \<lbrace>P a\<rbrace>, refinement.spec.env_hyp P A as (prog.p2s \<circ> Ps') a \<tturnstile> prog.p2s (Ps' a), \<lbrace>\<lambda>rv. Q a\<rbrace>"
  shows "prog.p2s (prog.Parallel as Ps) \<le> \<lbrace>\<Sqinter>a\<in>as. P a\<rbrace>, A \<tturnstile> prog.p2s (prog.Parallel as Ps'), \<lbrace>\<lambda>rv. \<Sqinter>a\<in>as. Q a\<rbrace>"
using assms by transfer (simp add: refinement.spec.Parallel comp_def)

lemma parallel:
  assumes "prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, refinement.spec.env_hyp (\<lambda>a. if a then P\<^sub>1 else P\<^sub>2) A UNIV (\<lambda>a. if a then prog.p2s c\<^sub>1' else prog.p2s c\<^sub>2') True \<tturnstile> prog.p2s c\<^sub>1', \<lbrace>Q\<^sub>1\<rbrace>"
  assumes "prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, refinement.spec.env_hyp (\<lambda>a. if a then P\<^sub>1 else P\<^sub>2) A UNIV (\<lambda>a. if a then prog.p2s c\<^sub>1' else prog.p2s c\<^sub>2') False \<tturnstile> prog.p2s c\<^sub>2', \<lbrace>Q\<^sub>2\<rbrace>"
  shows "prog.p2s (prog.parallel c\<^sub>1 c\<^sub>2) \<le> \<lbrace>P\<^sub>1 \<^bold>\<and> P\<^sub>2\<rbrace>, A \<tturnstile> prog.p2s (prog.parallel c\<^sub>1' c\<^sub>2'), \<lbrace>\<lambda>v. Q\<^sub>1 v \<^bold>\<and> Q\<^sub>2 v\<rbrace>"
unfolding prog.parallel_alt_def
by (rule refinement.pre[OF refinement.prog.Parallel[where A="A" and P="\<lambda>a. if a then P\<^sub>1 else P\<^sub>2" and Ps'="\<lambda>a. if a then c\<^sub>1' else c\<^sub>2'" and Q="\<lambda>a. if a then Q\<^sub>1 () else Q\<^sub>2 ()"]])
   (use assms in \<open>force simp: if_distrib comp_def\<close>)+

setup \<open>Sign.parent_path\<close>


subsection\<open> A relational assume/guarantee program logic for the \<^emph>\<open>('s, 'v) prog\<close> lattice\label{sec:programs-ag} \<close>

text\<open>

Similarly we specialize the assume/guarantee program logic of
\S\ref{sec:refinement-ag} to \<^typ>\<open>('s, 'v) prog\<close>.

References:
 \<^item> \<^citet>\<open>"XudeRoeverHe:1997" and "deRoeverEtAl:2001"\<close>
 \<^item> \<^citet>\<open>\<open>\S7\<close> in "PrensaNieto:2003"\<close>
 \<^item> \<^citet>\<open>\<open>\S3\<close> in "Vafeiadis:2008"\<close>

\<close>

subsubsection\<open> Galois considerations\label{sec:programs-ag-galois} \<close>

text\<open>

For suitably stable \<open>P\<close>, \<open>Q\<close>, \<open>\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>\<close> is interference closed and hence denotes a
point in \<^typ>\<open>('s, 'v) prog\<close>. In other words we can replace programs with their specifications.

\<close>

setup \<open>Sign.mandatory_path "ag.prog"\<close>

lemma galois:
  shows "prog.p2s c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> \<longleftrightarrow> c \<le> prog.s2p (\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>)"
by (simp add: prog.p2s_s2p.galois ag.spec.term.none_inteference)

lemmas s2p_ag = iffD1[OF ag.prog.galois]

lemma p2s_s2p_ag:
  shows "prog.p2s (prog.s2p (\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>)) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: ag.prog.galois)

lemma p2s_s2p_ag_stable:
  assumes "stable A P"
  assumes "\<And>v. stable A (Q v)"
  shows "prog.p2s (prog.s2p (\<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>)) = \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
by (rule prog.p2s_s2p.insertion[OF spec.interference.closed_ag[where r=UNIV, simplified, OF assms]])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "prog.ag"\<close>

lemma bot[iff]:
  shows "prog.p2s \<bottom> \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: ag.prog.galois)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "ag"\<close>

setup \<open>Sign.mandatory_path "prog"\<close>

lemma sup_conv:
  shows "prog.p2s (c\<^sub>1 \<squnion> c\<^sub>2) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> \<longleftrightarrow> prog.p2s c\<^sub>1 \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace> \<and> prog.p2s c\<^sub>2 \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: prog.p2s.simps)

lemmas sup = iffD2[OF ag.prog.sup_conv, unfolded conj_explode]

lemma bind: \<comment>\<open> Assumptions in weakest-pre order \<close>
  assumes "\<And>v. prog.p2s (g v) \<le> \<lbrace>Q' v\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "prog.p2s f \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q'\<rbrace>"
  shows "prog.p2s (f \<bind> g) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
by (simp add: prog.p2s.simps) (rule ag.spec.bind; fact)

lemma action: \<comment>\<open> Conclusion is insufficiently instantiated for use \<close>
  fixes F :: "('v \<times> 's \<times> 's) set"
  assumes Q: "\<And>v s s'. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> Q v s'"
  assumes G: "\<And>v s s'. \<lbrakk>P s; s \<noteq> s'; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> (s, s') \<in> G"
  assumes sP: "stable A P"
  assumes sQ: "\<And>s s' v. \<lbrakk>P s; (v, s, s') \<in> F\<rbrakk> \<Longrightarrow> stable A (Q v)"
  shows "prog.p2s (prog.action F) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
unfolding prog.p2s.action spec.interference.cl.action \<comment>\<open> sp proof \<close>
by (rule ag.gen_asm
         ag.spec.bind[rotated] ag.spec.stable_interference ag.spec.return
         ag.spec.action[where Q="\<lambda>v s. Q v s \<and> (\<exists>s s'. P s \<and> (v, s, s') \<in> F)"]
   | use assms in auto)+

lemma guard:
  assumes "\<And>s. \<lbrakk>P s; g s\<rbrakk> \<Longrightarrow> Q () s"
  assumes "stable A P"
  assumes "stable A (Q ())"
  shows "prog.p2s (prog.guard g) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (fastforce simp: prog.guard_def intro: ag.prog.action split: if_splits)

lemma Parallel:
  assumes "\<And>a. a \<in> as \<Longrightarrow> prog.p2s (Ps a) \<le> \<lbrace>P a\<rbrace>, A \<union> (\<Union>a'\<in>as-{a}. G a') \<turnstile> G a, \<lbrace>\<lambda>v. Q a\<rbrace>"
  shows "prog.p2s (prog.Parallel as Ps) \<le> \<lbrace>\<Sqinter>a\<in>as. P a\<rbrace>, A \<turnstile> \<Union>a\<in>as. G a, \<lbrace>\<lambda>v. \<Sqinter>a\<in>as. Q a\<rbrace>"
using assms by transfer (fast intro: ag.spec.Parallel)

lemma parallel:
  assumes "prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, A \<union> G\<^sub>2 \<turnstile> G\<^sub>1, \<lbrace>Q\<^sub>1\<rbrace>"
  assumes "prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, A \<union> G\<^sub>1 \<turnstile> G\<^sub>2, \<lbrace>Q\<^sub>2\<rbrace>"
  shows "prog.p2s (prog.parallel c\<^sub>1 c\<^sub>2) \<le> \<lbrace>P\<^sub>1 \<^bold>\<and> P\<^sub>2\<rbrace>, A \<turnstile> G\<^sub>1 \<union> G\<^sub>2, \<lbrace>\<lambda>v. Q\<^sub>1 v \<^bold>\<and> Q\<^sub>2 v\<rbrace>"
unfolding prog.parallel_alt_def
by (rule ag.pre[OF ag.prog.Parallel[where A="A" and G="\<lambda>a. if a then G\<^sub>1 else G\<^sub>2" and P="\<langle>P\<^sub>1 \<^bold>\<and> P\<^sub>2\<rangle>" and Q="\<lambda>a. if a then Q\<^sub>1 () else Q\<^sub>2 ()"]])
   (use assms in \<open>auto intro: ag.pre_imp\<close>)

lemma return:
  assumes sQ: "stable A (Q v)"
  shows "prog.p2s (prog.return v) \<le> \<lbrace>Q v\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (auto simp: prog.return_def intro: ag.prog.action)

lemma "if":
  assumes "b \<Longrightarrow> prog.p2s c\<^sub>1 \<le> \<lbrace>P\<^sub>1\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<not>b \<Longrightarrow> prog.p2s c\<^sub>2 \<le> \<lbrace>P\<^sub>2\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "prog.p2s (if b then c\<^sub>1 else c\<^sub>2) \<le> \<lbrace>if b then P\<^sub>1 else P\<^sub>2\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (fastforce intro: ag.pre_ag)

lemma case_option:
  assumes "x = None \<Longrightarrow> prog.p2s none \<le> \<lbrace>P\<^sub>n\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<And>v. x = Some v \<Longrightarrow> prog.p2s (some v) \<le> \<lbrace>P\<^sub>s v\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_option none some x) \<le> \<lbrace>case x of None \<Rightarrow> P\<^sub>n | Some v \<Rightarrow> P\<^sub>s v\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (fastforce intro: ag.pre_ag split: option.split)

lemma case_sum:
  assumes "\<And>v. x = Inl v \<Longrightarrow> prog.p2s (left v) \<le> \<lbrace>P\<^sub>l v\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<And>v. x = Inr v \<Longrightarrow> prog.p2s (right v) \<le> \<lbrace>P\<^sub>r v\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_sum left right x) \<le> \<lbrace>case_sum P\<^sub>l P\<^sub>r x\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (fastforce intro: ag.pre_ag split: sum.split)

lemma case_list:
  assumes "x = [] \<Longrightarrow> prog.p2s nil \<le> \<lbrace>P\<^sub>n\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  assumes "\<And>v vs. x = v # vs \<Longrightarrow> prog.p2s (cons v vs) \<le> \<lbrace>P\<^sub>c v vs\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "prog.p2s (case_list nil cons x) \<le> \<lbrace>case_list P\<^sub>n P\<^sub>c x\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by (fastforce intro: ag.pre_ag split: list.split)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsubsection\<open> A proof of the parallel rule using Abadi and Plotkin's composition principle\label{sec:abadi_plotkin-parallel} \<close>

text\<open>

Here we show that the key rule for \<^const>\<open>prog.Parallel\<close> (@{thm [source] "ag.spec.Parallel"})
can be established using the @{thm [source] "spec.ag_circular"} rule (\S\ref{sec:abadi_plotkin}).

The following proof is complicated by the need to discard a lot of
contextual information.

\<close>

notepad
begin

have imp_discharge_leL1:
  "x' \<le> x \<Longrightarrow> x' \<sqinter> (x \<sqinter> y \<^bold>\<longrightarrow>\<^sub>H z) = x' \<sqinter> (y \<^bold>\<longrightarrow>\<^sub>H z)" for x x' y z
by (simp add: heyting.curry_conv heyting.discharge(1))

have LHS_rel:
   "{proc x} \<times> UNIV \<union> (-{proc x}) \<times> (A \<union> (Id \<union> \<Union> (G ` (as - {x}))))
  = ((-(proc ` as)) \<times> (A \<union> (Id \<union> \<Union> (G ` (as - {x}))))
      \<union> ({proc x} \<times> UNIV \<union> proc ` (as - {x}) \<times> (A \<union> (Id \<union> \<Union> (G ` (as - {x}))))))" for A G as x
by blast

have rel_agents_split:
  "spec.rel (as \<times> r \<union> s) = spec.rel (as \<times> r \<union> fst ` s \<times> UNIV) \<sqinter> spec.rel (as \<times> UNIV \<union> s)"
  if "fst ` s \<inter> as = {}" for as r s
using that by (fastforce simp: image_iff simp flip: spec.rel.inf intro: arg_cong[where f="spec.rel"])

\<comment>\<open> @{thm [source] ag.spec.Parallel} \<close>
fix as :: "'a set"
fix A :: "'s rel"
fix G :: "'a \<Rightarrow> 's rel"
fix P :: "'a \<Rightarrow> 's pred"
fix Q :: "'a \<Rightarrow> 's pred"
fix Ps :: "'a \<Rightarrow> (sequential, 's, unit) spec"
assume proc_ag: "\<And>a. a \<in> as \<Longrightarrow> Ps a \<le> \<lbrace>P a\<rbrace>, A \<union> (\<Union>a'\<in>as-{a}. G a') \<turnstile> G a, \<lbrace>\<lambda>v. Q a\<rbrace>"
have "spec.Parallel as Ps \<le> \<lbrace>\<Sqinter>a\<in>as. P a\<rbrace>, A \<turnstile> \<Union>a\<in>as. G a, \<lbrace>\<lambda>v. \<Sqinter>a\<in>as. Q a\<rbrace>" (is "?lhs \<le> ?rhs")
proof(cases "as = {}")
  case True then show ?thesis
    by (simp add: spec.Parallel.no_agents ag.interference_le)
next
  case False then show ?thesis
apply -
supply inf.bounded_iff[simp del] \<comment>\<open> preserve RHS \<close>

\<comment>\<open> replace \<open>Ps\<close> with a/g specs. guard against empty \<open>A\<close>, \<open>G\<close> \<close>
apply (strengthen ord_to_strengthen(1)[OF proc_ag], assumption)
apply (subst ag.reflcl_ag)
apply (strengthen ord_to_strengthen(2)[OF reflcl_cl.sup_cl_le])

\<comment>\<open> Circular concurrent reasoning \<close>
unfolding ag_def

\<comment>\<open> Move a/g hypotheses to LHS, normalize \<close>
apply (simp add: heyting ac_simps)

\<comment>\<open> Discharge \<open>spec.pre P\<close> \<close>
apply (subst inf_assoc[symmetric])
apply (subst inf_commute)
apply (subst inf_assoc)
apply (subst (2) inf_commute)
apply (subst spec.Parallel.inf_pre, assumption)
apply (simp add: ac_simps)
\<comment>\<open> Idiom for rewriting under a quantifier, here \<^const>\<open>spec.Parallel\<close> \<close>
apply (rule order.trans)
 apply (rule inf.mono[OF order.refl])
 apply (rule spec.Parallel.mono)
 apply (subst imp_discharge_leL1)
  apply (simp add: Inf_lower spec.pre.INF; fail)
 \<comment>\<open> Discard \<^const>\<open>spec.pre\<close> hypothesis \<close>
 apply (rule inf_le2)

\<comment>\<open> Move environment assumption \<open>A\<close> hypothesis under \<^const>\<open>spec.toSequential\<close> and the \<^const>\<open>Inf\<close> \<close>
unfolding spec.Parallel_def
apply (subst inf.commute)
apply (subst spec.map.inf_distr)
apply (subst spec.invmap.rel)
apply (simp add: ac_simps flip: INF_inf_const1)

\<comment>\<open> Eradicate \<^const>\<open>spec.toSequential\<close>: move to parallel space \<close>
apply (simp add: spec.map_invmap.galois spec.invmap.inf spec.invmap.post spec.invmap.rel
           flip: spec.term.all.invmap spec.term.all.map)

\<comment>\<open> Eradicate \<^const>\<open>spec.toConcurrent\<close> \<close>
apply (simp add: ac_simps spec.invmap.heyting spec.invmap.inf spec.invmap.rel
                 spec.invmap.pre spec.invmap.post)

\<comment>\<open> Normalize the relations \<close>
apply (simp add: inf_sup_distrib1 Times_Int_Times map_prod_vimage_Times ac_simps spec.rel.reflcl
           flip: spec.rel.inf image_Int inf.assoc)

\<comment>\<open> Discharge environment assumption \<open>A\<close> and that for agents in \<open>-as\<close> \<close>
apply (subst LHS_rel)
\<comment>\<open> Idiom for rewriting under a quantifier, here \<^const>\<open>Inf\<close> \<close>
apply (rule order.trans)
 apply (rule INF_mono[where B=as])
 apply (rule rev_bexI, assumption)
 apply (subst (2) rel_agents_split, fastforce)
 apply (subst imp_discharge_leL1)
  apply (rule spec.rel.mono, fastforce simp: image_Un)
 apply (rule order.refl)
apply (simp flip: sup.assoc Times_Un_distrib1)
apply (simp add: ac_simps INF_inf_const1)

\<comment>\<open> Apply Abadi/Plotkin \<close>

\<comment>\<open> Change coordinates \<close>
apply (subst INF_rename_bij[where X="proc ` as" and \<pi>="the_inv proc"])
 apply (fastforce simp: bij_betw_iff_bijections)
apply (simp add: image_comp cong: INF_cong)

\<comment>\<open> The circular reasoning principle only applies to the relational part as \<^const>\<open>spec.post\<close> is not termination closed.
    Therefore split the goal \<close>
apply (subst heyting.infR)
apply (subst INF_inf_distrib[symmetric])
apply (rule order.trans)
 apply (rule inf_mono[OF order.refl])+
 apply (rule order.trans[rotated])
  apply (rule spec.ag_circular[where
             as="proc ` as"
         and Ps="\<lambda>a. spec.rel ({a} \<times> (Id \<union> G (the_inv proc a)) \<union> insert env (proc ` (- {the_inv proc a})) \<times> UNIV)",
          simplified spec.idle_le spec.term.closed.rel, simplified,
          OF subsetD[OF spec.cam.closed.antimono spec.cam.closed.rel[OF order.refl]]])
  apply (clarsimp simp: image_iff)
  apply (metis ComplI agent.exhaust singletonD)
 apply (rule INFI)
 apply (simp add: heyting ac_simps flip: spec.rel.INF INF_inf_const1)
  \<comment>\<open> Idiom for rewriting under a quantifier, here \<^const>\<open>Inf\<close> \<close>
 apply (rule order.trans)
  apply (rule INF_mono[where B=as])
  apply (rule rev_bexI, assumption)
  apply (subst heyting.discharge)
   apply (rule spec.rel.mono_reflcl)
   apply fastforce
  apply (simp flip: spec.rel.inf)
  apply (rule order.refl)
 apply (simp flip: spec.rel.INF)
 apply (rule spec.rel.mono)
 apply (clarsimp simp: image_iff)
 apply (metis ComplI agent.exhaust singletonD)
apply (simp add: ac_simps flip: spec.rel.INF)
apply (subst inf.assoc[symmetric])
apply (simp flip: spec.rel.inf)

\<comment>\<open> Conclude guarantee \<open>G\<close> \<close>
apply (rule le_infI[rotated])
 apply (rule le_infI1)
 apply (rule spec.rel.mono_reflcl, blast)

\<comment>\<open> Conclude \<open>spec.post Q\<close> \<close>
apply (subst (2) INF_inf_const1[symmetric], force)
\<comment>\<open> Idiom for rewriting under a quantifier, here \<^const>\<open>Inf\<close> \<close>
apply (rule order.trans)
 apply (rule INF_mono[where B=as])
 apply (rule rev_bexI, blast)
 apply (subst heyting.discharge)
  apply (force intro: spec.rel.mono)
 apply (rule order.refl)
apply (simp add: spec.post.Ball flip: INF_inf_distrib)
done
qed

end


subsection\<open> Specification inhabitation\label{sec:programs-inhabitation} \<close>

setup \<open>Sign.mandatory_path "inhabits.prog"\<close>

lemma Sup:
  assumes "prog.p2s P -s, xs\<rightarrow> P'"
  assumes "P \<in> X"
  shows "prog.p2s (\<Squnion>X) -s, xs\<rightarrow> P'"
by (auto simp: prog.p2s.Sup intro: inhabits.Sup inhabits.supL assms)

lemma supL:
  assumes "prog.p2s P -s, xs\<rightarrow> P'"
  shows "prog.p2s (P \<squnion> Q) -s, xs\<rightarrow> P'"
by (simp add: prog.p2s.simps assms inhabits.supL)

lemma supR:
  assumes "prog.p2s Q -s, xs\<rightarrow> Q'"
  shows "prog.p2s (P \<squnion> Q) -s, xs\<rightarrow> Q'"
by (simp add: prog.p2s.simps assms inhabits.supR)

lemma bind:
  assumes "prog.p2s f -s, xs\<rightarrow> prog.p2s f'"
  shows "prog.p2s (f \<bind> g) -s, xs\<rightarrow> prog.p2s (f' \<bind> g)"
by (simp add: prog.p2s.simps inhabits.spec.bind assms)

lemma return:
  shows "prog.p2s (prog.return v) -s, []\<rightarrow> spec.return v"
by (metis prog.p2s.return inhabits.pre inhabits.tau[OF spec.idle.interference.cl_le]
          spec.interference.expansive)

lemma action_step:
  fixes F :: "('v \<times> 's \<times> 's) set"
  assumes "(v, s, s') \<in> F"
  shows "prog.p2s (prog.action F) -s, [(self, s')]\<rightarrow> prog.p2s (prog.return v)"
apply (simp only: prog.p2s.action prog.p2s.return spec.interference.cl.action spec.interference.cl.return)
apply (rule inhabits.pre[OF _ order.refl])
 apply (rule inhabits.spec.bind'[OF inhabits.spec.rel.term])
 apply (simp add: spec.bind.returnL spec.idle_le)
 apply (rule inhabits.spec.bind'[OF inhabits.spec.action.step])
  using assms apply force
 apply (simp add: spec.bind.returnL spec.idle_le)
 apply (rule inhabits.tau)
 apply (simp add: spec.idle_le)
apply simp
done

lemma action_stutter:
  fixes F :: "('v \<times> 's \<times> 's) set"
  assumes "(v, s, s) \<in> F"
  shows "prog.p2s (prog.action F) -s, []\<rightarrow> prog.p2s (prog.return v)"
apply (simp only: prog.p2s.action prog.p2s.return spec.interference.cl.action spec.interference.cl.return)
apply (rule inhabits.pre[OF _ order.refl])
 apply (rule inhabits.spec.bind'[OF inhabits.spec.rel.term])
 apply (simp add: spec.bind.returnL spec.idle_le)
 apply (rule inhabits.spec.bind'[OF inhabits.spec.action.stutter])
  using assms apply force
 apply (simp add: spec.bind.returnL spec.idle_le)
 apply (rule inhabits.tau)
 apply (simp add: spec.idle_le)
apply simp
done

lemma parallelL:
  assumes "prog.p2s P -s, xs\<rightarrow> prog.p2s P'"
  shows "prog.p2s (P \<parallel> Q) -s, xs\<rightarrow> prog.p2s (P' \<parallel> Q)"
by (simp add: prog.p2s.simps inhabits.spec.parallelL assms prog.p2s.interference_wind_bind)

lemma parallelR:
  assumes "prog.p2s Q -s, xs\<rightarrow> prog.p2s Q'"
  shows "prog.p2s (P \<parallel> Q) -s, xs\<rightarrow> prog.p2s (P \<parallel> Q')"
by (simp add: prog.p2s.simps inhabits.spec.parallelR assms prog.p2s.interference_wind_bind)

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
