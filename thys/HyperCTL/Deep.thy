section {* Deep representation of HyperCTL* -- syntax and semantics *}

(*<*)
theory Deep
imports Shallow "~~/src/HOL/Library/Infinite_Set"
begin
(*>*)

subsection{* Path variables and environments *}

datatype pvar = Pvariable (natOf : nat)

text {* Deeply embedded (syntactic) formulas *}

datatype 'aprop dfmla =
  Atom 'aprop pvar |
  Fls | Neg "'aprop dfmla" | Dis "'aprop dfmla" "'aprop dfmla" |
  Next "'aprop dfmla" | Until "'aprop dfmla" "'aprop dfmla" |
  Exi pvar "'aprop dfmla"

text{* Derived operators *}

definition "Tr \<equiv> Neg Fls"
definition "Con \<phi> \<psi> \<equiv> Neg (Dis (Neg \<phi>) (Neg \<psi>))"
definition "Imp \<phi> \<psi> \<equiv> Dis (Neg \<phi>) \<psi>"
definition "Eq \<phi> \<psi> \<equiv> Con (Imp \<phi> \<psi>) (Imp \<psi> \<phi>) "
definition "Fall p \<phi> \<equiv> Neg (Exi p (Neg \<phi>))"
definition "Ev \<phi> \<equiv> Until Tr \<phi>"
definition "Alw \<phi> \<equiv> Neg (Ev (Neg \<phi>))"
definition "Wuntil \<phi> \<psi> \<equiv> Dis (Until \<phi> \<psi>) (Alw \<phi>)"
definition "Fall2 p p' \<phi> \<equiv> Fall p (Fall p' \<phi>)"

lemmas der_Op_defs =
Tr_def Con_def Imp_def Eq_def Ev_def Alw_def Wuntil_def Fall_def Fall2_def

text{* Well-formed formulas are those that do not have a temporal operator
outside the scope of any quantifier -- indeed, in HyperCTL* such a situation does not make sense, 
since the temporal operators refer to previously introduced/quantified paths. *}

primrec wff :: "'aprop dfmla \<Rightarrow> bool" where
 "wff (Atom a p) = True"
|"wff Fls = True"
|"wff (Neg \<phi>) = wff \<phi>"
|"wff (Dis \<phi> \<psi>) = (wff \<phi> \<and> wff \<psi>)"
|"wff (Next \<phi>) = False"
|"wff (Until \<phi> \<psi>) = False"
|"wff (Exi p \<phi>) = True"


text {* The ability to pick a fresh variable *}

lemma finite_fresh_pvar:
assumes "finite (P :: pvar set)"
obtains p where "p \<notin> P"
proof-
  have "finite (natOf ` P)" by (metis assms finite_imageI)
  then obtain n where "n \<notin> natOf ` P" by (metis unbounded_k_infinite)
  hence "Pvariable n \<notin> P" by (metis imageI pvar.sel)
  thus ?thesis using that by auto
qed

definition getFresh :: "pvar set \<Rightarrow> pvar" where
"getFresh P \<equiv> SOME p. p \<notin> P"

lemma getFresh:
assumes "finite P" shows "getFresh P \<notin> P"
by (metis assms exE_some finite_fresh_pvar getFresh_def)


text {* The free-variables operator *}

primrec FV :: "'aprop dfmla \<Rightarrow> pvar set" where
 "FV (Atom a p) = {p}"
|"FV Fls = {}"
|"FV (Neg \<phi>) = FV \<phi>"
|"FV (Dis \<phi> \<psi>) = FV \<phi> \<union> FV \<psi>"
|"FV (Next \<phi>) = FV \<phi>"
|"FV (Until \<phi> \<psi>) = FV \<phi> \<union> FV \<psi>"
|"FV (Exi p \<phi>) = FV \<phi> - {p}"

text{* Environments *}

type_synonym env = "pvar \<Rightarrow> nat"

definition "eqOn P env env1 \<equiv> \<forall> p. p \<in> P \<longrightarrow> env p = env1 p"

lemma eqOn_Un[simp]:
"eqOn (P \<union> Q) env env1 \<longleftrightarrow> eqOn P env env1 \<and> eqOn Q env env1"
using assms unfolding eqOn_def by auto

lemma eqOn_update[simp]:
"eqOn P (env(p := \<pi>)) (env1(p := \<pi>)) \<longleftrightarrow> eqOn (P - {p}) env env1"
unfolding eqOn_def by auto

lemma eqOn_singl[simp]:
"eqOn {p} env env1 \<longleftrightarrow> env p = env1 p"
unfolding eqOn_def by auto


context Shallow
begin

subsection {* The semantic operator *}


text{* The semantics will interpret deep (syntactic) formulas as shallow formulas.
Recall that the latter are predicates on lists of paths -- the interpretation will
be parameterized by an environment mapping each path variable to a number indicating
the index (in the list) for the path denoted by the variable.

The semantics will only
be meaningful if the indexes of a formula's free variables are smaller than the length
of the path list -- we call this property ``compatibility''. *}

primrec sem :: "'aprop dfmla \<Rightarrow> env \<Rightarrow> ('state,'aprop) sfmla" where
 "sem (Atom a p) env = atom a (env p)"
|"sem Fls env = fls"
|"sem (Neg \<phi>) env = neg (sem \<phi> env)"
|"sem (Dis \<phi> \<psi>) env = dis (sem \<phi> env) (sem \<psi> env)"
|"sem (Next \<phi>) env = next (sem \<phi> env)"
|"sem (Until \<phi> \<psi>) env = until (sem \<phi> env) (sem \<psi> env)"
|"sem (Exi p \<phi>) env = exi (\<lambda> \<pi> \<pi>l. sem \<phi> (env(p := length \<pi>l)) (\<pi>l @ [\<pi>]))"

lemma sem_Exi_explicit:
"sem (Exi p \<phi>) env \<pi>l \<longleftrightarrow>
 (\<exists> \<pi>. wfp AP' \<pi> \<and> stateOf \<pi> = (if \<pi>l \<noteq> [] then stateOf (last \<pi>l) else s0) \<and>
       sem \<phi> (env(p := length \<pi>l)) (\<pi>l @ [\<pi>]))"
unfolding sem.simps
unfolding exi_def ..

lemma sem_derived[simp]:
 "sem Tr env = tr"
 "sem (Con \<phi> \<psi>) env = con (sem \<phi> env) (sem \<psi> env)"
 "sem (Imp \<phi> \<psi>) env = imp (sem \<phi> env) (sem \<psi> env)"
 "sem (Eq \<phi> \<psi>) env = eq (sem \<phi> env) (sem \<psi> env)"
 "sem (Fall p \<phi>) env = fall (\<lambda> \<pi> \<pi>l. sem \<phi> (env(p := length \<pi>l)) (\<pi>l @ [\<pi>]))"
 "sem (Ev \<phi>) env = ev (sem \<phi> env)"
 "sem (Alw \<phi>) env = alw (sem \<phi> env)"
 "sem (Wuntil \<phi> \<psi>) env = wuntil (sem \<phi> env) (sem \<psi> env)"
unfolding der_Op_defs der_op_defs by (auto simp: neg_def[abs_def])

lemma sem_Fall2[simp]:
"sem (Fall2 p p' \<phi>) env =
 fall2 (\<lambda> \<pi>' \<pi> \<pi>l. sem \<phi> (env (p := length \<pi>l, p' := Suc(length \<pi>l))) (\<pi>l @ [\<pi>,\<pi>']))"
unfolding Fall2_def fall2_def by (auto simp add: fall_def exi_def[abs_def] neg_def[abs_def])


text{* Compatibility of a pair (environment,path list) on a set of variables means
no out-or-range references: *}

definition "cpt P env \<pi>l \<equiv> \<forall> p \<in> P. env p < length \<pi>l"

lemma cpt_Un[simp]:
"cpt (P \<union> Q) env \<pi>l \<longleftrightarrow> cpt P env \<pi>l \<and> cpt Q env \<pi>l"
using assms unfolding cpt_def by auto

lemma cpt_singl[simp]:
"cpt {p} env \<pi>l \<longleftrightarrow> env p < length \<pi>l"
unfolding cpt_def by auto

lemma cpt_map_stl[simp]:
"cpt P env \<pi>l \<Longrightarrow> cpt P env (map stl \<pi>l)"
unfolding cpt_def by auto


text {* Next we prove that the semantics of well-formed formulas only depends on the interpretation
of the free variables of a formula and on the current state of the last recorded path --
we call the latter the ``pointer'' of the path list. *}

fun pointerOf :: "('state,'aprop) path list \<Rightarrow> 'state" where
"pointerOf \<pi>l = (if \<pi>l \<noteq> [] then stateOf (last \<pi>l) else s0)"

text{* Equality of two pairs (environment,path list) on a set of variables: *}

definition eqOn ::
"pvar set \<Rightarrow> env \<Rightarrow> ('state,'aprop) path list \<Rightarrow> env \<Rightarrow> ('state,'aprop) path list \<Rightarrow> bool"
where
"eqOn P env \<pi>l env1 \<pi>l1 \<equiv> \<forall> p. p \<in> P \<longrightarrow> \<pi>l!(env p) = \<pi>l1!(env1 p)"

lemma eqOn_Un[simp]:
"eqOn (P \<union> Q) env \<pi>l env1 \<pi>l1 \<longleftrightarrow> eqOn P env \<pi>l env1 \<pi>l1 \<and> eqOn Q env \<pi>l env1 \<pi>l1"
using assms unfolding eqOn_def by auto

lemma eqOn_singl[simp]:
"eqOn {p} env \<pi>l env1 \<pi>l1 \<longleftrightarrow> \<pi>l!(env p) = \<pi>l1!(env1 p)"
unfolding eqOn_def by auto

lemma eqOn_map_stl[simp]:
"cpt P env \<pi>l \<Longrightarrow> cpt P env1 \<pi>l1 \<Longrightarrow>
 eqOn P env \<pi>l env1 \<pi>l1 \<Longrightarrow> eqOn P env (map stl \<pi>l) env1 (map stl \<pi>l1)"
unfolding eqOn_def cpt_def by auto

lemma cpt_map_sdrop[simp]:
"cpt P env \<pi>l \<Longrightarrow> cpt P env (map (sdrop i) \<pi>l)"
unfolding cpt_def by auto

lemma cpt_update[simp]:
assumes "cpt (P - {p}) env \<pi>l"
shows "cpt P (env(p := length \<pi>l)) (\<pi>l @ [\<pi>])"
using assms unfolding cpt_def by simp (metis Diff_iff less_SucI singleton_iff)

lemma eqOn_map_sdrop[simp]:
"cpt V env \<pi>l \<Longrightarrow> cpt V env1 \<pi>l1 \<Longrightarrow>
 eqOn V env \<pi>l env1 \<pi>l1 \<Longrightarrow> eqOn V env (map (sdrop i) \<pi>l) env1 (map (sdrop i) \<pi>l1)"
unfolding eqOn_def cpt_def by auto

lemma eqOn_update[simp]:
assumes "cpt (P - {p}) env \<pi>l" and "cpt (P - {p}) env1 \<pi>l1"
shows
"eqOn P (env(p := length \<pi>l)) (\<pi>l @ [\<pi>]) (env1(p := length \<pi>l1)) (\<pi>l1 @ [\<pi>])
 \<longleftrightarrow>
 eqOn (P - {p}) env \<pi>l env1 \<pi>l1"
using assms unfolding eqOn_def cpt_def by simp (metis DiffI nth_append singleton_iff)

lemma eqOn_FV_sem_NE:
assumes "cpt (FV \<phi>) env \<pi>l" and "cpt (FV \<phi>) env1 \<pi>l1" and "eqOn (FV \<phi>) env \<pi>l env1 \<pi>l1"
and "\<pi>l \<noteq> []" and "\<pi>l1 \<noteq> []" and "last \<pi>l = last \<pi>l1"
shows "sem \<phi> env \<pi>l = sem \<phi> env1 \<pi>l1"
using assms proof (induction \<phi> arbitrary: env \<pi>l env1 \<pi>l1)
  case (Until \<phi> \<psi> env \<pi>l env1 \<pi>l1)
  hence "\<And> i. sem \<phi> env (map (sdrop i) \<pi>l) = sem \<phi> env1 (map (sdrop i) \<pi>l1) \<and>
              sem \<psi> env (map (sdrop i) \<pi>l) = sem \<psi> env1 (map (sdrop i) \<pi>l1)"
  using Until by (auto simp: last_map)
  thus ?case by (auto simp: op_defs)
next
  case (Exi p \<phi> env \<pi>l env1 \<pi>l1)
  hence 1:
  "\<And> \<pi>. cpt (FV \<phi>) (env(p := length \<pi>l)) (\<pi>l @ [\<pi>]) \<and>
         cpt (FV \<phi>) (env1(p := length \<pi>l1)) (\<pi>l1 @ [\<pi>]) \<and>
         eqOn (FV \<phi>) (env(p := length \<pi>l)) (\<pi>l @ [\<pi>]) (env1(p := length \<pi>l1)) (\<pi>l1 @ [\<pi>])"
  by simp_all
  thus ?case unfolding sem.simps exi_def using Exi
  by (intro iff_exI) (metis append_is_Nil_conv last_snoc)
qed(auto simp: last_map op_defs)

text{* The next theorem states that the semantics of a formula on an environment
and a list of paths only depends on the pointer of the list of paths.
 *}

theorem eqOn_FV_sem:
assumes "wff \<phi>" and "pointerOf \<pi>l = pointerOf \<pi>l1"
and "cpt (FV \<phi>) env \<pi>l" and "cpt (FV \<phi>) env1 \<pi>l1" and "eqOn (FV \<phi>) env \<pi>l env1 \<pi>l1"
shows "sem \<phi> env \<pi>l = sem \<phi> env1 \<pi>l1"
using assms proof (induction \<phi> arbitrary: env \<pi>l env1 \<pi>l1)
  case (Until \<phi> \<psi> env \<pi>l env1 \<pi>l1)
  hence "\<And> i. sem \<phi> env (map (sdrop i) \<pi>l) = sem \<phi> env1 (map (sdrop i) \<pi>l1) \<and>
              sem \<psi> env (map (sdrop i) \<pi>l) = sem \<psi> env1 (map (sdrop i) \<pi>l1)"
  using Until by (auto simp: last_map)
  thus ?case by (auto simp: op_defs)
next
  case (Exi p \<phi> env \<pi>l env1 \<pi>l1)
  have "\<And> \<pi>. sem \<phi> (env(p := length \<pi>l)) (\<pi>l @ [\<pi>]) =
             sem \<phi> (env1(p := length \<pi>l1)) (\<pi>l1 @ [\<pi>])"
  apply(rule eqOn_FV_sem_NE) using Exi by auto
  thus ?case unfolding sem.simps exi_def using Exi by (intro iff_exI conj_cong) simp_all
qed(auto simp: last_map op_defs)

corollary FV_sem:
assumes "wff \<phi>" and "\<forall> p \<in> FV \<phi>. env p = env1 p"
and "cpt (FV \<phi>) env \<pi>l" and "cpt (FV \<phi>) env1 \<pi>l"
shows "sem \<phi> env \<pi>l = sem \<phi> env1 \<pi>l"
apply(rule eqOn_FV_sem)
using assms unfolding eqOn_def by auto

text{* As a consequence, the interpretation of a closed formula (i.e., a formula
with no free variables) will not depend on the environment and, from the
list of paths, will only depend on its pointer: *}

corollary interp_closed:
assumes "wff \<phi>" and "FV \<phi> = {}" and "pointerOf \<pi>l = pointerOf \<pi>l1"
shows "sem \<phi> env \<pi>l = sem \<phi> env1 \<pi>l1"
apply(rule eqOn_FV_sem)
using assms unfolding eqOn_def cpt_def by auto


text{* Therefore, it makes sense to define the interpretation of a closed formula
by choosing any environment and any list of paths such that its pointer is the initial state
(e.g., the empty list) -- knowing that the choices are irrelevant. *}

definition "semClosed \<phi> \<equiv> sem \<phi> (any::env) (SOME \<pi>l. pointerOf \<pi>l = s0)"

lemma semClosed:
assumes \<phi>: "wff \<phi>" "FV \<phi> = {}" and p: "pointerOf \<pi>l = s0"
shows "semClosed \<phi> = sem \<phi> env \<pi>l"
proof-
  have "pointerOf (SOME \<pi>l. pointerOf \<pi>l = s0) = s0"
  by (rule someI[of _ "[]"]) simp
  thus ?thesis unfolding semClosed_def using interp_closed[OF \<phi>] p by auto
qed

lemma semClosed_Nil:
assumes \<phi>: "wff \<phi>" "FV \<phi> = {}"
shows "semClosed \<phi> = sem \<phi> env []"
using assms semClosed by auto



subsection{* The conjunction of a finite set of formulas *}


text{* This is defined by making the set into a list (by choosing any ordering of the
elements) and iterating binary conjunction. *}

definition Scon :: "'aprop dfmla set \<Rightarrow> 'aprop dfmla" where
"Scon \<phi>s \<equiv> foldr Con (asList \<phi>s) Tr"

lemma sem_Scon[simp]:
assumes "finite \<phi>s"
shows "sem (Scon \<phi>s) env = scon ((\<lambda> \<phi>. sem \<phi> env) ` \<phi>s)"
proof-
  def \<phi>l \<equiv> "asList \<phi>s"
  have "sem (foldr Con \<phi>l Tr) env = scon ((\<lambda> \<phi>. sem \<phi> env) ` (set \<phi>l))"
  by (induct \<phi>l) (auto simp: scon_def)
  thus ?thesis unfolding \<phi>l_def Scon_def by (metis assms set_asList)
qed

lemma FV_Scon[simp]:
assumes "finite \<phi>s"
shows "FV (Scon \<phi>s) = \<Union> (FV ` \<phi>s)"
proof-
  def \<phi>l \<equiv> "asList \<phi>s"
  have "FV (foldr Con \<phi>l Tr) = \<Union> (set (map FV \<phi>l))"
  apply(induct \<phi>l) by (auto simp: der_Op_defs)
  thus ?thesis unfolding \<phi>l_def Scon_def by (metis assms set_map set_asList)
qed



(*<*)
end (* context Shallow  *)
(*>*)

text{* end-of-context Shallow  *}


(*<*)
end
(*>*)
