(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
 *
 * This file       : Examples Related to Numerical Series and State-based Modeling
 *
 * Copyright (c) 2025 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter\<open>Annex: A Note on State-based Processes in HOL-CSP\<close>

theory    "FunSeriesInHOL-CSP"
  imports "HOL-CSP" "HOL.Transcendental" "GenFixrec-HOLCF"
begin

text\<open>This section is intended to give an intuition to the power of HOL-CSP processes by a set 
of examples. In our view, it can be stated that HOL-CSP are a more powerful modeling instrument
for indefinite behavior than, for example, co-inductive definitions, since they posses a theory
of synchronisation and monadic sequential composition that co-inductively defined streams lack.
On the other hand, there is no denying that the entire machinery is more complex. 
\<close>

section\<open>The 'Random' Key-Generator\<close>

subsection\<open>Example for the basic Construction with \<open>\<mu>\<close>\<close>


abbreviation key_generator_fun :: \<open>('\<alpha> set \<Rightarrow> '\<alpha> process) \<Rightarrow> ('\<alpha> set \<Rightarrow> '\<alpha> process)\<close>
  where \<open>key_generator_fun X A \<equiv> \<sqinter>a \<in> A \<rightarrow> X (A - {a})\<close>

definition key_generator :: \<open>'\<alpha> set \<Rightarrow> '\<alpha> process\<close> (\<open>KEY\<close>)
  where   \<open>key_generator \<equiv> \<mu> X. (\<lambda> A. \<sqinter>a \<in> A \<rightarrow> X (A - {a}))\<close>

lemma key_generator_fun_cont[simp]: \<open>cont key_generator_fun\<close>
  by (simp add: cont_fun)

lemma key_generator_unfold: \<open>KEY A = \<sqinter>a \<in> A \<rightarrow> KEY (A - {a})\<close>
  by (subst cont_process_rec[OF key_generator_def[THEN meta_eq_to_obj_eq]]) simp_all


text\<open>Now, the process \<^term>\<open>KEY \<nat>\<close> denotes the set of all traces that enumerate the natural
numbers without repetition... \<close>

subsection\<open>Example in High-level Notation\<close>

text\<open>The \<open>Fixrec ... where ...\<close> notation provided by the generic fixpoint-support package
has the same effect as the construction above:\<close>

Fixrec keygen ::"'\<alpha> set \<Rightarrow> '\<alpha> process" where kg_rec :  "keygen A =  (\<sqinter>a \<in> A \<rightarrow> keygen (A - {a}))"


section\<open>Cauchy-Series as Processes\<close>

subsection\<open>The Construction in basic Steps (Again)\<close>

text\<open>It is kind of fun - but also instructive wrt. the power and generality of the process type -
to see Cauchy-sequences of numerical approximations in the number system with base 10 as processes.
This shows that processes in HOL-CSP are not finite, not rational, but transcendent objects with
a non-enumerable cardinality.  
\<close>

definition digits :: \<open>real \<Rightarrow> int process\<close> 
  where   \<open>digits \<equiv> \<mu> X. (\<lambda>x. \<lfloor>x\<rfloor> \<rightarrow> X ((frac x) * 10)) \<close>

lemma digits_unfold: \<open>digits x = \<lfloor>x\<rfloor> \<rightarrow> digits (frac x * 10)\<close>
  apply (subst cont_process_rec[OF digits_def[THEN meta_eq_to_obj_eq]])
  by (simp add: cont_fun)(simp)

text\<open> Note that the floor function \<open>\<lfloor>x\<rfloor>\<close> yields the largest integer smaller or equal \<open>x\<close>, while
\<open>frac x\<close> returns the rest between \<open>\<lfloor>x\<rfloor>\<close> and \<open>x\<close>.

Now, the process \<^term>\<open>digits pi\<close> enumerates the representation at base 10 of the
transcendental number \<open>\<pi>\<close>, so: \<open>3 \<rightarrow> 1 \<rightarrow> 4 \<rightarrow> 1 \<rightarrow> 5 \<rightarrow> 9 \<rightarrow>  ...\<close>, while
while \<^term>\<open>digits (exp (1::real))\<close> does the same for the transcendental number \<open>e\<close>. 
While these two perfectly well-defined mathematical objects imported from the
\<^theory>\<open>HOL.Transcendental\<close> theory have as such no computational content, their approximation
by a HOL-CSP process has. Although we do not yet have a code-generator that shows this... ;-)\<close>

subsection\<open>The Example again in High-level Notation\<close>

text\<open>The \<open>Fixrec\<close>-package supports this construction directly: \<close>
Fixrec digits' ::"real \<Rightarrow> int process" 
  where digits'_rec :  "digits' x = \<lfloor>x\<rfloor> \<rightarrow> digits' (frac x * 10)"

section\<open>The Collatz-Function as Process\<close>

text\<open>Note that the Collatz function is unknown to be terminating; a standard definition in HOL 
via the recursive function definitions such as @{command primrec} or  @{command fun} is therefore 
out of reach. This example shows, however, that it is perfectly possible to represent the Collatz 
process as a recursive HOL-CSP process, since HOL-CSP is built for modeling potentially 
non-terminating computations. \<close>

abbreviation Even where "Even \<equiv> Collect even"  \<comment> \<open>the set of even numbers\<close>
abbreviation Odd where  "Odd \<equiv> Collect odd"     \<comment> \<open>the set of odd numbers\<close>
abbreviation Div3 where "Div3 \<equiv> {x. x mod 3 = 0}"

text\<open>We use the deterministic choice to express a case-distinction:\<close>

Fixrec  Collatz ::"nat \<Rightarrow> nat process" 
  where Collatz_rec :  "Collatz n =  (\<box>x \<in> ({0, 1} \<inter> {n}) \<rightarrow> Skip)
                                   \<box> (\<box>x \<in> ((Even - {0}) \<inter> {n}) \<rightarrow> Collatz (x div 2  ))
                                   \<box> (\<box>x \<in> ((Odd  - {1}) \<inter> {n}) \<rightarrow> Collatz (3 * x + 1))"

section\<open>True Concurrent Evolution of States.\<close>

text\<open>It is a common misconception of CSP that it can not handle "true-concurrent' computations 
given that its fundamental concept of \<^emph>\<open>events\<close>: They are "indivisible obervations on a specific 
time-point". However, the contrary is the case: Since HOL-CSP allows for modeling non-determinism
and potentially infinite states,  
true-concurrent calculations over non-overlapping parts of a state are possible
between synchronisation points. If portions of a state are overlapping and computations do not
agree --- so: races will occur --- then these situations are represented in HOL-CSP as deadlock. \<close>

Fixrec  Twos\<^sub>L :: \<open>nat \<Rightarrow> (nat \<times> nat) process\<close>
  where Twos\<^sub>L_unfold: \<open>Twos\<^sub>L n\<^sub>1 =  (\<box>\<sigma> \<in> ({n\<^sub>1<..} \<inter> Even) \<times> UNIV \<rightarrow> Twos\<^sub>L (fst \<sigma>))\<close>

Fixrec Threes\<^sub>R :: \<open>nat \<Rightarrow> (nat \<times> nat) process\<close>
  where  Threes\<^sub>R_unfold: \<open>Threes\<^sub>R n\<^sub>2 = (\<box>\<sigma> \<in> UNIV \<times> ({n\<^sub>2<..} \<inter> Div3) \<rightarrow> Threes\<^sub>R (snd \<sigma>))\<close>


text\<open>These two processes work on a state \<open>\<sigma>\<close>, consisting of a pair of two counters \<open>n\<^sub>1\<close> and \<open>n\<^sub>2\<close>.
While \<^const>\<open>Twos\<^sub>L\<close> choses an even number larger than its current local state \<open>n\<^sub>1\<close>,  \<^const>\<open>Threes\<^sub>R\<close>
chooses a number devisable by three larger than its current local state \<open>n\<^sub>2\<close>. Putting these two
together via:

     @{term [indent=10, margin=60]\<open>Twos\<^sub>L 0 \<lbrakk>Id\<rbrakk>  Threes\<^sub>R 0\<close>}

... where \<^term>\<open>Id\<close> is the identity relation, this synchronization over these two processes 
calculate independently two values but have to agree on a joint state. A trace of this combined 
processes is,  for example:
 
     @{cartouche [indent=10, margin=60]\<open>(2,6) \<rightarrow> (24,24) \<rightarrow> (16,33) \<rightarrow> ... \<close>}

Of course, this example is a bit simplistic since the the global state \<open>\<sigma>=(n\<^sub>1,n\<^sub>2)\<close> has a simple 
structure, the access to the global variables is distinct and the underlying choices are deter-
ministic, so to speak, \<^emph>\<open>angelic\<close>. An obvious generalization of this handling of the common state 
are algebraic lenses as provided by the theory \<^verbatim>\<open>Optics\<close> in the AFP. Wrt. to the choice, one might
model a more aggressive, i.e. \<^emph>\<open>demonic\<close> behaviour as follows: \<close>

Fixrec Twos\<^sub>L' :: \<open>nat \<Rightarrow> (nat \<times> nat) process\<close>
  where Twos\<^sub>L'_unfold: \<open>Twos\<^sub>L' n\<^sub>1 = (\<sqinter>\<sigma> \<in> ({n\<^sub>1<..} \<inter> Even) \<times> UNIV \<rightarrow> Twos\<^sub>L' (fst \<sigma>))\<close>

Fixrec Threes\<^sub>R' :: \<open>nat \<Rightarrow> (nat \<times> nat) process\<close>
  where Threes\<^sub>R'_unfold: \<open>Threes\<^sub>R' n\<^sub>2 = (\<sqinter>\<sigma> \<in> UNIV \<times> ({n\<^sub>2<..} \<inter> Div3) \<rightarrow> Threes\<^sub>R' (snd \<sigma>))\<close>

text\<open>The intersection may again be defined via:

     @{term [indent=10, margin=60]\<open>Twos\<^sub>L' 0 \<lbrakk>Id\<rbrakk> Threes\<^sub>R' 0\<close>} 

but the traces of this combined process will contain explicit deadlocks on all places
where an agreement could not be reached due to "ruthless behaviour" demonic processes that
chose deviant values from each other... Which means that races occurred. \<close>

text\<open>One might want to prove these facts, i.e. that the synchronized processes produce only
streams enjoying the conjunction of the devisability properties and the agreement is angelic 
or demonic. This is not too hard to do in HOL-CSP. The handy recursive equations needed for this,
e.g. @{thm [source] Twos\<^sub>L_unfold} and @{thm [source] Threes\<^sub>R'_unfold}, are provided by the 
\<open>Fixrec\<close>-package, as well as the fixpoint definitions @{thm [source] Twos\<^sub>L_rec_def} etc. 
that allow for fixpoint induction.\<close>

text\<open>And there we go: We state that \<^const>\<open>Twos\<^sub>L\<close> and \<^const>\<open>Threes\<^sub>R\<close> in parallel composition
are the same to a process that does these computations in one step. The proof proceeds by breaking
the stated equality into two \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>-refinements that were each proven by fixpoint-induction.\<close>


lemma parallel_exec :\<open>(Twos\<^sub>L (fst \<sigma>) ||  Threes\<^sub>R (snd \<sigma>)) 
        = ((\<mu> X. (\<lambda>(n\<^sub>1, n\<^sub>2). (\<box>\<sigma> \<in>((({n\<^sub>1<..} \<inter> Even )\<times>({n\<^sub>2<..} \<inter> Div3))) \<rightarrow> X \<sigma>)))\<sigma>)\<close>
      (is "?lhs \<sigma> = (fix \<cdot> ?rhs) \<sigma>")
  proof (rule FD_antisym)
    show \<open> ?lhs \<sigma> \<sqsubseteq>\<^sub>F\<^sub>D (fix \<cdot> ?rhs)(\<sigma>)\<close> for \<sigma>
      unfolding Twos\<^sub>L_def Twos\<^sub>L_rec_def Threes\<^sub>R_def Threes\<^sub>R_rec_def
    proof - 
      have * : \<open>adm (\<lambda>x. \<forall>xa.     fst x (fst xa) || snd x (snd xa)
                              \<sqsubseteq>\<^sub>F\<^sub>D (\<mu> x. (\<lambda>(n\<^sub>1, n\<^sub>2). Mprefix (({n\<^sub>1<..} \<inter> Even) 
                                                             \<times> ({n\<^sub>2<..} \<inter> Div3)) x)) xa)\<close>
        apply(rule adm_all,rule le_FD_adm_cont) 
        by (simp_all add: cont2cont_fun)
      have ** : \<open>   ({a<..} \<inter> Even) \<times> UNIV \<inter> UNIV \<times> ({b<..} \<inter> Div3) 
                  = ({a<..} \<inter> Even) \<times> ({b<..} \<inter> Div3)\<close> for a b::nat
        by (simp add: Times_Int_Times)   
      show \<open>   (\<mu> x. (\<lambda>n\<^sub>1. \<box>\<sigma>\<in>({n\<^sub>1<..} \<inter> Even) \<times> UNIV \<rightarrow> x (fst \<sigma>))) (fst \<sigma>) 
            || (\<mu> x. (\<lambda>n\<^sub>2. \<box>\<sigma>\<in>UNIV \<times> ({n\<^sub>2<..} \<inter> Div3) \<rightarrow> x (snd \<sigma>))) (snd \<sigma>) \<sqsubseteq>\<^sub>F\<^sub>D (fix \<cdot> ?rhs)(\<sigma>) \<close>
            (is "(fix \<cdot> ?lhs1)(fst \<sigma>)  || (fix \<cdot> ?lhs2)(snd \<sigma>) \<sqsubseteq>\<^sub>F\<^sub>D  _ ")
      apply(induct arbitrary:"\<sigma>"  rule: parallel_fix_ind [where F = \<open>?lhs1\<close> and G = \<open>?lhs2\<close>]) 
        using * apply auto 
        apply(subst Mprefix_Par_Mprefix)
        using ** apply(auto)
        apply(subst cont_process_rec [where P = \<open>fix \<cdot> ?rhs\<close> ]) apply(rule refl) apply(auto)
        by(rule mono_Mprefix_FD)  force 
  qed
    next
    show \<open>(fix \<cdot> ?rhs) \<sigma> \<sqsubseteq>\<^sub>F\<^sub>D ?lhs \<sigma>\<close> for \<sigma>
      apply(induct arbitrary:"\<sigma>"  rule: fix_ind  [where F = \<open>?rhs\<close>], auto)
      apply(subst Twos\<^sub>L_unfold, subst Threes\<^sub>R_unfold) 
      apply(subst Mprefix_Sync_Mprefix_subset, simp_all)
      by (metis (no_types, lifting) Sigma_cong Times_Int_Times inf_top.right_neutral 
                inf_top_left mono_Mprefix_FD surjective_pairing)
  qed


text\<open>Of course, we could use this modeling technique --- which is roughly similar to the conjunction
of two preconditions --- by adding a process that ensures that first and second component of 
the joint agree in their value, that is: 

     @{cartouche [indent=10, margin=60]\<open>(6,6) \<rightarrow> (24,24) \<rightarrow> (36,36) \<rightarrow> ... \<close>}

We bind the combined process to the constant \<open>Join\<close>:
\<close>

Fixrec Join :: \<open>nat \<times> nat \<Rightarrow> (nat \<times> nat) process\<close>
  where Join_unfold: \<open>Join (n\<^sub>1, n\<^sub>2) = (\<box>\<sigma> \<in> ({n\<^sub>1<..} \<inter> Even) \<times> ({n\<^sub>2<..} \<inter> Div3) \<rightarrow> Join \<sigma>)\<close>

text\<open>With \<^const>\<open>Join\<close>, the statement of @{thm [source] parallel_exec} reads:\<close>

corollary parallel_exec_Join: \<open>(Twos\<^sub>L (fst \<sigma>) || Threes\<^sub>R (snd \<sigma>)) = Join \<sigma>\<close>
  unfolding Join_def Join_rec_def by (fact parallel_exec)

text\<open>... which is set under the constraint as follows:

     \<^term>\<open> Join \<sigma> || (\<mu> X . (\<lambda>\<sigma>. \<box>\<sigma>\<in>Id \<rightarrow> X \<sigma>)) \<sigma> \<close>

We refrain from a formal proof which will follow the lines of @{thm "parallel_exec"}.\<close>

end
