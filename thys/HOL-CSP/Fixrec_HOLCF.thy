(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - Seeing Processes as a Scott Space
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : HOLCF instance and Conceptual tests of the generic Fixrec package 
 *
 * Copyright (c) 2025/26 Université Paris-Saclay, France
 ******************************************************************************\<close>
(*>*)

chapter \<open>The HOLCF Instance of \<^verbatim>\<open>Fixrec\<close>\<close>

theory Fixrec_HOLCF
  imports "GenFixrec-HOLCF"
begin

section\<open>The Instance Setup\<close>

text \<open>The tests are organised by concept; currently, there are instances of the generic Fixrec
package for Scott-Spaces (formalised in the library session HOLCF) and Restriction Spaces (RS).
Expected failures are checked by \<open>expect_failure\<close>, which runs the command semantics on the 
current theory and asserts that it fails with a message containing a given fragment.\<close>

ML \<open>
fun expect_failure langs vars eqns fragment =
  let val spec = (map (fn (n, T) => (Binding.name n, SOME T, NoSyn)) vars,
                  map (fn (n, e) => (false, ((Binding.name n, []), e))) eqns)
      val msg_of = Protocol_Message.clean_output o Runtime.exn_message
  in case Exn.result (GenFixrec.add_fixrec_langs_global (map (rpair Position.none) langs) spec)
                     (Context.the_global_context ()) of
       Exn.Res _   => error ("expected failure, but Fixrec succeeded: " ^ commas langs)
     | Exn.Exn exn => if String.isSubstring fragment (msg_of exn) then ()
                      else error ("unexpected failure message:\n" ^ msg_of exn)
  end
\<close>


section \<open>Language Selection\<close>

text \<open>A language that always fails to prove the fixpoint unfolding; used to test fallback.\<close>

setup \<open>fn thy => Context.Theory thy
   |> GenFixrec.update_language (Binding.make ("BROKEN", \<^here>))
        {mk_fix = #mk_fix HOLCF_instance.holcf, dest_fix = #dest_fix HOLCF_instance.holcf, lambda' = #lambda' HOLCF_instance.holcf,
         apply = #apply HOLCF_instance.holcf, shift_tac = #shift_tac HOLCF_instance.holcf, fix_tac = K no_tac,
         proj_tac = #proj_tac HOLCF_instance.holcf, fixind_tac = #fixind_tac HOLCF_instance.holcf}
   |> Context.the_theory\<close>

text \<open>Without brackets, \<open>HOLCF\<close> is the default:\<close>
Fixrec l1 :: \<open>int process\<close> where l1_eq : \<open>l1 = 1 \<rightarrow> l1\<close>

text \<open>Explicit selection:\<close>
Fixrec [HOLCF] l2 :: \<open>int process\<close> where l2_eq : \<open>l2 = 2 \<rightarrow> l2\<close>

text \<open>Languages are tried from left to right; the first one that succeeds is taken:\<close>
Fixrec [BROKEN, HOLCF] l3 :: \<open>int process\<close> where l3_eq : \<open>l3 = 3 \<rightarrow> l3\<close>

ML \<open>
val proc = "int process"
(* all languages fail: every failure is reported *)
val _ = expect_failure ["BROKEN"] [("e1", proc)] [("e1_eq", "e1 = 1 \<rightarrow> e1")]
                       "no language succeeded"
(* unknown and misspelled (case-sensitive) language names *)
val _ = expect_failure ["FOO"] [("e2", proc)] [("e2_eq", "e2 = 1 \<rightarrow> e2")]
                       "Undefined Fixrec language: \"FOO\""
val _ = expect_failure ["holcf"] [("e3", proc)] [("e3_eq", "e3 = 1 \<rightarrow> e3")]
                       "Undefined Fixrec language: \"holcf\""
val _ = expect_failure [] [("e4", proc)] [("e4_eq", "e4 = 1 \<rightarrow> e4")]
                       "no language given"
\<close>


section \<open>Unshifted Equations\<close>

text \<open>The classical form \<open>c = E\<close>, with explicit abstractions on the right-hand side:\<close>

Fixrec u1 :: \<open>int \<Rightarrow> int process\<close> where u1_eq : \<open>u1 = (\<lambda>x. x \<rightarrow> u1 (x+1))\<close>
Fixrec u2 :: \<open>int \<rightarrow> int process\<close> where u2_eq : \<open>u2 = (\<Lambda> x. x \<rightarrow> u2\<cdot>(x+1))\<close>


section \<open>Generic Shift over HOL Application\<close>

text \<open>Arguments on the left-hand side are shifted to abstractions on the right-hand side by the
core, independently of the language: single and curried arguments, tuples, curried tuples.\<close>

Fixrec s1 :: \<open>int \<Rightarrow> int process\<close> where s1_eq : \<open>s1 x = x \<rightarrow> s1 (x+1)\<close>
Fixrec s2 :: \<open>int \<Rightarrow> nat \<Rightarrow> int process\<close> where s2_eq : \<open>s2 x n = x \<rightarrow> s2 (x+1) (Suc n)\<close>
Fixrec s3 :: \<open>int \<times> nat \<Rightarrow> int process\<close> where s3_eq : \<open>s3 (x,n) = x \<rightarrow> s3 (x+1,n)\<close>
Fixrec s4 :: \<open>int \<times> int \<times> int \<Rightarrow> int process\<close> where s4_eq : \<open>s4 (x,y,z) = x \<rightarrow> s4 (y,z,x)\<close>
Fixrec s5 :: \<open>int \<times> nat \<Rightarrow> bool \<times> int \<Rightarrow> int process\<close>
  where s5_eq : \<open>s5 (x,n) (b,y) = x \<rightarrow> s5 (y,Suc n) (\<not>b,x)\<close>

text \<open>The shift is equivalent to the unshifted form:\<close>
lemma \<open>s1 = (\<lambda>x. x \<rightarrow> s1 (x+1))\<close> using s1_eq by blast

ML \<open>
(* arguments must be free variables or tuples of them *)
val _ = expect_failure ["HOLCF"] [("e5", "int \<Rightarrow> int process")] [("e5_eq", "e5 0 = 0 \<rightarrow> e5 0")]
                       "args must be free variables or tuples of them"
(* the head of the lhs must be a declared constant *)
val _ = expect_failure ["HOLCF"] [("e6", "int \<Rightarrow> int process")] [("e6_eq", "(if True then e6 else e6) x = x \<rightarrow> e6 x")]
                       "lhs head must be one of the declared constants"
\<close>


section \<open>Domain-Specific Shift: HOLCF Application and Abstraction\<close>

text \<open>HOLCF comes with its own function space \<open>\<rightarrow>\<close> and the pair \<open>f\<cdot>x\<close> / \<open>\<Lambda> x. E\<close>.
Shifting over \<open>\<cdot>\<close> produces \<open>\<Lambda>\<close>-abstractions (\<open>lambda'\<close> of the language); it can be mixed
with the generic shift over HOL application.\<close>

Fixrec c1 :: \<open>int \<rightarrow> int process\<close> where c1_eq : \<open>c1\<cdot>x = x \<rightarrow> c1\<cdot>(x+1)\<close>
Fixrec c2 :: \<open>int \<rightarrow> int \<rightarrow> int process\<close> where c2_eq : \<open>c2\<cdot>x\<cdot>y = x \<rightarrow> c2\<cdot>y\<cdot>x\<close>
Fixrec c3 :: \<open>int \<times> int \<rightarrow> int process\<close> where c3_eq : \<open>c3\<cdot>(x,y) = x \<rightarrow> c3\<cdot>(y,x)\<close>
Fixrec c4 :: \<open>int \<times> int \<times> int \<rightarrow> int process\<close> where c4_eq : \<open>c4\<cdot>(x,y,z) = x \<rightarrow> c4\<cdot>(y,z,x)\<close>
Fixrec c5 :: \<open>nat \<Rightarrow> int \<rightarrow> int process\<close> where c5_eq : \<open>c5 n\<cdot>x = x \<rightarrow> c5 (Suc n)\<cdot>(x+1)\<close>
Fixrec c6 :: \<open>int \<Rightarrow> nat \<times> bool \<Rightarrow> int \<times> int \<rightarrow> int process\<close>
  where c6_eq : \<open>c6 k (n,b)\<cdot>(x,y) = x \<rightarrow> c6 k (n,b)\<cdot>(y,x+k)\<close>

text \<open>The shift is equivalent to the unshifted form:\<close>
lemma \<open>c1 = (\<Lambda> x. x \<rightarrow> c1\<cdot>(x+1))\<close> by (rule cfun_eqI, subst c1_eq, simp)


section \<open>Mutual Recursion\<close>

Fixrec m1 :: \<open>int \<Rightarrow> int process\<close> and m2 :: \<open>int \<Rightarrow> int process\<close>
  where m1_eq : \<open>m1 x = 1 \<rightarrow> m2 x\<close>
  |     m2_eq : \<open>m2 x = 2 \<rightarrow> m1 (x+1)\<close>

text \<open>Mixing shifted and unshifted equations, functions and constants:\<close>
Fixrec m3 :: \<open>int \<Rightarrow> int process\<close> and m4 :: \<open>int process\<close>
  where m3_eq : \<open>m3 x = x \<rightarrow> m4\<close>
  |     m4_eq : \<open>m4 = 0 \<rightarrow> m3 1\<close>

text \<open>Mixing both function spaces:\<close>
Fixrec m5 :: \<open>int \<rightarrow> int process\<close> and m6 :: \<open>int \<Rightarrow> int process\<close>
  where m5_eq : \<open>m5\<cdot>x = 1 \<rightarrow> m6 x\<close>
  |     m6_eq : \<open>m6 x = 2 \<rightarrow> m5\<cdot>(x+1)\<close>


text \<open>Equations that are not (self-)recursive, alone or within a system:\<close>
Fixrec n1 :: \<open>int \<Rightarrow> int process\<close> where n1_eq : \<open>n1 x = x \<rightarrow> Skip\<close>
Fixrec n2 :: \<open>int \<Rightarrow> int process\<close> and n3 :: \<open>int \<Rightarrow> int process\<close>
  where n2_eq : \<open>n2 x = x \<rightarrow> n3 x\<close>
  |     n3_eq : \<open>n3 x = x \<rightarrow> n3 (x+1)\<close>


text \<open>A larger mutual system (guarded equations, choices, finite non-determinism, a member
that is not self-recursive):\<close>
Fixrec t1 :: \<open>int \<Rightarrow> int process\<close> and t2 :: \<open>int \<Rightarrow> int process\<close>
  and t3 :: \<open>int \<Rightarrow> int process\<close> and t4 :: \<open>int process\<close> and t5 :: \<open>int \<Rightarrow> int process\<close>
  where t1_eq : \<open>t1 x = 1 \<rightarrow> t2 x\<close>
  |     t2_eq : \<open>t2 x = (2 \<rightarrow> t3 x) \<box> (3 \<rightarrow> t1 (x+1))\<close>
  |     t3_eq : \<open>t3 x = (\<sqinter> a \<in> {0..x}. a \<rightarrow> t4)\<close>
  |     t4_eq : \<open>t4 = 0 \<rightarrow> t5 1\<close>
  |     t5_eq : \<open>t5 x = (x \<rightarrow> t1 x) \<sqinter> (x \<rightarrow> t4)\<close>


section \<open>Polymorphism\<close>

Fixrec p1 :: \<open>'a \<Rightarrow> 'a process\<close> where p1_eq : \<open>p1 x = x \<rightarrow> p1 x\<close>

text \<open>Mutually recursive equations must share their type variables:\<close>
Fixrec p2 :: \<open>'a \<Rightarrow> 'a process\<close> and p3 :: \<open>'a \<Rightarrow> 'a process\<close>
  where p2_eq : \<open>p2 x = x \<rightarrow> p3 x\<close>
  |     p3_eq : \<open>p3 x = x \<rightarrow> p2 x\<close>

lemma \<open>p1 x = x \<rightarrow> p1 x\<close> by (fact p1_eq)

text \<open>Type variables are of sort \<open>type\<close>, not \<open>cpo\<close>/\<open>domain\<close>:\<close>
lemma \<open>p1 (n::nat) = n \<rightarrow> p1 n\<close> by (fact p1_eq)


section \<open>Generated Theorems\<close>

text \<open>For an equation system \<open>c\<^sub>1 \<dots> c\<^sub>n\<close>, \<^verbatim>\<open>Fixrec\<close> generates the fixpoint definition
\<open>c\<^sub>1_\<dots>_c\<^sub>n_rec_def\<close>, its unfolding \<open>c\<^sub>1_\<dots>_c\<^sub>n_rec_unfold\<close>, the projections \<open>c\<^sub>i_def\<close>, the
equations under their given names (exactly in the stated form) and a fixpoint induction
rule \<open>c\<^sub>1_\<dots>_c\<^sub>n_induct\<close>.\<close>

thm m1_m2_rec_def m1_m2_rec_unfold m1_def m2_def m1_eq m2_eq m1_m2_induct

lemma \<open>c6 k (n,b)\<cdot>(x,y) = x \<rightarrow> c6 k (n,b)\<cdot>(y,x+k)\<close> by (fact c6_eq)
lemma \<open>s5 (x,n) (b,y) = x \<rightarrow> s5 (y,Suc n) (\<not>b,x)\<close> by (fact s5_eq)

text \<open>Fixpoint induction over the HOLCF fixpoint: admissibility, base case \<open>\<bottom>\<close>, step.\<close>

ML \<open>
val _ = @{assert} (Thm.nprems_of @{thm c1_induct} = 3)
val _ = @{assert} (Thm.nprems_of @{thm m1_m2_induct} = 3)
\<close>


text \<open>Unlike HOLCF's \<^verbatim>\<open>fixrec\<close>, the equations are \<^emph>\<open>not\<close> simp rules by default (unguarded use
of recursive equations by the simplifier loops); \<open>[simp]\<close> declares them explicitly:\<close>

Fixrec sa :: \<open>int \<Rightarrow> int process\<close> where sa_eq : \<open>sa x = x \<rightarrow> Skip\<close>
Fixrec sb :: \<open>int \<Rightarrow> int process\<close> where sb_eq [simp] : \<open>sb x = x \<rightarrow> Skip\<close>

lemma \<open>sb 1 = 1 \<rightarrow> Skip\<close> by simp

ML \<open>
val _ = @{assert} (is_none (try (Goal.prove \<^context> [] [] @{prop \<open>sa 1 = 1 \<rightarrow> Skip\<close>})
                                (fn {context, ...} => asm_full_simp_tac context 1)))
\<close>

section \<open>Semantic Properties of the Instance\<close>

text \<open>In HOLCF, every continuous equation has a (least) solution, even an unguarded one;
here it is \<open>\<bottom>\<close>:\<close>

Fixrec d1 :: \<open>int \<Rightarrow> int process\<close> where d1_eq : \<open>d1 x = d1 (x+1)\<close>

lemma \<open>d1 = \<bottom>\<close>
  by (induct rule: d1_induct) simp_all


section \<open>Local Contexts: Locales, Contexts, Interpretation\<close>

text \<open>\<^verbatim>\<open>Fixrec\<close> is a local-theory command: it can be used inside locales and other local
contexts. Locale parameters may occur in the equations; the generated constants are
abstracted over the parameters they depend on, and all theorems are available under
interpretation.\<close>

locale L1 = fixes k :: int assumes k_pos : \<open>0 < k\<close>
begin
Fixrec r1 :: \<open>int \<Rightarrow> int process\<close> 
  where r1_eq : \<open>r1 x = x \<rightarrow> r1 (x + k)\<close>

Fixrec r2 :: \<open>int \<Rightarrow> int process\<close> and r3 :: \<open>int process\<close>
  where r2_eq : \<open>r2 x = x \<rightarrow> r3\<close>
  |     r3_eq : \<open>r3 = k \<rightarrow> r2 k\<close>

lemma \<open>r1 x = x \<rightarrow> r1 (x + k)\<close> by (fact r1_eq)
thm r1_rec_def r1_rec_unfold r1_def r1_induct r2_r3_induct
end

text \<open>The global constants take the parameter as argument:\<close>
term \<open>L1.r1 :: int \<Rightarrow> int \<Rightarrow> int process\<close>

text \<open>Re-entering the locale:\<close>
context L1 begin
lemma \<open>r3 = k \<rightarrow> r2 k\<close> by (fact r3_eq)
end

text \<open>Interpretation:\<close>
interpretation L1_5 : L1 5 by standard simp
lemma \<open>L1_5.r1 x = x \<rightarrow> L1_5.r1 (x + 5)\<close> by (fact L1_5.r1_eq)

text \<open>Unnamed local contexts:\<close>
context fixes m :: int begin
Fixrec r4 :: \<open>int process\<close> where r4_eq : \<open>r4 = m \<rightarrow> r4\<close>
end
term \<open>r4 :: int \<Rightarrow> int process\<close>

text \<open>Polymorphic locales:\<close>
locale L3 = fixes e :: \<open>'a\<close>
begin
Fixrec r5 :: \<open>'a process\<close> where r5_eq : \<open>r5 = e \<rightarrow> r5\<close>
end

text \<open>Locale assumptions are available in the proofs of the construction: \<open>\<sqinter> a \<in> A. _\<close>
is only continuous (in HOLCF) for finite \<open>A\<close>.\<close>
locale L2 = fixes A :: \<open>int set\<close> assumes finite_A [simp] : \<open>finite A\<close>
begin
Fixrec r6 :: \<open>int process\<close> where r6_eq : \<open>r6 = (\<sqinter> a \<in> A. a \<rightarrow> r6)\<close>
end

text \<open>Without the assumption, the construction fails:\<close>
ML \<open>
val _ = expect_failure ["HOLCF"] [("e8", "int set \<Rightarrow> int process")] 
                       [("e8_eq", "e8 A = (\<sqinter> a \<in> A. a \<rightarrow> e8 A)")] "no language succeeded"
\<close>


chapter \<open>Tests Moved from the Instance Theory (verbatim)\<close>

section\<open>Tests\<close>

(* the classic fixrec package. Just for a comparison.*)
fixrec f\<^sub>1 :: \<open>'a :: pcpo \<rightarrow> 'a\<close>  
   and g\<^sub>1 :: \<open>'a :: pcpo \<rightarrow> 'a\<close>
  where \<open>f\<^sub>1 \<cdot> n = g\<^sub>1 \<cdot> n\<close>
     |  \<open>g\<^sub>1 \<cdot> n = f\<^sub>1 \<cdot> n\<close>


(* the new fixrec package. *)
Fixrec g :: \<open>'a::cpo \<Rightarrow> int process\<close> 
   and h :: \<open>('a \<rightarrow> int process)\<close>
   and j :: \<open>('a \<rightarrow> int process)\<close>
  (* TODO: add different polymorphic variables*)
   where a : \<open>g = (\<lambda> x. 3 \<rightarrow> g x)\<close>   
   |     b : \<open>h = (\<Lambda> x. 4 \<rightarrow> j \<cdot> x)\<close>  
   |     c : \<open>j = (\<Lambda> x. 5 \<rightarrow> h \<cdot> x)\<close>  

(* generated : *)
thm  g_h_j_rec_def  g_h_j_rec_unfold g_def h_def j_def a b c 


thm g_h_j_induct[simplified , simplified case_prod_beta, 
                 simplified, folded g_def h_def j_def]

text\<open> Making recursive equation unnecessarily interdependent in an \<^verbatim>\<open>Fixrec\<close> definition is never
a good idea: Induction schemes tend to complicate things up to a point where they become unusable.
Another problem comes with polymorphism: mutual recursive equations can be polymorphic, but
they \<^bold>\<open>must\<close> contain all the same polymorphic variables (otherwise, the proof of the projections
will fail necessarily; the error-message is in these cases rather spurious.). 
Try to replace the \<^typ>\<open>int\<close> in the equations \<open>hh\<close> and \<open>jj\<close> in the following equation system
in order to see the problem.\<close>

term\<open> (AA \<cdot> x) \<cdot> (y,z)\<close>

Fixrec [HOLCF] gg :: \<open>(int \<times> int) \<Rightarrow> (int list \<times> bool) \<Rightarrow> int process\<close> 
           and hh :: \<open>int \<rightarrow> (int \<times> int) \<rightarrow> int process\<close>
           and jj :: \<open>int \<rightarrow> int process\<close>
   where aa        : \<open>gg (x,y)(L,z)    = x \<rightarrow> gg (x+1,y-1)(x#L, - z)\<close>  
   |     bb        : \<open>(hh\<cdot>x)\<cdot>(y,z) = (4 \<rightarrow> jj \<cdot> x)\<close>  
   |     cc        : \<open>jj\<cdot>x        = (5 \<rightarrow> hh \<cdot> x \<cdot> (x*x,x))\<close>  

thm aa bb cc

text\<open>Mixing one-ary arguments and tuples.\<close>
Fixrec [HOLCF] ggg :: \<open>(int \<times> int) \<Rightarrow> (int list \<times> bool) \<Rightarrow> int process\<close> 
           and hhh :: \<open>int \<rightarrow> (tr \<times> int) \<rightarrow> int process\<close>
           and jjj :: \<open>int \<rightarrow> tr \<rightarrow> int process\<close>
   where aaa        : \<open>ggg (x,y)(L,z) = x \<rightarrow> ggg (x+1,y-1)(x#L, \<not> z)\<close>   
   |     bbb        : \<open>hhh\<cdot>x\<cdot>(y,z)   = (4 \<rightarrow> jjj\<cdot>x\<cdot>y)\<close>  
   |     ccc        : \<open>jjj\<cdot>x\<cdot>y         = (5 \<rightarrow> hhh\<cdot>x\<cdot>(neg\<cdot>y,x))\<close>  

text\<open>Mixing total and continuous function spaces requires care: a \<open>\<Lambda>\<close>-abstraction is only a
proper continuous function if its body is continuous in the bound variable. In the following
system, \<open>hhhh x = \<Lambda>(y,z). 4 \<rightarrow> (jjjj\<cdot>x) y\<close> with \<open>y :: tr\<close> requires the \<^emph>\<open>total\<close> function 
\<open>jjjj\<cdot>x :: tr \<Rightarrow> int process\<close> to be continuous on the non-discrete type \<^typ>\<open>tr\<close>, which does not
hold in general; the continuity proof of the fixpoint construction fails (as it would for 
HOLCF's \<^verbatim>\<open>fixrec\<close>). Over discrete argument types (see below), such mixtures are unproblematic.\<close>

(*
Fixrec [HOLCF] gggg :: \<open>(int \<times> int) \<Rightarrow> (int list \<times> bool) \<Rightarrow> int process\<close> 
           and hhhh :: \<open>(int \<Rightarrow> ((tr \<times> int) \<rightarrow> int process))\<close>
           and jjjj :: \<open>(int \<rightarrow> (tr \<Rightarrow> int process))\<close>
   where aaaa        : \<open>gggg (x,y)(L,z)    = x \<rightarrow> gggg (x+1,y-1)(x#L, \<not> z)\<close>  
   |     bbbb        : \<open>(hhhh x)\<cdot>(y,z)    = (4 \<rightarrow> (jjjj \<cdot> x) y)\<close>  
   |     cccc        : \<open>(jjjj\<cdot>x) y       = (5 \<rightarrow> (hhhh x) \<cdot> (neg\<cdot>y,x))\<close>  
*)

ML \<open>
val _ = expect_failure ["HOLCF"]
          [("g5", "(int \<times> int) \<Rightarrow> (int list \<times> bool) \<Rightarrow> int process"),
           ("h5", "int \<Rightarrow> ((tr \<times> int) \<rightarrow> int process)"),
           ("j5", "int \<rightarrow> (tr \<Rightarrow> int process)")]
          [("a5", "g5 (x,y)(L,z) = x \<rightarrow> g5 (x+1,y-1)(x#L, \<not> z)"),
           ("b5", "(h5 x)\<cdot>(y,z) = (4 \<rightarrow> (j5\<cdot>x) y)"),
           ("c5", "(j5\<cdot>x) y = (5 \<rightarrow> (h5 x)\<cdot>(neg\<cdot>y,x))")]
          "cont"
\<close>

text\<open>The same mixture over a discrete argument type:\<close>
Fixrec [HOLCF] g4 :: \<open>(int \<times> int) \<Rightarrow> (int list \<times> bool) \<Rightarrow> int process\<close> 
           and h4 :: \<open>(int \<Rightarrow> ((int \<times> int) \<rightarrow> int process))\<close>
           and j4 :: \<open>(int \<rightarrow> (int \<Rightarrow> int process))\<close>
   where a4        : \<open>g4 (x,y)(L,z)    = x \<rightarrow> g4 (x+1,y-1)(x#L, \<not> z)\<close>  
   |     b4        : \<open>(h4 x)\<cdot>(y,z)    = (4 \<rightarrow> (j4 \<cdot> x) y)\<close>  
   |     c4        : \<open>(j4\<cdot>x) y       = (5 \<rightarrow> (h4 x) \<cdot> (- y,x))\<close>  

(*
Interesting failure:
Fixrec [HOLCF] gggg :: \<open>(int \<times> int) \<Rightarrow> (int list \<times> bool) \<Rightarrow> int process\<close> 
           and hhhh :: \<open>(int \<Rightarrow> ((tr \<times> int) \<rightarrow> int process))\<close>
           and jjjj :: \<open>(int \<rightarrow> (tr \<Rightarrow> int process))\<close>
   where aaaa        : \<open>gggg (x,y)(L,z)    = x \<rightarrow> gggg (x+1,y-1)(x#L, \<not> z)\<close>  
   |     bbbb        : \<open>(hhh x)\<cdot>(y,z)    = (4 \<rightarrow> (jjjj \<cdot> x) y)\<close>  
   |     cccc        : \<open>(jjjj\<cdot>x) y       = (5 \<rightarrow> (hhhh x) \<cdot> (neg\<cdot>y,x))\<close>  
*)


ML\<open>

fun prove_projection'  defs unfold ctxt def = 
       EVERY [resolve0_tac [def RS HOLCF_instance.aux2'] 1,
              resolve0_tac [unfold RS HOLCF_instance.aux2] 1,
              auto_tac (HOLCF_instance.add_prod_splits ctxt), 
              HOLCF_instance.metis_step ctxt defs 1]


\<close>
ML\<open>val prove_projection = HOLCF_instance.prove_projection\<close>
lemma "gg (x,y)(L,z) = ( x \<rightarrow> gg (x+1,y-1)(x#L, - z))" by (fact aa)

text\<open>The projection proof as performed by the package (structural: pair rules and refolding):\<close>
lemma "gg (x,y)(L,z) = ( x \<rightarrow> gg (x+1,y-1)(x#L, - z))"
  by(tactic \<open>prove_projection [@{thm gg_def},@{thm hh_def},@{thm jj_def}] @{thm gg_hh_jj_rec_unfold} @{context}  @{thm gg_def} \<close>)
  

section\<open>Simulations (for Comprehension and Debugging)\<close>


ML\<open> (*for tests ... *)
local open HOLogic in

fun substitute_curried_pred ctxt vartab thm =
    let val frees = map (fn((s,t,_),_) => Free(Binding.name_of s,t)) vartab;
        val Var ((P, idx), ty') $ S = dest_Trueprop(Thm.concl_of thm);
        val prodT'= strip_tupleT (domain_type ty')
        val frees'= map (fn (Free(s,_),t) => Free(s,t)) (frees ~~ prodT') 
      
        val P' = list_comb (Var((P^"'",idx),prodT' ---> boolT), frees')
        val proJT' =  tupled_lambda (mk_tuple frees') P'
        val subst = Vars.make1(((P,idx),ty'), Thm.cterm_of ctxt proJT');
    in  thm |> Thm.instantiate(TVars.empty,subst) end

(* val thm' =  substitute_curried_pred @{context} (!VARTAB) @{thm g_h_j_induct} *)
end\<close>


thm def_cont_fix_ind[OF g_h_j_rec_def, 
                     where P = \<open>\<lambda>(x, y, z). P' x y z\<close>, 
                     simplified, simplified case_prod_beta, simplified]


(* Tests to show what happens in the generic proj-procedure. *)
definition g_h_j_rec' 
  where "g_h_j_rec' \<equiv> \<mu> x. case x of (g', h', j') \<Rightarrow> (\<lambda>x. 3 \<rightarrow> g' x, \<Lambda> x. 4 \<rightarrow> j'\<cdot>x, \<Lambda> x. 5 \<rightarrow> h'\<cdot>x)"


definition g' where "g' \<equiv> fst g_h_j_rec'"

definition h' where "h' \<equiv> fst (snd g_h_j_rec')"

lemma a' : "g = (\<lambda> x. 3 \<rightarrow> g x)"
  by(tactic \<open>prove_projection [@{thm g_def},@{thm h_def},@{thm j_def}] 
                              @{thm g_h_j_rec_unfold} 
                              @{context} 
                              @{thm g_def}\<close>)



lemma b' : "h = (\<Lambda> x. 4 \<rightarrow> j \<cdot> x)"
  by(tactic \<open>prove_projection [@{thm g_def},@{thm h_def},@{thm j_def}]
                              @{thm g_h_j_rec_unfold} 
                              @{context} 
                              @{thm h_def}\<close>)


   
lemma g_h_j_induct' :
  assumes ** : \<open>adm ( \<lambda>(g, h, j). P' g h j)\<close>
    and ***: \<open>P' (\<bottom>::'a::cpo \<Rightarrow> int process) (\<bottom>::'a  \<rightarrow>  int process) (\<bottom>::'a  \<rightarrow>  int process)\<close>
    and ****: "(\<And>g h j. P' g h j \<Longrightarrow> P' (\<lambda>xa. 3 \<rightarrow> g xa) (\<Lambda> xa. 4 \<rightarrow> j\<cdot>xa) (\<Lambda> xa. 5 \<rightarrow> h\<cdot>xa))"
  shows\<open>P' g h j\<close>
proof (rule def_cont_fix_ind[OF g_h_j_rec_def, 
                             where P = \<open>\<lambda>(x, y, z). P' x y z\<close>, 
                             simplified, simplified case_prod_beta, 
                             simplified, folded g_def h_def j_def]) 
  show \<open>cont (\<lambda>x. (\<lambda>xa. 3 \<rightarrow> fst x xa, \<Lambda> xa. 4 \<rightarrow> snd (snd x)\<cdot>xa, \<Lambda> xa. 5 \<rightarrow> fst (snd x)\<cdot>xa))\<close>
    by (simp add: prod_cont_iff cont_fun)
next
  show \<open>adm ( \<lambda>(g, h, j). P' g h j)\<close> by fact
next
  show \<open>P' \<bottom> \<bottom> \<bottom>\<close> by fact
next
  from **** 
  show \<open>P' (fst x) (fst (snd x)) (snd (snd x)) \<Longrightarrow>
        P' (\<lambda>xa. 3 \<rightarrow> fst x xa) (\<Lambda> xa. 4 \<rightarrow> snd (snd x)\<cdot>xa) (\<Lambda> xa. 5 \<rightarrow> fst (snd x)\<cdot>xa)\<close> for x
       by simp 
qed



(* declare [[ML_print_depth=200 ]] *)

end
