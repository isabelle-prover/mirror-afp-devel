(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 * Author: Benjamin Puyobro, Université Paris-Saclay,
           IRT SystemX, CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)


section \<open>Product\<close>

(*<*)
theory Prod_Ultrametric_Restriction_Spaces
  imports Ultrametric_Restriction_Spaces Restriction_Spaces
begin
  (*>*)

text \<open>
The product type \<^typ>\<open>'a \<times> 'b\<close> of to metric spaces is already instantiated as
a metric space by setting @{thm dist_prod_def[no_vars]}.
Unfortunately, this definition is not compatible with the distance required
by the \<^class>\<open>non_decseq_restriction_space\<close>..
We first have to define a new product type with a trivial \<^theory_text>\<open>typedef\<close>.
\<close>

subsection \<open>Isomorphic Product Construction\<close>

subsubsection \<open>Definition and First Properties\<close>

typedef ('a, 'b) prod\<^sub>m\<^sub>a\<^sub>x (\<open>(_ \<times>\<^sub>m\<^sub>a\<^sub>x/ _)\<close> [21, 20] 20) = \<open>UNIV :: ('a \<times> 'b) set\<close>
  morphisms from_prod\<^sub>m\<^sub>a\<^sub>x to_prod\<^sub>m\<^sub>a\<^sub>x by simp

\<comment>\<open>Simplifications because the \<^theory_text>\<open>typedef\<close> is trivial.\<close>

declare from_prod\<^sub>m\<^sub>a\<^sub>x_inject  [simp]
  from_prod\<^sub>m\<^sub>a\<^sub>x_inverse [simp]

lemmas to_prod\<^sub>m\<^sub>a\<^sub>x_inject_simplified [simp] = to_prod\<^sub>m\<^sub>a\<^sub>x_inject [simplified]
  and to_prod\<^sub>m\<^sub>a\<^sub>x_inverse_simplified[simp] = to_prod\<^sub>m\<^sub>a\<^sub>x_inverse[simplified]

(* useful ? *)
lemmas to_prod\<^sub>m\<^sub>a\<^sub>x_induct_simplified = to_prod\<^sub>m\<^sub>a\<^sub>x_induct[simplified]
  and to_prod\<^sub>m\<^sub>a\<^sub>x_cases_simplified  = to_prod\<^sub>m\<^sub>a\<^sub>x_cases [simplified]
  and from_prod\<^sub>m\<^sub>a\<^sub>x_induct_simplified = from_prod\<^sub>m\<^sub>a\<^sub>x_induct[simplified]
  and from_prod\<^sub>m\<^sub>a\<^sub>x_cases_simplified  = from_prod\<^sub>m\<^sub>a\<^sub>x_cases [simplified]


setup_lifting type_definition_prod\<^sub>m\<^sub>a\<^sub>x

lift_definition Pair\<^sub>m\<^sub>a\<^sub>x :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b\<close> is Pair .


free_constructors case_prod\<^sub>m\<^sub>a\<^sub>x for Pair\<^sub>m\<^sub>a\<^sub>x fst\<^sub>m\<^sub>a\<^sub>x snd\<^sub>m\<^sub>a\<^sub>x
  by (metis Pair\<^sub>m\<^sub>a\<^sub>x.abs_eq from_prod\<^sub>m\<^sub>a\<^sub>x_inverse surjective_pairing)
    (metis Pair\<^sub>m\<^sub>a\<^sub>x.rep_eq prod.inject)


lemma fst\<^sub>m\<^sub>a\<^sub>x_def : \<open>fst\<^sub>m\<^sub>a\<^sub>x \<equiv> map_fun from_prod\<^sub>m\<^sub>a\<^sub>x id fst\<close>
  by (intro eq_reflection ext, simp add: fst\<^sub>m\<^sub>a\<^sub>x_def,
      metis Pair\<^sub>m\<^sub>a\<^sub>x.rep_eq from_prod\<^sub>m\<^sub>a\<^sub>x_inverse fst\<^sub>m\<^sub>a\<^sub>x_def prod.collapse prod\<^sub>m\<^sub>a\<^sub>x.sel(1))
lemma fst\<^sub>m\<^sub>a\<^sub>x_rep_eq : \<open>fst\<^sub>m\<^sub>a\<^sub>x x = fst (from_prod\<^sub>m\<^sub>a\<^sub>x x)\<close>
  by (metis Pair\<^sub>m\<^sub>a\<^sub>x.rep_eq fst_conv prod\<^sub>m\<^sub>a\<^sub>x.collapse)

lemma fst\<^sub>m\<^sub>a\<^sub>x_abs_eq [simp] : \<open>fst\<^sub>m\<^sub>a\<^sub>x (to_prod\<^sub>m\<^sub>a\<^sub>x y) = fst y\<close>
  by (metis Pair\<^sub>m\<^sub>a\<^sub>x.abs_eq prod.exhaust_sel prod\<^sub>m\<^sub>a\<^sub>x.sel(1))

lemma fst\<^sub>m\<^sub>a\<^sub>x_transfer [transfer_rule]: \<open>rel_fun (pcr_prod\<^sub>m\<^sub>a\<^sub>x (=) (=)) (=) fst fst\<^sub>m\<^sub>a\<^sub>x\<close>
  by (metis (mono_tags) Pair\<^sub>m\<^sub>a\<^sub>x.rep_eq cr_prod\<^sub>m\<^sub>a\<^sub>x_def fst_conv prod\<^sub>m\<^sub>a\<^sub>x.collapse prod\<^sub>m\<^sub>a\<^sub>x.pcr_cr_eq rel_funI)


lemma snd\<^sub>m\<^sub>a\<^sub>x_def : \<open>snd\<^sub>m\<^sub>a\<^sub>x \<equiv> map_fun from_prod\<^sub>m\<^sub>a\<^sub>x id snd\<close>
  by (intro eq_reflection ext, simp add: snd\<^sub>m\<^sub>a\<^sub>x_def,
      metis Pair\<^sub>m\<^sub>a\<^sub>x.rep_eq from_prod\<^sub>m\<^sub>a\<^sub>x_inverse prod.collapse prod\<^sub>m\<^sub>a\<^sub>x.case)

lemma snd\<^sub>m\<^sub>a\<^sub>x_rep_eq : \<open>snd\<^sub>m\<^sub>a\<^sub>x x = snd (from_prod\<^sub>m\<^sub>a\<^sub>x x)\<close>
  by (metis Pair\<^sub>m\<^sub>a\<^sub>x.rep_eq prod\<^sub>m\<^sub>a\<^sub>x.collapse snd_conv)

lemma snd\<^sub>m\<^sub>a\<^sub>x_abs_eq [simp] : \<open>snd\<^sub>m\<^sub>a\<^sub>x (to_prod\<^sub>m\<^sub>a\<^sub>x y) = snd y\<close>
  by (metis Pair\<^sub>m\<^sub>a\<^sub>x.abs_eq prod.exhaust_sel prod\<^sub>m\<^sub>a\<^sub>x.sel(2))

lemma snd\<^sub>m\<^sub>a\<^sub>x_transfer [transfer_rule] : \<open>rel_fun (pcr_prod\<^sub>m\<^sub>a\<^sub>x (=) (=)) (=) snd snd\<^sub>m\<^sub>a\<^sub>x\<close>
  by (metis (mono_tags, lifting) Pair\<^sub>m\<^sub>a\<^sub>x.rep_eq cr_prod\<^sub>m\<^sub>a\<^sub>x_def
      prod\<^sub>m\<^sub>a\<^sub>x.collapse prod\<^sub>m\<^sub>a\<^sub>x.pcr_cr_eq rel_funI snd_conv)


lemma case_prod\<^sub>m\<^sub>a\<^sub>x_def : \<open>case_prod\<^sub>m\<^sub>a\<^sub>x \<equiv> map_fun id (map_fun from_prod\<^sub>m\<^sub>a\<^sub>x id) case_prod\<close>
  by (intro eq_reflection ext, simp add: prod\<^sub>m\<^sub>a\<^sub>x.case_eq_if fst\<^sub>m\<^sub>a\<^sub>x_rep_eq snd\<^sub>m\<^sub>a\<^sub>x_rep_eq split_beta)

lemma case_prod\<^sub>m\<^sub>a\<^sub>x_rep_eq : \<open>case_prod\<^sub>m\<^sub>a\<^sub>x f p = (case from_prod\<^sub>m\<^sub>a\<^sub>x p of (x, y) \<Rightarrow> f x y)\<close>
  by (simp add: fst\<^sub>m\<^sub>a\<^sub>x_rep_eq prod\<^sub>m\<^sub>a\<^sub>x.case_eq_if snd\<^sub>m\<^sub>a\<^sub>x_rep_eq split_beta)

lemma case_prod\<^sub>m\<^sub>a\<^sub>x_abs_eq [simp] : \<open>case_prod\<^sub>m\<^sub>a\<^sub>x f (to_prod\<^sub>m\<^sub>a\<^sub>x q) = (case q of (x, y) \<Rightarrow> f x y)\<close>
  by (simp add: prod\<^sub>m\<^sub>a\<^sub>x.case_eq_if split_beta)

lemma case_prod\<^sub>m\<^sub>a\<^sub>x_transfer [transfer_rule] : \<open>rel_fun (=) (rel_fun (pcr_prod\<^sub>m\<^sub>a\<^sub>x (=) (=)) (=)) case_prod case_prod\<^sub>m\<^sub>a\<^sub>x\<close>
  by (simp add: cr_prod\<^sub>m\<^sub>a\<^sub>x_def fst\<^sub>m\<^sub>a\<^sub>x_rep_eq prod\<^sub>m\<^sub>a\<^sub>x.case_eq_if prod\<^sub>m\<^sub>a\<^sub>x.pcr_cr_eq rel_fun_def snd\<^sub>m\<^sub>a\<^sub>x_rep_eq split_beta)



subsection \<open>Syntactic Sugar\<close>

text \<open>The following syntactic sugar is of course recovered from the theory \<^theory>\<open>HOL.Product_Type\<close>.\<close>

nonterminal tuple_args\<^sub>m\<^sub>a\<^sub>x and patterns\<^sub>m\<^sub>a\<^sub>x
syntax
  "_tuple\<^sub>m\<^sub>a\<^sub>x"      :: "'a \<Rightarrow> tuple_args\<^sub>m\<^sub>a\<^sub>x \<Rightarrow> 'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b"        (\<open>(1\<lblot>_,/ _\<rblot>)\<close>)
  "_tuple_arg\<^sub>m\<^sub>a\<^sub>x"  :: "'a \<Rightarrow> tuple_args\<^sub>m\<^sub>a\<^sub>x"                   (\<open>_\<close>)
  "_tuple_args\<^sub>m\<^sub>a\<^sub>x" :: "'a \<Rightarrow> tuple_args\<^sub>m\<^sub>a\<^sub>x \<Rightarrow> tuple_args\<^sub>m\<^sub>a\<^sub>x"   (\<open>_,/ _\<close>)
  "_pattern\<^sub>m\<^sub>a\<^sub>x"    :: "pttrn \<Rightarrow> patterns\<^sub>m\<^sub>a\<^sub>x \<Rightarrow> pttrn"         (\<open>\<lblot>_,/ _\<rblot>\<close>)
  ""              :: "pttrn \<Rightarrow> patterns\<^sub>m\<^sub>a\<^sub>x"                  (\<open>_\<close>)
  "_patterns\<^sub>m\<^sub>a\<^sub>x"   :: "pttrn \<Rightarrow> patterns\<^sub>m\<^sub>a\<^sub>x \<Rightarrow> patterns\<^sub>m\<^sub>a\<^sub>x"    (\<open>_,/ _\<close>)
translations
  "\<lblot>x, y\<rblot>" \<rightleftharpoons> "CONST Pair\<^sub>m\<^sub>a\<^sub>x x y"
  "_pattern\<^sub>m\<^sub>a\<^sub>x x y" \<rightleftharpoons> "CONST Pair\<^sub>m\<^sub>a\<^sub>x x y"
  "_patterns\<^sub>m\<^sub>a\<^sub>x x y" \<rightleftharpoons> "CONST Pair\<^sub>m\<^sub>a\<^sub>x x y"
  "_tuple\<^sub>m\<^sub>a\<^sub>x x (_tuple_args\<^sub>m\<^sub>a\<^sub>x y z)" \<rightleftharpoons> "_tuple\<^sub>m\<^sub>a\<^sub>x x (_tuple_arg\<^sub>m\<^sub>a\<^sub>x (_tuple\<^sub>m\<^sub>a\<^sub>x y z))"
  "\<lambda>\<lblot>x, y, zs\<rblot>. b" \<rightleftharpoons> "CONST case_prod\<^sub>m\<^sub>a\<^sub>x (\<lambda>x \<lblot>y, zs\<rblot>. b)"
  "\<lambda>\<lblot>x, y\<rblot>. b" \<rightleftharpoons> "CONST case_prod\<^sub>m\<^sub>a\<^sub>x (\<lambda>x y. b)"
  "_abs (CONST Pair\<^sub>m\<^sub>a\<^sub>x x y) t" \<rightharpoonup> "\<lambda>\<lblot>x, y\<rblot>. t"
  \<comment> \<open>This rule accommodates tuples in \<open>case C \<dots> \<lblot>x, y\<rblot> \<dots> \<Rightarrow> \<dots>\<close>:
     The \<open>\<lblot>x, y\<rblot>\<close> is parsed as \<open>Pair\<^sub>m\<^sub>a\<^sub>x x y\<close> because it is \<open>logic\<close>,
     not \<open>pttrn\<close>.\<close>

text \<open>With this syntactic sugar, one can write
\<^term>\<open>case a of \<lblot>b, c, d, e\<rblot> \<Rightarrow> \<lblot>c, d\<rblot>\<close>, \<^term>\<open>\<lambda>\<lblot>y, u\<rblot>. a\<close>,
\<^term>\<open>\<lambda>\<lblot>a, b\<rblot>. \<lblot>a, b, c , d ,e\<rblot>\<close>, \<^term>\<open>\<lambda>\<lblot>a, b, c\<rblot>. a\<close>, \<open>\<dots>\<close>
as for the type \<^typ>\<open>'a \<times> 'b\<close>.\<close>


\<comment> \<open>Conversions between \<open>_tuple\<close> and \<open>_tuple\<^sub>m\<^sub>a\<^sub>x\<close>.\<close>
lemmas to_prod\<^sub>m\<^sub>a\<^sub>x_tuple     [simp] = Pair\<^sub>m\<^sub>a\<^sub>x.abs_eq[symmetric]
  and from_prod\<^sub>m\<^sub>a\<^sub>x_tuple\<^sub>m\<^sub>a\<^sub>x [simp] = Pair\<^sub>m\<^sub>a\<^sub>x.rep_eq



subsection \<open>Product\<close>

text \<open>We first redo the work of \<^theory>\<open>Restriction_Spaces.Restriction_Spaces_Prod\<close>.\<close>

instantiation prod\<^sub>m\<^sub>a\<^sub>x :: (restriction, restriction) restriction
begin

lift_definition restriction_prod\<^sub>m\<^sub>a\<^sub>x :: \<open>'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b \<Rightarrow> nat \<Rightarrow> 'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b\<close> is \<open>(\<down>)\<close> .

lemma restriction_prod\<^sub>m\<^sub>a\<^sub>x_def' : \<open>p \<down> n = \<lblot>fst\<^sub>m\<^sub>a\<^sub>x p \<down> n, snd\<^sub>m\<^sub>a\<^sub>x p \<down> n\<rblot>\<close>
  by transfer (simp add: restriction_prod_def)

instance by (intro_classes, transfer, simp)

end


instance prod\<^sub>m\<^sub>a\<^sub>x :: (restriction_space, restriction_space) restriction_space
  by (intro_classes; transfer) (simp_all add: ex_not_restriction_related)



instantiation prod\<^sub>m\<^sub>a\<^sub>x :: (restriction_\<sigma>, restriction_\<sigma>) restriction_\<sigma>
begin

definition restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x :: \<open>('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) itself \<Rightarrow> nat \<Rightarrow> real\<close>
  where \<open>restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x _ n \<equiv>
         max (restriction_\<sigma> TYPE('a) n) (restriction_\<sigma> TYPE('b) n)\<close>

instance by intro_classes
end


instantiation prod\<^sub>m\<^sub>a\<^sub>x :: (non_decseq_restriction_space, non_decseq_restriction_space)
  non_decseq_restriction_space
begin

definition dist_prod\<^sub>m\<^sub>a\<^sub>x :: \<open>['a \<times>\<^sub>m\<^sub>a\<^sub>x 'b, 'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b] \<Rightarrow> real\<close>
  where \<open>dist_prod\<^sub>m\<^sub>a\<^sub>x f g \<equiv> INF n \<in> restriction_related_set f g. restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) n\<close>

definition uniformity_prod\<^sub>m\<^sub>a\<^sub>x :: \<open>(('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) \<times> 'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) filter\<close>
  where \<open>uniformity_prod\<^sub>m\<^sub>a\<^sub>x \<equiv> INF e\<in>{0 <..}. principal {(x, y). dist x y < e}\<close>

definition open_prod\<^sub>m\<^sub>a\<^sub>x :: \<open>('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) set \<Rightarrow> bool\<close>
  where \<open>open_prod\<^sub>m\<^sub>a\<^sub>x U \<equiv> \<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity\<close>


instance
proof intro_classes
  show \<open>restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) \<longlonglongrightarrow> 0\<close>
    by (rule real_tendsto_sandwich
        [of \<open>\<lambda>n. 0\<close> _ _ \<open>\<lambda>n. restriction_\<sigma> TYPE('a) n + restriction_\<sigma> TYPE('b) n\<close>])
      (simp_all add: order_less_imp_le restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def max_def
        restriction_\<sigma>_tendsto_zero tendsto_add_zero)
qed (simp_all add: uniformity_prod\<^sub>m\<^sub>a\<^sub>x_def open_prod\<^sub>m\<^sub>a\<^sub>x_def
    restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def max_def dist_prod\<^sub>m\<^sub>a\<^sub>x_def)

end

instance prod\<^sub>m\<^sub>a\<^sub>x :: (decseq_restriction_space, decseq_restriction_space) decseq_restriction_space
proof intro_classes
  show \<open>decseq (restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b))\<close>
  proof (intro decseq_SucI)
    show \<open>restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) (Suc n) \<le> restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) n\<close> for n
      using decseq_SucD[of \<open>restriction_\<sigma> TYPE('a)\<close> n]
        decseq_SucD[of \<open>restriction_\<sigma> TYPE('b)\<close> n]
      by (auto simp add: restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def decseq_restriction_\<sigma>)
  qed
qed

instance prod\<^sub>m\<^sub>a\<^sub>x :: (strict_decseq_restriction_space, strict_decseq_restriction_space) strict_decseq_restriction_space
proof intro_classes
  show \<open>strict_decseq (restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b))\<close>
  proof (intro strict_decseq_SucI)
    show \<open>restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) (Suc n) < restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) n\<close> for n
      using strict_decseq_SucD[of \<open>restriction_\<sigma> TYPE('a)\<close> n]
        strict_decseq_SucD[of \<open>restriction_\<sigma> TYPE('b)\<close> n]
      by (auto simp add: restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def strict_decseq_restriction_\<sigma>)
  qed
qed


instantiation prod\<^sub>m\<^sub>a\<^sub>x :: (restriction_\<delta>, restriction_\<delta>) restriction_\<delta>
begin

definition restriction_\<delta>_prod\<^sub>m\<^sub>a\<^sub>x :: \<open>('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) itself \<Rightarrow> real\<close>
  where \<open>restriction_\<delta>_prod\<^sub>m\<^sub>a\<^sub>x _ \<equiv> max (restriction_\<delta> TYPE('a)) (restriction_\<delta> TYPE('b))\<close>

instance by intro_classes (simp_all add: restriction_\<delta>_prod\<^sub>m\<^sub>a\<^sub>x_def max_def)

end

instance prod\<^sub>m\<^sub>a\<^sub>x :: (at_least_geometric_restriction_space, at_least_geometric_restriction_space)
  at_least_geometric_restriction_space
proof intro_classes
  show \<open>0 < restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) n\<close> for n by simp
next
  show \<open>restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) (Suc n)
        \<le> restriction_\<delta> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) * restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) n\<close> for n
    by (auto intro: order_trans[OF restriction_\<sigma>_le]
        simp add: restriction_\<delta>_prod\<^sub>m\<^sub>a\<^sub>x_def mult_mono' restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def)
next
  show \<open>dist p1 p2 = Inf (restriction_\<sigma>_related_set p1 p2)\<close> for p1 p2 :: \<open>'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b\<close>
    by (simp add: dist_prod\<^sub>m\<^sub>a\<^sub>x_def)
qed


instance prod\<^sub>m\<^sub>a\<^sub>x :: (geometric_restriction_space, geometric_restriction_space) geometric_restriction_space
proof intro_classes
  show \<open>restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) n = restriction_\<delta> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) ^ n\<close> for n
    by (simp add: restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def restriction_\<sigma>_is restriction_\<delta>_prod\<^sub>m\<^sub>a\<^sub>x_def max_def)
      (meson nle_le power_mono zero_le_restriction_\<delta>)
next
  show \<open>dist p1 p2 = Inf (restriction_\<sigma>_related_set p1 p2)\<close> for p1 p2 :: \<open>'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b\<close>
    by (simp add: dist_prod\<^sub>m\<^sub>a\<^sub>x_def)
qed



lemma max_dist_projections_le_dist_prod\<^sub>m\<^sub>a\<^sub>x :
  \<open>max (dist (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2)) (dist (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2)) \<le> dist p1 p2\<close>
proof (unfold dist_restriction_is max_def, split if_split, intro conjI impI)
  show \<open>Inf (restriction_\<sigma>_related_set (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2)) \<le> Inf (restriction_\<sigma>_related_set p1 p2)\<close>
  proof (rule cINF_superset_mono[OF nonempty_restriction_related_set])
    show \<open>bdd_below (restriction_\<sigma>_related_set (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2))\<close>
      by (meson bdd_belowI2 zero_le_restriction_\<sigma>)
  qed (simp_all add: subset_iff add: restriction_prod\<^sub>m\<^sub>a\<^sub>x_def' restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def)
next
  show \<open>Inf (restriction_\<sigma>_related_set (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2)) \<le> Inf (restriction_\<sigma>_related_set p1 p2)\<close>
  proof (rule cINF_superset_mono[OF nonempty_restriction_related_set])
    show \<open>bdd_below (restriction_\<sigma>_related_set (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2))\<close>
      by (meson bdd_belowI2 zero_le_restriction_\<sigma>)
  qed (simp_all add: subset_iff add: restriction_prod\<^sub>m\<^sub>a\<^sub>x_def' restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def)
qed


subsection \<open>Completeness\<close>

subsubsection \<open>Preliminaries\<close>

default_sort non_decseq_restriction_space \<comment>\<open>Otherwise we should always specify.\<close>

lemma restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_commute :
  \<open>restriction_\<sigma> TYPE('b \<times>\<^sub>m\<^sub>a\<^sub>x 'a) = restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b)\<close>
  unfolding restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def by (rule ext) simp

definition dist_left_prod\<^sub>m\<^sub>a\<^sub>x :: \<open>('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) itself \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real\<close>
  where \<open>dist_left_prod\<^sub>m\<^sub>a\<^sub>x _ x y \<equiv> INF n \<in> restriction_related_set x y. restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) n\<close>

definition dist_right_prod\<^sub>m\<^sub>a\<^sub>x :: \<open>('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) itself \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> real\<close>
  where \<open>dist_right_prod\<^sub>m\<^sub>a\<^sub>x _ x y \<equiv> INF n \<in> restriction_related_set x y. restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) n\<close>

lemma dist_right_prod\<^sub>m\<^sub>a\<^sub>x_is_dist_left_prod\<^sub>m\<^sub>a\<^sub>x :
  \<open>dist_right_prod\<^sub>m\<^sub>a\<^sub>x TYPE('b \<times>\<^sub>m\<^sub>a\<^sub>x 'a) = dist_left_prod\<^sub>m\<^sub>a\<^sub>x TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b)\<close>
  unfolding dist_left_prod\<^sub>m\<^sub>a\<^sub>x_def dist_right_prod\<^sub>m\<^sub>a\<^sub>x_def
  by (subst restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_commute) simp


lemma dist_le_dist_left_prod\<^sub>m\<^sub>a\<^sub>x : \<open>dist x y \<le> dist_left_prod\<^sub>m\<^sub>a\<^sub>x TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) x y\<close>
proof (unfold dist_left_prod\<^sub>m\<^sub>a\<^sub>x_def dist_restriction_is,
    rule cINF_mono[OF nonempty_restriction_related_set[of x y]])
  show \<open>bdd_below (restriction_\<sigma>_related_set x y)\<close>
  by (meson bdd_belowI2 zero_le_restriction_\<sigma>)
next
  show \<open>m \<in> restriction_related_set x y \<Longrightarrow>
        \<exists>n\<in>restriction_related_set x y. \<sigma>\<^sub>\<down> TYPE('a) n \<le> \<sigma>\<^sub>\<down> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) m\<close> for m
    by (metis max.cobounded1 restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def)
qed

lemma dist_le_dist_right_prod\<^sub>m\<^sub>a\<^sub>x : \<open>dist x y \<le> dist_right_prod\<^sub>m\<^sub>a\<^sub>x TYPE('b \<times>\<^sub>m\<^sub>a\<^sub>x 'a) x y\<close>
  by (simp add: dist_le_dist_left_prod\<^sub>m\<^sub>a\<^sub>x dist_right_prod\<^sub>m\<^sub>a\<^sub>x_is_dist_left_prod\<^sub>m\<^sub>a\<^sub>x)



lemma 
  fixes p1 p2 :: \<open>'a :: decseq_restriction_space \<times>\<^sub>m\<^sub>a\<^sub>x 'b :: decseq_restriction_space\<close>
  shows dist_prod\<^sub>m\<^sub>a\<^sub>x_le_max_dist_left_prod\<^sub>m\<^sub>a\<^sub>x_dist_right_prod\<^sub>m\<^sub>a\<^sub>x : 
    \<open>dist p1 p2 \<le> max (dist_left_prod\<^sub>m\<^sub>a\<^sub>x  TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2))
                           (dist_right_prod\<^sub>m\<^sub>a\<^sub>x TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2))\<close>
proof -
  interpret left  : DecseqRestrictionSpace \<open>(\<down>)\<close> \<open>(=)\<close> \<open>UNIV\<close>
    \<open>restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b)\<close> \<open>dist_left_prod\<^sub>m\<^sub>a\<^sub>x TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b)\<close>
    by unfold_locales
      (simp_all add: restriction_\<sigma>_tendsto_zero dist_left_prod\<^sub>m\<^sub>a\<^sub>x_def decseq_restriction_\<sigma>)

  interpret right : DecseqRestrictionSpace \<open>(\<down>)\<close> \<open>(=)\<close> \<open>UNIV :: 'b set\<close>
    \<open>restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b)\<close> \<open>dist_right_prod\<^sub>m\<^sub>a\<^sub>x TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b)\<close>
    by unfold_locales
      (simp_all add: restriction_\<sigma>_tendsto_zero dist_right_prod\<^sub>m\<^sub>a\<^sub>x_def decseq_restriction_\<sigma>)

  show \<open>dist p1 p2 \<le> max (dist_left_prod\<^sub>m\<^sub>a\<^sub>x  TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2))
                          (dist_right_prod\<^sub>m\<^sub>a\<^sub>x TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2))\<close>
    by (auto simp add: dist_restriction_is_bis left.dist_restriction_is_bis
        right.dist_restriction_is_bis prod\<^sub>m\<^sub>a\<^sub>x.expand restriction_prod\<^sub>m\<^sub>a\<^sub>x_def')
      (smt (verit, best) Collect_cong nle_le restriction_related_le)
qed


default_sort type \<comment>\<open>Back to normal.\<close>



subsubsection \<open>Complete Restriction Space\<close>

text \<open>When the instances \<^typ>\<open>'a\<close> and \<^typ>\<open>'b\<close> of \<^class>\<open>decseq_restriction_space\<close>
      are also instances of \<^class>\<open>complete_space\<close>,
      the type \<^typ>\<open>'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b\<close> is an instance of \<^class>\<open>complete_space\<close>.\<close>

lemma restriction_chain_prod\<^sub>m\<^sub>a\<^sub>x_iff :
  \<open>restriction_chain \<sigma> \<longleftrightarrow> restriction_chain (\<lambda>n. fst\<^sub>m\<^sub>a\<^sub>x (\<sigma> n)) \<and>
                              restriction_chain (\<lambda>n. snd\<^sub>m\<^sub>a\<^sub>x (\<sigma> n))\<close>
  by (simp add: restriction_chain_def, transfer)
    (metis fst_conv prod.collapse restriction_prod_def snd_conv)

lemma restriction_tendsto_prod\<^sub>m\<^sub>a\<^sub>x_iff :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longleftrightarrow> (\<lambda>n. fst\<^sub>m\<^sub>a\<^sub>x (\<sigma> n)) \<midarrow>\<down>\<rightarrow> fst\<^sub>m\<^sub>a\<^sub>x \<Sigma> \<and> (\<lambda>n. snd\<^sub>m\<^sub>a\<^sub>x (\<sigma> n)) \<midarrow>\<down>\<rightarrow> snd\<^sub>m\<^sub>a\<^sub>x \<Sigma>\<close>
  by (simp add: restriction_tendsto_def, transfer, simp add: restriction_prod_def)
    (meson nle_le order.trans)

lemma restriction_convergent_prod\<^sub>m\<^sub>a\<^sub>x_iff :
  \<open>restriction_convergent \<sigma> \<longleftrightarrow> restriction_convergent (\<lambda>n. fst\<^sub>m\<^sub>a\<^sub>x (\<sigma> n)) \<and>
                                restriction_convergent (\<lambda>n. snd\<^sub>m\<^sub>a\<^sub>x (\<sigma> n))\<close>
  by (simp add: restriction_convergent_def restriction_tendsto_prod\<^sub>m\<^sub>a\<^sub>x_iff)
    (metis prod\<^sub>m\<^sub>a\<^sub>x.sel)


instance prod\<^sub>m\<^sub>a\<^sub>x :: (complete_decseq_restriction_space, complete_decseq_restriction_space)
  complete_decseq_restriction_space
proof (intro_classes, transfer)
  fix \<sigma> :: \<open>nat \<Rightarrow> 'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b\<close> assume \<open>chain\<^sub>\<down> \<sigma>\<close>
  hence \<open>chain\<^sub>\<down> (\<lambda>n. fst\<^sub>m\<^sub>a\<^sub>x (\<sigma> n))\<close> \<open>chain\<^sub>\<down> (\<lambda>n. snd\<^sub>m\<^sub>a\<^sub>x (\<sigma> n))\<close>
    by (simp_all add: restriction_chain_prod\<^sub>m\<^sub>a\<^sub>x_iff)
  hence \<open>convergent\<^sub>\<down> (\<lambda>n. fst\<^sub>m\<^sub>a\<^sub>x (\<sigma> n))\<close> \<open>convergent\<^sub>\<down> (\<lambda>n. snd\<^sub>m\<^sub>a\<^sub>x (\<sigma> n))\<close>
    by (simp_all add: restriction_chain_imp_restriction_convergent)
  thus \<open>convergent\<^sub>\<down> \<sigma>\<close>
    by (simp add: restriction_convergent_prod\<^sub>m\<^sub>a\<^sub>x_iff)
qed    



instance prod\<^sub>m\<^sub>a\<^sub>x :: (complete_strict_decseq_restriction_space, complete_strict_decseq_restriction_space)
  complete_strict_decseq_restriction_space
  by intro_classes (simp add: restriction_chain_imp_restriction_convergent)

instance prod\<^sub>m\<^sub>a\<^sub>x :: (complete_at_least_geometric_restriction_space, complete_at_least_geometric_restriction_space)
  complete_at_least_geometric_restriction_space
  by intro_classes (simp add: restriction_chain_imp_restriction_convergent)

instance prod\<^sub>m\<^sub>a\<^sub>x :: (complete_geometric_restriction_space, complete_geometric_restriction_space)
  complete_geometric_restriction_space
  by intro_classes (simp add: restriction_chain_imp_restriction_convergent)


text \<open>When the types \<^typ>\<open>'a\<close> and \<^typ>\<open>'b\<close> share the same restriction sequence,
      we have the following equality.\<close>


lemma same_restriction_\<sigma>_imp_restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_is [simp] :
  \<open>restriction_\<sigma> TYPE('b :: non_decseq_restriction_space) =
   restriction_\<sigma> TYPE('a :: non_decseq_restriction_space) \<Longrightarrow>
   restriction_\<sigma> TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) = restriction_\<sigma> TYPE('a)\<close>
  unfolding restriction_\<sigma>_prod\<^sub>m\<^sub>a\<^sub>x_def by simp


lemma same_restriction_\<sigma>_imp_dist_prod\<^sub>m\<^sub>a\<^sub>x_eq_max_dist_projections :
  \<open>dist p1 p2 = max (dist (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2)) (dist (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2))\<close>
  if same_restriction_\<sigma> [simp] : \<open>restriction_\<sigma> TYPE('b) = restriction_\<sigma> TYPE('a)\<close>
  for p1 p2 :: \<open>'a :: decseq_restriction_space \<times>\<^sub>m\<^sub>a\<^sub>x 'b :: decseq_restriction_space\<close>
proof (rule order_antisym)
  have \<open>dist_left_prod\<^sub>m\<^sub>a\<^sub>x TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2) = dist (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2)\<close>
    by (simp add: dist_left_prod\<^sub>m\<^sub>a\<^sub>x_def dist_restriction_is)
  moreover have \<open>dist_right_prod\<^sub>m\<^sub>a\<^sub>x TYPE('a \<times>\<^sub>m\<^sub>a\<^sub>x 'b) (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2) = dist (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2)\<close>
    by (simp add: dist_right_prod\<^sub>m\<^sub>a\<^sub>x_def dist_restriction_is)
  ultimately show \<open>dist p1 p2 \<le> max (dist (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2)) (dist (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2))\<close>
    by (metis dist_prod\<^sub>m\<^sub>a\<^sub>x_le_max_dist_left_prod\<^sub>m\<^sub>a\<^sub>x_dist_right_prod\<^sub>m\<^sub>a\<^sub>x)
next
  show \<open>max (dist (fst\<^sub>m\<^sub>a\<^sub>x p1) (fst\<^sub>m\<^sub>a\<^sub>x p2)) (dist (snd\<^sub>m\<^sub>a\<^sub>x p1) (snd\<^sub>m\<^sub>a\<^sub>x p2)) \<le> dist p1 p2\<close>
    by (fact max_dist_projections_le_dist_prod\<^sub>m\<^sub>a\<^sub>x)
qed



text \<open>Now, one can write things like \<^term>\<open>\<upsilon> \<lblot>x, y\<rblot> . f \<lblot>x, y\<rblot>\<close>.\<close>


text \<open>We could of course imagine more support for \<^typ>\<open>'a \<times>\<^sub>m\<^sub>a\<^sub>x 'b\<close> type,
      but as restriction spaces are intended to be used without recourse
      to metric spaces, we have not undertaken this task for the time being.\<close>




(*<*)
end
  (*>*)
