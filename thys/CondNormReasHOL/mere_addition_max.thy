section \<open>The Mere Addition Paradox: Max Rule\<close>

  text \<open>There are surprising results with the max rule. Transitivity alone generates an inconsistencty
only when combined with totality. What is more, given transitivity (or quasi-transitivity) alone, 
the formulas turn out to be all satisfiable in an infinite model. \<close>

theory mere_addition_max  (* Christoph Benzmüller, Xavier Parent, 2024  *)
  imports DDLcube

begin

consts A::\<sigma> Aplus::\<sigma> B::\<sigma>  i1::i i2::i i3::i i4::i i5::i i6::i i7::i i8::i 

axiomatization where
 \<comment>\<open>A is striclty better than B\<close>
 PP0: "\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>A|A\<^bold>\<or>B>\<^bold>\<and>\<circle><\<^bold>\<not>B|A\<^bold>\<or>B>)\<rfloor>" and
 \<comment>\<open>Aplus is at least as good as A\<close>
 PP1: "\<lfloor>\<^bold>\<not>\<circle><\<^bold>\<not>Aplus|A\<^bold>\<or>Aplus>\<rfloor>" and
 \<comment>\<open>B is strictly better than Aplus\<close>
 PP2: "\<lfloor>(\<^bold>\<not>\<circle><\<^bold>\<not>B|Aplus\<^bold>\<or>B> \<^bold>\<and> \<circle><\<^bold>\<not>Aplus|Aplus\<^bold>\<or>B>)\<rfloor>" 


  text \<open>Nitpick finds no finite model when the betterness 
   relation is assumed to be transitive:\<close>

theorem T0:
  assumes transitivity  
  shows True
  nitpick [satisfy,expect=none] \<comment>\<open>no model found\<close>
  oops  

  text \<open>Nitpick shows consistency in the absence of transitivity:\<close>

theorem T1:
  shows True
  nitpick [satisfy,expect=genuine,card i=3]  \<comment>\<open>model found\<close>
  oops

  text \<open>Sledgehammer confirms inconsistency in the presence of the interval order condition:\<close>

theorem T2:
  assumes reflexivity and Ferrers
  shows False
  \<comment>\<open>sledgehammer\<close>
  by (metis PP0 PP1 PP2 assms(1) assms(2))
  
  text \<open>Nitpick shows consistency if transitivity is weakened into acyclicity:\<close>

theorem T3:
  assumes loopfree
  shows True
  nitpick [satisfy,expect=genuine,card=3] \<comment>\<open>model found\<close>
  oops

  text \<open>If transitivity or quasi-transitivity is assumed, Nitpick shows inconsistency assuming a finite model
   of cardinality (up to) seven (if we provide the exact dependencies)--for higher cardinalities 
   it returns a time out (depending on the computer it may prove falsity also for cardinality eight, 
   etc.:\<close>

theorem T4:
    assumes
      transitivity and
      OnlyOnes: "\<forall>y. y=i1 \<or> y=i2 \<or> y=i3 \<or> y=i4 \<or> y= i5 \<or> y= i6 \<or> y= i7"
    shows False
    using assfactor_def PP0 PP1 PP2 assms 
  \<comment>\<open>sledgehammer()\<close> 
  \<comment>\<open>proof found by Sledgehammer, but reconstruction fails\<close>
  oops

theorem T5:
    assumes
      Quasitransit and
      OnlyOnes: "\<forall>y. y=i1 \<or> y=i2 \<or> y=i3 \<or> y=i4 \<or> y= i5 \<or> y= i6 \<or> y=i7"
    shows False
  using assfactor_def PP0 PP1 PP2 assms
  \<comment>\<open>sledgehammer()\<close>
  \<comment>\<open>proof found by Sledgehammer, but reconstruction fails\<close>
  oops

text \<open>Infinity is encoded as follows: there is a surjective mapping G from 
   domain i to a proper subset M of domain i. Testing whether infinity holds in general Nitpick 
finds a countermodel:\<close>

abbreviation "infinity \<equiv> \<exists>M. (\<exists>z::i. \<not>(M z) \<and> (\<exists>G. (\<forall>y::i. (\<exists>x. (M x) \<and> (G x) = y))))"

lemma "infinity" nitpick[expect=genuine] oops \<comment>\<open>countermodel found\<close>

  text \<open>Now we run the same query under the assumption of (quasi-)transitivity: we do 
not get any finite countermodel reported anymore:\<close>

lemma 
  assumes transitivity
  shows   infinity
  \<comment>\<open>nitpick\<close>   \<comment>\<open>no countermodel found anymore; nitpicks runs out of time\<close>
  \<comment>\<open>sledgehammer\<close>  \<comment>\<open>but the provers are still too weak to prove it automatically; see \cite{J68} for a pen and paper proof\<close>
  oops

lemma 
  assumes Quasitransit 
  shows   infinity
  \<comment>\<open>nitpick\<close>   \<comment>\<open>no countermodel found anymore; nitpicks runs out of time\<close>
  \<comment>\<open>sledgehammer\<close>  \<comment>\<open>but the provers are still too weak to prove it automatically; see \cite{J68} for a pen and paper proof\<close>
   oops

   text \<open>Transitivity and totality together give inconsistency:\<close>

theorem T0':
  assumes transitivity and totality  
  shows False
  \<comment>\<open>sledgehammer\<close>
  by (metis PP0 PP1 PP2 assms(1) assms(2)) 

end
