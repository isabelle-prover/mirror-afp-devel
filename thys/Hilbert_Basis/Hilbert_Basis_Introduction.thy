(*<*)
theory Hilbert_Basis_Introduction
  imports Main

begin
(*>*)


section\<open>A Proof of Hilbert Basis Theorems and 
          an Extension to Formal Power Series\<close>

text\<open>
The Hilbert Basis Theorem is enlisted in the extension of Wiedijk's 
catalogue "Formalizing 100 Theorems" \cite{source3} , a well-known collection 
of challenge problems for the formalisation of mathematics.

In this paper, we present a formal proof of several versions
of this theorem in Isabelle/HOL. Hilbert's basis theorem asserts that 
every ideal of a polynomial ring over a commutative ring has a finite generating 
family (a finite basis in Hilbert's terminology). 
A prominent alternative formulation is:
every polynomial ring over a Noetherian ring is also Noetherian.

In more detail, the statement and our generalization can be presented as follows:

  \<^item> \<^bold>\<open>Hilbert's Basis Theorem.\<close> Let \<open>\<RR>[X]\<close> denote the ring of polynomials in the indeterminate \<open>X\<close> 
  over the commutative ring \<open>\<RR>\<close>. Then \<open>\<RR>[X]\<close> is Noetherian iff \<open>\<RR>\<close> is.
  \<^item> \<^bold>\<open>Corrollary\<close>. \<open>\<RR>[X\<^sub>1,...,X\<^sub>n]\<close> is Noetherian iff \<open>\<RR>\<close> is. 
  \<^item> \<^bold>\<open>Extension\<close>. If \<open>\<RR>\<close> is a Noetherian ring, then \<open>\<RR>[[X]]\<close> is a Noetherian ring,
  where \<open>\<RR>[[X]]\<close> denotes the formal power series over the ring \<open>\<RR>\<close>.\\

We also provide isomorphisms between the three types of polynomial rings defined in HOL-Algebra.
Together with the fact that the noetherian property is preserved by isomorphism, we get 
Hilbert's Basis theorem for all three models. We believe that this technique has a wider
potential of applications in the AFP library.

\newpage\<close>
(*<*)
end
(*>*)