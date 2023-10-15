\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Galois\<close>
subsection \<open>Basic Abbreviations\<close>
theory Galois_Base
  imports
    Order_Functors_Base
begin

locale galois = order_functors
begin

text \<open>The locale @{locale galois} serves to define concepts that ultimately lead
to the definition of Galois connections and Galois equivalences.
Galois connections and equivalences are special cases of adjoints and
adjoint equivalences, respectively, known from category theory.
As such, in what follows, we sometimes borrow vocabulary from category theory
to highlight this connection.

A \<^emph>\<open>Galois connection\<close> between two relations @{term "(\<le>\<^bsub>L\<^esub>)"} and
@{term "(\<le>\<^bsub>R\<^esub>)"} consists of two monotone functions (i.e. order functors)
@{term "l"} and @{term "r"} such that @{term "x \<le>\<^bsub>L\<^esub> r y \<longleftrightarrow> l x \<le>\<^bsub>R\<^esub> y"}.
We call this the \<^emph>\<open>Galois property\<close>.
@{term "l"} is called the \<^emph>\<open>left adjoint\<close> and @{term "r"} the \<^emph>\<open>right adjoint\<close>.
We call @{term "(\<le>\<^bsub>L\<^esub>)"} the \<^emph>\<open>left relation\<close> and @{term "(\<le>\<^bsub>R\<^esub>)"} the \<^emph>\<open>right relation\<close>.
By composing the adjoints, we obtain the unit @{term "\<eta>"} and counit @{term "\<epsilon>"}
of the Galois connection.\<close>

end

end