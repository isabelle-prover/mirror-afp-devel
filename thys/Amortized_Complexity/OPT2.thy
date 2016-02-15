(*  Title:       Analysis of OPT2
    Author:      Max Haslbeck
*)
(*<*)
theory OPT2
imports 
Partial_Cost_Model
RExp_Var
begin

lemma "(N::nat set) \<noteq> {} \<Longrightarrow> Inf N : N"
unfolding Inf_nat_def using LeastI[of "%x. x : N"] by force

lemma nn_contains_Inf:
  fixes S :: "nat set"
  assumes nn: "S \<noteq> {}"
  shows "Inf S \<in> S"
using assms Inf_nat_def LeastI by force

(*>*)

chapter "OPT2: an Optimal Algorithm for Lists of Length 2"

text {*
\label{ch:OPT2}


One key feature of the list factoring technique, introduced in the last chapter, is certainly that
even complicated algorithms for the list update problem are surprisingly simple on lists of length $2$.
It is even possible to state an optimal offline algorithm: OPT2.

We have seen in the analysis of MTF and BIT, that in principle competitive analysis can be carried 
out without any knowledge of the optimal offline algorithm. With OPT2 we have more information about
the structure of the optimal algorithm which can be used when proving competitivness of algorithms 
for the list update problem on lists of size $2$.

In this chapter we study the nature of OPT2: we give its definition due to Reingold and Westbrook
\cite{reingold96off}, show that it indeed attains the optimal cost on lists of size 2 and then
determine the cost of OPT2 on different specific request sequences.

*}

section "Formalization of OPT2"
(*<*)
fun OPT2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> (nat * nat list) list" where
  "OPT2 [] [x,y] = []"
| "OPT2 [a] [x,y] = [(0,[])]"
| "OPT2 (a#b#\<sigma>') [x,y] =  (if a=x then (0,[]) # (OPT2 (b#\<sigma>') [x,y])
                                  else (if b=x then (0,[])# (OPT2 (b#\<sigma>') [x,y])
                                               else (1,[])# (OPT2 (b#\<sigma>') [y,x])))"
         

lemma OPT2_length: "length (OPT2 \<sigma> [x, y]) = length \<sigma>"
apply(induct \<sigma> arbitrary: x y)
  apply(simp)
  apply(case_tac \<sigma>) by(auto)

lemma OPT2x: "OPT2 (x#\<sigma>') [x,y] = (0,[])#(OPT2 \<sigma>' [x,y])"
apply(cases \<sigma>') by (simp_all)


 
(*>*)

text {*

First we state the informal definition due to Reingold and Westbrook \cite{reingold96off}:

\begin{definition}[OPT2 informal]
After each request, move the requested item to the front via free exchanges if the next request is
also to that item. Otherwise do nothing.
\end{definition}

Observe that this algorithm only needs knowledge of the current and next request.
Thus OPT2 is neither a pure offline nor an online algorithm; it is called an algorithm with lookahead.
Further remarks on such algorithms can be found in the last section of this chapter.

We define a function OPT2 that, given a request sequence and an initial list of two elements,
generates OPT2's strategy:

\begin{definition}[OPT2]@{text " "}\\
\begin{tabular}{l@ {~~@{text "="}~~} p{10cm}}
 @{thm (lhs) OPT2.simps(1)[no_vars]} & @{thm (rhs) OPT2.simps(1)[no_vars]}\\
 @{thm (lhs) OPT2.simps(2)[no_vars]} & @{thm (rhs) OPT2.simps(2)[no_vars]}\\
 @{thm (lhs) OPT2.simps(3)[no_vars]} & @{thm[break] (rhs) OPT2.simps(3)[no_vars]} 
\end{tabular}
\end{definition}

Two simple properties of OPT2 can be stated:
The length of the strategy matches the length of the request sequence and
if the next requested element is in front of the list OPT2 will not do anything in this step.
Recall that an action consists of the number of positions the requested
element is moved forward by free exchanges and a list of indices for the paid exchanges. 

\begin{lemma}
\label{thmOPT2x}
@{thm OPT2_length[no_vars] OPT2x[no_vars]}
\end{lemma}

*}


section "OPT2 is Optimal on Lists of Length 2"

(*<*)
 
lemma swapOpt: "T\<^sub>p_opt [x,y] \<sigma> \<le> 1 + T\<^sub>p_opt [y,x] \<sigma>"
proof -
  show ?thesis
  proof (cases "length \<sigma> > 0")
    case True

    have "T\<^sub>p_opt [y,x] \<sigma> \<in> {T\<^sub>p [y, x] \<sigma> as |as. length as = length \<sigma>}"
    unfolding T_opt_def 
      apply(rule nn_contains_Inf)
      apply(auto) by (rule Ex_list_of_length)

    then obtain asyx where costyx: "T\<^sub>p [y,x] \<sigma> asyx = T\<^sub>p_opt [y,x] \<sigma>"
                       and lenyx: "length asyx = length \<sigma>"
              unfolding T_opt_def by auto

    from True lenyx have "length asyx > 0" by auto
    then obtain A asyx' where aa: "asyx = A # asyx'" using list.exhaust by blast
    then obtain m1 a1 where AA: "A = (m1,a1)" by fastforce
    
    let ?asxy = "(m1,a1@[0]) # asyx'"
    
    from True obtain q \<sigma>' where qq: "\<sigma> = q # \<sigma>'" using list.exhaust by blast
  
    have t: "t\<^sub>p [x, y] q (m1, a1@[0]) = Suc (t\<^sub>p [y, x] q (m1, a1))"
    unfolding t\<^sub>p_def
    apply(simp) unfolding swap_def by (simp)
  
    have s: "step [x, y] q (m1, a1 @ [0]) = step [y, x] q (m1, a1)" 
    unfolding step_def mtf2_def by(simp add: swap_def)
  
    have T: "T\<^sub>p [x,y] \<sigma> ?asxy = 1 + T\<^sub>p [y,x] \<sigma> asyx" unfolding qq aa AA by(auto simp add: s t)
   
    have l: "1 + T\<^sub>p_opt [y,x] \<sigma> = T\<^sub>p [x, y] \<sigma> ?asxy" using T costyx by simp
    have "length ?asxy = length \<sigma>" using lenyx aa by auto
    then have inside: "?asxy \<in> {as. size as = size \<sigma>}" by force
    then have b: "T\<^sub>p [x, y] \<sigma> ?asxy \<in> {T\<^sub>p [x, y] \<sigma> as | as. size as = size \<sigma>}" by auto

    then show ?thesis unfolding l unfolding T_opt_def
      apply(rule cInf_lower) by simp
  qed (simp add: T_opt_def)         
qed
(*>*)

text {*

Before we tackle the proof for OPT2 observe that the following lemma holds:

\begin{lemma}
\label{thm_swapOpt}
@{thm swapOpt[no_vars]}
\end{lemma}
\begin{proof}
Suppose we have a strategy @{term "S"} to optimally serve the request sequence @{term "\<sigma>"} with initial list @{term "[y,x]"}
and look for a strategy to serve @{term "\<sigma>"} starting from @{term "[x,y]"}.
We can first swap the two elements by one paid exchange and then use @{term "S"} to serve the sequence.
This way we can bound the optimal cost for @{term "\<sigma>"} starting from @{term "[x,y]"}.
\end{proof}

*}


(*<*)

section "Lemmas"

lemma tt: "a \<in> {x,y} \<Longrightarrow> OPT2 (rest1) (step [x,y] a (hd (OPT2 (a # rest1) [x, y])))
       = tl (OPT2 (a # rest1) [x, y])"
apply(cases rest1) by(auto simp add: step_def mtf2_def swap_def)

lemma splitqsallg: "Strat \<noteq> [] \<Longrightarrow> a \<in> {x,y} \<Longrightarrow>
         t\<^sub>p [x, y] a (hd (Strat)) +
          (let L=step [x,y] a (hd (Strat)) 
              in T\<^sub>p L (rest1) (tl Strat)) =  T\<^sub>p [x, y] (a # rest1) Strat"
proof -
  assume ne: "Strat \<noteq> []"
  assume axy: "a \<in> {x,y}" (* not needed *)
  have "T\<^sub>p [x, y] (a # rest1) (Strat) 
        = T\<^sub>p [x, y] (a # rest1) ((hd (Strat)) # (tl (Strat)))"
        by(simp only: List.list.collapse[OF ne])
  then show ?thesis by auto
qed

lemma splitqs: "a \<in> {x,y} \<Longrightarrow> T\<^sub>p [x, y] (a # rest1) (OPT2 (a # rest1) [x, y])
        =  t\<^sub>p [x, y] a (hd (OPT2 (a # rest1) [x, y])) +
          (let L=step [x,y] a (hd (OPT2 (a # rest1) [x, y])) 
              in T\<^sub>p L (rest1) (OPT2 (rest1) L))"
proof -
  assume axy: "a \<in> {x,y}"
  have ne: "OPT2 (a # rest1) [x, y] \<noteq> []" apply(cases rest1) by(simp_all)
  have "T\<^sub>p [x, y] (a # rest1) (OPT2 (a # rest1) [x, y]) 
        = T\<^sub>p [x, y] (a # rest1) ((hd (OPT2 (a # rest1) [x, y])) # (tl (OPT2 (a # rest1) [x, y])))"
        by(simp only: List.list.collapse[OF ne])
  also have "\<dots> = T\<^sub>p [x, y] (a # rest1) ((hd (OPT2 (a # rest1) [x, y])) # (OPT2 (rest1) (step [x,y] a (hd (OPT2 (a # rest1) [x, y])))))"
      by(simp only: tt[OF axy])
  also have "\<dots> =   t\<^sub>p [x, y] a (hd (OPT2 (a # rest1) [x, y])) +
          (let L=step [x,y] a (hd (OPT2 (a # rest1) [x, y])) 
              in T\<^sub>p L (rest1) (OPT2 (rest1) L))" by(simp)
  finally show ?thesis .
qed

lemma tpx: "t\<^sub>p [x, y] x (hd (OPT2 (x # rest1) [x, y])) = 0"
by (simp add: OPT2x t\<^sub>p_def)

lemma yup: "T\<^sub>p [x, y] (x # rest1) (OPT2 (x # rest1) [x, y])
        = (let L=step [x,y] x (hd (OPT2 (x # rest1) [x, y])) 
              in T\<^sub>p L (rest1) (OPT2 (rest1) L))"
by (simp add: splitqs tpx)

lemma swapsxy: "A \<in> { [x,y], [y,x]} \<Longrightarrow> swaps sws A \<in> { [x,y], [y,x]}"
apply(induct sws)
  apply(simp)
  apply(simp) unfolding swap_def by auto

lemma mtf2xy: "A \<in> { [x,y], [y,x]} \<Longrightarrow> r\<in>{x,y} \<Longrightarrow> mtf2 a r A \<in> { [x,y], [y,x]}"
by (metis mtf2_def swapsxy)

lemma stepxy: assumes "q \<in> {x,y}" "A \<in> { [x,y], [y,x]}" 
    shows "step A q a \<in> { [x,y], [y,x]}"
unfolding step_def apply(simp only: split_def Let_def)
apply(rule mtf2xy)
  apply(rule swapsxy) by fact+
  
(*>*)



text {*

Let us now turn to proving OPT2's optimality. As OPT2 obviously pays at least as much as the optimal
offline algorithm the more demanding part of the proof is showing that OPT2 pays no more than 
the optimal offline algorithm:

*}



(*<*)
lemma OPT2_is_lb: "set \<sigma> \<subseteq> {x,y} \<Longrightarrow> x\<noteq>y \<Longrightarrow> T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) \<le> T\<^sub>p_opt [x,y] \<sigma>"
(*>*)

text_raw  {*
\begin{lemma}[{\cite[Proposition 4]{reingold96off}}]
@{term "?thesis"}
\end{lemma}
\begin{proof}
*}
text {*

First we will give an outline of the proof and then show the details for one case.

Assume the initial list to be @{term "[x,y]"} and only elements @{term "x"} and @{term "y"}
being requested.

The lemma is proven by well-founded induction on the length of the request sequence @{term "\<sigma>"}.

We start by doing a case distinction on whether the requested element is @{term x} and thus
in front of the list.

If indeed @{term x} is requested, no matter what requests follow, OPT2 will do nothing in this move
and keep the list untouched (Lemma \ref{thmOPT2x}).
The optimal offline algorithm now has two options:
Either it acts as OPT2 -- then the induction hypothesis can be applied right away --
or it swaps the list, then we can use Lemma \ref{thm_swapOpt} and it remains to show 
that serving the request while reversing the list costs at least $1$ more than acting like OPT2 and
leaving the list untouched.

In the second case (the requested element is @{term y}) another case distinction
has to be done on the second requested element. Depending on whether the optimal algorithm transforms
the list as OPT2 or not, the induction hypothesis can be applied at once or again with lemma
\ref{thm_swapOpt}.

We will present the first case in more detail. As for the second case, the proof is established 
essentially by the same method, only some more case distinctions obscure the argument.
For more details feel free to look into the proof text.


*}
(*<*)
proof (induct "length \<sigma>" arbitrary: x y \<sigma> rule: less_induct)
  case (less)
  show ?case
  proof (cases \<sigma>)
    case (Cons a \<sigma>')
    note Cons1=Cons
    show ?thesis unfolding Cons
      proof(cases "a=x") (* der Fall, dass das vordere Element gefragt wird *)
        case True
        from True Cons have qsform: "\<sigma> = x#\<sigma>'" by auto
        thm cInf_greatest Ex_list_of_length
        have up: "T\<^sub>p [x, y] (x # \<sigma>') (OPT2 (x # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (x # \<sigma>')"
          unfolding True

(*>*)
text {*

Consider now the case that the request sequence is of the form @{thm qsform[no_vars]}.
Our current goal is @{term ?thesis}.

*}


(*<*)
          unfolding T_opt_def apply(rule cInf_greatest)
            apply(simp add: Ex_list_of_length)
            proof -
              fix el
              assume "el \<in> {T\<^sub>p [x, y] (x # \<sigma>') as |as. length as = length (x # \<sigma>')}"
              then obtain Strat where lStrat: "length Strat = length (x # \<sigma>')"
                        and el: "T\<^sub>p [x, y] (x # \<sigma>') Strat = el" by auto
              then have ne: "Strat \<noteq> []" by auto
              let ?LA="step [x,y] x (hd (OPT2 (x # \<sigma>') [x, y]))"
              
              have  E0:  "T\<^sub>p [x, y] (x # \<sigma>') (OPT2 (x # \<sigma>') [x, y])
                            =T\<^sub>p ?LA (\<sigma>') (OPT2 (\<sigma>') ?LA)" using yup by auto
              also have E1: "\<dots> = T\<^sub>p [x,y] (\<sigma>') (OPT2 (\<sigma>') [x,y])" by (simp add: OPT2x step_def)
              also have E2: "\<dots> \<le>  T\<^sub>p_opt [x,y] \<sigma>'" apply(rule less(1)) using Cons less(2,3) by auto
              also have "\<dots> \<le> T\<^sub>p [x, y] (x # \<sigma>') Strat"
                   proof (cases "(step [x, y] x (hd Strat)) = [x,y]")
                      case True
                      thm exI[where x="tl Strat"]
                      have aha: "T\<^sub>p_opt [x, y] \<sigma>' \<le> T\<^sub>p [x, y] \<sigma>' (tl Strat)"                     
                        unfolding T_opt_def apply(rule cInf_lower)
                          apply(auto) apply(rule exI[where x="tl Strat"]) using lStrat by auto

                      also have E4: "\<dots> \<le> t\<^sub>p [x, y] x (hd Strat) + T\<^sub>p (step [x, y] x (hd Strat)) \<sigma>' (tl Strat)" 
                        unfolding True by(simp)
                      also have E5: "\<dots> = T\<^sub>p [x, y] (x # \<sigma>') Strat" using splitqsallg[of Strat x x y \<sigma>', OF ne, simplified]
                        by (auto)
                      finally show ?thesis by auto  

(*>*)
text {*
To show that, we fix an arbitrary optimal strategy @{term "Strat"}.

In the case that @{term "Strat"} leaves the list untouched (@{thm True}) the induction hypothesis
suffices to complete the proof:

\begin{center}
\begin{tabular}{l@ {~~@{text ""}~~} p{14cm}}
  & @{thm (lhs) E0}\\ 
@{text "="} & @{thm[break] (rhs) E0}\\
@{text "="} & @{thm (rhs) E1}\\
@{text "\<le>"} & @{thm (rhs) E2}\\
@{text "\<le>"} & @{thm (rhs) aha}\\
@{text "\<le>"} & @{thm (rhs) E4}\\
@{text "="} & @{thm (rhs) E5}
\end{tabular}
\end{center}

First we unfold the calculation of OPT2's strategy: it will not do anything and also pay nothing,
as @{term x} is located in the first position.
Then we can apply the induction hypothesis for the shorter request sequence @{term "\<sigma>'"}.
Obviously, if we use the tail of @{term Strat} as a strategy for the request sequence @{term \<sigma>'} it
will cost at least as much as the optimal strategy.
The last two steps bridge the gap to the total cost of strategy @{term Strat} on the whole request sequence
and are justified by the fact that @{term Strat} does not change the list in this case and the cost of that step is
non-negative.

*}
(*<*)

            
                   next
                      case False
                      have tp1: "t\<^sub>p [x, y] x (hd Strat) \<ge> 1"
                      proof (rule ccontr)
                        let ?a = "hd Strat"
                        assume "\<not> 1 \<le> t\<^sub>p [x, y] x ?a"
                        then have tp0: "t\<^sub>p [x, y] x ?a = 0" by auto
                        then have "size (snd ?a) = 0" unfolding t\<^sub>p_def by(simp add: split_def)
                        then have nopaid: "(snd ?a) = []" by auto
                        have "step [x, y] x ?a = [x, y]"
                          unfolding step_def apply(simp add: split_def nopaid)
                          unfolding mtf2_def by(simp)
                        then show "False" using False by auto
                      qed

                      from False have yx: "step [x, y] x (hd Strat) = [y, x]"
                        using stepxy[where x=x and y=y and a="hd Strat"] by auto

                      have E3: "T\<^sub>p_opt [x, y] \<sigma>' \<le> 1 + T\<^sub>p_opt [y, x] \<sigma>'" using swapOpt by auto
                      also have E4: "\<dots> \<le> 1 + T\<^sub>p [y, x] \<sigma>' (tl Strat)"        
                        apply(simp) unfolding T_opt_def apply(rule cInf_lower)
                          apply(auto) apply(rule exI[where x="tl Strat"]) using lStrat by auto
                      also have E5: "\<dots> = 1 + T\<^sub>p (step [x, y] x (hd Strat)) \<sigma>' (tl Strat)" using yx by auto
                      also have E6: "\<dots> \<le> t\<^sub>p [x, y] x (hd Strat) + T\<^sub>p (step [x, y] x (hd Strat)) \<sigma>' (tl Strat)" using tp1 by auto
                      
                      also have E7: "\<dots> = T\<^sub>p [x, y] (x # \<sigma>') Strat" using splitqsallg[of Strat x x y \<sigma>', OF ne, simplified]
                         by (auto)
                      finally show ?thesis by auto(*>*)

text {*

The case that @{term "Strat"} reverses the list (@{thm yx}) is a bit more intricate as we cannot
simply apply the induction hypothesis. Lemma \ref{thm_swapOpt} comes to the rescue:

\begin{center}
\begin{tabular}{l@ {~~@{text ""}~~} p{14cm}}
  & @{thm (lhs) E0}\\ 
@{text "="} & @{thm[break] (rhs) E0}\\
@{text "="} & @{thm (rhs) E1}\\
@{text "\<le>"} & @{thm (rhs) E2}\\
@{text "\<le>"} & @{thm (rhs) E3}\\
@{text "\<le>"} & @{thm (rhs) E4}\\
@{text "="} & @{thm (rhs) E5}\\
@{text "\<le>"} & @{thm (rhs) E6}\\
@{text "="} & @{thm (rhs) E7}
\end{tabular}
\end{center}

We begin as for the first case, but after applying the induction hypothesis we use Lemma \ref{thm_swapOpt}.
Then again using @{term Strat} on the remainder of the request sequence costs at least as much as the
optimal strategy and we bridge the gap until we obtain the total cost of @{term Strat} on the request sequence.
The tricky part, showing that @{thm tp1[no_vars]}, can be done by a proof by contradiction:
if the strategy does not pay anything for the serving of the request, it must not do any paid exchange
but then it is not able to reverse the list.


*}


(*<*)
                   qed
              also have "\<dots> = el" using True el by simp
              finally show "T\<^sub>p [x, y] (x # \<sigma>') (OPT2 (x # \<sigma>') [x, y]) \<le> el" by auto        
            qed
         then show "T\<^sub>p [x, y] (a # \<sigma>') (OPT2 (a # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (a # \<sigma>')"
         using True by simp
      next


        case False (* der Fall 2: dass das hintere Element zuerst gefragt wird *)
        with less Cons have ay: "a=y" by auto
        show "T\<^sub>p [x, y] (a # \<sigma>') (OPT2 (a # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (a # \<sigma>')" unfolding ay
        proof(cases \<sigma>')
          case Nil (* simpler Fall 2x: das war schon der letzte request *)

          have up: "T\<^sub>p_opt [x, y] [y] \<ge> 1"
            unfolding T_opt_def apply(rule cInf_greatest)
            apply(simp add: Ex_list_of_length)
            proof -
              fix el
              assume "el \<in> {T\<^sub>p [x, y] [y] as |as. length as = length [y]}"
              then obtain Strat where Strat: "length Strat = length [y]" and
                            el: "el = T\<^sub>p [x, y] [y] Strat " by auto
              from Strat obtain a where a: "Strat = [a]" by (metis Suc_length_conv length_0_conv)
              show "1 \<le> el" unfolding el a apply(simp) unfolding t\<^sub>p_def apply(simp add: split_def)
                apply(cases "snd a")
                  apply(simp add: less(3))
                  by(simp)
            qed
          thm exI[where x="[([],0)]"]

          show "T\<^sub>p [x, y] (y # \<sigma>') (OPT2 (y # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (y # \<sigma>')" unfolding Nil
            apply(simp) unfolding t\<^sub>p_def using less(3) apply(simp)
            using up by(simp)
        next
          case (Cons b rest2) (* simpler Fall 2y: es kommen noch requests *)

          show up: "T\<^sub>p [x, y] (y # \<sigma>') (OPT2 (y # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (y # \<sigma>')"
            unfolding Cons
          proof (cases "b=x") (* Fall 2y_x: request seq= [y,x] *)
            case True
            
            show "T\<^sub>p [x, y] (y # b # rest2) (OPT2 (y # b # rest2) [x, y]) \<le> T\<^sub>p_opt [x, y] (y # b # rest2)"
              unfolding True
              unfolding T_opt_def apply(rule cInf_greatest)
                apply(simp add: Ex_list_of_length)
                proof - (* jetzt muss ich für jede Strategie in T\<^sub>p_opt zeigen, dass er nicht besser
                          ist als OPT2, eigentlich würde ich hier gerne ausrechnen wie dieses Set aussieht:
                          es gibt nämlich nur endlich viele möglichkeiten! *)
                  fix el
                  assume "el \<in> {T\<^sub>p [x, y] (y # x # rest2) as |as. length as = length (y # x # rest2)}"
                  then obtain Strat where lenStrat: "length Strat = length (y # x # rest2)" and
                               Strat: "el = T\<^sub>p [x, y] (y # x # rest2) Strat" by auto
                  (* ich nehm eine Strategie aus der Menge und nenn sie Strat *)
                  have v: " set rest2 \<subseteq> {x, y}" using less(2)[unfolded Cons1 Cons] by auto
                  

                  (* ich weiß dass Strat zu beginn L=[x,y] hat,
                    aber nicht genau wie L nach 1 bzw. 2 requestes aussehen: *)
                  let ?L1 = "(step [x, y] y (hd Strat))"
                  let ?L2 = "(step ?L1 x (hd (tl Strat)))"

                  (* lets work on how Strat can look like: *)
                  let ?a1 = "hd Strat"
                  let ?a2 = "hd (tl Strat)"
                  let ?r = "tl (tl Strat)"

                  have "Strat = ?a1 # ?a2 # ?r" by (metis Nitpick.size_list_simp(2) Suc_length_conv lenStrat list.collapse list.discI list.inject)
                  
                  


                  have 1: "T\<^sub>p [x, y] (y # x # rest2) Strat
                        = t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))
                            + T\<^sub>p ?L2 rest2 (tl (tl Strat))"  
                    proof - 
                      have a: "Strat \<noteq> []" using lenStrat by auto
                      have b: "(tl Strat) \<noteq> []" using lenStrat by (metis Nitpick.size_list_simp(2) Suc_length_conv list.discI list.inject)

                      have 1: "T\<^sub>p [x, y] (y # x # rest2) Strat
                                = t\<^sub>p [x, y] y (hd Strat) + T\<^sub>p ?L1 (x # rest2) (tl Strat)"
                                  using splitqsallg[OF a, where a=y and x=x and y=y, simplified] by (simp)
                      have tt: "step [x, y] y (hd Strat) \<noteq> [x, y] \<Longrightarrow> step [x, y] y (hd Strat) = [y,x]" 
                        using stepxy[where A="[x,y]"] by blast

                      have 2: "T\<^sub>p ?L1 (x # rest2) (tl Strat) = t\<^sub>p ?L1 x (hd (tl Strat)) +  T\<^sub>p ?L2 (rest2) (tl (tl Strat))"
                                  apply(cases "?L1=[x,y]")
                                    using splitqsallg[OF b, where a=x and x=x and y=y, simplified] apply(auto)
                                    using tt splitqsallg[OF b, where a=x and x=y and y=x, simplified] by auto
                      thm splitqsallg
                      from 1 2 show ?thesis by auto
                    qed

                  have " T\<^sub>p [x, y] (y # x # rest2) (OPT2 (y # x # rest2) [x, y])
                    =  1 +  T\<^sub>p [x, y] (rest2) (OPT2 (rest2) [x, y])"
                    unfolding True
                    using less(3) by(simp add: t\<^sub>p_def step_def OPT2x)
                    thm Cons1 Cons less(2)
                  also have "\<dots> \<le> 1 +  T\<^sub>p_opt [x, y] (rest2)" apply(simp)
                    apply(rule less(1))
                      apply(simp add: less(2) Cons1 Cons)
                      apply(fact) by fact
                      thm cInf_lower
                  also

                  have "\<dots> \<le> T\<^sub>p [x, y] (y # x # rest2) Strat"
                  proof (cases "?L2 = [x,y]") (* falls Strat die Liste erzeugt, die auch OPT2 erzeugt,
                          kann ich einfach die iH verwenden *)
                    case True
                    have 2: "t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))
                            + T\<^sub>p [x,y] rest2 (tl (tl Strat)) \<ge> t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))
                            + T\<^sub>p_opt [x,y] rest2" apply(simp)
                            unfolding T_opt_def apply(rule cInf_lower)
                            apply(simp) apply(rule exI[where x="tl (tl Strat)"]) by (auto simp: lenStrat)
                    have 3: "t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))
                            + T\<^sub>p_opt [x,y] rest2 \<ge> 1 + T\<^sub>p_opt [x,y] rest2" apply(simp)
                            proof -
                              have "t\<^sub>p [x, y] y (hd Strat) \<ge> 1"
                              unfolding t\<^sub>p_def apply(simp add: split_def)
                              apply(cases "snd (hd Strat)") by (simp_all add: less(3))
                              then show "Suc 0 \<le> t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))" by auto
                            qed
                    from 1 2 3 True show ?thesis by auto
                  next
                    case False (* Falls Strat die Liste umdreht, muss ich die Abschätzung verwenden
                        und zeigen, dass mindestens 1 mehr gezahlt wird als bei OPT2 *)
                    note L2F=this
                    have L1: "?L1 \<in> {[x, y], [y, x]}" apply(rule stepxy) by simp_all
                    have "?L2 \<in> {[x, y], [y, x]}" apply(rule stepxy) using L1 by simp_all
                    with False have 2: "?L2 = [y,x]" by auto

                    thm 1
                    have k: "T\<^sub>p [x, y] (y # x # rest2) Strat
                        =   t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat)) +
                            T\<^sub>p [y,x] rest2 (tl (tl Strat))" using 1 2 by auto

                    have l: "t\<^sub>p [x, y] y (hd Strat) > 0"
                        using less(3) unfolding t\<^sub>p_def apply(cases "snd (hd Strat) = []")
                          by (simp_all add: split_def)

                    have r: "T\<^sub>p [x, y] (y # x # rest2) Strat \<ge> 2 + T\<^sub>p [y,x] rest2 (tl (tl Strat))"
                    proof (cases "?L1 = [x,y]") (* nochmal ein case distinct auf wie Strat
                        die Liste nach dem ersten Request hat *)
                      case True (* angenommen sie lässt sie gleich (also so wie OPT2) *)
                      note T=this
                      then have "t\<^sub>p ?L1 x (hd (tl Strat)) > 0" unfolding True
                        proof(cases "snd (hd (tl Strat)) = []")
                          case True
                          have "?L2 = [x,y]" unfolding T  apply(simp add: split_def step_def) 
                          unfolding True mtf2_def by(simp)
                          with L2F have "False" by auto
                          then show "0 < t\<^sub>p [x, y] x (hd (tl Strat))" ..
                        next
                          case False
                          then show "0 < t\<^sub>p [x, y] x (hd (tl Strat))"
                            unfolding t\<^sub>p_def by(simp add: split_def)
                        qed                          
                      with l have " t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat)) \<ge> 2" by auto
                      with k show ?thesis by auto
                    next
                      case False (* angenommen Strat dreht im ersten Schritt die Liste um *)
                      (*have "?L1 \<in> {[y,x], [x,y]}" using stepxy2[OF less(3)[symmetric], where A="[x,y]", simplified] by auto *)
                      from L1 False have 2: "?L1 = [y,x]" by auto
                      { fix k sws T
                        have "T\<in>{[x,y],[y,x]} \<Longrightarrow> mtf2 k x T = [y,x] \<Longrightarrow> T = [y,x]"
                          apply(rule ccontr) by (simp add: less(3) mtf2_def)
                      }
                      term ?L1
                      have t1: "t\<^sub>p [x, y] y (hd Strat) \<ge> 1" unfolding t\<^sub>p_def apply(simp add: split_def)
                        apply(cases "(snd (hd Strat))") using `x \<noteq> y` by auto
                      have t2: "t\<^sub>p [y,x] x (hd (tl Strat)) \<ge> 1" unfolding t\<^sub>p_def apply(simp add: split_def)
                        apply(cases "(snd (hd (tl Strat)))") using `x \<noteq> y` by auto
                      have "T\<^sub>p [x, y] (y # x # rest2) Strat
                          = t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p (step [x, y] y (hd Strat)) x (hd (tl Strat)) + T\<^sub>p [y, x] rest2 (tl (tl Strat))"
                            by(rule k)
                      with t1 t2 2 show ?thesis by auto
                    qed
                    have t: "T\<^sub>p [y, x] rest2 (tl (tl Strat)) \<ge> T\<^sub>p_opt [y, x] rest2" 
                      unfolding T_opt_def apply(rule cInf_lower)
                      apply(auto) apply(rule exI[where x="(tl (tl Strat))"]) by(simp add: lenStrat)
                    show ?thesis
                    proof -
                      have "1 + T\<^sub>p_opt [x, y] rest2 \<le> 2 + T\<^sub>p_opt [y, x] rest2"
                      using  swapOpt by auto
                      also have "\<dots> \<le> 2 + T\<^sub>p [y, x] rest2 (tl (tl Strat))" using t by auto
                      also have "\<dots> \<le> T\<^sub>p [x, y] (y # x # rest2) Strat" using r by auto
                      finally show ?thesis .
                    qed
                      
                  qed
                  also have "\<dots> = el" using Strat by auto
                  finally show "T\<^sub>p [x, y] (y # x # rest2) (OPT2 (y # x # rest2) [x, y]) \<le> el" .
                qed


          next
            case False (* Fall 2y_y *)
            with Cons1 Cons less(2) have bisy: "b=y" by auto
            with less(3) have "OPT2 (y # b # rest2) [x, y] = (1,[])# (OPT2 (b#rest2) [y,x])" by simp
            show "T\<^sub>p [x, y] (y # b # rest2) (OPT2 (y # b # rest2) [x, y]) \<le> T\<^sub>p_opt [x, y] (y # b # rest2)" 
              unfolding bisy
              unfolding T_opt_def apply(rule cInf_greatest)
                apply(simp add: Ex_list_of_length)
                proof - (* jetzt muss ich für jede Strategie in T\<^sub>p_opt zeigen, dass er nicht besser
                          ist als OPT2, eigentlich würde ich hier gerne ausrechnen wie dieses Set aussieht:
                          es gibt nämlich nur endlich viele möglichkeiten! *)
                  fix el
                  assume "el \<in> {T\<^sub>p [x, y] (y # y # rest2) as |as. length as = length (y # y # rest2)}"
                  then obtain Strat where lenStrat: "length Strat = length (y # y # rest2)" and
                               Strat: "el = T\<^sub>p [x, y] (y # y # rest2) Strat" by auto
                  (* ich nehm eine Strategie aus der Menge und nenn sie Strat *)
                  have v: " set rest2 \<subseteq> {x, y}" using less(2)[unfolded Cons1 Cons] by auto
                  

                  (* ich weiß dass Strat zu beginn L=[x,y] hat,
                    aber nicht genau wie L nach 1 bzw. 2 requestes aussehen: *)
                  let ?L1 = "(step [x, y] y (hd Strat))"
                  let ?L2 = "(step ?L1 y (hd (tl Strat)))"

                  (* lets work on how Strat can look like: *)
                  let ?a1 = "hd Strat"
                  let ?a2 = "hd (tl Strat)"
                  let ?r = "tl (tl Strat)"

                  have "Strat = ?a1 # ?a2 # ?r" by (metis Nitpick.size_list_simp(2) Suc_length_conv lenStrat list.collapse list.discI list.inject)
                  
                  


                  have 1: "T\<^sub>p [x, y] (y # y # rest2) Strat
                        = t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))
                            + T\<^sub>p ?L2 rest2 (tl (tl Strat))" 
                    proof - 
                      have a: "Strat \<noteq> []" using lenStrat by auto
                      have b: "(tl Strat) \<noteq> []" using lenStrat by (metis Nitpick.size_list_simp(2) Suc_length_conv list.discI list.inject)

                      have 1: "T\<^sub>p [x, y] (y # y # rest2) Strat
                                = t\<^sub>p [x, y] y (hd Strat) + T\<^sub>p ?L1 (y # rest2) (tl Strat)"
                                  using splitqsallg[OF a, where a=y and x=x and y=y, simplified] by (simp)
                      have tt: "step [x, y] y (hd Strat) \<noteq> [x, y] \<Longrightarrow> step [x, y] y (hd Strat) = [y,x]" 
                        using stepxy[where A="[x,y]"] by blast
                     
                      have 2: "T\<^sub>p ?L1 (y # rest2) (tl Strat) = t\<^sub>p ?L1 y (hd (tl Strat)) +  T\<^sub>p ?L2 (rest2) (tl (tl Strat))"
                                  apply(cases "?L1=[x,y]")
                                    using splitqsallg[OF b, where a=y and x=x and y=y, simplified] apply(auto)
                                    using tt splitqsallg[OF b, where a=y and x=y and y=x, simplified] by auto
                      thm splitqsallg
                      from 1 2 show ?thesis by auto
                    qed

                  have " T\<^sub>p [x, y] (y # y # rest2) (OPT2 (y # y # rest2) [x, y])
                    =  1 +  T\<^sub>p [y, x] (rest2) (OPT2 (rest2) [y, x])" 
                    using less(3) by(simp add: t\<^sub>p_def step_def mtf2_def swap_def OPT2x)
                    thm Cons1 Cons less(2)
                  also have "\<dots> \<le> 1 +  T\<^sub>p_opt [y, x] (rest2)" apply(simp)
                    apply(rule less(1))
                      apply(simp add: less(2) Cons1 Cons)
                      using v less(3) by(auto)
                      thm cInf_lower
                  also

                  have "\<dots> \<le> T\<^sub>p [x, y] (y # y # rest2) Strat"
                  proof (cases "?L2 = [y,x]") (* falls Strat die Liste erzeugt, die auch OPT2 erzeugt,
                          kann ich einfach die iH verwenden *)
                    case True
                    have 2: "t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))
                            + T\<^sub>p [y,x] rest2 (tl (tl Strat)) \<ge> t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))
                            + T\<^sub>p_opt [y,x] rest2" apply(simp)
                            unfolding T_opt_def apply(rule cInf_lower)
                            apply(simp) apply(rule exI[where x="tl (tl Strat)"]) by (auto simp: lenStrat)
                    have 3: "t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))
                            + T\<^sub>p_opt [y,x] rest2 \<ge> 1 + T\<^sub>p_opt [y,x] rest2" apply(simp)
                            proof -
                              have "t\<^sub>p [x, y] y (hd Strat) \<ge> 1"
                              unfolding t\<^sub>p_def apply(simp add: split_def)
                              apply(cases "snd (hd Strat)") by (simp_all add: less(3))
                              then show "Suc 0 \<le> t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))" by auto
                            qed
                    from 1 2 3 True show ?thesis by auto 
                    (* bis hier wars eigentlich copy paste von Fally_x*)
                  next
                    case False (* Falls Strat die Liste umdreht, muss ich die Abschätzung verwenden
                        und zeigen, dass mindestens 1 mehr gezahlt wird als bei OPT2 *)
                    note L2F=this
                    have L1: "?L1 \<in> {[x, y], [y, x]}" apply(rule stepxy) by simp_all
                    have "?L2 \<in> {[x, y], [y, x]}" apply(rule stepxy) using L1 by simp_all
                    with False have 2: "?L2 = [x,y]" by auto

                    thm 1
                    have k: "T\<^sub>p [x, y] (y # y # rest2) Strat
                        =   t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat)) +
                            T\<^sub>p [x,y] rest2 (tl (tl Strat))" using 1 2 by auto

                    have l: "t\<^sub>p [x, y] y (hd Strat) > 0"
                        using less(3) unfolding t\<^sub>p_def apply(cases "snd (hd Strat) = []")
                          by (simp_all add: split_def)

                    have r: "T\<^sub>p [x, y] (y # y # rest2) Strat \<ge> 2 + T\<^sub>p [x,y] rest2 (tl (tl Strat))"
                    proof (cases "?L1 = [y,x]") (* nochmal ein case distinct auf wie Strat
                        die Liste nach dem ersten Request hat *)
                      case False  (* False means: not act as OPT2 *)
                          (* angenommen sie lässt sie gleich (also nicht so wie OPT2) *)
                      from L1 False have "?L1 = [x,y]" by auto
                      note T=this
                      then have "t\<^sub>p ?L1 y (hd (tl Strat)) > 0" unfolding T
                      unfolding t\<^sub>p_def apply(simp add: split_def)
                        apply(cases "snd (hd (tl Strat)) = []")
                          using `x \<noteq> y` by auto
                      with l k show ?thesis by auto
                    next

                      case True  (* angenommen Strat dreht im ersten Schritt die Liste um, nicht wie OPT2 *)
                      note T=this
                          
                        have "t\<^sub>p ?L1 y (hd (tl Strat)) > 0" unfolding T
                        proof(cases "snd (hd (tl Strat)) = []")
                          case True
                          have "?L2 = [y,x]" unfolding T  apply(simp add: split_def step_def) 
                          unfolding True mtf2_def by(simp)
                          with L2F have "False" by auto
                          then show "0 < t\<^sub>p [y, x] y (hd (tl Strat))" ..
                        next
                          case False
                          then show "0 < t\<^sub>p [y, x] y (hd (tl Strat))"
                            unfolding t\<^sub>p_def by(simp add: split_def)
                        qed                          
                      with l have " t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat)) \<ge> 2" by auto
                      with k show ?thesis by auto
                    
                    qed
                    have t: "T\<^sub>p [x, y] rest2 (tl (tl Strat)) \<ge> T\<^sub>p_opt [x, y] rest2" 
                      unfolding T_opt_def apply(rule cInf_lower)
                      apply(auto) apply(rule exI[where x="(tl (tl Strat))"]) by(simp add: lenStrat)
                    show ?thesis
                    proof -
                      have "1 + T\<^sub>p_opt [y, x] rest2 \<le> 2 + T\<^sub>p_opt [x, y] rest2"
                      using  swapOpt by auto
                      also have "\<dots> \<le> 2 + T\<^sub>p [x, y] rest2 (tl (tl Strat))" using t by auto
                      also have "\<dots> \<le> T\<^sub>p [x, y] (y # y # rest2) Strat" using r by auto
                      finally show ?thesis .
                    qed
                      
                  qed
                  also have "\<dots> = el" using Strat by auto
                  finally show "T\<^sub>p [x, y] (y # y # rest2) (OPT2 (y # y # rest2) [x, y]) \<le> el" .
                qed




















          qed
        qed
     qed
  qed (simp add: T_opt_def)
(*>*)text_raw {*
\end{proof}
*}(*<*)
qed


lemma OPT2_is_ub: "set qs \<subseteq> {x,y} \<Longrightarrow> x\<noteq>y \<Longrightarrow> T\<^sub>p [x,y] qs (OPT2 qs [x,y]) \<ge> T\<^sub>p_opt [x,y] qs"
  unfolding T_opt_def apply(rule cInf_lower)
            apply(simp) apply(rule exI[where x="(OPT2 qs [x, y])"])
            by (auto simp add: OPT2_length)



lemma OPT2_is_opt: "set qs \<subseteq> {x,y} \<Longrightarrow> x\<noteq>y \<Longrightarrow> T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = T\<^sub>p_opt [x,y] qs"
by (simp add: OPT2_is_lb OPT2_is_ub antisym)

(*>*)
text{*

As a corollary we obtain the result that OPT2 is optimal on lists of length 2.

\begin{corollary}[OPT2 is optimal]
@{thm (concl) OPT2_is_opt[no_vars]}
\end{corollary}

With OPT2 we obtain an reference algorithm which can be used to analyse online algorithms on lists
of length $2$.
In the following chapter we analyze the online algorithm TS and determine its cost on $3$
different types of request sequences for lists of size $2$. 
With the knowledge of the optimal cost for these request sequences we can prove TS to be
2-competitive.
With OPT2 at hand this can easily be determined.

*}



section "Further properties of OPT2"

text {*

In this section we will examine further properties of OPT2 that will help in the analysis of other
online algorithms.

*}

(*<*)
lemma OPT2_A: "x \<noteq> y \<Longrightarrow> qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y]) \<Longrightarrow> T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = 1"
proof -
  case goal1
  from goal1(2) obtain u v where qs: "qs=u@v" and u: "u=[x] \<or> u=[]" and v: "v = [y,y]" by (auto simp: conc_def)
  from u have pref1: "T\<^sub>p [x,y] (u@v) (OPT2 (u@v) [x,y]) = T\<^sub>p [x,y] v (OPT2 v [x,y])"
    apply(cases "u=[]")
      apply(simp)
      by(simp add: OPT2x t\<^sub>p_def step_def)

  have ende: "T\<^sub>p [x,y] v (OPT2 v [x,y]) = 1" unfolding v using goal1(1) by(simp add: mtf2_def swap_def t\<^sub>p_def step_def)

  from pref1 ende qs show ?case by auto
qed
  

lemma OPT2_B: "x \<noteq> y \<Longrightarrow> qs=u@v \<Longrightarrow> u=[] \<or> u=[x] \<Longrightarrow> v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x)), Atom y, Atom y])
      \<Longrightarrow> T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v div 2)"
proof -
  case goal1
  from goal1(3) have pref1: "T\<^sub>p [x,y] (u@v) (OPT2 (u@v) [x,y]) = T\<^sub>p [x,y] v (OPT2 v [x,y])"
    apply(cases "u=[]")
      apply(simp)
      by(simp add: OPT2x t\<^sub>p_def step_def)

  from goal1(4) obtain a w where v: "v=a@w" and "a\<in>lang (Times (Atom y) (Atom x))" and w: "w\<in>lang (seq[Star(Times (Atom y) (Atom x)), Atom y, Atom y])" by(auto)
  from this(2) have aa: "a=[y,x]" by(simp add: conc_def)

  from goal1(1) this v have pref2: "T\<^sub>p [x,y] v (OPT2 v [x,y]) = 1 + T\<^sub>p [x,y] w (OPT2 w [x,y])"
   by(simp add: t\<^sub>p_def step_def OPT2x)

  from w obtain c d where w2: "w=c@d" and c: "c \<in> lang (Star (Times (Atom y) (Atom x)))" and d: "d \<in> lang (Times (Atom y) (Atom y))" by auto
  then have dd: "d=[y,y]" by auto

  from c[simplified] have star: "T\<^sub>p [x,y] (c@d) (OPT2 (c@d) [x,y]) = (length c div 2) +  T\<^sub>p [x,y] d (OPT2 d [x,y])"
    proof(induct c rule: star_induct)
      case (append r s)       
      then have r: "r=[y,x]" by auto
      then have "T\<^sub>p [x, y] ((r @ s) @ d) (OPT2 ((r @ s) @ d) [x, y]) = T\<^sub>p [x, y] ([y,x] @ (s @ d)) (OPT2 ([y,x] @ (s @ d)) [x, y])" by simp
      also have "\<dots> = 1 + T\<^sub>p [x, y] (s @ d) (OPT2 (s @ d) [x, y])"
        using goal1(1) by(simp add: t\<^sub>p_def step_def OPT2x)
      also have "\<dots> =  1 + length s div 2 + T\<^sub>p [x, y] d (OPT2 d [x, y])" using append by simp
      also have "\<dots> =  length (r @ s) div 2 + T\<^sub>p [x, y] d (OPT2 d [x, y])" using r by auto
      finally show ?case .
    qed simp

  have ende: "T\<^sub>p [x,y] d (OPT2 d [x,y]) = 1" unfolding dd using goal1(1) by(simp add: mtf2_def swap_def t\<^sub>p_def step_def)
  
  have vv: "v = [y,x]@c@[y,y]" using w2 dd v aa by auto

  from pref1 pref2 star w2 ende have
    "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) = 1 + length c div 2 + 1" unfolding goal1(2) by auto
  also have "\<dots> = (length v div 2)" using vv by auto
  finally show ?case .
qed



lemma OPT2_C: "x \<noteq> y \<Longrightarrow> qs=u@v \<Longrightarrow> u=[] \<or> u=[x] \<Longrightarrow> v \<in> lang (seq[Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom x])
      \<Longrightarrow> T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v div 2)"
proof -
  case goal1
  from goal1(3) have pref1: "T\<^sub>p [x,y] (u@v) (OPT2 (u@v) [x,y]) = T\<^sub>p [x,y] v (OPT2 v [x,y])"
    apply(cases "u=[]")
      apply(simp)
      by(simp add: OPT2x t\<^sub>p_def step_def)

  from goal1(4) obtain a w where v: "v=a@w" and aa: "a=[y,x]" and w: "w\<in>lang (seq[Star(Times (Atom y) (Atom x)), Atom x])" by(auto simp: conc_def)

  from goal1(1) this v have pref2: "T\<^sub>p [x,y] v (OPT2 v [x,y]) = 1 + T\<^sub>p [x,y] w (OPT2 w [x,y])"
   by(simp add: t\<^sub>p_def step_def OPT2x)

  from w obtain c d where w2: "w=c@d" and c: "c \<in> lang (Star (Times (Atom y) (Atom x)))" and d: "d \<in> lang (Atom x)" by auto
  then have dd: "d=[x]" by auto

  from c[simplified] have star: "T\<^sub>p [x,y] (c@d) (OPT2 (c@d) [x,y]) = (length c div 2) +  T\<^sub>p [x,y] d (OPT2 d [x,y]) \<and> (length c) mod 2 = 0"
    proof(induct c rule: star_induct)
      case (append r s)
      from append have mod: "length s mod 2 = 0" by simp
      from append have r: "r=[y,x]" by auto
      then have "T\<^sub>p [x, y] ((r @ s) @ d) (OPT2 ((r @ s) @ d) [x, y]) = T\<^sub>p [x, y] ([y,x] @ (s @ d)) (OPT2 ([y,x] @ (s @ d)) [x, y])" by simp
      also have "\<dots> = 1 + T\<^sub>p [x, y] (s @ d) (OPT2 (s @ d) [x, y])"
        using goal1(1) by(simp add: t\<^sub>p_def step_def OPT2x)
      also have "\<dots> =  1 + length s div 2 + T\<^sub>p [x, y] d (OPT2 d [x, y])" using append by simp
      also have "\<dots> =  length (r @ s) div 2 + T\<^sub>p [x, y] d (OPT2 d [x, y])" using r by auto
      finally show ?case by(simp add: mod r)
    qed simp

  have ende: "T\<^sub>p [x,y] d (OPT2 d [x,y]) = 0" unfolding dd using goal1(1) by(simp add: mtf2_def swap_def t\<^sub>p_def step_def)
  
  have vv: "v = [y,x]@c@[x]" using w2 dd v aa by auto

  from pref1 pref2 star w2 ende have
    "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) = 1 + length c div 2" unfolding goal1(2) by auto
  also have "\<dots> = (length v div 2)" using vv star by auto
  finally show ?case .
qed
(*>*)



text {*

First, for known request sequences it is now easy to calculate the optimal cost on lists of length 2.
We can use this to determine the cost of certain classes of request sequences which can be represented
by regular expressions over two elements @{term x} and @{term y}.
The proofs can be established by mere simulation and induction on the number of repetitions in the
case of star expressions.

\begin{table}[ht]
\centering
\label{tab_OPT2cost}
\begin{tabular}{l|c}
@{term "\<sigma>"} &  @{term "T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y])"} \\ \hline
\hline
 @{thm (rhs) L_A_def[simplified seq.simps, no_vars]}          & $1$ \\ \hline
 @{thm (rhs) L_B_def[simplified seq.simps, no_vars]}  & $\frac{@{term "length \<sigma>"}}{2}$ \\ \hline
 @{thm (rhs) L_C_def[simplified seq.simps, no_vars]}  & $\frac{@{term "length \<sigma> - 1"}}{2}$  \\ 
\end{tabular}
\caption{Costs of OPT2 for request sequence of three classes.}
\end{table}

*}

(*<*)
lemma OPT2_ub: "set qs \<subseteq> {x,y} \<Longrightarrow> T\<^sub>p [x,y] qs (OPT2 qs [x,y]) \<le> length qs"
proof(induct qs arbitrary: x y)
  case (Cons q qs)
  then have "set qs \<subseteq> {x,y}" "q\<in>{x,y}" by auto
  note Cons1=Cons this
  show ?case
  proof (cases qs)
    case Nil
    with Cons1 show "T\<^sub>p [x,y] (q # qs) (OPT2 (q # qs) [x,y]) \<le> length (q # qs)"
        apply(simp add: t\<^sub>p_def) by blast
  next
    case (Cons q' qs')
    with Cons1 have "q'\<in>{x,y}" by auto
    note Cons=Cons this
    thm if_True if_splits(1)
    from Cons1 Cons have T: "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) \<le> length qs"
                            "T\<^sub>p [y, x] qs (OPT2 qs [y, x]) \<le> length qs" by auto
    show "T\<^sub>p [x,y] (q # qs) (OPT2 (q # qs) [x,y]) \<le> length (q # qs)"
          unfolding Cons apply(simp only: OPT2.simps)
          apply(split if_splits(1))
            apply(safe)
            proof -
              case goal1
              have "T\<^sub>p [x, y] (x # q' # qs') ((0, []) # OPT2 (q' # qs') [x, y])
                      = t\<^sub>p [x, y] x (0,[]) + T\<^sub>p [x, y] qs (OPT2 qs [x, y])"
                        by(simp add: step_def Cons)
              also have "\<dots> \<le> t\<^sub>p [x, y] x (0,[]) + length qs" using T by auto
              also have "\<dots> \<le> length (x # q' # qs')" using Cons by(simp add: t\<^sub>p_def)
              finally show ?case .
            next
              case goal2
              with Cons1 Cons show ?case
                apply(split if_splits(1))
                apply(safe)
                proof -
                  case goal1
                  then have "T\<^sub>p [x, y] (y # x # qs') ((0, []) # OPT2 (x # qs') [x, y])
                          = t\<^sub>p [x, y] y (0,[]) + T\<^sub>p [x, y] qs (OPT2 qs [x, y])"
                            by(simp add: step_def)
                  also have "\<dots> \<le> t\<^sub>p [x, y] y (0,[]) + length qs" using T by auto
                  also have "\<dots> \<le> length (y # x # qs')" using Cons by(simp add: t\<^sub>p_def)
                  finally show ?case .
                next
                  case goal2
                  then have "T\<^sub>p [x, y] (y # y # qs') ((1, []) # OPT2 (y # qs') [y, x])
                          = t\<^sub>p [x, y] y (1,[]) + T\<^sub>p [y, x] qs (OPT2 qs [y, x])"
                            by(simp add: step_def mtf2_def swap_def)
                  also have "\<dots> \<le> t\<^sub>p [x, y] y (1,[]) + length qs" using T by auto
                  also have "\<dots> \<le> length (y # y # qs')" using Cons by(simp add: t\<^sub>p_def)
                  finally show ?case .
                qed
           qed
  qed
qed simp

(*>*)

text {*

Furthermore we can give an easy upper bound on the cost of OPT2:
Obviously OPT2 can at most have cost $1$ for every request and we obtain the following lemma:

\begin{lemma}
@{thm (concl) OPT2_ub[where qs="\<sigma>", no_vars]}
\end{lemma}


*}

(*<*)

lemma OPT2_padded: "R\<in>{[x,y],[y,x]} \<Longrightarrow> set qs \<subseteq> {x,y} 
      \<Longrightarrow>  T\<^sub>p R (qs@[x,x]) (OPT2 (qs@[x,x]) R)
              \<le> T\<^sub>p R (qs@[x]) (OPT2 (qs@[x]) R) + 1"
apply(induct qs arbitrary: R)
  apply(simp)
    apply(case_tac "R=[x,y]")
      apply(simp add: step_def t\<^sub>p_def )
      apply(simp add: step_def mtf2_def swap_def t\<^sub>p_def)
  proof -
    case goal1
    then have a: "a \<in> {x,y}" by auto 
    with goal1 show ?case
      apply(cases qs)
        apply(cases "a=x")
          apply(cases "R=[x,y]")
            apply(simp add: step_def t\<^sub>p_def)
            apply(simp add: step_def mtf2_def swap_def t\<^sub>p_def)
          apply(cases "R=[x,y]")
            apply(simp add: step_def t\<^sub>p_def)
            apply(simp add: step_def mtf2_def swap_def t\<^sub>p_def)
      proof -
        case (goal1 p ps)
        show ?case
          apply(cases "a=x")
            apply(cases "R=[x,y]")
              apply(simp add: OPT2x step_def) using goal1 apply(simp)
              using goal1(2) apply(simp)
                apply(cases qs)
                  apply(simp add: step_def mtf2_def swap_def t\<^sub>p_def)
                  using goal1 by(auto simp add: swap_def mtf2_def step_def)
       qed
qed
(*>*)

text {*
 
Moreover we can show that requesting the last requested element again has additional cost at most $1$.

\begin{lemma}
@{text " "}\\
If @{thm (prem 1) OPT2_padded[where qs="\<sigma>", no_vars]} then
@{thm[break] (concl) OPT2_padded[where qs="\<sigma>", no_vars]}
\end{lemma}
\begin{proof}
Unfortunately the calculation of OPT2's strategy depends on the rest of the request sequence (if only
it needs lookahead 1) thus one cannot append one more element easily. One way of proving the lemma
nonetheless is by induction on @{term \<sigma>} for arbitrary @{term R} and again a lot of case distinctions 
which can fortunately be solved mechanically.
\end{proof}
*}


(*<*)

lemma  OPT2_split11:
  assumes xy: "x\<noteq>y"
  shows "R\<in>{[x,y],[y,x]} \<Longrightarrow> set xs \<subseteq> {x,y} \<Longrightarrow> set ys \<subseteq> {x,y} \<Longrightarrow> OPT2 (xs@[x,x]@ys) R = OPT2 (xs@[x,x]) R @ OPT2 ys [x,y]"
proof (induct xs arbitrary: R)
  case Nil
  then show ?case
  apply(simp)
  apply(cases ys)
    apply(simp)
    apply(cases "R=[x,y]") 
      apply(simp)
      by(simp)
next
  case (Cons a as)
  note iH=this
  then have AS: "set as \<subseteq> {x,y}" and A: "a \<in> {x,y}" by auto
  note iH=Cons(1)[where R="[y,x]", simplified, OF AS Cons(4)]
  note iH'=Cons(1)[where R="[x,y]", simplified, OF AS Cons(4)]
  show ?case
  proof (cases "R=[x,y]")
    case True
    note R=this
    from iH iH' show ?thesis
    apply(cases "a=x")
      apply(simp add: R OPT2x)
      using A apply(simp)
      apply(cases as)
        apply(simp add: R)
        using AS apply(simp)
        apply(case_tac "aa=x")
          by(simp_all add: R)
  next
    case False
    with Cons(2) have R: "R=[y,x]" by auto
    from iH iH' show ?thesis
    apply(cases "a=y")
      apply(simp add: R OPT2x)
      using A apply(simp)
      apply(cases as)
        apply(simp add: R) 
        apply(case_tac "aa=y")
          by (simp_all add: R)
   qed 
qed
(*>*)

text {*

Finally, observe that in an execution of OPT2 after the occurrence of two equal elements @{term "xx"}
one after the other OPT2's list has element @{term x} at the front. This enables us to partition the
request sequence in phases and restart OPT2 repeatedly.

\begin{lemma}
If @{thm (prem 2) OPT2_split11[no_vars]} then @{thm (concl) OPT2_split11[where xs="\<sigma>\<^sub>1" and ys="\<sigma>\<^sub>2", no_vars]}.
\end{lemma}
\begin{proof}
This lemma can be proven by an induction on @{term "\<sigma>\<^sub>1"} for arbitrary @{term "R"}. For the inductive
step assume without loss of generality that @{term "R=[x,y]"}; then with a case distinction on the
following requests one can apply the induction hypothesis.
\end{proof}


*}


section "Remarks"

text {*


As we observed, OPT2 is no online algorithm but an algorithm with lookahead.

\begin{definition}[\cite{reingold96off}]
A list update algorithm is said to have \emph{lookahead}-$k(n)$ if it makes each decision knowing
only the next $k(n)$ unprocessed requests, where $k(n)$ is some function independent of the request
sequence, but perhaps depending on the initial list size.
\end{definition}

Consequently an online algorithm has lookahead-0, while an offline algorithm has unbounded lookahead.
For further results on algorithms for the list update problem with lookahead \cite{albers1994lookahead}
by Albers is a good starting point.

In the next chapter we will exploit the knowledge we obtained in this chapter when analysing the online
algorithm TS.
As we have seen we can partition the request sequence in phases ending with two
requests to the same element, knowing OPT2's list state at the end of these phases.
This technique will be introduced in the next chapter as \emph{phase partitioning} and
will be used together with the list factoring technique to show TS being 2-competitive.

*}

(*<*)
end

(*>*)