chapter \<open>Overview\<close>

(*<*)
theory Alpha_Beta_Overview
imports
  Alpha_Beta_Lattice
  LaTeXsugar2
begin
(*>*)

text\<open>
\section{Introduction}

Alpha-beta pruning is an efficient search strategy for two-player game trees.
It was invented in the late 1950s and is at the heart of most implementations
of combinatorial game playing programs. Most publications assume that the game values
are numbers augmented with $\pm\infty$. This generalizes easily to an arbitrary linear order
with $\bot$ and $\top$ values. We consider this standard case first. Later it was realized
that alpha-beta pruning can be generalized to distributive lattices.
We consider this case separately. In both cases we analyze two variants:
\emph{fail-hard} (analyzed by Knuth and Moore \cite{KnuthM75})
and \emph{fail-soft} (introduced by Fishburn~\cite{Fishburn80}).
Our analysis focusses on functional correctness, not quantitative results.
All algorithms operate on game trees of this type:
\begin{quote}
@{datatype tree}
\end{quote}

%During our investigations we also discovered that the implementation of alpha-beta pruning
%that Hughes \cite{Hughes89} derives is (probably) correct in that it computes the correct values,
%but it visits more nodes than alpha-beta pruning would, i.e.\ it is not alpha-beta pruning.
%Hughes was unaware of this when we contacted him but had Quickcheck confirm it.
%Verification is not a luxury.


\section{Linear Orders}

We assume that the type of values is a bounded linear order with $\bot$ and $\top$.
Game trees are evaluated in the standard manner via functions @{const maxmin} (the maximizer)
and the dual @{const minmax} (the minimizer).
\begin{quote}
@{fun maxmin}\medskip\\
@{fun minmax}\bigskip\\
@{fun maxs}\medskip\\
@{fun mins}
\end{quote}
The maximizer and minimizer functions are dual to each other. In this overview we will only show
the maximizer side from now on.


\subsection{Fail-Hard}

The fail-hard variant of alpha-beta pruning is defined like this:
\begin{quote}
@{fun ab_max}\medskip\\
@{fun [margin=70] ab_maxs}
\end{quote}
The intuitive meaning of @{term "ab_max a b t"} roughly is this:
search \<open>t\<close>, focussing on values in the interval from \<open>a\<close> to \<open>b\<close>.
That is, \<open>a\<close> is the maximum value that the maximizer is already assured of
and \<open>b\<close> is the minimum value that the minimizer is already assured of (by the search so far).
During the search, the maximizer will increase \<open>a\<close>, the minimizer will decrease \<open>b\<close>.

The desired correctness property is that alpha-beta pruning with the full interval yields
the value of the game tree:
\begin{quote}
@{thm ab_max_bot_top} \hfill \eqnum{ab_max_bot_top}
\end{quote}
Knuth and Moore generalize this property for arbitrary \<open>a\<close> and \<open>b\<close>,
using the following predicate:
\begin{quote}
@{prop "knuth2 x y a b"} \<open>\<equiv>\<close>\\
@{prop [source] "((y \<le> a \<longrightarrow> x \<le> a) \<and>\<^latex>\<open>\\\<close> (a < y \<and> y < b \<longrightarrow> y = x) \<and>\<^latex>\<open>\\\<close> (b \<le> y \<longrightarrow> b \<le> x))"}
\end{quote}
It follows easily that @{prop "knuth \<bottom> \<top> x y"} implies \<open>x = y\<close>.
(Also interesting to note is commutativity: @{thm knuth_comm}.)
We have verified Knuth and Moore's correctness theorem
\begin{quote}
@{thm knuth_val_ab(1)}
\end{quote}
which immediately implies (\ref{ab_max_bot_top}).


\subsection{Fail-Soft}

Fishburn introduced the fail-soft variant that agrees with fail-hard if the value is in between \<open>a\<close> and \<open>b\<close> but is more precise otherwise,
where fail-hard just returns \<open>a\<close> or \<open>b\<close>:
\begin{quote}
@{fun ab_max'}\medskip\\
@{fun [margin=70] ab_maxs'}
\end{quote}

Fishburn claims that fail-soft searches the same part of the tree as fail-hard
but that sometimes fail-soft bounds the real value more tightly than fail-hard
because fail-soft satisfies
\begin{quote}
@{thm fishburn_val_ab'(1)} \hfill \eqnum{fishburn_val_ab'}
\end{quote}
where \<open>\<le>\<close> is a strengthened version of \<open>\<cong>\<close>:
\begin{quote}
@{prop "fishburn2 ab v a b"} \<open>\<equiv>\<close>\\
@{prop [source] "((ab \<le> a \<longrightarrow> v \<le> ab) \<and>\<^latex>\<open>\\\<close> (a < ab \<and> ab < b \<longrightarrow> ab = v) \<and>\<^latex>\<open>\\\<close> (b \<le> ab \<longrightarrow> ab \<le> v))"}
%{abbrev [break,margin=40] "fishburn a b v ab"}
\end{quote}
We can confirm both claims. However, what Fishburn misses is that fail-hard already satisfies
@{const fishburn}:
\begin{quote}
@{thm fishburn_val_ab(1)}
\end{quote}
Thus (\ref{fishburn_val_ab'}) does not imply that fail-soft is better.
However, we have proved
\begin{quote}
@{thm fishburn_ab'_ab(1)}
\end{quote}
which does indeed show that fail-soft approximates the real value at least as well as fail-hard.

Fail-soft does not improve matters if one only looks at the top-level call with \<open>\<bottom>\<close> and \<open>\<top>\<close>.
It comes into its own when the tree is actually a graph and nodes are visited repeatedly from
different directions with different \<open>a\<close> and \<open>b\<close> which are typically not \<open>\<bottom>\<close> and \<open>\<top>\<close>.
Then it becomes crucial to store the results of previous alpha-beta calls in a cache and
use it to (possibly) narrow the search window on successive searches of the same subgraph.
The justification: Let \<open>ab\<close> be some search function that @{const fishburn} the real value.
If on a previous call @{prop "b \<le> ab a b t"}, then in a subsequent search of the same \<open>t\<close>
with possibly different \<open>a'\<close> and \<open>b'\<close>, we can replace \<open>a'\<close> by @{term "(max a' (ab a b t))"}:
\begin{quote}
@{thm [break,margin=70] ab_twice_lb}
\end{quote}
There is a dual lemma for replacing \<open>b'\<close> by @{term "(min b' (ab a b t))"}.

We have a verified version of alpha-beta pruning with a cache, but it is not yet
part of this development.


\subsection{Negation}

Traditionally the definition of both the evaluation and of alpha-beta pruning
does not define a minimizer and maximizer separately. Instead it defines only one function
and uses negation (on numbers!) to flip between the two players. This is evaluation and
alpha-beta pruning:
\begin{quote}
@{fun negmax}
\end{quote}
\begin{quote}
@{fun ab_negmax}\medskip\\
@{fun ab_negmaxs}
\end{quote}
\begin{quote}
@{fun ab_negmax'}\medskip\\
@{fun ab_negmaxs'}
\end{quote}
However, what does ``\<open>-\<close>'' on a linear order mean? It turns out that the following two
properties of ``\<open>-\<close>'' are required to make things work:
\begin{quote}
@{thm de_morgan_min} \qquad @{thm neg_neg}
\end{quote}
We call such linear orders \emph{de Morgan orders}. We have proved correctness of alpha-beta pruning
on de Morgan orders
\begin{quote}
@{thm fishburn_negmax_ab_negmax(1)}\\
@{thm fishburn_val_ab_neg(1)}\\
@{thm fishburn_ab'_ab_neg(1)}
\end{quote}
by relating everything back to ordinary linear orders.


\section{Lattices}

Bird and Hughes \cite{BirdH87} were the first to generalize alpha-beta pruning from linear orders
to lattices. The generalization of the code is easy: simply replace @{const min} and @{const max}
by @{const inf} and @{const sup}. Thus, the value of a game tree is now defined like this:
\begin{quote}
@{fun supinf}\medskip\\
@{fun sups}
\end{quote}
And similarly fail-hard and fail-soft alpha-beta pruning:
\begin{quote}
@{fun ab_sup}\medskip\\
@{fun [margin=70] ab_sups}
\end{quote}
\begin{quote}
@{fun ab_sup'}\medskip\\
@{fun [margin=70] ab_sups'}
\end{quote}
It turns out that this version of alpha-beta pruning works for bounded distributive lattices.
To prove this we can generalize both \<open>\<cong>\<close> and \<open>\<le>\<close> by first rephrasing them (for linear orders)
\begin{quote}
@{thm knuth_iff_max_min}

@{thm fishburn_iff_min_max}
\end{quote}
and then deriving from the right-hand sides new versions \<open>\<simeq>\<close> and \<open>\<sqsubseteq>\<close> appropriate for lattices:
\begin{quote}
@{prop "eq_mod x y a b"} \<open>\<equiv>\<close> @{prop [source] "a \<squnion> x \<sqinter> b = a \<squnion> y \<sqinter> b"}

@{prop "bounded2 ab v a b"} \<open>\<equiv>\<close> @{prop [source] "b \<sqinter> v \<le> ab \<and> ab \<le> a \<squnion> v"}
\end{quote}
%Trivially {lemma "\<bottom> \<squnion> x \<sqinter> \<top> = \<bottom> \<squnion> y \<sqinter> \<top> \<Longrightarrow> x = (y::_::bounded_lattice)" by (simp)}.
%Bird and Hughes do not cite Knuth and Moore
As for linear orders, \<open>\<sqsubseteq>\<close> implies \<open>\<simeq>\<close>, but not the other way around:
\begin{quote}
@{thm eq_mod_if_bounded}
\end{quote}
Both fail-hard and fail-soft are correct w.r.t.\ \<open>\<sqsubseteq>\<close>:
\begin{quote}
@{thm bounded_val_ab(1)}\\
@{thm bounded_val_ab'(1)}
\end{quote}


\subsection{Negation}

This time we extend bounded distributive lattices to \emph{de Morgan algebras} by adding ``\<open>-\<close>''
and assuming
\begin{quote}
@{thm de_Morgan_inf} \qquad @{thm neg_neg}
\end{quote}
Game tree evaluation:
\begin{quote}
@{fun negsup}
\end{quote}
Fail-hard alpha-beta pruning:
\begin{quote}
@{fun ab_negsup}\medskip\\
@{fun ab_negsups}
\end{quote}
Fail-soft alpha-beta pruning:
\begin{quote}
@{fun ab_negsup'}\medskip\\
@{fun ab_negsups'}
\end{quote}
Correctness:
\begin{quote}
@{thm bounded_negsup_ab_negsup}\\
@{thm bounded_val_ab'_neg(1)}
\end{quote}

\<close>
(*<*)
end
(*>*)