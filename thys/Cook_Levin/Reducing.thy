chapter \<open>Reducing $\NP$ languages to \SAT{}\label{s:Reducing}\<close>

theory Reducing
  imports Satisfiability Oblivious
begin

text \<open>
We have already shown that \SAT{} is in $\NP$. It remains to show that \SAT{} is
$\NP$-hard, that is, that every language $L \in \NP$ can be polynomial-time
reduced to \SAT{}. This, in turn, can be split in two parts. First, showing that
for every $x$ there is a CNF formula $\Phi$ such that $x\in L$ iff.\ $\Phi$ is
satisfiable. Second, that $\Phi$ can be computed from $x$ in polynomial time.
This chapter is devoted to the first part, which is the core of the proof. In
the subsequent two chapters we painstakingly construct a polynomial-time Turing
machine computing $\Phi$ from $x$ in order to show something that is usually
considered ``obvious''.

The proof corresponds to lemma~2.11 from the textbook~\cite{ccama}. Of course we
have to be much more explicit than the textbook, and the first section describes
in some detail how we derive the formula $\Phi$.
\<close>


section \<open>Introduction\<close>

text \<open>
Let $L \in \NP$. In order to reduce $L$ to \SAT{}, we need to construct for
every string $x\in\bbOI^*$ a CNF formula $\Phi$ such that $x\in L$ iff.\ $\Phi$
is satisfiable. In this section we describe how $\Phi$ looks like.


\subsection{Preliminaries}

We denote the length of a string $s\in\bbOI^*$ by $|s|$. We define
\[
    num(s) = \left\{\begin{array}{ll}
        k       & \text{if } s = \bbbI^k\bbbO^{|s|-k},\\
        |s| + 1 & \text{otherwise.}
    \end{array}\right.
\]
Essentially $num$ interprets some strings as unary codes of numbers. All other
strings are interpreted as an ``error value''.

For a string $s$ and a sequence $w\in\nat^n$ of numbers we write $s(w)$ for
$num(s_{w_0}\dots s_{w_{n-1}})$. Likewise for an assignment $\alpha\colon \nat
\to \bbOI$ we write $\alpha(w) = num(\alpha(w_0)\dots\alpha(w_{n-1}))$.

We define two families of CNF formulas. Variables are written $v_0, v_1, v_2,
\dots$, and negated variables are written $\bar v_0, \bar v_1, \bar v_2, \dots$
Let $w\in\nat^n$ be a list of numbers. For $k \leq n$ define
\[
    \Psi(w, k) = \bigwedge_{i=0}^{k-1} v_{w_i} \land \bigwedge_{i=k}^{n - 1}
    \bar v_{w_i}.
\]
This formula is satisfied by an assignment $\alpha$ iff.\ $\alpha(w) = k$.  In a
similar fashion we define for $n > 2$,
\[
    \Upsilon(w) = v_{w_0} \land v_{w_1} \land \bigwedge_{i=3}^{n - 1} \bar v_{w_i},
\]
which is satisfied by an assignment $\alpha$ iff.\ $\alpha(w) \in \{2, 3\} =
\{\mathbf{0}, \mathbf{1}\}$, where as usual the boldface $\mathbf{0}$ and
$\mathbf{1}$ refer to the symbols represented by the numbers~2 and~3.

For $a \leq b$ we write $[a:b]$ for the interval $[a, \dots, b - 1] \in \nat^{b
- a}$. For intervals the CNF formulas become:
\[
    \Psi([a:b], k) = \bigwedge_{i=a}^{a+k-1} v_i \land \bigwedge_{i=a+k}^{b - 1}
    \bar v_i
\qquad \text{and} \qquad
    \Upsilon([a:b]) = v_a \land v_{a+1} \land \bigwedge_{i=a+3}^{b - 1} \bar v_i.
\]

Let $\phi$ be a CNF formula and let $\sigma\in\nat^*$ be a sequence of variable
indices such that for all variables $v_i$ occurring in $\phi$ we have $i <
|\sigma|$. Then we define the CNF formula $\sigma(\phi)$ as the formula
resulting from replacing every variable $v_i$ in $\phi$ by the variable
$v_{\sigma_i}$. This corresponds to our function @{const relabel}.


\subsection{Construction of the CNF formula}

Let $M$ be the two-tape oblivious verifier Turing machine for $L$ from
lemma~@{text NP_imp_oblivious_2tape}. Let $p$ be the polynomial function for the
length of the certificates, and let $T\colon \nat \to \nat$ be the polynomial
running-time bound. Let $G$ be $M$'s alphabet size.

Let $x\in\bbOI^n$ be fixed thoughout the rest of this section. We seek a CNF
formula $\Phi$ that is satisfiable iff.\ $x\in L$. We are going to transform
``$x\in L$'' via several equivalent statements to the statement ``$\Phi$ is
satisfiable'' for a suitable $\Phi$ defined along the way.  The Isabelle
formalization later in this chapter does not prove these equivalences
explicitly.  They are only meant to explain the shape of $\Phi$.


\subsubsection{1st equivalence}

From lemma~@{text NP_imp_oblivious_2tape} about $M$ we get the first equivalent
statement: There exists a certificate $u \in \bbOI^{p(n)}$
such that $M$ on input $\langle x, u\rangle$ halts with the symbol \textbf{1}
under its output tape head.  The running time of $M$ is bounded by $T(|\langle
x, u\rangle|) = T(2n+2+2p(n))$. We abbreviate $|\langle x, u\rangle| = 2n+2+2p(n)$
by $m$.


\subsubsection{2nd equivalence}

For the second equivalent statement, we define what the textbook calls
``snapshots''.  For every $u\in\{\bbbO,\bbbI\}^{p(n)}$ let $z_0^u(t)$ be the
symbol under the input tape head of $M$ on input $\langle x, u\rangle$ at step
$t$. Similarly we define $z_1^u(t)$ as the symbol under the output tape head of
$M$ at step $t$ and $z_2^u(t)$ as the state $M$ is in at step $t$.  A triple
$z^u(t) = (z^u_0(t), z^u_1(t), z^u_2(t))$ is called a snapshot. For the initial
snapshot we have:
\begin{equation}
    z_0^u(0) = z_1^u(0) = \triangleright\qquad\text{and}\qquad z_2^u(0) = 0.
    \tag{Z0}
\end{equation}

The crucial idea is that the snapshots for $t > 0$ can be characterized
recursively using two auxiliary functions $\inputpos$ and $\prev$.

Since $M$ is oblivious, the positions of the tape heads on input $\langle x,
u\rangle$ after $t$ steps are the same for all $u$ of length $p(n)$. We denote
the input head positions by $\inputpos(t)$.

For every $t$ we denote by $\prev(t)$ the last step before $t$ in which the
output tape head of $M$ was in the same cell as in step $t$. Due to $M$'s
obliviousness this is again the same for all $u$ of length $p(n)$. If there is
no such previous step, because $t$ is the first time the cell is reached, we set
$\prev(t) = t$. (This deviates from the textbook, which sets $\prev(t) = 1$.) In
the other case we have $\prev(t) < t$.

Also due to $M$'s obliviousness, the halting time on input $\langle x, u\rangle$
is the same for all $u$ of length $p(n)$, and we denote it by $T' \le T(|\langle
x, u\rangle|)$.  Thus we have $\inputpos(t) \le T'$ for all $t$. If we define
the symbol sequence $y(u) = \triangleright \langle x, u\rangle \Box^{T'}$, the
first component of the snapshots is, for arbitrary $t$:
\begin{equation}
    z_0^u(t) = y(u)_{\inputpos(t)}.
    \tag{Z1}
\end{equation}

Next we consider the snapshot components $z_1^u(t)$ for $t > 0$. First consider
the case $\prev(t) < t$; that is, the last time before $t$ when $M$'s output
tape head was in the same cell as in step $t$ was in step $\prev(t)$. The
snapshot for step $\prev(t)$ has exactly the information needed to calculate the
actions of $M$ at step $t$: the symbols read from both tapes and the state which
$M$ is in. In some sort of hybrid notation:
\begin{equation}
    z_1^u(t) = (M\ !\ z_2^u(\prev(t)))\ [z_0^u(\prev(t)), z_1^u(\prev(t))]\ [.]\ 1.
    \tag{Z2}
\end{equation}
In the other case, $\prev(t) = t$, the output tape head has not been in this
cell before and is thus reading a blank. It cannot be reading the start symbol
because the output tape head was in cell zero at step $t = 0$ already. Formally:
\begin{equation}
    z_1^u(t) = \Box.
    \tag{Z3}
\end{equation}

The state $z_2^u(t)$ for $t > 0$ can be computed from the state $z_2^u(t-1)$ in
the previous step and the symbols $z_0^u(t-1)$ and $z_1^u(t-1)$ read in the
previous step:
\begin{equation}
    z_2^u(t) = \mathit{fst}\ ((M\ !\ z_2^u(t - 1))\ [z_0^u(t - 1), z_1^u(t - 1)]).
    \tag{Z4}
\end{equation}

For a string $u\in\bbOI^{p(n)}$ the equations (Z0) -- (Z4) uniquely determine
all the $z^u(0), \dots, z^u(T')$. Conversely, the snapshots for $u$ satisfy all
the equations. Therefore the equations characterize the sequence of snapshots.

The condition that $M$ halts with the output tape head on \textbf{1} can be
expressed with snapshots:
\begin{equation}
    z_1^{u}(T') = \mathbf{1}.
    \tag{Z5}
\end{equation}

This yields our second equivalent statement: $x\in L$ iff.\ there is a
$u\in\{\bbbO,\bbbI\}^{p(n)}$ and a sequence $z^u(0), \dots, z^u(T')$ satisfying
the equations (Z0) -- (Z5).


\subsubsection{3rd equivalence}

The length of $y(u)$ is $m' := m + 1 + T' = 3 + 2n + 2p(n) + T'$ because
$|\langle x, u\rangle| = m$ plus the start symbol plus the $T'$ blanks.

For the next equivalence we observe that the strings $y(u)$ for
$u\in\{\bbbO,\bbbI\}^{p(n)}$ can be characterized as follows. Consider
a predicate on strings $y$:
\begin{itemize}
    \item[(Y0)] $|y| = m'$;
    \item[(Y1)] $y_0 = \triangleright$ (the start symbol);
    \item[(Y2)] $y_{2n+1} = y_{2n+2} = \mathbf{1}$
        (the separator in the pair encoding);
    \item[(Y3)] $y_{2i+1} = \mathbf{0}$ for $i=0,\dots,n-1$ (the zeros
        before $x$);
    \item[(Y4)] $y_{2n+2+2i+1} = \mathbf{0}$ for $i=0, \dots, p(n)-1$ (the
        zeros before $u$);
    \item[(Y5)] $y_{2n+2p(n)+3+i} = \Box$ for $i=0, \dots, T' - 1$ (the
        blanks after the input proper);
    \item[(Y6)] $y_{2i+2} = \left\{\begin{array}{ll}
        \mathbf{0} & \text{if } x_i = \bbbO,\\
        \mathbf{1} & \text{otherwise}
      \end{array}\right.$ for $i = 0, \dots, n - 1$ (the bits of $x$);
    \item[(Y7)] $y_{2n+4+2i} \in \{\mathbf{0}, \mathbf{1}\}$ for $i=0,\dots,p(n)-1$
        (the bits of $u$).
\end{itemize}
Every $y(u)$ for some $u$ of length $p(n)$ satisfies this predicate. Conversely,
from a $y$ satisfying the predicate, a $u$ of length $p(n)$ can be extracted
such that $y = y(u)$.

From that we get the third equivalent statement: $x \in L$ iff.\ there is a $y
\in \{0, \dots, G - 1\}^{m'}$ with (Y0) -- (Y7) and a sequence $z^u(0), \dots,
z^u(T')$ with (Z0) -- (Z5).


\subsubsection{4th equivalence}

Each element of $y$ is a symbol from $M$'s alphabet, that is, a number less than
$G$. The same goes for the first two elements of each snapshot, $z_0^u(t)$ and
$z_1^u(t)$.  The third element, $z_2^u(t)$, is a number less than or equal to
the number of states of $M$. Let $H$ be the maximum of $G$ and the number of
states.  Every element of $y$ and of the snapshots can then be represented by a
bit string of length $H$ using $num$ (the textbook uses binary, but unary is
simpler for us).  So we use $3H$ bits to represent one snapshot. There are $T' +
1$ snapshots until $M$ halts. Thus all elements of all snapshots can be
represented by a string of length $3H\cdot(T'+1)$. Together with the string of
length $N := H\cdot m'$ for the input tape contents $y$, we have a total length
of $N + 3H\cdot(T'+1)$.

The equivalence can thus be stated as $x \in L$ iff.\ there is a string $s\in
\{\bbbO,\bbbI\}^{N + 3H\cdot(T'+1)}$ with certain properties. To write these
properties we introduce some intervals:
\begin{itemize}
    \item $\gamma_i = [iH : (i+1)H]$ for $i < m'$,
    \item $\zeta_0(t) = [N + 3Ht : N+3Ht + H]$ for $t \leq T'$,
    \item $\zeta_1(t) = [N + 3Ht + H : N+3Ht + 2H]$ for $t \leq T'$,
    \item $\zeta_2(t) = [N + 3Ht + 2H : N+3H(t + 1)]$ for $t \leq T'$.
\end{itemize}
These intervals slice the string $s$ in intervals of length $H$.  The string $s$
must satisfy properties analogous to (Y0) -- (Y7), which we express using the
intervals $\gamma_i$:

\begin{itemize}
    \item[(Y0)] $|s| = N + 3H(T' + 1)$
    \item[(Y1)] $s(\gamma_0) = \triangleright$ (the start symbol);
    \item[(Y2)] $s(\gamma_{2n+1}) = s(\gamma_{2n+2}) = \mathbf{1}$
        (the separator in the pair encoding);
    \item[(Y3)] $s(\gamma_{2i+1}) = \mathbf{0}$ for $i=0,\dots,n-1$ (the zeros
        before $x$);
    \item[(Y4)] $s(\gamma_{2n+2+2i+1}) = \mathbf{0}$ for $i=0,\dots,p(n)-1$ (the
        zeros before $u$);
    \item[(Y5)] $s(\gamma_{2n+2p(n)+3+i}) = \Box$ for $i=0,\dots,T' - 1$ (the
        blanks after the input proper);
    \item[(Y6)] $s(\gamma_{2i+2}) = \left\{\begin{array}{ll}
        \mathbf{0} & \text{if } x_i = \bbbO,\\
        \mathbf{1} & \text{otherwise}
      \end{array}\right.$ for $i = 0, \dots, n - 1$ (the bits of $x$);
    \item[(Y7)] $s(\gamma_{2n+4+2i}) \in \{\mathbf{0}, \mathbf{1}\}$ for $i=0,\dots,p(n)-1$
        (the bits of $u$).
\end{itemize}

Moreover the string $s$ must satisfy (Z0) -- (Z5).  For these properties we use
the $\zeta$ intervals.
\begin{itemize}
    \item[(Z0)] $s(\zeta_0(0)) = s(\zeta_1(0)) = \triangleright$ and $s(\zeta_2(0)) = 0$,
    \item[(Z1)] $s(\zeta_0(t)) = s(\gamma_{\inputpos(t)})$ for $t = 1, \dots, T'$,
    \item[(Z2)] $s(\zeta_1(t)) = (M\ !\ s(\zeta_2(\prev(t)))\ [s(\zeta_0(\prev(t))), s(\zeta_1(\prev(t)))]\ [.]\ 1$
        for $t = 1, \dots, T'$ with $\prev(t) < t$,
    \item[(Z3)] $s(\zeta_1(t)) = \Box$ for $t = 1, \dots, T'$ with $\prev(t) = t$,
    \item[(Z4)] $s(\zeta_2(t)) = \mathit{fst}\ ((M\ !\ s(\zeta_2(t - 1))\ [s(\zeta_0(t - 1), s(\zeta_1(t - 1)])$
        for $t = 1, \dots, T'$,
    \item[(Z5)] $s(\zeta_1(T')) = \mathbf{1}$.
\end{itemize}


\subsubsection{5th equivalence}

An assignment is an infinite bit string. For formulas over variables with
indices in the interval $[0 : N+3H(T'+1)]$, only the initial $N+3H(T'+1)$ bits of
the assignment are relevant. If we had a CNF formula $\Phi$ over these variables
that is satisfied exactly by the assignments $\alpha$ for which there is an $s$
with the above properties and $\alpha(i) = s_i$ for all $i < |s|$, then the
existence of such an $s$ would be equivalent to $\Phi$ being satisfiable.

Next we construct such a CNF formula.

Most properties are easy to translate using the formulas $\Psi$ and $\Upsilon$.
For example, $s(\gamma_0) = \triangleright$ corresponds to $\alpha(\gamma_0) =
\triangleright$.  A formula that is satisfied exactly by assignments with this
property is $\Psi(\gamma_0, 1)$. Likewise the property
$s(\gamma_{2n+4+2i})\in\{\mathbf{0}, \mathbf{1}\}$ corresponds to the CNF
formula $\Upsilon(\gamma_{2n+4+2i})$.

Property (Y0) corresponds to $\Phi$ having only variables $0, \dots, N+3H(T'+1)
- 1$. The other (Y$\cdot$) properties become:
\begin{itemize}
    \item[(Y1)] $\Phi_1 := \Psi(\gamma_0, 1)$,
    \item[(Y2)] $\Phi_2 := \Psi(\gamma_{2n+1}, 3) \land \Psi(\gamma_{2n+2}, 3)$,
    \item[(Y3)] $\Phi_3 := \bigwedge_{i=0}^{n-1}\Psi(\gamma_{2i+1}, 2)$,
    \item[(Y4)] $\Phi_4 := \bigwedge_{i=0}^{p(n) - 1}\Psi(\gamma_{2n+2+2i+1}, 2)$,
    \item[(Y5)] $\Phi_5 := \bigwedge_{i=0}^{T' - 1}\Psi(\gamma_{2n+2p(n)+3+i}, 0)$,
    \item[(Y6)] $\Phi_6 := \bigwedge_{i=0}^{n - 1}\Psi(\gamma_{2i+2}, x_i + 2)$,
    \item[(Y7)] $\Phi_7 := \bigwedge_{i=0}^{p(n) - 1}\Upsilon(\gamma_{2n+4+2i})$.
\end{itemize}

Property~(Z0) and property~(Z5) become these formulas:
\begin{itemize}
    \item[(Z0)] $\Phi_0 := \Psi(\zeta_0(0), 1) \land \Psi(\zeta_1(0), 1) \land \Psi(\zeta_2(0), 0)$,
    \item[(Z5)] $\Phi_8 := \Psi(\zeta_1(T'), 3)$.
\end{itemize}

The remaining properties (Z1) -- (Z4) are more complex. They apply to $t = 1,
\dots T'$. Let us first consider the case $\prev(t) < t$. With $\alpha$ for $s$
the properties become:
\begin{itemize}
    \item[(Z1)] $\alpha(\zeta_0(t)) = \alpha(\gamma_{\inputpos(t)})$,
    \item[(Z2)] $\alpha(\zeta_1(t)) =
        ((M\ !\ \alpha(\zeta_2(\prev(t))))\ [\alpha(\zeta_0(\prev(t))), \alpha(\zeta_1(\prev(t)))])\ [.]\ 1$,
    \item[(Z4)] $\alpha(\zeta_2(t)) =
        \mathit{fst}\ ((M\ !\ \alpha(\zeta_2(t-1)))\ [\alpha(\zeta_0(t-1)), \alpha(\zeta_1(t-1))])$.
\end{itemize}

For any $t$ the properties (Z1), (Z2), (Z4) use at most $10H$ variable indices,
namely all the variable indices in the nine $\zeta$'s and in
$\gamma_{\inputpos(t)}$, each of which have $H$ indices.

Now if the set of all these variable indices was $\{0, \dots, 10H - 1\}$ we
could apply lemma~@{thm [source] depon_ex_formula} to get a CNF formula $\psi$
over these variables that ``captures the spirit'' of the properties. We would
then merely have to relabel the formula with the actual variable indices we need
for each $t$.  More precisely, let $w_i = [iH : (i+1)H]$ for $i = 0, \dots, 9$
and consider the following criterion for $\alpha$ on the variable indices $\{0,
\dots 10H - 1\}$:
\begin{itemize}
    \item[($\mathrm{F}_1$)] $\alpha(w_6) = \alpha(w_9)$,
    \item[($\mathrm{F}_2$)] $\alpha(w_7) =
        ((M\ !\ \alpha(w_5))\ [\alpha(w_3), \alpha(w_4)])\ [.]\ 1,$
    \item[($\mathrm{F}_3$)] $\alpha(w_8) =
        \mathit{fst}\ ((M\ !\ \alpha(w_2))\ [\alpha(w_0), \alpha(w_1)]).$
\end{itemize}
Lemma~@{thm [source] depon_ex_formula} gives us a formula $\psi$ satisfied
exactly by those assignments $\alpha$ that meet the conditions ($\mathrm{F}_1$),
($\mathrm{F}_2$), ($\mathrm{F}_3$).  From this $\psi$ we can create all the
formulas we need for representing the properties~(Z1), (Z2), (Z4) by
substituting (``relabeling'' in our terminology) the variables $[0,10H)$
appropriately. The substitution for step $t$ is
\[
    \rho_t = \zeta_0(t-1) \circ \zeta_1(t-1) \circ \zeta_2(t-1) \circ
    \zeta_0(\prev(t)) \circ \zeta_1(\prev(t)) \circ \zeta_2(\prev(t)) \circ \zeta_0(t)
    \circ \zeta_1(t) \circ \zeta_2(t) \circ \gamma_{\inputpos(t)},
\]
where $\circ$ denotes the concatenation of lists. Then $\rho_t(\psi)$ is CNF
formula satisfied exactly by the assignments $\alpha$ satisfying (Z1), (Z2),
(Z4).

For the case $\prev(t) = t$ we have a criterion on the variable indices
$\{0, \dots, 7H - 1\}$:
\begin{itemize}
    \item[($\mathrm{F}_1'$)] $\alpha(w_3) = \alpha(w_6)$,
    \item[($\mathrm{F}_2'$)] $\alpha(w_4) = \Box$,
    \item[($\mathrm{F}_3'$)] $\alpha(w_5) = \mathit{fst}\ ((M\ !\ \alpha(w_2))\ [\alpha(w_0), \alpha(w_1)])$,
\end{itemize}
whence lemma~@{thm [source] depon_ex_formula} supplies us with a formula
$\psi'$.  With appropriate substitutions
\[
    \rho'_t = \zeta_0(t-1) \circ \zeta_1(t-1) \circ \zeta_2(t-1) \circ
    \zeta_0(t) \circ \zeta_1(t) \circ \zeta_2(t) \circ \gamma_{\inputpos(t)},
\]
we then define CNF formulas $\chi_t$ for all $t = 1, \dots, T'$:
\[
    \chi_t = \left\{\begin{array}{ll}
        \rho_t(\psi)   &\text{if }\prev(t) < t,\\
        \rho'_t(\psi') &\text{if }\prev(t) = t.
    \end{array}\right.
\]

The point of all that is that we can hard-code $\psi$ and $\psi'$ in the TM
performing the reduction (to be built in the final chapter) and for each $t$ the
TM only needs to construct the substitution $\rho_t$ or $\rho_t'$ and perform
the relabeling. Turing machines that perform these operations will be
constructed in the next chapter.

Since all $\chi_t$ are in CNF, so is the conjunction
\[
    \Phi_9 := \bigwedge_{t=1}^{T'}\chi_t\ .
\]

Finally the complete CNF formula is:
\[
    \Phi := \Phi_0 \land \Phi_1 \land
     \Phi_2 \land \Phi_3 \land
     \Phi_4 \land \Phi_5 \land
     \Phi_6 \land \Phi_7 \land
     \Phi_8 \land \Phi_9\ .
\]
\<close>


section \<open>Auxiliary CNF formulas\<close>

text \<open>
In this section we define the CNF formula families $\Psi$ and $\Upsilon$.  In
the introduction both families were parameterized by intervals of natural
numbers. Here we generalize the definition to allow arbitrary sequences of
numbers although we will not need this generalization.
\<close>

text \<open>
The number of variables set to true in a list of variables:
\<close>

definition numtrue :: "assignment \<Rightarrow> nat list \<Rightarrow> nat" where
  "numtrue \<alpha> vs \<equiv> length (filter \<alpha> vs)"

text \<open>
Checking whether the list of bits assigned to a list @{term vs} of variables has
the form $\bbbI\dots\bbbI\bbbO\dots\bbbO$:
\<close>

definition blocky :: "assignment \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "blocky \<alpha> vs k \<equiv> \<forall>i<length vs. \<alpha> (vs ! i) \<longleftrightarrow> i < k"

text \<open>
The next function represents the notation $\alpha(\gamma)$ from the
introduction, albeit generalized to lists that are not intervals $\gamma$.
\<close>

definition unary :: "assignment \<Rightarrow> nat list \<Rightarrow> nat" where
  "unary \<alpha> vs \<equiv> if (\<exists>k. blocky \<alpha> vs k) then numtrue \<alpha> vs else Suc (length vs)"

lemma numtrue_remap:
  assumes "\<forall>s\<in>set seq. s < length \<sigma>"
  shows "numtrue (remap \<sigma> \<alpha>) seq = numtrue \<alpha> (reseq \<sigma> seq)"
proof -
  have *: "length (filter f xs) = length (filter (f \<circ> ((!) xs)) [0..<length xs])" for f and xs :: "'a list"
    using length_filter_map map_nth by metis

  let ?s_alpha = "remap \<sigma> \<alpha>"
  let ?s_seq = "reseq \<sigma> seq"
  have "numtrue ?s_alpha seq = length (filter ?s_alpha seq)"
    using numtrue_def by simp
  then have lhs: "numtrue ?s_alpha seq = length (filter (?s_alpha \<circ> ((!) seq)) [0..<length seq])"
    using * by auto

  have "numtrue \<alpha> ?s_seq = length (filter \<alpha> ?s_seq)"
    using numtrue_def by simp
  then have "numtrue \<alpha> ?s_seq = length (filter (\<alpha> \<circ> ((!) ?s_seq)) [0..<length ?s_seq])"
    using * by metis
  then have rhs: "numtrue \<alpha> ?s_seq = length (filter (\<alpha> \<circ> ((!) ?s_seq)) [0..<length seq])"
    using reseq_def by simp

  have "(?s_alpha \<circ> ((!) seq)) i = (\<alpha> \<circ> ((!) ?s_seq)) i" if "i < length seq" for i
    using assms remap_def reseq_def that by simp
  then show ?thesis
    using lhs rhs by (metis atLeastLessThan_iff filter_cong set_upt)
qed

lemma unary_remap:
  assumes "\<forall>s\<in>set seq. s < length \<sigma>"
  shows "unary (remap \<sigma> \<alpha>) seq = unary \<alpha> (reseq \<sigma> seq)"
proof -
  have *: "blocky (remap \<sigma> \<alpha>) seq k = blocky \<alpha> (reseq \<sigma> seq) k" for k
    using blocky_def remap_def reseq_def assms by simp
  let ?alpha = "remap \<sigma> \<alpha>" and ?seq = "reseq \<sigma> seq"
  show ?thesis
  proof (cases "\<exists>k. blocky ?alpha seq k")
    case True
    then show ?thesis
      using * unary_def numtrue_remap assms by simp
  next
    case False
    then have "unary ?alpha seq = Suc (length seq)"
      using unary_def by simp
    moreover have "\<not> (\<exists>k. blocky \<alpha> ?seq k)"
      using False * assms by simp
    ultimately show ?thesis
      using unary_def by simp
  qed
qed

text \<open>
Now we define the family $\Psi$ of CNF formulas. It is parameterized by a list
@{term vs} of variable indices and a number $k \leq |\mathit{vs}|$. The formula
is satisfied exactly by those assignments that set to true the first $k$
variables in $vs$ and to false the other variables. This is more general than we
need, because for us $vs$ will always be an interval.
\<close>

definition Psi :: "nat list \<Rightarrow> nat \<Rightarrow> formula" ("\<Psi>") where
  "\<Psi> vs k \<equiv> map (\<lambda>s. [Pos s]) (take k vs) @ map (\<lambda>s. [Neg s]) (drop k vs)"

lemma Psi_unary:
  assumes "k \<le> length vs" and "\<alpha> \<Turnstile> \<Psi> vs k"
  shows "unary \<alpha> vs = k"
proof -
  have "\<alpha> \<Turnstile> map (\<lambda>s. [Pos s]) (take k vs)"
    using satisfies_def assms Psi_def by simp
  then have "satisfies_clause \<alpha> [Pos v]" if "v \<in> set (take k vs)" for v
    using satisfies_def that by simp
  then have "satisfies_literal \<alpha> (Pos v)" if "v \<in> set (take k vs)" for v
    using satisfies_clause_def that by simp
  then have pos: "\<alpha> v" if "v \<in> set (take k vs)" for v
    using that by simp

  have "\<alpha> \<Turnstile> map (\<lambda>s. [Neg s]) (drop k vs)"
    using satisfies_def assms Psi_def by simp
  then have "satisfies_clause \<alpha> [Neg v]" if "v \<in> set (drop k vs)" for v
    using satisfies_def that by simp
  then have "satisfies_literal \<alpha> (Neg v)" if "v \<in> set (drop k vs)" for v
    using satisfies_clause_def that by simp
  then have neg: "\<not> \<alpha> v" if "v \<in> set (drop k vs)" for v
    using that by simp

  have "blocky \<alpha> vs k"
  proof -
    have "\<alpha> (vs ! i)" if "i < k" for i
      using pos that assms(1) by (metis in_set_conv_nth length_take min_absorb2 nth_take)
    moreover have "\<not> \<alpha> (vs ! i)" if "i \<ge> k" "i < length vs" for i
      using that assms(1) neg
      by (metis Cons_nth_drop_Suc list.set_intros(1) set_drop_subset_set_drop subsetD)
    ultimately show ?thesis
      using blocky_def by (metis linorder_not_le)
  qed
  moreover have "numtrue \<alpha> vs = k"
  proof -
    have "filter \<alpha> vs = take k vs"
      using pos neg
      by (metis (mono_tags, lifting) append.right_neutral append_take_drop_id filter_True filter_append filter_empty_conv)
    then show ?thesis
      using numtrue_def assms(1) by simp
  qed
  ultimately show ?thesis
    using unary_def by auto
qed

text \<open>
We will only ever consider cases where $k \leq |vs|$. So we can use $blocky$ to
show that an assignment satisfies a $\Psi$ formula.
\<close>

lemma satisfies_Psi:
  assumes "k \<le> length vs" and "blocky \<alpha> vs k"
  shows "\<alpha> \<Turnstile> \<Psi> vs k"
proof -
  have "\<alpha> \<Turnstile> map (\<lambda>s. [Pos s]) (take k vs)"
    (is "\<alpha> \<Turnstile> ?phi")
  proof -
    {
      fix c :: clause
      assume c: "c \<in> set ?phi"
      then obtain s where "c = [Pos s]" and "s \<in> set (take k vs)"
        by auto
      then obtain i where "i < k" and "s = vs ! i"
        using assms(1)
        by (smt (verit, best) in_set_conv_nth le_antisym le_trans nat_le_linear nat_less_le nth_take nth_take_lemma take_all_iff)
      then have "c = [Pos (vs ! i)]"
        using `c = [Pos s]` by simp
      moreover have "i < length vs"
        using assms(1) `i < k` by simp
      ultimately have "\<alpha> (vs ! i)"
        using assms(2) blocky_def \<open>i < k\<close> by blast
      then have "satisfies_clause \<alpha> c"
        using satisfies_clause_def by (simp add: \<open>c = [Pos (vs ! i)]\<close>)
    }
    then show ?thesis
      using satisfies_def by simp
  qed
  moreover have "\<alpha> \<Turnstile> map (\<lambda>s. [Neg s]) (drop k vs)"
    (is "\<alpha> \<Turnstile> ?phi")
  proof -
    {
      fix c :: clause
      assume c: "c \<in> set ?phi"
      then obtain s where "c = [Neg s]" and "s \<in> set (drop k vs)"
        by auto
      then obtain j where "j < length vs - k" and "s = drop k vs ! j"
        by (metis in_set_conv_nth length_drop)
      define i where "i = j + k"
      then have "i \<ge> k" and "s = vs ! i"
        by (auto simp add: \<open>s = drop k vs ! j\<close> add.commute assms(1) i_def)
      then have "c = [Neg (vs ! i)]"
        using `c = [Neg s]` by simp
      moreover have "i < length vs"
        using assms(1) using \<open>j < length vs - k\<close> i_def by simp
      ultimately have "\<not> \<alpha> (vs ! i)"
        using assms(2) blocky_def[of \<alpha> vs k] i_def by simp
      then have "satisfies_clause \<alpha> c"
        using satisfies_clause_def by (simp add: \<open>c = [Neg (vs ! i)]\<close>)
    }
    then show ?thesis
      using satisfies_def by simp
  qed
  ultimately show ?thesis
    using satisfies_def Psi_def by auto
qed

lemma blocky_imp_unary:
  assumes "k \<le> length vs" and "blocky \<alpha> vs k"
  shows "unary \<alpha> vs = k"
  using assms satisfies_Psi Psi_unary by simp

text \<open>
The family $\Upsilon$ of CNF formulas also takes as parameter a list of variable
indices.
\<close>

definition Upsilon :: "nat list \<Rightarrow> formula" ("\<Upsilon>") where
  "\<Upsilon> vs \<equiv> map (\<lambda>s. [Pos s]) (take 2 vs) @ map (\<lambda>s. [Neg s]) (drop 3 vs)"

text \<open>
For $|\mathit{vs}| > 2$, an assignment satisfies $\Upsilon(\mathit{vs})$ iff.\
it satisfies $\Psi(\mathit{vs}, 2)$ or $\Psi(\mathit{vs}, 3)$.
\<close>

lemma Psi_2_imp_Upsilon:
  fixes \<alpha> :: assignment
  assumes "\<alpha> \<Turnstile> \<Psi> vs 2" and "length vs > 2"
  shows "\<alpha> \<Turnstile> \<Upsilon> vs"
proof -
  have "\<alpha> \<Turnstile> map (\<lambda>s. [Pos s]) (take 2 vs)"
    using assms Psi_def satisfies_def by simp
  moreover have "\<alpha> \<Turnstile> map (\<lambda>s. [Neg s]) (drop 3 vs)"
    using assms Psi_def satisfies_def
    by (smt (z3) Cons_nth_drop_Suc One_nat_def Suc_1 Un_iff insert_iff list.set(2) list.simps(9)
      numeral_3_eq_3 set_append)
  ultimately show ?thesis
    using Upsilon_def satisfies_def by auto
qed

lemma Psi_3_imp_Upsilon:
  assumes "\<alpha> \<Turnstile> \<Psi> vs 3" and "length vs > 2"
  shows "\<alpha> \<Turnstile> \<Upsilon> vs"
proof -
  have "\<alpha> \<Turnstile> map (\<lambda>s. [Pos s]) (take 2 vs)"
    using assms Psi_def satisfies_def
    by (metis eval_nat_numeral(3) map_append satisfies_append(1) take_Suc_conv_app_nth)
  moreover have "\<alpha> \<Turnstile> map (\<lambda>s. [Neg s]) (drop 3 vs)"
    using assms Psi_def satisfies_def by simp
  ultimately show ?thesis
    using Upsilon_def satisfies_def by auto
qed

lemma Upsilon_imp_Psi_2_or_3:
  assumes "\<alpha> \<Turnstile> \<Upsilon> vs" and "length vs > 2"
  shows "\<alpha> \<Turnstile> \<Psi> vs 2 \<or> \<alpha> \<Turnstile> \<Psi> vs 3"
proof -
  have "\<alpha> \<Turnstile> map (\<lambda>s. [Pos s]) (take 2 vs)"
    using satisfies_def assms Upsilon_def by simp
  then have "satisfies_clause \<alpha> [Pos v]" if "v \<in> set (take 2 vs)" for v
    using satisfies_def that by simp
  then have "satisfies_literal \<alpha> (Pos v)" if "v \<in> set (take 2 vs)" for v
    using satisfies_clause_def that by simp
  then have 1: "\<alpha> v" if "v \<in> set (take 2 vs)" for v
    using that by simp
  then have 2: "satisfies_clause \<alpha> [Pos v]" if "v \<in> set (take 2 vs)" for v
    using that satisfies_clause_def by simp

  have "\<alpha> \<Turnstile> map (\<lambda>s. [Neg s]) (drop 3 vs)"
    using satisfies_def assms Upsilon_def by simp
  then have "satisfies_clause \<alpha> [Neg v]" if "v \<in> set (drop 3 vs)" for v
    using satisfies_def that by simp
  then have "satisfies_literal \<alpha> (Neg v)" if "v \<in> set (drop 3 vs)" for v
    using satisfies_clause_def that by simp
  then have 3: "\<not> \<alpha> v" if "v \<in> set (drop 3 vs)" for v
    using that by simp
  then have 4: "satisfies_clause \<alpha> [Neg v]" if "v \<in> set (drop 3 vs)" for v
    using that satisfies_clause_def by simp

  show ?thesis
  proof (cases "\<alpha> (vs ! 2)")
    case True
    then have "\<alpha> v" if "v \<in> set (take 3 vs)" for v
      using that 1 assms(2)
      by (metis (no_types, lifting) in_set_conv_nth le_simps(3) length_take less_imp_le_nat linorder_neqE_nat
       min_absorb2 not_less_eq nth_take numeral_One numeral_plus_numeral plus_1_eq_Suc semiring_norm(3))
    then have "satisfies_clause \<alpha> [Pos v]" if "v \<in> set (take 3 vs)" for v
      using that satisfies_clause_def by simp
    then have "\<alpha> \<Turnstile> \<Psi> vs 3"
      using 4 Psi_def satisfies_def by auto
    then show ?thesis
      by simp
  next
    case False
    then have "\<not> \<alpha> v" if "v \<in> set (drop 2 vs)" for v
      using that 3 assms(2)
      by (metis Cons_nth_drop_Suc numeral_plus_numeral numerals(1) plus_1_eq_Suc semiring_norm(3) set_ConsD)
    then have "satisfies_clause \<alpha> [Neg v]" if "v \<in> set (drop 2 vs)" for v
      using that satisfies_clause_def by simp
    then have "\<alpha> \<Turnstile> \<Psi> vs 2"
      using 2 Psi_def satisfies_def by auto
    then show ?thesis
      by simp
  qed
qed

lemma Upsilon_unary:
  assumes "\<alpha> \<Turnstile> \<Upsilon> vs" and "length vs > 2"
  shows "unary \<alpha> vs = 2 \<or> unary \<alpha> vs = 3"
  using assms Upsilon_imp_Psi_2_or_3 Psi_unary by fastforce


section \<open>The functions $\inputpos$ and $\prev$\<close>

text \<open>
Sequences of the symbol~\textbf{0}:
\<close>

definition zeros :: "nat \<Rightarrow> symbol list" where
  "zeros n \<equiv> string_to_symbols (replicate n \<bbbO>)"

lemma length_zeros [simp]: "length (zeros n) = n"
  using zeros_def by simp

lemma bit_symbols_zeros: "bit_symbols (zeros n)"
  using zeros_def by simp

lemma zeros: "zeros n = replicate n \<zero>"
  using zeros_def by simp

text \<open>
The assumptions in the following locale are the conditions that according to
lemma~@{text NP_imp_oblivious_2tape} hold for all $\NP$ languages.  The
construction of $\Phi$ will take place inside this locale, which in later
chapters will be extended to contain the Turing machine outputting $\Phi$ and
the correctness proof for this Turing machine.
\<close>

locale reduction_sat =
  fixes L :: language
  fixes M :: machine
    and G :: nat
    and T p :: "nat \<Rightarrow> nat"
  assumes T: "big_oh_poly T"
  assumes p: "polynomial p"
  assumes tm_M: "turing_machine 2 G M"
    and oblivious_M: "oblivious M"
    and T_halt: "\<And>y. bit_symbols y \<Longrightarrow> fst (execute M (start_config 2 y) (T (length y))) = length M"
    and cert: "\<And>x.
     x \<in> L \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> execute M (start_config 2 \<langle>x; u\<rangle>) (T (length \<langle>x; u\<rangle>)) <.> 1 = \<one>)"
begin

text \<open>
The value $H$ is an upper bound for the number of states of $M$ and the alphabet
size of $M$.
\<close>

definition H :: nat where
  "H \<equiv> max G (length M)"

lemma H_ge_G: "H \<ge> G"
  using H_def by simp

lemma H_gr_2: "H > 2"
  using H_def tm_M turing_machine_def by auto

lemma H_ge_3: "H \<ge> 3"
  using H_gr_2 by simp

lemma H_ge_length_M: "H \<ge> length M"
  using H_def by simp

text \<open>
The number of symbols used for encoding one snapshot is $Z = 3H$:
\<close>

definition Z :: nat where
  "Z \<equiv> 3 * H"

text \<open>
The configuration after running $M$ on input $y$ for $t$ steps:
\<close>

abbreviation exc :: "symbol list \<Rightarrow> nat \<Rightarrow> config" where
  "exc y t \<equiv> execute M (start_config 2 y) t"

text \<open>
The function $T$ is just some polynomial upper bound for the running time. The
next function, $TT$, is the actual running time. Since $M$ is oblivious, its
running time depends only on the length of the input. The argument @{term "zeros
n"} is thus merely a placeholder for an arbitrary symbol sequence of length $n$.
\<close>

definition TT :: "nat \<Rightarrow> nat" where
  "TT n \<equiv> LEAST t. fst (exc (zeros n) t) = length M"

lemma TT: "fst (exc (zeros n) (TT n)) = length M"
proof -
  let ?P = "\<lambda>t. fst (exc (zeros n) t) = length M"
  have "?P (T n)"
    using T_halt bit_symbols_zeros length_zeros by metis
  then show ?thesis
  using wellorder_Least_lemma[of ?P] TT_def by simp
qed

lemma TT_le: "TT n \<le> T n"
  using wellorder_Least_lemma length_zeros TT_def T_halt[OF bit_symbols_zeros[of n]] by fastforce

lemma less_TT: "t < TT n \<Longrightarrow> fst (exc (zeros n) t) < length M"
proof -
  assume "t < TT n"
  then have "fst (exc (zeros n) t) \<noteq> length M"
    using TT_def not_less_Least by auto
  moreover have "fst (exc (zeros n) t) \<le> length M" for t
    using tm_M start_config_def turing_machine_execute_states by auto
  ultimately show "fst (exc (zeros n) t) < length M"
    using less_le by blast
qed

lemma oblivious_halt_state:
  assumes "bit_symbols zs"
  shows "fst (exc zs t) < length M \<longleftrightarrow> fst (exc (zeros (length zs)) t) < length M"
proof -
  obtain e where
    e: "\<forall>zs. bit_symbols zs \<longrightarrow> (\<exists>tps. trace M (start_config 2 zs) (e (length zs)) (length M, tps))"
    using oblivious_M oblivious_def by auto
  let ?es = "e (length zs)"
  have "\<forall>i<length ?es. fst (exc zs i) < length M"
    using trace_def e assms by simp
  moreover have "fst (exc zs (length ?es)) = length M"
    using trace_def e assms by auto
  moreover have "\<forall>i<length ?es. fst (exc (zeros (length zs)) i) < length M"
    using length_zeros bit_symbols_zeros trace_def e by simp
  moreover have "fst (exc (zeros (length zs)) (length ?es)) = length M"
    using length_zeros bit_symbols_zeros trace_def e assms
    by (smt (verit, ccfv_SIG) fst_conv)
  ultimately show ?thesis
    by (metis (no_types, lifting) execute_after_halting_ge le_less_linear)
qed

corollary less_TT':
  assumes "bit_symbols zs" and "t < TT (length zs)"
  shows "fst (exc zs t) < length M"
  using assms oblivious_halt_state less_TT by simp

corollary TT':
  assumes "bit_symbols zs"
  shows "fst (exc zs (TT (length zs))) = length M"
  using assms TT oblivious_halt_state
  by (metis (no_types, lifting) fst_conv start_config_def start_config_length less_le tm_M
    turing_machine_execute_states zero_le zero_less_numeral)

lemma exc_TT_eq_exc_T:
  assumes "bit_symbols zs"
  shows "exc zs (TT (length zs)) = exc zs (T (length zs))"
  using execute_after_halting_ge[OF TT'[OF assms] TT_le] by simp

text \<open>
The position of the input tape head of $M$ depends only on the length $n$ of the
input and the step $t$, at least as long as the input is over the alphabet
$\{\mathbf{0}, \mathbf{1}\}$.
\<close>

definition inputpos :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "inputpos n t \<equiv> exc (zeros n) t <#> 0"

lemma inputpos_oblivious:
  assumes "bit_symbols zs"
  shows "exc zs t <#> 0 = inputpos (length zs) t"
proof -
  obtain e where
    e: "(\<forall>zs. bit_symbols zs \<longrightarrow> (\<exists>tps. trace M (start_config 2 zs) (e (length zs)) (length M, tps)))"
    using oblivious_M oblivious_def by auto
  let ?es = "e (length zs)"
  obtain tps where t1: "trace M (start_config 2 zs) ?es (length M, tps)"
    using e assms by auto
  let ?zs = "(replicate (length zs) 2)"
  have "proper_symbols ?zs"
    by simp
  moreover have "length ?zs = length zs"
    by simp
  ultimately obtain tps0 where t0: "trace M (start_config 2 ?zs) ?es (length M, tps0)"
    using e by fastforce
  have le: "exc zs t <#> 0 = inputpos (length zs) t" if "t \<le> length ?es" for t
  proof (cases "t = 0")
    case True
    then show ?thesis
      by (simp add: start_config_def inputpos_def)
  next
    case False
    then obtain i where i: "Suc i = t"
      using gr0_implies_Suc by auto
    then have "exc zs (Suc i) <#> 0 = fst (?es ! i)"
      using t1 False that Suc_le_lessD trace_def by auto
    moreover have "exc ?zs (Suc i) <#> 0 = fst (?es ! i)"
      using t0 False i that Suc_le_lessD trace_def by auto
    ultimately show ?thesis
      using i inputpos_def zeros by simp
  qed
  moreover have "exc zs t <#> 0 = inputpos (length zs) t" if "t > length ?es"
  proof -
    have "exc ?zs (length ?es) = (length M, tps0)"
      using t0 trace_def by simp
    then have *: "exc ?zs t = exc ?zs (length ?es)"
      using that by (metis execute_after_halting_ge fst_eqD less_or_eq_imp_le)
    have "exc zs (length ?es) = (length M, tps)"
      using t1 trace_def by simp
    then have "exc zs t = exc zs (length ?es)"
      using that by (metis execute_after_halting_ge fst_eqD less_or_eq_imp_le)
    then show ?thesis
      using * le[of "length ?es"] by (simp add: inputpos_def zeros)
  qed
  ultimately show ?thesis
    by fastforce
qed

text \<open>
The position of the tape head on the output tape of $M$ also depends only on the
length $n$ of the input and the step $t$.
\<close>

lemma oblivious_headpos_1:
  assumes "bit_symbols zs"
  shows "exc zs t <#> 1 = exc (zeros (length zs)) t <#> 1"
proof -
  obtain e where
    e: "(\<forall>zs. bit_symbols zs \<longrightarrow> (\<exists>tps. trace M (start_config 2 zs) (e (length zs)) (length M, tps)))"
    using oblivious_M oblivious_def by auto
  let ?es = "e (length zs)"
  obtain tps where t1: "trace M (start_config 2 zs) ?es (length M, tps)"
    using e assms by auto
  let ?zs = "(replicate (length zs) 2)"
  have "proper_symbols ?zs"
    by simp
  moreover have "length ?zs = length zs"
    by simp
  ultimately obtain tps0 where t0: "trace M (start_config 2 ?zs) ?es (length M, tps0)"
    using e by fastforce
  have le: "exc zs t <#> 1 = exc (zeros (length zs)) t <#> 1" if "t \<le> length ?es" for t
  proof (cases "t = 0")
    case True
    then show ?thesis
      by (simp add: start_config_def inputpos_def)
  next
    case False
    then obtain i where i: "Suc i = t"
      using gr0_implies_Suc by auto
    then have "exc zs (Suc i) <#> 1 = snd (?es ! i)"
      using t1 False that Suc_le_lessD trace_def by auto
    moreover have "exc ?zs (Suc i) <#> 1 = snd (?es ! i)"
      using t0 False i that Suc_le_lessD trace_def by auto
    ultimately show ?thesis
      using i inputpos_def zeros by simp
  qed
  moreover have "exc zs t <#> 1 = exc (zeros (length zs)) t <#> 1" if "t > length ?es"
  proof -
    have "exc ?zs (length ?es) = (length M, tps0)"
      using t0 trace_def by simp
    then have *: "exc ?zs t = exc ?zs (length ?es)"
      using that by (metis execute_after_halting_ge fst_eqD less_or_eq_imp_le)
    have "exc zs (length ?es) = (length M, tps)"
      using t1 trace_def by simp
    then have "exc zs t = exc zs (length ?es)"
      using that by (metis execute_after_halting_ge fst_eqD less_or_eq_imp_le)
    then show ?thesis
      using * le[of "length ?es"] by (simp add: inputpos_def zeros)
  qed
  ultimately show ?thesis
    using le_less_linear by blast
qed

text \<open>
The value $\prev(t)$ is the most recent step in which $M$'s output tape head was
in the same position as in step $t$. If no such step exists, $\prev(t)$ is set to
$t$. Again due to $M$ being oblivious, $\prev$ depends only on the length $n$ of
the input (and on $t$, of course).
\<close>

definition prev :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "prev n t \<equiv>
    if \<exists>t'<t. exc (zeros n) t' <#> 1 = exc (zeros n) t <#> 1
    then GREATEST t'. t' < t \<and> exc (zeros n) t' <#> 1 = exc (zeros n) t <#> 1
    else t"

lemma oblivious_prev:
  assumes "bit_symbols zs"
  shows "prev (length zs) t =
   (if \<exists>t'<t. exc zs t' <#> 1 = exc zs t <#> 1
    then GREATEST t'. t' < t \<and> exc zs t' <#> 1 = exc zs t <#> 1
    else t)"
  using prev_def assms oblivious_headpos_1 by auto

lemma prev_less:
  assumes "\<exists>t'<t. exc (zeros n) t' <#> 1 = exc (zeros n) t <#> 1"
  shows "prev n t < t \<and> exc (zeros n) (prev n t) <#> 1 = exc (zeros n) t <#> 1"
proof -
  let ?P = "\<lambda>t'. t' < t \<and> exc (zeros n) t' <#> 1 = exc (zeros n) t <#> 1"
  have "prev n t = (GREATEST t'. t' < t \<and> exc (zeros n) t' <#> 1 = exc (zeros n) t <#> 1)"
    using assms prev_def by simp
  moreover have "\<forall>y. ?P y \<longrightarrow> y \<le> t"
    by simp
  ultimately show ?thesis
    using GreatestI_ex_nat[OF assms, of t] by simp
qed

corollary prev_less':
  assumes "bit_symbols zs"
  assumes "\<exists>t'<t. exc zs t' <#> 1 = exc zs t <#> 1"
  shows "prev (length zs) t < t \<and> exc zs (prev (length zs) t) <#> 1 = exc zs t <#> 1"
  using prev_less oblivious_headpos_1 assms by simp

lemma prev_greatest:
  assumes "t' < t" and "exc (zeros n) t' <#> 1 = exc (zeros n) t <#> 1"
  shows "t' \<le> prev n t"
proof -
  let ?P = "\<lambda>t'. t' < t \<and> exc (zeros n) t' <#> 1 = exc (zeros n) t <#> 1"
  have "prev n t = (GREATEST t'. t' < t \<and> exc (zeros n) t' <#> 1 = exc (zeros n) t <#> 1)"
    using assms prev_def by auto
  moreover have "?P t'"
    using assms by simp
  moreover have "\<forall>y. ?P y \<longrightarrow> y \<le> t"
    by simp
  ultimately show ?thesis
    using Greatest_le_nat[of ?P t' t] by simp
qed

corollary prev_greatest':
  assumes "bit_symbols zs"
  assumes "t' < t" and "exc zs t' <#> 1 = exc zs t <#> 1"
  shows "t' \<le> prev (length zs) t"
  using prev_greatest oblivious_headpos_1 assms by simp

lemma prev_eq: "prev n t = t \<longleftrightarrow> \<not> (\<exists>t'<t. exc (zeros n) t' <#> 1 = exc (zeros n) t <#> 1)"
  using prev_def nat_less_le prev_less by simp

lemma prev_le: "prev n t \<le> t"
  using prev_eq prev_less by (metis less_or_eq_imp_le)

corollary prev_eq':
  assumes "bit_symbols zs"
  shows "prev (length zs) t = t \<longleftrightarrow> \<not> (\<exists>t'<t. exc zs t' <#> 1 = exc zs t <#> 1)"
  using prev_eq oblivious_headpos_1 assms by simp

lemma prev_between:
  assumes "prev n t < t'" and "t' < t"
  shows "exc (zeros n) t' <#> 1 \<noteq> exc (zeros n) (prev n t) <#> 1"
  using assms by (metis (no_types, lifting) leD prev_eq prev_greatest prev_less)

lemma prev_write_read:
  assumes "bit_symbols zs" and "n = length zs"
    and "prev n t < t" and "cfg = exc zs (prev n t)" and "t \<le> TT n"
  shows "exc zs t <.> 1 = (M ! (fst cfg)) [cfg <.> 0, cfg <.> 1] [.] 1"
proof -
  let ?cfg = "exc zs (Suc (prev n t))"
  let ?sas = "(M ! (fst cfg)) [cfg <.> 0, cfg <.> 1]"
  let ?i = "cfg <#> 1"
  have 1: "fst cfg < length M"
    using assms less_TT' by simp
  have 2: "||cfg|| = 2"
    using assms execute_num_tapes start_config_length tm_M by auto
  then have 3: "read (snd cfg) = [cfg <.> 0, cfg <.> 1]"
    using read_def
    by (smt (z3) Cons_eq_map_conv Suc_1 length_0_conv length_Suc_conv list.simps(8)
      nth_Cons_0 nth_Cons_Suc numeral_1_eq_Suc_0 numeral_One)

  have *: "(?cfg <:> 1) ?i = (M ! (fst cfg)) [cfg <.> 0, cfg <.> 1] [.] 1"
  proof -
    have "?cfg <!> 1 = exe M cfg <!> 1"
      by (simp add: assms)
    also have "... = sem (M ! (fst cfg)) cfg <!> 1"
      using 1 exe_lt_length by simp
    also have "... = act (snd ((M ! (fst cfg)) (read (snd cfg))) ! 1) (snd cfg ! 1)"
      using sem_snd_tm tm_M 1 2 by (metis Suc_1 lessI prod.collapse)
    also have "... = act (?sas [!] 1) (cfg <!> 1)"
      using 3 by simp
    finally have *: "?cfg <!> 1 = act (?sas [!] 1) (cfg <!> 1)" .

    have "(?cfg <:> 1) ?i = fst (?cfg <!> 1) ?i"
      by simp
    also have ***: "... = ((fst (cfg <!> 1))(?i := (?sas [.] 1))) ?i"
      using * act by simp
    also have "... = ?sas [.] 1"
      by simp
    finally show "(?cfg <:> 1) ?i = ?sas [.] 1"
      using *** by simp
  qed

  have "((exc zs t') <:> 1) ?i = (M ! (fst cfg)) [cfg <.> 0, cfg <.> 1] [.] 1"
    if "Suc (prev n t) \<le> t'" and "t' \<le> t" for t'
  using that
  proof (induction t' rule: nat_induct_at_least)
    case base
    then show ?case
      using * by simp
  next
    case (Suc m)
    let ?cfg_m = "exc zs m"
    from Suc have between: "prev n t < m" "m < t"
      by simp_all
    then have *: "?cfg_m <#> 1 \<noteq> ?i"
      using prev_between assms oblivious_headpos_1 by simp

    have "m < TT n"
      using Suc assms by simp
    then have 1: "fst ?cfg_m < length M"
      using assms less_TT' by simp
    have 2: "||?cfg_m|| = 2"
      using execute_num_tapes start_config_length tm_M by auto

    have "exc zs (Suc m) <!> 1 = exe M ?cfg_m <!> 1"
      by simp
    also have "... = sem (M ! (fst ?cfg_m)) ?cfg_m <!> 1"
      using 1 exe_lt_length by simp
    also have "... = act (snd ((M ! (fst ?cfg_m)) (read (snd ?cfg_m))) ! 1) (snd ?cfg_m ! 1)"
      using sem_snd_tm tm_M 1 2 by (metis Suc_1 lessI prod.collapse)
    finally have "exc zs (Suc m) <!> 1 = act (snd ((M ! (fst ?cfg_m)) (read (snd ?cfg_m))) ! 1) (snd ?cfg_m ! 1)" .
    then have "(exc zs (Suc m) <:> 1) ?i = fst (snd ?cfg_m ! 1) ?i"
      using * act_changes_at_most_pos' by simp
    then show ?case
      using Suc by simp
  qed
  then have "((exc zs t) <:> 1) ?i = (M ! (fst cfg)) [cfg <.> 0, cfg <.> 1] [.] 1"
    using Suc_leI assms by simp
  moreover have "?i = exc zs t <#> 1"
    using assms(1,2,4) oblivious_headpos_1 prev_eq prev_less by (smt (z3))
  ultimately show ?thesis
    by simp
qed

lemma prev_no_write:
  assumes "bit_symbols zs" and "n = length zs"
    and "prev n t = t" and "t \<le> TT n" and "t > 0"
  shows "exc zs t <.> 1 = \<box>"
proof -
  let ?i = "exc zs t <#> 1"

  have 1: "\<not> (\<exists>t'<t. exc zs t' <#> 1 = ?i)"
    using prev_eq' assms(1,2,3) by simp

  have 2: "?i > 0"
  proof (rule ccontr)
    assume "\<not> 0 < ?i"
    then have eq0: "?i = 0"
      by simp
    moreover have "exc zs 0 <#> 1 = 0"
      by (simp add: start_config_pos)
    ultimately show False
      using 1 assms(5) by auto
  qed

  have 3: "(exc zs (Suc t') <:> 1) i = (exc zs t' <:> 1) i" if "i \<noteq> exc zs t' <#> 1" for i t'
  proof (cases "fst (exc zs t') < length M")
    case True
    let ?cfg = "exc zs t'"
    have len2: "||?cfg|| = 2"
      using execute_num_tapes start_config_length tm_M by auto
    have "exc zs (Suc t') <!> 1 = exe M ?cfg <!> 1"
      by simp
    also have "... = sem (M ! (fst ?cfg)) ?cfg <!> 1"
      using True exe_lt_length by simp
    also have "... = act (snd ((M ! (fst ?cfg)) (read (snd ?cfg))) ! 1) (snd ?cfg ! 1)"
      using sem_snd_tm tm_M True len2 by (metis Suc_1 lessI prod.collapse)
    finally have "exc zs (Suc t') <!> 1 = act (snd ((M ! (fst ?cfg)) (read (snd ?cfg))) ! 1) (snd ?cfg ! 1)" .
    then have "(exc zs (Suc t') <:> 1) i = fst (snd ?cfg ! 1) i"
      using that act_changes_at_most_pos' by simp
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using that by (simp add: exe_def)
  qed

  have "(exc zs t' <:> 1) ?i = (exc zs 0 <:> 1) ?i" if "t' \<le> t" for t'
    using that
  proof (induction t')
    case 0
    then show ?case
      by simp
  next
    case (Suc t')
    then show ?case
      by (metis 1 3 Suc_leD Suc_le_lessD)
  qed
  then have "exc zs t <.> 1 = (exc zs 0 <:> 1) ?i"
    by simp
  then show ?thesis
    using 2 One_nat_def execute.simps(1) start_config1 less_2_cases_iff less_one by presburger
qed

text \<open>
The intervals $\gamma_i$ and $w_0, \dots, w_9$ do not depend on $x$, and so can
be defined here already.
\<close>

definition gamma :: "nat \<Rightarrow> nat list" ("\<gamma>") where
  "\<gamma> i \<equiv> [i * H..<Suc i * H]"

lemma length_gamma [simp]: "length (\<gamma> i) = H"
  using gamma_def by simp

abbreviation "w\<^sub>0 \<equiv> [0..<H]"
abbreviation "w\<^sub>1 \<equiv> [H..<2*H]"
abbreviation "w\<^sub>2 \<equiv> [2*H..<Z]"
abbreviation "w\<^sub>3 \<equiv> [Z..<Z+H]"
abbreviation "w\<^sub>4 \<equiv> [Z+H..<Z+2*H]"
abbreviation "w\<^sub>5 \<equiv> [Z+2*H..<2*Z]"
abbreviation "w\<^sub>6 \<equiv> [2*Z..<2*Z+H]"
abbreviation "w\<^sub>7 \<equiv> [2*Z+H..<2*Z+2*H]"
abbreviation "w\<^sub>8 \<equiv> [2*Z+2*H..<3*Z]"
abbreviation "w\<^sub>9 \<equiv> [3*Z..<3*Z+H]"

lemma unary_upt_eq:
  fixes \<alpha>\<^sub>1 \<alpha>\<^sub>2 :: assignment
    and lower upper k :: nat
  assumes "\<forall>i<k. \<alpha>\<^sub>1 i = \<alpha>\<^sub>2 i" and "upper \<le> k"
  shows "unary \<alpha>\<^sub>1 [lower..<upper] = unary \<alpha>\<^sub>2 [lower..<upper]"
proof -
  have "numtrue \<alpha>\<^sub>1 [lower..<upper] = numtrue \<alpha>\<^sub>2 [lower..<upper]"
  proof -
    let ?vs = "[lower..<upper]"
    have "filter \<alpha>\<^sub>1 ?vs = filter \<alpha>\<^sub>2 ?vs"
      using assms by (metis atLeastLessThan_iff filter_cong less_le_trans set_upt)
    then show ?thesis
      using numtrue_def by simp
  qed
  moreover have "blocky \<alpha>\<^sub>1 [lower..<upper] = blocky \<alpha>\<^sub>2 [lower..<upper]"
    using blocky_def assms by auto
  ultimately show ?thesis
    using assms unary_def by simp
qed

text \<open>
For the case @{term "prev m t < t"}, we have the following predicate on
assignments, which corresponds to ($\mathrm{F}_1$), ($\mathrm{F}_2$),
($\mathrm{F}_3$) from the introduction:
\<close>

definition F :: "assignment \<Rightarrow> bool" where
  "F \<alpha> \<equiv>
     unary \<alpha> w\<^sub>6 = unary \<alpha> w\<^sub>9 \<and>
     unary \<alpha> w\<^sub>7 = (M ! (unary \<alpha> w\<^sub>5)) [unary \<alpha> w\<^sub>3, unary \<alpha> w\<^sub>4] [.] 1 \<and>
     unary \<alpha> w\<^sub>8 = fst ((M ! (unary \<alpha> w\<^sub>2)) [unary \<alpha> w\<^sub>0, unary \<alpha> w\<^sub>1])"

lemma depon_F: "depon (3 * Z + H) F"
  using depon_def F_def Z_def unary_upt_eq by simp

text \<open>
There is a CNF formula $\psi$ that contains the first $3Z + H$ variables and
is satisfied by exactly the assignments specified by $F$.
\<close>

definition psi :: formula ("\<psi>") where
  "\<psi> \<equiv> SOME \<phi>.
    fsize \<phi> \<le> (3 * Z + H) * 2 ^ (3 * Z + H) \<and>
    length \<phi> \<le> 2 ^ (3 * Z + H) \<and>
    variables \<phi> \<subseteq> {..<3 * Z + H} \<and>
    (\<forall>\<alpha>. F \<alpha> = \<alpha> \<Turnstile> \<phi>)"

lemma psi:
  "fsize \<psi> \<le> (3 * Z + H) * 2 ^ (3*Z + H) \<and>
   length \<psi> \<le> 2 ^ (3 * Z + H) \<and>
   variables \<psi> \<subseteq> {..<3 * Z + H} \<and>
   (\<forall>\<alpha>. F \<alpha> = \<alpha> \<Turnstile> \<psi>)"
  using psi_def someI_ex[OF depon_ex_formula[OF depon_F]] by metis

lemma satisfies_psi:
  assumes "length \<sigma> = 3 * Z + H"
  shows "\<alpha> \<Turnstile> relabel \<sigma> \<psi> = remap \<sigma> \<alpha> \<Turnstile> \<psi>"
  using assms psi satisfies_sigma by simp

lemma psi_F: "remap \<sigma> \<alpha> \<Turnstile> \<psi> = F (remap \<sigma> \<alpha>)"
  using psi by simp

corollary satisfies_F:
  assumes "length \<sigma> = 3 * Z + H"
  shows "\<alpha> \<Turnstile> relabel \<sigma> \<psi> = F (remap \<sigma> \<alpha>)"
  using assms satisfies_psi psi_F by simp

text \<open>
For the case @{term "prev m t = t"}, the following predicate corresponds to
($\mathrm{F}_1'$), ($\mathrm{F}_2'$), ($\mathrm{F}_3'$) from the introduction:
\<close>

definition F' :: "assignment \<Rightarrow> bool" where
  "F' \<alpha> \<equiv>
     unary \<alpha> w\<^sub>3 = unary \<alpha> w\<^sub>6 \<and>
     unary \<alpha> w\<^sub>4 = 0 \<and>
     unary \<alpha> w\<^sub>5 = fst ((M ! (unary \<alpha> w\<^sub>2)) [unary \<alpha> w\<^sub>0, unary \<alpha> w\<^sub>1])"

lemma depon_F': "depon (2 * Z + H) F'"
  using depon_def F'_def Z_def unary_upt_eq by simp

text \<open>
The CNF formula $\psi'$ is analogous to $\psi$ from the previous case.
\<close>

definition psi' :: formula ("\<psi>''") where
  "\<psi>' \<equiv> SOME \<phi>.
    fsize \<phi> \<le> (2*Z+H) * 2 ^ (2*Z+H) \<and>
    length \<phi> \<le> 2 ^ (2*Z+H) \<and>
    variables \<phi> \<subseteq> {..<2*Z+H} \<and>
    (\<forall>\<alpha>. F' \<alpha> = \<alpha> \<Turnstile> \<phi>)"

lemma psi':
  "fsize \<psi>' \<le> (2*Z+H) * 2 ^ (2*Z+H) \<and>
   length \<psi>' \<le> 2 ^ (2*Z+H) \<and>
   variables \<psi>' \<subseteq> {..<2*Z+H} \<and>
   (\<forall>\<alpha>. F' \<alpha> = \<alpha> \<Turnstile> \<psi>')"
  using psi'_def someI_ex[OF depon_ex_formula[OF depon_F']] by metis

lemma satisfies_psi':
  assumes "length \<sigma> = 2*Z+H"
  shows "\<alpha> \<Turnstile> relabel \<sigma> \<psi>' = remap \<sigma> \<alpha> \<Turnstile> \<psi>'"
  using assms psi' satisfies_sigma by simp

lemma psi'_F': "remap \<sigma> \<alpha> \<Turnstile> \<psi>' = F' (remap \<sigma> \<alpha>)"
  using psi' by simp

corollary satisfies_F':
  assumes "length \<sigma> = 2*Z+H"
  shows "\<alpha> \<Turnstile> relabel \<sigma> \<psi>' = F' (remap \<sigma> \<alpha>)"
  using assms satisfies_psi' psi'_F' by simp

end  (* locale reduction_sat *)


section \<open>Snapshots\<close>

text \<open>
The snapshots and much of the rest of the construction of $\Phi$ depend on the
string $x$. We encapsulate this in a sublocale of @{locale reduction_sat}.
\<close>

locale reduction_sat_x = reduction_sat +
  fixes x :: string
begin

abbreviation n :: nat where
  "n \<equiv> length x"

text \<open>
Turing machines consume the string $x$ as a sequence $xs$ of symbols:
\<close>

abbreviation xs :: "symbol list" where
  "xs \<equiv> string_to_symbols x"

lemma bs_xs: "bit_symbols xs"
  by simp

text \<open>
For the verifier Turing machine $M$ we are only concerned with inputs of the
form $\langle x, u\rangle$ for a string $u$ of length $p(n)$. The pair $\langle
x, u\rangle$ has the length $m = 2n + 2p(n) + 2$.
\<close>

definition m :: nat where
  "m \<equiv> 2 * n + 2 * p n + 2"

text \<open>
On input $\langle x, u\rangle$ the Turing machine $M$ halts after $T' = TT(m)$
steps.
\<close>

definition T' :: nat where
  "T' \<equiv> TT m"

text \<open>
The positions of both of $M$'s tape heads are bounded by $T'$.
\<close>

lemma inputpos_less: "inputpos m t \<le> T'"
proof -
  define u :: string where "u = replicate (p n) False"
  let ?i = "inputpos m t"
  have y: "bit_symbols \<langle>x; u\<rangle>"
    by simp
  have len: "length \<langle>x; u\<rangle> = m"
    using u_def m_def length_pair by simp
  then have "exc \<langle>x; u\<rangle> t <#> 0 \<le> T'"
    using TT'[OF y] T'_def head_pos_le_halting_time[OF tm_M, of "\<langle>x; u\<rangle>" T' 0] by simp
  then show ?thesis
    using inputpos_oblivious[OF y] len by simp
qed

lemma headpos_1_less: "exc (zeros m) t <#> 1 \<le> T'"
proof -
  define u :: string where "u = replicate (p n) False"
  let ?i = "inputpos m t"
  have y: "bit_symbols \<langle>x; u\<rangle>"
    by simp
  have len: "length \<langle>x; u\<rangle> = m"
    using u_def m_def length_pair by simp
  then have "exc \<langle>x; u\<rangle> t <#> 1 \<le> T'"
    using TT'[OF y] T'_def head_pos_le_halting_time[OF tm_M, of "\<langle>x; u\<rangle>" "T'" 1] by simp
  then show ?thesis
    using oblivious_headpos_1[OF y] len by simp
qed

text \<open>
The formula $\Phi$ must contain a condition for every symbol that $M$ is reading
from the input tape.  While $T'$ is an upper bound for the input tape head
position of $M$, it might be that $T'$ is less than the length of the input
$\langle x, u\rangle$.  So the portion of the input read by $M$ might be a
prefix of the input or it might be the input followed by some blanks afterwards.
This would make for an awkward case distinction.  We do not have to be very
precise here and can afford to bound the portion of the input tape read by $M$
by the number $m' = 2n + 2p(n) + 3 + T'$, which is the length of the start
symbol followed by the input $\langle x, u\rangle$ followed by $T'$ blanks.
This symbol sequence was called $y(u)$ in the introduction. Here we will call it
@{term "ysymbols u"}.
\<close>

definition m' :: nat where
  "m' \<equiv> 2 * n + 2 * p n + 3 + T'"

definition ysymbols :: "string \<Rightarrow> symbol list" where
  "ysymbols u \<equiv> 1 # \<langle>x; u\<rangle> @ replicate T' 0"

lemma length_ysymbols: "length u = p n \<Longrightarrow> length (ysymbols u) = m'"
  using ysymbols_def m'_def m_def length_pair by simp

lemma ysymbols_init:
  assumes "i < length (ysymbols u)"
  shows "ysymbols u ! i = (start_config 2 \<langle>x; u\<rangle> <:> 0) i"
proof -
  let ?y = "\<langle>x; u\<rangle>"
  have init: "start_config 2 ?y <:> 0 = (\<lambda>i. if i = 0 then 1 else if i \<le> length ?y then ?y ! (i - 1) else 0)"
    using start_config_def by auto
  have "i < length ?y + 1 + T'"
    using assms ysymbols_def by simp
  then consider "i = 0" | "i > 0 \<and> i \<le> length ?y" | "i > length ?y \<and> i < length ?y + 1 + T'"
    by linarith
  then show "ysymbols u ! i = (start_config 2 ?y <:> 0) i"
  proof (cases)
    case 1
    then show ?thesis
      using ysymbols_def init by simp
  next
    case 2
    then have "ysymbols u ! i = \<langle>x; u\<rangle> ! (i - 1)"
      using ysymbols_def
      by (smt (z3) One_nat_def Suc_less_eq Suc_pred le_imp_less_Suc neq0_conv nth_Cons' nth_append)
    then show ?thesis
      using init 2 by simp
  next
    case 3
    then have "(start_config 2 ?y <:> 0) i = 0"
      using init by simp
    moreover have "ysymbols u ! i = 0"
      unfolding ysymbols_def using 3 nth_append[of "1#\<langle>x; u\<rangle>" "replicate T' 0" i] by auto
    ultimately show ?thesis
      by simp
  qed
qed

lemma ysymbols_at_0: "ysymbols u ! 0 = 1"
  using ysymbols_def by simp

lemma ysymbols_first_at:
  assumes "j < length x"
  shows "ysymbols u ! (2*j+1) = 2"
    and "ysymbols u ! (2*j+2) = (if x ! j then 3 else 2)"
proof -
  have *: "ysymbols u = (1 # \<langle>x; u\<rangle>) @ replicate T' 0"
    using ysymbols_def by simp

  let ?i = "2 * j + 1"
  have len: "2*j < length \<langle>x, u\<rangle>"
    using assms length_string_pair by simp
  have "?i < length (1 # \<langle>x; u\<rangle>)"
    using assms length_pair by simp
  then have "ysymbols u ! ?i = (1 # \<langle>x; u\<rangle>) ! ?i"
    using * nth_append by metis
  also have "... = \<langle>x; u\<rangle> ! (2*j)"
    by simp
  also have "... = 2"
    using string_pair_first_nth assms len by simp
  finally show "ysymbols u ! ?i = 2" .

  let ?i = "2 * j + 2"
  have len2: "?i < length (1 # \<langle>x; u\<rangle>)"
    using assms length_pair by simp
  then have "ysymbols u ! ?i = (1 # \<langle>x; u\<rangle>) ! ?i"
    using * nth_append by metis
  also have "... = \<langle>x; u\<rangle> ! (2*j+1)"
    by simp
  also have "... = (if x ! j then 3 else 2)"
    using string_pair_first_nth(2) assms len2 by simp
  finally show "ysymbols u ! ?i = (if x ! j then 3 else 2)" .
qed

lemma ysymbols_at_2n1: "ysymbols u ! (2*n+1) = 3"
proof -
  let ?i = "2 * n + 1"
  have "ysymbols u ! ?i = \<langle>x; u\<rangle> ! (2*n)"
    using ysymbols_def
    by (metis (no_types, lifting) add.commute add_2_eq_Suc' le_add2 le_imp_less_Suc length_pair
      less_SucI nth_Cons_Suc nth_append plus_1_eq_Suc)
  also have "... = (if \<langle>x, u\<rangle> ! (2*n) then 3 else 2)"
    using length_pair by simp
  also have "... = 3"
    using string_pair_sep_nth by simp
  finally show ?thesis .
qed

lemma ysymbols_at_2n2: "ysymbols u ! (2*n+2) = 3"
proof -
  let ?i = "2 * n + 2"
  have "ysymbols u ! ?i = \<langle>x; u\<rangle> ! (2*n+1)"
    using ysymbols_def
    by (smt (z3) One_nat_def add.commute add.right_neutral add_2_eq_Suc' add_Suc_right le_add2
      le_imp_less_Suc length_pair nth_Cons_Suc nth_append)
  also have "... = (if \<langle>x, u\<rangle> ! (2*n+1) then 3 else 2)"
    using length_pair by simp
  also have "... = 3"
    using string_pair_sep_nth by simp
  finally show ?thesis .
qed

lemma ysymbols_second_at:
  assumes "j < length u"
  shows "ysymbols u ! (2*n+2+2*j+1) = 2"
    and "ysymbols u ! (2*n+2+2*j+2) = (if u ! j then 3 else 2)"
proof -
  have *: "ysymbols u = (1 # \<langle>x; u\<rangle>) @ replicate T' 0"
    using ysymbols_def by simp

  let ?i = "2 * n + 2 + 2 * j + 1"
  have len: "2 * n + 2 + 2*j < length \<langle>x, u\<rangle>"
    using assms length_string_pair by simp
  have "?i < length (1 # \<langle>x; u\<rangle>)"
    using assms length_pair by simp
  then have "ysymbols u ! ?i = (1 # \<langle>x; u\<rangle>) ! ?i"
    using * nth_append by metis
  also have "... = \<langle>x; u\<rangle> ! (2*n+2+2*j)"
    by simp
  also have "... = 2"
    using string_pair_second_nth(1) assms len by simp
  finally show "ysymbols u ! ?i = 2" .

  let ?i = "2*n+2+2 * j + 2"
  have len2: "?i < length (1 # \<langle>x; u\<rangle>)"
    using assms length_pair by simp
  then have "ysymbols u ! ?i = (1 # \<langle>x; u\<rangle>) ! ?i"
    using * nth_append by metis
  also have "... = \<langle>x; u\<rangle> ! (2*n+2+2*j+1)"
    by simp
  also have "... = (if u ! j then 3 else 2)"
    using string_pair_second_nth(2) assms len2 by simp
  finally show "ysymbols u ! ?i = (if u ! j then 3 else 2)" .
qed

lemma ysymbols_last:
  assumes "length u = p n" and "i > m" and "i < m + 1 + T'"
  shows "ysymbols u ! i = 0"
  using assms length_ysymbols m_def m'_def ysymbols_def nth_append[of "1#\<langle>x; u\<rangle>" "replicate T' 0" i] by simp

text \<open>
The number of symbols used for unary encoding $m'$ symbols will be called $N$:
\<close>

definition N :: nat where
  "N \<equiv> H * m'"

lemma N_eq: "N = H * (2 * n + 2 * p n + 3 + T')"
  using m'_def N_def by simp

lemma m': "m' * H = N "
  using m'_def N_def by simp

lemma inputpos_less': "inputpos m t < m'"
  using inputpos_less m_def m'_def
  by (metis Suc_1 add_less_mono1 le_neq_implies_less lessI linorder_neqE_nat
   not_add_less2 numeral_plus_numeral semiring_norm(3) trans_less_add2)

lemma T'_less: "T' < N"
proof -
  have "T' < 2 * n + 2 * p n + 3 + T'"
    by simp
  also have "... < H * (2 * n + 2 * p n + 3 + T')"
    using H_gr_2 by simp
  also have "... = N"
    using N_eq by simp
  finally show ?thesis .
qed

text \<open>The three components of a snapshot:\<close>

definition z0 :: "string \<Rightarrow> nat \<Rightarrow> symbol" where
  "z0 u t \<equiv> exc \<langle>x; u\<rangle> t <.> 0"

definition z1 :: "string \<Rightarrow> nat \<Rightarrow> symbol" where
  "z1 u t \<equiv> exc \<langle>x; u\<rangle> t <.> 1"

definition z2 :: "string \<Rightarrow> nat \<Rightarrow> state" where
  "z2 u t \<equiv> fst (exc \<langle>x; u\<rangle> t)"

lemma z0_le: "z0 u t \<le> H"
  using z0_def H_ge_G tape_alphabet[OF tm_M, where ?j=0 and ?zs="\<langle>x; u\<rangle>"] symbols_lt_pair[of x u] tm_M turing_machine_def
  by (metis (no_types, lifting) dual_order.strict_trans1 less_or_eq_imp_le zero_less_numeral)

lemma z1_le: "z1 u t \<le> H"
  using z1_def H_ge_G tape_alphabet[OF tm_M, where ?j=1 and ?zs="\<langle>x; u\<rangle>"] symbols_lt_pair[of x u] tm_M turing_machine_def
  by (metis (no_types, lifting) dual_order.strict_trans1 less_or_eq_imp_le one_less_numeral_iff semiring_norm(76))

lemma z2_le: "z2 u t \<le> H"
proof -
  have "z2 u t \<le> length M"
    using z2_def turing_machine_execute_states[OF tm_M] start_config_def by simp
  then show ?thesis
    using H_ge_length_M by simp
qed

text \<open>
The next lemma corresponds to (Z1) from the second equivalence mentioned in the
introduction. It expresses the first element of a snapshot in terms of $y(u)$
and $\inputpos$.
\<close>

lemma z0:
  assumes "length u = p n"
  shows "z0 u t = ysymbols u ! (inputpos m t)"
proof -
  let ?i = "inputpos m t"
  let ?y = "\<langle>x; u\<rangle>"
  have "bit_symbols ?y"
    by simp
  have len: "length ?y = m"
    using assms m_def length_pair by simp

  have "?i < length (ysymbols u)"
    using inputpos_less' assms length_ysymbols by simp
  then have *: "ysymbols u ! ?i = (start_config 2 ?y <:> 0) ?i"
    using ysymbols_init by simp

  have "z0 u t = exc ?y t <.> 0"
    using z0_def by simp
  also have "... = (start_config 2 ?y <:> 0) (exc ?y t <#> 0)"
    using tm_M input_tape_constant start_config_length by simp
  also have "... = (start_config 2 ?y <:> 0) ?i"
    using inputpos_oblivious[OF `bit_symbols ?y`] len by simp
  also have "... = ysymbols u ! ?i"
    using * by simp
  finally show ?thesis .
qed

text \<open>
The next lemma corresponds to (Z2) from the second equivalence mentioned in the
introduction. It shows how, in the case $\prev(t) < t$, the second component of
a snapshot can be expressed recursively using snapshots for earlier steps.
\<close>

lemma z1:
  assumes "length u = p n" and "prev m t < t" and "t \<le> T'"
  shows "z1 u t = (M ! (z2 u (prev m t))) [z0 u (prev m t), z1 u (prev m t)] [.] 1"
proof -
  let ?y = "\<langle>x; u\<rangle>"
  let ?cfg = "exc ?y (prev m t)"
  have "bit_symbols ?y"
    by simp
  moreover have len: "length ?y = m"
    using assms m_def length_pair by simp
  ultimately have "exc ?y t <.> 1 = (M ! (fst ?cfg)) [?cfg <.> 0, ?cfg <.> 1] [.] 1"
    using prev_write_read[of ?y m t ?cfg] assms(2,3) T'_def by fastforce
  then show ?thesis
    using z0_def z1_def z2_def by simp
qed

text \<open>
The next lemma corresponds to (Z3) from the second equivalence mentioned in the
introduction. It shows that in the case $\prev(t) = t$, the second component of
a snapshot equals the blank symbol.
\<close>

lemma z1':
  assumes "length u = p n" and "prev m t = t" and "0 < t" and "t \<le> T'"
  shows "z1 u t = \<box>"
proof -
  let ?y = "\<langle>x; u\<rangle>"
  let ?cfg = "exc ?y (prev m t)"
  have "bit_symbols ?y"
    by simp
  moreover have len: "length ?y = m"
    using assms m_def length_pair by simp
  ultimately have "exc ?y t <.> 1 = \<box>"
    using prev_no_write[of ?y m t] assms T'_def by fastforce
  then show ?thesis
    using z0_def z1_def z2_def by simp
qed

text \<open>
The next lemma corresponds to (Z4) from the second equivalence mentioned in the
introduction. It shows how the third component of a snapshot can be expressed
recursively using snapshots for earlier steps.
\<close>

lemma z2:
  assumes "length u = p n" and "t < T'"
  shows "z2 u (Suc t) = fst ((M ! (z2 u t)) [z0 u t, z1 u t])"
proof -
  let ?y = "\<langle>x; u\<rangle>"
  have "bit_symbols ?y"
    by simp
  moreover have len: "length ?y = m"
    using assms m_def length_pair by simp
  ultimately have run: "fst (exc ?y t) < length M"
    using less_TT' assms(2) T'_def by simp

  have "||exc ?y t|| = 2"
    using start_config_length execute_num_tapes tm_M by simp
  then have "snd (exc ?y t) = [exc ?y t <!> 0, exc ?y t <!> 1]"
    by auto (smt (z3) Suc_length_conv length_0_conv nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
  then have *: "read (snd (exc ?y t)) = [exc ?y t <.> 0, exc ?y t <.> 1]"
    using read_def by (metis (no_types, lifting) list.simps(8) list.simps(9))

  have "z2 u (Suc t) = fst (exc ?y (Suc t))"
    using z2_def by simp
  also have "... = fst (exe M (exc ?y t))"
    by simp
  also have "... = fst (sem (M ! fst (exc ?y t)) (exc ?y t))"
    using exe_lt_length run by simp
  also have "... = fst (sem (M ! (z2 u t)) (exc ?y t))"
    using z2_def by simp
  also have "... = fst ((M ! (z2 u t)) (read (snd (exc ?y t))))"
    using sem_fst by simp
  also have "... = fst ((M ! (z2 u t)) [exc ?y t <.> 0, exc ?y t <.> 1])"
    using * by simp
  also have "... = fst ((M ! (z2 u t)) [z0 u t, z1 u t])"
    using z0_def z1_def by simp
  finally show ?thesis .
qed

corollary z2':
  assumes "length u = p n" and "t > 0" and "t \<le> T'"
  shows "z2 u t = fst ((M ! (z2 u (t - 1))) [z0 u (t - 1), z1 u (t - 1)])"
  using assms z2 by (metis Suc_diff_1 Suc_less_eq le_imp_less_Suc)

text \<open>
The intervals $\zeta_0$, $\zeta_1$, and $\zeta_2$ are long enough for a unary
encoding of the three components of a snapshot:
\<close>

definition zeta0 :: "nat \<Rightarrow> nat list" ("\<zeta>\<^sub>0") where
  "\<zeta>\<^sub>0 t \<equiv> [N + t * Z..<N + t * Z + H]"

definition zeta1 :: "nat \<Rightarrow> nat list" ("\<zeta>\<^sub>1") where
  "\<zeta>\<^sub>1 t \<equiv> [N + t * Z + H..<N + t * Z + 2 * H]"

definition zeta2 :: "nat \<Rightarrow> nat list" ("\<zeta>\<^sub>2") where
  "\<zeta>\<^sub>2 t \<equiv> [N + t * Z + 2 * H..<N + (Suc t) * Z]"

lemma length_zeta0 [simp]: "length (\<zeta>\<^sub>0 t) = H"
  using zeta0_def by simp

lemma length_zeta1 [simp]: "length (\<zeta>\<^sub>1 t) = H"
  using zeta1_def by simp

lemma length_zeta2 [simp]: "length (\<zeta>\<^sub>2 t) = H"
  using zeta2_def Z_def by simp

text \<open>
The substitutions $\rho_t$, which have to be applied to $\psi$ to get the CNF
formulas $\chi_t$ for the case $\prev(t) < t$:
\<close>

definition rho :: "nat \<Rightarrow> nat list" ("\<rho>") where
  "\<rho> t \<equiv>
     \<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
     \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t) @
     \<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @
     \<gamma> (inputpos m t)"

lemma length_rho: "length (\<rho> t) = 3 * Z + H"
  using rho_def Z_def by simp

text \<open>
The substitutions $\rho_t'$, which have to be applied to $\psi'$ to get
the CNF formulas $\chi_t$ for the case $\prev(t) = t$:
\<close>

definition rho' :: "nat \<Rightarrow> nat list" ("\<rho>''") where
  "\<rho>' t \<equiv>
     \<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
     \<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @
     \<gamma> (inputpos m t)"

lemma length_rho': "length (\<rho>' t) = 2 * Z + H"
  using rho'_def Z_def by simp

text \<open>
An auxiliary lemma for accessing the $n$-th element of a list sandwiched between
two lists. It will be applied to $xs = \rho_t$ or $xs = \rho'_t$:
\<close>

lemma nth_append3:
  fixes xs ys zs ws :: "'a list" and n i :: nat
  assumes "xs = ys @ zs @ ws" and "i < length zs" and "n = length ys"
  shows "xs ! (n + i) = zs ! i"
  using assms by (simp add: nth_append)

text \<open>The formulas $\chi_t$ representing snapshots for $0 < t \leq T'$:\<close>

definition chi :: "nat \<Rightarrow> formula" ("\<chi>") where
  "\<chi> t \<equiv> if prev m t < t then relabel (\<rho> t) \<psi> else relabel (\<rho>' t) \<psi>'"

text \<open>
The crucial feature of the formulas $\chi_t$ for $t > 0$ is that they are
satisfied by exactly those assignments that represent in their bits $N$ to $N +
Z\cdot(T' + 1)$ the $T' + 1$ snapshots of $M$ on input $\langle x, u\rangle$
when the relevant portion of the input tape is encoded in the first $N$ bits of
the assignment.

This works because the $\chi_t$ constrain the assignment to meet the recursive
characterizations (Z1) --- (Z4) for the snapshots.

The next two lemmas make this more precise.  We first consider the case
$\prev(t) < t$.  The following lemma says $\alpha$ satisfies $\chi_t$ iff.\
$\alpha$ satisfies the properties (Z1), (Z2), and (Z4).
\<close>

lemma satisfies_chi_less:
  fixes \<alpha> :: assignment
  assumes "prev m t < t"
  shows "\<alpha> \<Turnstile> \<chi> t \<longleftrightarrow>
    unary \<alpha> (\<zeta>\<^sub>0 t) = unary \<alpha> (\<gamma> (inputpos m t)) \<and>
    unary \<alpha> (\<zeta>\<^sub>1 t) = (M ! (unary \<alpha> (\<zeta>\<^sub>2 (prev m t)))) [unary \<alpha> (\<zeta>\<^sub>0 (prev m t)), unary \<alpha> (\<zeta>\<^sub>1 (prev m t))] [.] 1 \<and>
    unary \<alpha> (\<zeta>\<^sub>2 t) = fst ((M ! (unary \<alpha> (\<zeta>\<^sub>2 (t - 1)))) [unary \<alpha> (\<zeta>\<^sub>0 (t - 1)), unary \<alpha> (\<zeta>\<^sub>1 (t - 1))])"
proof -
  let ?sigma = "\<rho> t"
  have "\<alpha> \<Turnstile> \<chi> t = \<alpha> \<Turnstile> relabel ?sigma psi"
    using assms chi_def by simp
  then have "\<alpha> \<Turnstile> \<chi> t = F (remap ?sigma \<alpha>)"
      (is "_ = F ?alpha")
    by (simp add: length_rho satisfies_F)
  then have *: "\<alpha> \<Turnstile> \<chi> t =
     (unary ?alpha w\<^sub>6 = unary ?alpha w\<^sub>9 \<and>
      unary ?alpha w\<^sub>7 = (M ! (unary ?alpha w\<^sub>5)) [unary ?alpha w\<^sub>3, unary ?alpha w\<^sub>4] [.] 1 \<and>
      unary ?alpha w\<^sub>8 = fst ((M ! (unary ?alpha w\<^sub>2)) [unary ?alpha w\<^sub>0, unary ?alpha w\<^sub>1]))"
    using F_def by simp

  have w_less_len_rho:
    "\<forall>s\<in>set w\<^sub>0. s < length (\<rho> t)"
    "\<forall>s\<in>set w\<^sub>1. s < length (\<rho> t)"
    "\<forall>s\<in>set w\<^sub>2. s < length (\<rho> t)"
    "\<forall>s\<in>set w\<^sub>3. s < length (\<rho> t)"
    "\<forall>s\<in>set w\<^sub>4. s < length (\<rho> t)"
    "\<forall>s\<in>set w\<^sub>5. s < length (\<rho> t)"
    "\<forall>s\<in>set w\<^sub>6. s < length (\<rho> t)"
    "\<forall>s\<in>set w\<^sub>7. s < length (\<rho> t)"
    "\<forall>s\<in>set w\<^sub>8. s < length (\<rho> t)"
    "\<forall>s\<in>set w\<^sub>9. s < length (\<rho> t)"
    using length_rho Z_def by simp_all

  have **: "\<alpha> \<Turnstile> \<chi> t =
     (unary \<alpha> (reseq ?sigma w\<^sub>6) = unary \<alpha> (reseq ?sigma w\<^sub>9) \<and>
      unary \<alpha> (reseq ?sigma w\<^sub>7) = (M ! (unary \<alpha> (reseq ?sigma w\<^sub>5))) [unary \<alpha> (reseq ?sigma w\<^sub>3), unary \<alpha> (reseq ?sigma w\<^sub>4)] [.] 1 \<and>
      unary \<alpha> (reseq ?sigma w\<^sub>8) = fst ((M ! (unary \<alpha> (reseq ?sigma w\<^sub>2))) [unary \<alpha> (reseq ?sigma w\<^sub>0), unary \<alpha> (reseq ?sigma w\<^sub>1)]))"
    using * w_less_len_rho unary_remap[where ?\<sigma>="?sigma" and ?\<alpha>=\<alpha>]
    by presburger

  have 1: "reseq ?sigma w\<^sub>0 = \<zeta>\<^sub>0 (t - 1)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta0_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = [] @ \<zeta>\<^sub>0 (t - 1) @ (\<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t) @ \<zeta>\<^sub>0 t @
         \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t))"
        using rho_def by simp
      have "?sigma ! i = \<zeta>\<^sub>0 (t - 1) ! i"
        using nth_append3[OF 1, of i 0] Z_def that by simp
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 2: "reseq ?sigma w\<^sub>1 = \<zeta>\<^sub>1 (t - 1)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta1_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = \<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t) @ \<zeta>\<^sub>0 t @
         \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho_def by simp
      have "?sigma ! (H+i) = \<zeta>\<^sub>1 (t - 1) ! i"
        using that zeta0_def zeta1_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 3: "reseq ?sigma w\<^sub>2 = \<zeta>\<^sub>2 (t - 1)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show len: "length ?l = length ?r"
      using zeta2_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1)) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t) @ \<zeta>\<^sub>0 t @
         \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho_def by simp
      have "?sigma ! (2*H+i) = \<zeta>\<^sub>2 (t - 1) ! i"
        using len that zeta0_def zeta1_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 4: "reseq ?sigma w\<^sub>3 = \<zeta>\<^sub>0 (prev m t)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta0_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1)) @
          \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t) @ \<zeta>\<^sub>0 t @
         \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho_def by simp
      have "?sigma ! (Z+i) = \<zeta>\<^sub>0 (prev m t) ! i"
        using that Z_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 5: "reseq ?sigma w\<^sub>4 = \<zeta>\<^sub>1 (prev m t)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta1_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 (prev m t)) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t) @ \<zeta>\<^sub>0 t @
         \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho_def by simp
      have "?sigma ! (Z+H+i) = \<zeta>\<^sub>1 (prev m t) ! i"
        using that Z_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 6: "reseq ?sigma w\<^sub>5 = \<zeta>\<^sub>2 (prev m t)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta2_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t)) @ \<zeta>\<^sub>2 (prev m t) @ \<zeta>\<^sub>0 t @
         \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho_def by simp
      have "?sigma ! (Z+2*H+i) = \<zeta>\<^sub>2 (prev m t) ! i"
        using that zeta0_def zeta1_def zeta2_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 7: "reseq ?sigma w\<^sub>6 = \<zeta>\<^sub>0 t" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta0_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t)) @
          \<zeta>\<^sub>0 t @
         \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho_def by simp
      have "?sigma ! (2*Z+i) = \<zeta>\<^sub>0 t ! i"
        using that Z_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 8: "reseq ?sigma w\<^sub>7 = \<zeta>\<^sub>1 t" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta1_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t) @ \<zeta>\<^sub>0 t) @
          \<zeta>\<^sub>1 t @
          \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho_def by simp
      have "?sigma ! (2*Z+H+i) = \<zeta>\<^sub>1 t ! i"
        using that Z_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 9: "reseq ?sigma w\<^sub>8 = \<zeta>\<^sub>2 t" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta2_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t) @ \<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t) @
          \<zeta>\<^sub>2 t @
          \<gamma> (inputpos m t)"
        using rho_def by simp
      have "?sigma ! (2*Z+2*H+i) = \<zeta>\<^sub>2 t ! i"
        using that zeta2_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 10: "reseq ?sigma w\<^sub>9 = \<gamma> (inputpos m t)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using gamma_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t) @
          \<zeta>\<^sub>0 t @
         \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t) @ \<gamma> (inputpos m t) @ []"
        using rho_def by simp
      have "?sigma ! (3*Z+i) = \<gamma> (inputpos m t) ! i"
        using that Z_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  show ?thesis
    using ** 1 2 3 4 5 6 7 8 9 10 by simp
qed

text \<open>
Next we consider the case $\prev(t) = t$. The following lemma says $\alpha$
satisfies $\chi_t$ iff.\ $\alpha$ satisfies the properties (Z1), (Z2), and (Z3).
\<close>

lemma satisfies_chi_eq:
  assumes "prev m t = t" and "t \<le> T'"
  shows "\<alpha> \<Turnstile> \<chi> t \<longleftrightarrow>
    unary \<alpha> (\<zeta>\<^sub>0 t) = unary \<alpha> (\<gamma> (inputpos m t)) \<and>
    unary \<alpha> (\<zeta>\<^sub>1 t) = 0 \<and>
    unary \<alpha> (\<zeta>\<^sub>2 t) = fst ((M ! (unary \<alpha> (\<zeta>\<^sub>2 (t - 1)))) [unary \<alpha> (\<zeta>\<^sub>0 (t - 1)), unary \<alpha> (\<zeta>\<^sub>1 (t - 1))])"
proof -
  let ?sigma = "\<rho>' t"
  have "\<alpha> \<Turnstile> \<chi> t = \<alpha> \<Turnstile> relabel ?sigma \<psi>'"
    using assms(1) chi_def by simp
  then have "\<alpha> \<Turnstile> \<chi> t = F' (remap ?sigma \<alpha>)"
      (is "_ = F' ?alpha")
    by (simp add: length_rho' satisfies_F')
  then have *: "\<alpha> \<Turnstile> \<chi> t =
     (unary ?alpha w\<^sub>3 = unary ?alpha w\<^sub>6 \<and>
      unary ?alpha w\<^sub>4 = 0 \<and>
      unary ?alpha w\<^sub>5 = fst ((M ! (unary ?alpha w\<^sub>2)) [unary ?alpha w\<^sub>0, unary ?alpha w\<^sub>1]))"
    using F'_def by simp

  have w_less_len_rho':
    "\<forall>s\<in>set w\<^sub>0. s < length (\<rho>' t)"
    "\<forall>s\<in>set w\<^sub>1. s < length (\<rho>' t)"
    "\<forall>s\<in>set w\<^sub>2. s < length (\<rho>' t)"
    "\<forall>s\<in>set w\<^sub>3. s < length (\<rho>' t)"
    "\<forall>s\<in>set w\<^sub>4. s < length (\<rho>' t)"
    "\<forall>s\<in>set w\<^sub>5. s < length (\<rho>' t)"
    "\<forall>s\<in>set w\<^sub>6. s < length (\<rho>' t)"
    using length_rho' Z_def by simp_all

  have **: "\<alpha> \<Turnstile> \<chi> t =
     (unary \<alpha> (reseq ?sigma w\<^sub>3) = unary \<alpha> (reseq ?sigma w\<^sub>6) \<and>
      unary \<alpha> (reseq ?sigma w\<^sub>4) = 0 \<and>
      unary \<alpha> (reseq ?sigma w\<^sub>5) = fst ((M ! (unary \<alpha> (reseq ?sigma w\<^sub>2))) [unary \<alpha> (reseq ?sigma w\<^sub>0), unary \<alpha> (reseq ?sigma w\<^sub>1)]))"
    using * w_less_len_rho' unary_remap[where ?\<sigma>="?sigma" and ?\<alpha>=\<alpha>]
    by presburger

  have 1: "reseq ?sigma w\<^sub>0 = \<zeta>\<^sub>0 (t - 1)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta0_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = [] @ \<zeta>\<^sub>0 (t - 1) @ (\<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t))"
        using rho'_def by simp
      have "?sigma ! i = \<zeta>\<^sub>0 (t - 1) ! i"
        using nth_append3[OF 1, of i 0] Z_def that by simp
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 2: "reseq ?sigma w\<^sub>1 = \<zeta>\<^sub>1 (t - 1)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta1_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = \<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho'_def by simp
      have "?sigma ! (H+i) = \<zeta>\<^sub>1 (t - 1) ! i"
        using that zeta0_def zeta1_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 3: "reseq ?sigma w\<^sub>2 = \<zeta>\<^sub>2 (t - 1)" (is "?l = ?r")
  proof (rule nth_equalityI)
    show len: "length ?l = length ?r"
      using zeta2_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1)) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho'_def by simp
      have "?sigma ! (2*H+i) = \<zeta>\<^sub>2 (t - 1) ! i"
        using len that zeta0_def zeta1_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 4: "reseq ?sigma w\<^sub>3 = \<zeta>\<^sub>0 t" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta0_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1)) @
          \<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho'_def by simp
      have "?sigma ! (Z+i) = \<zeta>\<^sub>0 t ! i"
        using that Z_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 5: "reseq ?sigma w\<^sub>4 = \<zeta>\<^sub>1 t" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta1_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 t) @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho'_def by simp
      have "?sigma ! (Z+H+i) = \<zeta>\<^sub>1 t ! i"
        using that Z_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 6: "reseq ?sigma w\<^sub>5 = \<zeta>\<^sub>2 t" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using zeta2_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t) @ \<zeta>\<^sub>2 t @ \<gamma> (inputpos m t)"
        using rho'_def by simp
      have "?sigma ! (Z+2*H+i) = \<zeta>\<^sub>2 t ! i"
        using that zeta0_def zeta1_def zeta2_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  have 7: "reseq ?sigma w\<^sub>6 = (\<gamma> (inputpos m t))" (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using gamma_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have 1: "?sigma = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1) @
          \<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t) @ \<gamma> (inputpos m t) @ []"
        using rho'_def by simp
      have "?sigma ! (2*Z+i) = \<gamma> (inputpos m t) ! i"
        using that Z_def gamma_def by (intro nth_append3[OF 1]) auto
      then show ?thesis
        using reseq_def that by simp
    qed
  qed

  show ?thesis
    using ** 1 2 3 4 5 6 7 by simp
qed


section \<open>The CNF formula $\Phi$\<close>

text \<open>
We can now formulate all the parts $\Phi_0, \dots, \Phi_9$ of the complete
formula $\Phi$, and thus $\Phi$ itself.

Representing the snapshot in step~0:
\<close>

definition PHI0 :: formula ("\<Phi>\<^sub>0") where
  "\<Phi>\<^sub>0 \<equiv> \<Psi> (\<zeta>\<^sub>0 0) 1 @ \<Psi> (\<zeta>\<^sub>1 0) 1 @ \<Psi> (\<zeta>\<^sub>2 0) 0"

text \<open>The start symbol at the beginning of the input tape:\<close>

definition PHI1 :: formula ("\<Phi>\<^sub>1") where
  "\<Phi>\<^sub>1 \<equiv> \<Psi> (\<gamma> 0) 1"

text \<open>The separator \textbf{11} between $x$ and $u$:\<close>

definition PHI2 :: formula ("\<Phi>\<^sub>2") where
  "\<Phi>\<^sub>2 \<equiv> \<Psi> (\<gamma> (2*n+1)) 3 @ \<Psi> (\<gamma> (2*n+2)) 3"

text \<open>The zeros before the symbols of $x$:\<close>

definition PHI3 :: formula ("\<Phi>\<^sub>3") where
  "\<Phi>\<^sub>3 \<equiv> concat (map (\<lambda>i. \<Psi> (\<gamma> (2*i+1)) 2) [0..<n])"

text \<open>The zeros before the symbols of $u$:\<close>

definition PHI4 :: formula ("\<Phi>\<^sub>4") where
  "\<Phi>\<^sub>4 \<equiv> concat (map (\<lambda>i. \<Psi> (\<gamma> (2*n+2+2*i+1)) 2) [0..<p n])"

text \<open>The blank symbols after the input $\langle x, u\rangle$:\<close>

definition PHI5 :: formula ("\<Phi>\<^sub>5") where
  "\<Phi>\<^sub>5 \<equiv> concat (map (\<lambda>i. \<Psi> (\<gamma> (2*n + 2*p n + 3 + i)) 0) [0..<T'])"

text \<open>The symbols of $x$:\<close>

definition PHI6 :: formula ("\<Phi>\<^sub>6") where
  "\<Phi>\<^sub>6 \<equiv> concat (map (\<lambda>i. \<Psi> (\<gamma> (2*i+2)) (if x ! i then 3 else 2)) [0..<n])"

text \<open>Constraining the symbols of $u$ to be from $\{\mathbf{0}, \mathbf{1}\}$:\<close>

definition PHI7 :: formula ("\<Phi>\<^sub>7") where
  "\<Phi>\<^sub>7 \<equiv> concat (map (\<lambda>i. \<Upsilon> (\<gamma> (2*n+4+2*i))) [0..<p n])"

text \<open>Reading a \textbf{1} in the final step to signal acceptance of $\langle x, u\rangle$:\<close>

definition PHI8 :: formula ("\<Phi>\<^sub>8") where
  "\<Phi>\<^sub>8 \<equiv> \<Psi> (\<zeta>\<^sub>1 T') 3"

text \<open>The snapshots after the first and before the last:\<close>

definition PHI9 :: formula ("\<Phi>\<^sub>9") where
  "\<Phi>\<^sub>9 \<equiv> concat (map (\<lambda>t. \<chi> (Suc t)) [0..<T'])"

text \<open>The complete formula:\<close>

definition PHI :: formula ("\<Phi>") where
  "\<Phi> \<equiv> \<Phi>\<^sub>0 @ \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 @ \<Phi>\<^sub>3 @ \<Phi>\<^sub>4 @ \<Phi>\<^sub>5 @ \<Phi>\<^sub>6 @ \<Phi>\<^sub>7 @ \<Phi>\<^sub>8 @ \<Phi>\<^sub>9"


section \<open>Correctness of the formula\<close>

text \<open>
We have to show that the formula $\Phi$ is satisfiable if and only if $x \in L$.
There is a subsection for both of the implications. Instead of $x \in L$ we will
use the right-hand side of the following equivalence.
\<close>

lemma L_iff_ex_u: "x \<in> L \<longleftrightarrow>  (\<exists>u. length u = p n \<and> exc \<langle>x; u\<rangle> T' <.> 1 = \<one>)"
proof -
  have "x \<in> L \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> exc \<langle>x; u\<rangle> (T (length \<langle>x; u\<rangle>)) <.> 1 = \<one>)"
    using cert by simp
  also have "... \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> exc \<langle>x; u\<rangle> (TT (length \<langle>x; u\<rangle>)) <.> 1 = \<one>)"
  proof -
    have "bit_symbols \<langle>x; u\<rangle>" for u
      by simp
    then have "exc \<langle>x; u\<rangle> (TT (length \<langle>x; u\<rangle>)) = exc \<langle>x; u\<rangle> (T (length \<langle>x; u\<rangle>))" for u
      using exc_TT_eq_exc_T by blast
    then show ?thesis
      by simp
  qed
  also have "... \<longleftrightarrow>  (\<exists>u. length u = p n \<and> exc \<langle>x; u\<rangle> T' <.> 1 = \<one>)"
    using T'_def length_pair m_def by auto
  finally show ?thesis .
qed


subsection \<open>$\Phi$ satisfiable implies $x\in L$\<close>

text \<open>
The proof starts from an assignment $\alpha$ satisfying $\Phi$ and shows that
there is a string $u$ of length $p(n)$ such that $M$, on input $\langle x,
u\rangle$, halts with the output tape head on the symbol \textbf{1}. The overarching
idea is that $\alpha$, by satisfying $\Phi$, encodes a string $u$ and a
computation of $M$ on $u$ that results in $M$ halting with the output tape head on
the symbol~\textbf{1}.

The assignment $\alpha$ is an infinite bit string, whose first $N = m'\cdot H$
bits are supposed to encode the first $m'$ symbols on $M$'s input tape, which
contains the pair $\langle x, u\rangle$. The first step of the proof is thus to
extract a $u$ of length $p(n)$ from the first $N$ bits of $\alpha$.  The Formula
$\Phi_7$ ensures that the symbols representing $u$ are \textbf{0} or \textbf{1}
and thus represent a bit string.

Next the proof shows that the first $N$ bits of $\alpha$ encode the relevant
portion $y(u)$ of the input tape for the $u$ just extracted, that is, $y(u)_i =
\alpha(\gamma_i)$ for $i < m'$. The proof exploits the constraints set by
$\Phi_1$ to $\Phi_6$. In particular this implies that $y(u)_{\inputpos(t)} =
\alpha(\gamma_{\inputpos(t)})$ for all $t$.

The next $Z\cdot (T' + 1)$ bits of $\alpha$ encode $T' + 1$ snapshots.  More
precisely, we prove $z_0(u, t) = \alpha(\zeta_0^t)$ and $z_1(u, t) =
\alpha(\zeta_1^t)$ and $z_2(u, t) = \alpha(\zeta_2^t)$ for all $t \leq T'$. This
works by induction on $t$. The case $t = 0$ is covered by the formula $\Phi_0$.
For $0 < t \leq T'$ the formulas $\chi_t$ are responsible, which make up
$\Phi_9$. Basically $\chi_t$ represents the recursive characterization of the
snapshot $z_t$ in terms of earlier snapshots (of $t-1$ and possibly $prev(t)$).
This is the trickiest part and we need some preliminary lemmas for that.

Once that is done, we know that some bits of $\alpha$, namely
$\alpha(\zeta_1(T'))$, encode the symbol under the output tape head after $T'$ steps,
that is, when $M$ has halted. Formula $\Phi_8$ ensures that this symbol is
\textbf{1}, which concludes the proof.

\null
\<close>

lemma sat_PHI_imp_ex_u:
  assumes "satisfiable \<Phi>"
  shows "\<exists>u. length u = p n \<and> exc \<langle>x; u\<rangle> T' <.> 1 = \<one>"
proof -
  obtain \<alpha> where \<alpha>: "\<alpha> \<Turnstile> \<Phi>"
    using assms satisfiable_def by auto

  define us where "us = map (\<lambda>i. unary \<alpha> (\<gamma> (2*n+4+2*i))) [0..<p n]"

  have len_us: "length us = p n"
    using us_def by simp

  have us23: "us ! i = 2 \<or> us ! i = 3" if "i < p n" for i
  proof -
    have "\<alpha> \<Turnstile> \<Phi>\<^sub>7"
      using PHI_def satisfies_def \<alpha> by simp
    then have "\<alpha> \<Turnstile> \<Upsilon> (\<gamma> (2*n+4+2*i))"
      using that PHI7_def satisfies_concat_map by auto
    then have "unary \<alpha> (\<gamma> (2*n+4+2*i)) = 2 \<or> unary \<alpha> (\<gamma> (2*n+4+2*i)) = 3"
      using Upsilon_unary length_gamma H_gr_2 by simp
    then show ?thesis
      using us_def that by simp
  qed

  define u :: string where "u = symbols_to_string us"

  have len_u: "length u = p n"
    using u_def len_us by simp

  have "ysymbols u ! i = unary \<alpha> (\<gamma> i)" if "i < m'" for i
  proof -
    consider
        "i = 0"
      | "1 \<le> i \<and> i < 2 * n + 1"
      | "2 * n + 1 \<le> i \<and> i < 2 * n + 3"
      | "2 * n + 3 \<le> i \<and> i < m + 1"
      | "i \<ge> m + 1 \<and> i < m + 1 + T'"
      using `i < m'` m'_def m_def by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "\<alpha> \<Turnstile> \<Psi> (\<gamma> i) 1"
        using PHI_def PHI1_def \<alpha> satisfies_append by metis
      then have "unary \<alpha> (\<gamma> i) = 1"
        using Psi_unary H_gr_2 gamma_def by simp
      moreover have "ysymbols u ! i = 1"
        using 1 by (simp add: ysymbols_def)
      ultimately show ?thesis
        by simp
    next
      case 2
      define j where "j = (i - 1) div 2"
      then have "j < n"
        using 2 by auto
      have "i = 2 * j + 1 \<or> i = 2 * j + 2"
        using 2 j_def by auto
      then show ?thesis
      proof
        assume i: "i = 2 * j + 1"
        have "\<alpha> \<Turnstile> \<Phi>\<^sub>3"
          using PHI_def satisfies_def \<alpha> by simp
        then have "\<alpha> \<Turnstile> \<Psi> (\<gamma> (2*j+1)) 2"
          using PHI3_def satisfies_concat_map[OF _ `j < n`] by auto
        then have "unary \<alpha> (\<gamma> (2*j+1)) = 2"
          using Psi_unary H_gr_2 gamma_def by simp
        moreover have "ysymbols u ! (2*j+1) = 2"
          using ysymbols_first_at[OF `j < n`] by simp
        ultimately show ?thesis
          using i by simp
      next
        assume i: "i = 2 * j + 2"
        have "\<alpha> \<Turnstile> \<Phi>\<^sub>6"
          using PHI_def satisfies_def \<alpha> by simp
        then have "\<alpha> \<Turnstile> \<Psi> (\<gamma> (2*j+2)) (if x ! j then 3 else 2)"
          using PHI6_def satisfies_concat_map[OF _ `j < n`] by fastforce
        then have "unary \<alpha> (\<gamma> (2*j+2)) = (if x ! j then 3 else 2)"
          using Psi_unary H_gr_2 gamma_def by simp
        moreover have "ysymbols u ! (2*j+2) = (if x ! j then 3 else 2)"
          using ysymbols_first_at[OF `j < n`] by simp
        ultimately show ?thesis
          using i by simp
      qed
    next
      case 3
      then have "i = 2*n + 1 \<or> i = 2*n + 2"
        by auto
      then show ?thesis
      proof
        assume i: "i = 2 * n + 1"
        then have "\<alpha> \<Turnstile> \<Psi> (\<gamma> i) 3"
          using PHI_def PHI2_def \<alpha> satisfies_append by metis
        then have "unary \<alpha> (\<gamma> i) = 3"
          using Psi_unary H_gr_2 gamma_def by simp
        moreover have "ysymbols u ! i = 3"
          using i ysymbols_at_2n1 by simp
        ultimately show ?thesis
          by simp
      next
        assume i: "i = 2 * n + 2"
        then have "\<alpha> \<Turnstile> \<Psi> (\<gamma> i) 3"
          using PHI_def PHI2_def \<alpha> satisfies_append by metis
        then have "unary \<alpha> (\<gamma> i) = 3"
          using Psi_unary H_gr_2 gamma_def by simp
        moreover have "ysymbols u ! i = 3"
          using i ysymbols_at_2n2 by simp
        ultimately show ?thesis
          by simp
      qed
    next
      case 4
      moreover define j where "j = (i - 2*n-3) div 2"
      ultimately have j: "j < p n"
        using m_def by auto
      have "i = 2*n+2+2 * j + 1 \<or> i = 2*n+2+2 * j + 2"
        using 4 j_def by auto
      then show ?thesis
      proof
        assume i: "i = 2 * n + 2 + 2 * j + 1"
        have "\<alpha> \<Turnstile> \<Phi>\<^sub>4"
          using PHI_def satisfies_def \<alpha> by simp
        then have "\<alpha> \<Turnstile> \<Psi> (\<gamma> (2*n+2+2*j+1)) 2"
          using PHI4_def satisfies_concat_map[OF _ `j < p n`] by auto
        then have "unary \<alpha> (\<gamma> (2*n+2+2*j+1)) = 2"
          using Psi_unary H_gr_2 gamma_def by simp
        moreover have "ysymbols u ! (2*n+2+2*j+1) = 2"
          using \<open>j < p n\<close> ysymbols_second_at(1) len_u by presburger
        ultimately show ?thesis
          using i by simp
      next
        assume i: "i = 2 * n + 2 + 2 * j + 2"
        have "us ! j = unary \<alpha> (\<gamma> (2*n+4+2*j))"
          using us_def `j < p n` by simp
        then have "us ! j = unary \<alpha> (\<gamma> (2*n+2+2*j+2))"
          by (simp add: numeral_Bit0)
        then have "unary \<alpha> (\<gamma> (2*n+2+2*j+2)) = (if u ! j then 3 else 2)"
          using u_def us23 \<open>j < p local.n\<close> len_us by fastforce
        then have *: "unary \<alpha> (\<gamma> i) = (if u ! j then 3 else 2)"
          using i by simp
        have "ysymbols u ! (2*n+2+2*j+2) = (if u ! j then 3 else 2)"
          using ysymbols_second_at(2) `j < p n` len_u by simp
        then have "ysymbols u ! i = (if u ! j then 3 else 2)"
          using i by simp
        then show ?thesis
          using * i by simp
      qed
    next
      case 5
      then have "\<alpha> \<Turnstile> \<Phi>\<^sub>5"
        using PHI_def satisfies_def \<alpha> by simp
      then have "\<alpha> \<Turnstile> \<Psi> (\<gamma> (2*n+2*p n + 3 + i')) 0" if "i' < T'" for i'
        unfolding PHI5_def using \<alpha> satisfies_concat_map[OF _ that, of \<alpha>] that by auto
      moreover obtain i' where i': "i' < T'" "i = m + 1 + i'"
        using 5 by (metis add_less_cancel_left le_Suc_ex)
      ultimately have "\<alpha> \<Turnstile> \<Psi> (\<gamma> i) 0"
        using m_def numeral_3_eq_3 by simp
      then have "unary \<alpha> (\<gamma> i) = 0"
        using Psi_unary H_gr_2 gamma_def by simp
      moreover have "ysymbols u ! i = 0"
        using 5 ysymbols_last len_u by simp
      ultimately show ?thesis
        by simp
    qed
  qed
  then have ysymbols: "ysymbols u ! (inputpos m t) = unary \<alpha> (\<gamma> (inputpos m t))" for t
    using inputpos_less' len_u by simp

  have "z0 u t = unary \<alpha> (\<zeta>\<^sub>0 t) \<and> z1 u t = unary \<alpha> (\<zeta>\<^sub>1 t) \<and> z2 u t = unary \<alpha> (\<zeta>\<^sub>2 t)"
      if "t \<le> T'" for t
    using that
  proof (induction t rule: nat_less_induct)
    case (1 t)
    show ?case
    proof (cases "t = 0")
      case True
      have "\<alpha> \<Turnstile> \<Phi>\<^sub>0"
        using \<alpha> PHI_def satisfies_def by simp
      then have
        1: "\<alpha> \<Turnstile> \<Psi> (\<zeta>\<^sub>0 0) 1" and
        2: "\<alpha> \<Turnstile> \<Psi> (\<zeta>\<^sub>1 0) 1" and
        3: "\<alpha> \<Turnstile> \<Psi> (\<zeta>\<^sub>2 0) 0"
        using PHI0_def by (metis satisfies_append(1), metis satisfies_append, metis satisfies_append(2))
      have "unary \<alpha> (\<zeta>\<^sub>0 0) = 1"
        using Psi_unary[OF _ 1] H_gr_2 by simp
      moreover have "unary \<alpha> (\<zeta>\<^sub>1 0) = 1"
        using Psi_unary[OF _ 2] H_gr_2 by simp
      moreover have "unary \<alpha> (\<zeta>\<^sub>2 0) = 0"
        using Psi_unary[OF _ 3] by simp
      moreover have "z0 u 0 = \<triangleright>"
        using z0_def start_config2 by (simp add: start_config_pos)
      moreover have "z1 u 0 = \<triangleright>"
        using z1_def by (simp add: start_config2 start_config_pos)
      moreover have "z2 u 0 = \<box>"
        using z2_def by (simp add: start_config_def)
      ultimately show ?thesis
        using True by simp
    next
      case False
      then have "t > 0"
        by simp
      let ?t = "t - 1"
      have sat_chi: "\<alpha> \<Turnstile> \<chi> t"
      proof -
        have "\<alpha> \<Turnstile> \<Phi>\<^sub>9"
          using \<alpha> PHI_def satisfies_def by simp
        moreover have "?t < T'"
          using 1 `t > 0` by simp
        ultimately have "\<alpha> \<Turnstile> \<chi> (Suc ?t)"
          using satisfies_concat_map PHI9_def by auto
        then show ?thesis
          using \<open>t > 0\<close> by simp
      qed
      show ?thesis
      proof (cases "prev m t < t")
        case True
        then show ?thesis
          using satisfies_chi_less z0 z1 z2' 1 len_u ysymbols sat_chi True `t \<le> T'` len_u by simp
      next
        case False
        then have eq: "prev m t = t"
          using prev_eq prev_less by blast
        show ?thesis
          using satisfies_chi_eq z0 z1' z2' ysymbols sat_chi eq `t > 0` `t \<le> T'` len_u 1 `t > 0` by simp
      qed
    qed
  qed
  then have "z1 u T' = unary \<alpha> (\<zeta>\<^sub>1 T')"
    by simp
  moreover have "unary \<alpha> (\<zeta>\<^sub>1 T') = 3"
  proof -
    have "\<alpha> \<Turnstile> \<Phi>\<^sub>8"
      using \<alpha> PHI_def satisfies_def by simp
    then have "\<alpha> \<Turnstile> \<Psi> (\<zeta>\<^sub>1 T') 3"
      using PHI8_def by simp
    then show ?thesis
      using Psi_unary[of 3 "\<zeta>\<^sub>1 T'"] length_zeta1 H_gr_2 by simp
  qed
  ultimately have "z1 u T' = \<one>"
    by simp
  then have "exc \<langle>x; u\<rangle> T' <.> 1 = \<one>"
    using z1_def by simp
  then show ?thesis
    using len_u by auto
qed


subsection \<open>$x\in L$ implies $\Phi$ satisfiable\<close>

text \<open>
For the other direction, we assume a string $x \in L$ and show that the formula
$\Phi$ derived from it is satisfiable. From $x \in L$ it follows that there is a
certificate $u$ of length $p(n)$ such that $M$ on input $\langle x, u\rangle$
halts after $T'$ steps with the output tape head on the symbol~\textbf{1}.

An assignment that satisfies $\Phi$ must have its first $N = m' \cdot H$ bits
set in such a way that they encode the relevant portion $y(u)$ of the input
tape, that is, with $\langle x, u\rangle$ followed by $T'$ blanks.  This will
take care of satisfying $\Phi_1, \dots, \Phi_7$.  The next $Z\cdot (T' + 1)$
bits of $\alpha$ must be set such that they encode the $T' + 1$ snapshots of $M$
when started on $\langle x, u\rangle$. This way $\Phi_0$ and $\Phi_9$ will be
satisfied.  Finally, $\Phi_8$ is satisfied because by the choice of $u$ the last
snapshot contains a \textbf{1} as the symbol under the output tape head.

The following function maps a string $u$ to an assignment as just described.
\<close>

definition beta :: "string \<Rightarrow> assignment" ("\<beta>") where
  "\<beta> u i \<equiv>
    if i < N then
      let
        j = i div H;
        k = i mod H
      in
        if j = 0 then k < 1
        else if j = 2 * n + 1 \<or> j = 2 * n + 2 then k < 3
        else if j \<ge> 2 * n + 2 * p n + 3 then k < 0
        else if odd j then k < 2
        else if j \<le> 2 * n then k < (if x ! (j div 2 - 1) then 3 else 2)
        else k < (if u ! (j div 2 - n - 2) then 3 else 2)
    else if i < N + Z * (Suc T') then
      let t = (i - N) div Z; k = (i - N) mod Z in
        if k < H then k < z0 u t
        else if k < 2 * H then k - H < z1 u t
        else k - 2 * H < z2 u t
    else False"

text \<open>
In order to show that $\beta(u)$ satisfies $\Phi$, we show that it satisfies all
parts of $\Phi$. These parts consist mostly of $\Psi$ formulas, whose
satisfiability can be proved using lemma~@{thm [source] satisfies_Psi}. To apply
this lemma, the following ones will be helpful.
\<close>

lemma blocky_gammaI:
  assumes "\<And>k. k < H \<Longrightarrow> \<alpha> (j * H + k) = (k < l)"
  shows "blocky \<alpha> (\<gamma> j) l"
  unfolding blocky_def gamma_def using assms by simp

lemma blocky_zeta0I:
  assumes "\<And>k. k < H \<Longrightarrow> \<alpha> (N + t * Z + k) = (k < l)"
  shows "blocky \<alpha> (\<zeta>\<^sub>0 t) l"
  unfolding blocky_def zeta0_def using assms by simp

lemma blocky_zeta1I:
  assumes "\<And>k. k < H \<Longrightarrow> \<alpha> (N + t * Z + H + k) = (k < l)"
  shows "blocky \<alpha> (\<zeta>\<^sub>1 t) l"
  unfolding blocky_def zeta1_def using assms by simp

lemma blocky_zeta2I:
  assumes "\<And>k. k < H \<Longrightarrow> \<alpha> (N + t * Z + 2 * H + k) = (k < l)"
  shows "blocky \<alpha> (\<zeta>\<^sub>2 t) l"
  unfolding blocky_def zeta2_def using Z_def assms by simp

lemma beta_1: "blocky (\<beta> u) (\<gamma> 0) 1"
proof (intro blocky_gammaI)
  fix k :: nat
  assume k: "k < H"
  let ?i = "0 * H + k"
  have "?i < N"
    using N_eq add_mult_distrib2 k by auto
  then show "\<beta> u ?i = (k < 1)"
    using beta_def k by simp
qed

lemma beta_2a: "blocky (\<beta> u) (\<gamma> (2*n+1)) 3"
proof (intro blocky_gammaI)
  fix k :: nat
  assume k: "k < H"
  let ?i = "(2*n+1) * H + k"
  let ?j = "?i div H"
  let ?k = "?i mod H"
  have "?i < N"
    using N_eq add_mult_distrib2 k by auto
  moreover have j: "?j = 2 * n + 1"
    using k by (metis add_cancel_left_right div_less div_mult_self3 less_nat_zero_code)
  moreover have "?k = k"
    using k by (metis mod_if mod_mult_self3)
  moreover have "\<not> ?j = 0"
    using j by linarith
  ultimately show "\<beta> u ?i = (k < 3)"
    using beta_def by simp
qed

lemma beta_2b: "blocky (\<beta> u) (\<gamma> (2*n+2)) 3"
proof (intro blocky_gammaI)
  fix k :: nat
  assume k: "k < H"
  let ?i = "(2*n+2) * H + k"
  let ?j = "?i div H"
  let ?k = "?i mod H"
  have "?i < N"
    using N_eq add_mult_distrib2 k by auto
  moreover have "?j = 2 * n + 2"
    using k by (metis add_cancel_left_right div_less div_mult_self3 less_nat_zero_code)
  moreover have "?k = k"
    using k by (metis mod_if mod_mult_self3)
  moreover have "\<not> ?j = 0"
    using calculation(2) by linarith
  ultimately show "\<beta> u ?i = (k < 3)"
    using beta_def Let_def k by presburger
qed

lemma beta_3:
  assumes "ii < n"
  shows "blocky (\<beta> u) (\<gamma> (2 * ii + 1)) 2"
proof (intro blocky_gammaI)
  fix k ::nat
  assume k: "k < H"
  let ?i = "(2*ii+1) * H + k"
  let ?j = "?i div H"
  let ?k = "?i mod H"
  have "?i < N"
  proof -
    have "?i < (2*n+1) * H + k"
      using assms k by simp
    also have "... < (2*n+1) * H + H"
      using k by simp
    also have "... = H * (2*n+2)"
      by simp
    also have "... \<le> H * (2*n+3)"
      by (metis add.commute add.left_commute add_2_eq_Suc le_add2 mult_le_mono2 numeral_3_eq_3)
    also have "... \<le> H * (2*n+2*p n+3)"
      by simp
    also have "... \<le> H * (2*n+2*p n+3 + T')"
      by simp
    finally have "?i < H * (2*n+2*p n+3 + T')" .
    then show ?thesis
      using N_eq by simp
  qed
  moreover have j: "?j = 2 * ii + 1"
    using k by (metis add_cancel_left_right div_less div_mult_self3 less_nat_zero_code)
  moreover have "?k = k"
    using k by (metis mod_if mod_mult_self3)
  moreover have "\<not> ?j = 0"
    using j by linarith
  moreover have "\<not> (?j = 2*n+1 \<or> ?j = 2*n+2)"
    using j assms by simp
  moreover have "\<not> ?j \<ge> 2*n+2*p n + 3"
    using j assms by simp
  moreover have "odd ?j"
    using j by simp
  ultimately show "\<beta> u ?i = (k < 2)"
    using beta_def by simp
qed

lemma beta_4:
  assumes "ii < p n" and "length u = p n"
  shows "blocky (\<beta> u) (\<gamma> (2*n+2+2*ii+1)) 2"
proof (intro blocky_gammaI)
  fix k :: nat
  assume k: "k < H"
  let ?i = "(2*n+2+2*ii+1) * H + k"
  let ?j = "?i div H"
  let ?k = "?i mod H"
  have "?i < N"
  proof -
    have "?i = (2*n+2*ii+3) * H + k"
      by (simp add: numeral_3_eq_3)
    also have "... < (2*n+2*ii+3) * H + H"
      using k by simp
    also have "... = H * (2*n+2*ii+4)"
      by algebra
    also have "... \<le> H * (2*n+2*p n+3)"
      using assms(1) by simp
    also have "... \<le> H * (2*n+2*p n+3 + T')"
      by simp
    finally have "?i < H * (2*n+2*p n+3 + T')" .
    then show ?thesis
      using N_eq by simp
  qed
  moreover have j: "?j = 2 * n + 2 + 2 * ii + 1"
    using k by (metis add_cancel_left_right div_less div_mult_self3 less_nat_zero_code)
  moreover have "?k = k"
    using k by (metis mod_if mod_mult_self3)
  moreover have "\<not> ?j = 0"
    using j by linarith
  moreover have "\<not> (?j = 2*n+1 \<or> ?j = 2*n+2)"
    using j assms by simp
  moreover have "\<not> ?j \<ge> 2*n+2*p n + 3"
    using j assms by simp
  moreover have "odd ?j"
    using j by simp
  ultimately show "\<beta> u ?i = (k < 2)"
    using beta_def by simp
qed

lemma beta_5:
  assumes "ii < T'"
  shows "blocky (\<beta> u) (\<gamma> (2*n+2*p n + 3 + ii)) 0"
proof (intro blocky_gammaI)
  fix k :: nat
  assume k: "k < H"
  let ?i = "(2*n+2*p n + 3 + ii) * H + k"
  let ?j = "?i div H"
  let ?k = "?i mod H"
  have "?i < N"
  proof -
    have "?i < (2*n+2*p n + 3 + ii) * H + H"
      using k by simp
    also have "... \<le> (2*n+2*p n + 3 + T' - 1) * H + H"
    proof -
      have "2*n+2*p n + 3 + ii \<le> 2*n+2*p n + 3 + T' - 1"
        using assms by simp
      then show ?thesis
        using add_le_mono1 mult_le_mono1 by presburger
    qed
    also have "... \<le> (2*n+2*p n + 2 + T') * H + H"
      by simp
    also have "... \<le> H * (2*n+2*p n + 3 + T')"
      by (simp add: numeral_3_eq_3)
    finally have "?i < H * (2*n+2*p n + 3 + T')" .
    then show ?thesis
      using N_eq by simp
  qed
  moreover have j: "?j = 2 * n + 2*p n + 3 + ii"
    using k by (metis add_cancel_left_right div_less div_mult_self3 less_nat_zero_code)
  moreover have "?k = k"
    using k by (metis mod_if mod_mult_self3)
  moreover have "\<not> ?j = 0"
    using j by linarith
  moreover have "\<not> (?j = 2*n+1 \<or> ?j = 2*n+2)"
    using j by simp
  ultimately show "\<beta> u ?i = (k < 0)"
    using beta_def Let_def k by simp
qed

lemma beta_6:
  assumes "ii < n"
  shows "blocky (\<beta> u) (\<gamma> (2 * ii + 2)) (if x ! ii then 3 else 2)"
proof (intro blocky_gammaI)
  fix k :: nat
  assume k: "k < H"
  let ?i = "(2*ii+2) * H + k"
  let ?j = "?i div H"
  let ?k = "?i mod H"
  have "?i < N"
  proof -
    have "?i \<le> (2*n+2) * H + k"
      using assms by simp
    also have "... < (2*n+2) * H + H"
      using k by simp
    also have "... = (2*n+3) * H"
      by algebra
    also have "... \<le> (2*n + 2*p n + 3) * H"
      by simp
    also have "... \<le> (2*n + 2*p n + 3 + T') * H"
      by simp
    finally have "?i < (2*n + 2*p n + 3 + T') * H" .
    then show ?thesis
      using N_eq by (metis mult.commute)
  qed
  moreover have j: "?j = 2 * ii + 2"
    using k by (metis add_cancel_left_right div_less div_mult_self3 less_nat_zero_code)
  moreover have "?k = k"
    using k by (metis mod_if mod_mult_self3)
  moreover have "\<not> ?j = 0"
    using j by linarith
  moreover have "\<not> (?j = 2*n+1 \<or> ?j = 2*n+2)"
    using j assms by simp
  moreover have "\<not> ?j = 2*n+2*p n + 3"
    using j assms by simp
  moreover have "\<not> odd ?j"
    using j by simp
  moreover have "?j \<le> 2 * n"
    using j assms by simp
  ultimately show "\<beta> u ?i = (k < (if x ! ii then 3 else 2))"
    using beta_def by simp
qed

lemma beta_7:
  assumes "ii < p n" and "length u = p n"
  shows "blocky (\<beta> u) (\<gamma> (2 * n + 4 + 2 * ii)) (if u ! ii then 3 else 2)"
proof (intro blocky_gammaI)
  fix k :: nat
  assume k: "k < H"
  let ?i = "(2*n+4+2*ii) * H + k"
  let ?j = "?i div H"
  let ?k = "?i mod H"
  have "?i < N"
  proof -
    have 1: "ii \<le> p n - 1"
      using assms(1) by simp
    have 2: "p n > 0"
      using assms(1) by simp
    have "?i \<le> (2*n+4+2*(p n - 1)) * H + k"
      using 1 by simp
    also have "... = (2*n+4+2*p n-2) * H + k"
      using 2 diff_mult_distrib2 by auto
    also have "... = (2*n+2+2*p n) * H + k"
      by simp
    also have "... < (2*n+2+2*p n) * H + H"
      using k by simp
    also have "... = (2*n+3+2*p n) * H"
      by algebra
    also have "... = H * (2*n + 2*p n + 3)"
      by simp
    also have "... \<le> H * (2*n + 2*p n + 3 + T')"
      by simp
    finally have "?i < H * (2*n + 2*p n + 3 + T')" .
    then show ?thesis
      using N_eq by simp
  qed
  moreover have j: "?j = 2 * n + 4 + 2 * ii"
    using k by (metis add_cancel_left_right div_less div_mult_self3 less_nat_zero_code)
  moreover have "?k = k"
    using k by (metis mod_if mod_mult_self3)
  moreover have "\<not> ?j = 0"
    using j by linarith
  moreover have "\<not> (?j = 2*n+1 \<or> ?j = 2*n+2)"
    using j assms by simp
  moreover have "\<not> odd ?j"
    using j by simp
  moreover have "\<not> ?j \<le> 2 * n"
    using j assms by simp
  moreover have "?j \<le> 2 * n + 2 * p n + 2"
    using j assms by simp
  ultimately show "\<beta> u ?i = (k < (if u ! ii then 3 else 2))"
    using beta_def by simp
qed

lemma beta_zeta0:
  assumes "t \<le> T'"
  shows "blocky (\<beta> u) (\<zeta>\<^sub>0 t) (z0 u t)"
proof (intro blocky_zeta0I)
  fix k ::nat
  assume k: "k < H"
  let ?i = "N + t * Z + k"
  let ?t = "(?i - N) div Z"
  let ?k = "(?i - N) mod Z"
  have "\<not> ?i < N"
    by simp
  moreover have "?i < N + Z * (Suc T')"
  proof -
    have "?i \<le> N + T' * Z + k"
      using assms by simp
    also have "... < N + T' * Z + H"
      using k by simp
    also have "... \<le> N + T' * Z + Z"
      using Z_def by simp
    also have "... = N + Z * (Suc T')"
      by simp
    finally show ?thesis
      by simp
  qed
  moreover have kk: "?k = k"
    using k Z_def by simp
  moreover have "?t = t"
    using k Z_def by simp
  moreover have "?k < H"
    using kk k by simp
  ultimately show "\<beta> u ?i = (k < z0 u t)"
    using beta_def by simp
qed

lemma beta_zeta1:
  assumes "t \<le> T'"
  shows "blocky (\<beta> u) (\<zeta>\<^sub>1 t) (z1 u t)"
proof (intro blocky_zeta1I)
  fix k :: nat
  assume k: "k < H"
  let ?i = "N + t * Z + H + k"
  let ?t = "(?i - N) div Z"
  let ?k = "(?i - N) mod Z"
  have "\<not> ?i < N"
    by simp
  moreover have "?i < N + Z * (Suc T')"
  proof -
    have "?i \<le> N + T' * Z + H + k"
      using assms by simp
    also have "... < N + T' * Z + H + H"
      using k by simp
    also have "... \<le> N + T' * Z + Z"
      using Z_def by simp
    also have "... = N + Z * (Suc T')"
      by simp
    finally show ?thesis
      by simp
  qed
  moreover have "?t = t"
    using k Z_def by simp
  moreover have kk: "?k = H + k"
    using k Z_def by simp
  moreover have "\<not> ?k < H"
    using kk by simp
  moreover have "?k < 2 * H"
    using kk k by simp
  ultimately have "\<beta> u ?i = (?k - H < z1 u t)"
    using beta_def by simp
  then show "\<beta> u ?i = (k < z1 u t)"
    using kk by simp
qed

lemma beta_zeta2:
  assumes "t \<le> T'"
  shows "blocky (\<beta> u) (\<zeta>\<^sub>2 t) (z2 u t)"
proof (intro blocky_zeta2I)
  fix k :: nat
  assume k: "k < H"
  let ?i = "N + t * Z + 2 * H + k"
  let ?t = "(?i - N) div Z"
  let ?k = "(?i - N) mod Z"
  have 1: "2 * H + k < Z"
    using k Z_def by simp
  have "\<not> ?i < N"
    by simp
  moreover have "?i < N + Z * (Suc T')"
  proof -
    have "?i \<le> N + T' * Z + 2 * H + k"
      using assms by simp
    also have "... < N + T' * Z + 2 * H + H"
      using k by simp
    also have "... \<le> N + T' * Z + Z"
      using Z_def by simp
    also have "... = N + Z * (Suc T')"
      by simp
    finally show ?thesis
      by simp
  qed
  moreover have "?t = t"
    using 1 by simp
  moreover have kk: "?k = 2 * H + k"
    using k Z_def by simp
  moreover have "\<not> ?k < H"
    using kk by simp
  moreover have "\<not> ?k < 2 * H"
    using kk by simp
  ultimately have "\<beta> u ?i = (?k - 2 * H < z2 u t)"
    using beta_def by simp
  then show "\<beta> u ?i = (k < z2 u t)"
    using kk by simp
qed

text \<open>
We can finally show that $\beta(u)$ satisfies $\Phi$ if $u$ is a certificate for
$x$.
\<close>

lemma satisfies_beta_PHI:
  assumes "length u = p n" and "exc \<langle>x; u\<rangle> T' <.> 1 = \<one>"
  shows "\<beta> u \<Turnstile> \<Phi>"
proof -
  have "\<beta> u \<Turnstile> \<Phi>\<^sub>0"
  proof -
    have "blocky (\<beta> u) (\<zeta>\<^sub>0 0) (z0 u 0)"
      using beta_zeta0 by simp
    then have "blocky (\<beta> u) (\<zeta>\<^sub>0 0) 1"
      using z0_def start_config2 start_config_pos by auto
    then have "\<beta> u \<Turnstile> \<Psi> (\<zeta>\<^sub>0 0) 1"
      using satisfies_Psi H_gr_2 by simp
    moreover have "\<beta> u \<Turnstile> \<Psi> (\<zeta>\<^sub>1 0) 1"
    proof -
      have "blocky (\<beta> u) (\<zeta>\<^sub>1 0) (z1 u 0)"
        using beta_zeta1 by simp
      then have "blocky (\<beta> u) (\<zeta>\<^sub>1 0) 1"
        using z1_def start_config2 start_config_pos by simp
      then show ?thesis
        using satisfies_Psi H_gr_2 by simp
    qed
    moreover have "\<beta> u \<Turnstile> \<Psi> (\<zeta>\<^sub>2 0) 0"
    proof -
      have "blocky (\<beta> u) (\<zeta>\<^sub>2 0) (z2 u 0)"
        using beta_zeta2 by simp
      then have "blocky (\<beta> u) (\<zeta>\<^sub>2 0) 0"
        using z2_def start_config_def by simp
      then show ?thesis
        using satisfies_Psi H_gr_2 by simp
    qed
    ultimately show ?thesis
      using PHI0_def satisfies_def by auto
  qed
  moreover have "\<beta> u \<Turnstile> \<Phi>\<^sub>1"
    using PHI1_def H_gr_2 satisfies_Psi beta_1 by simp
  moreover have "\<beta> u \<Turnstile> \<Phi>\<^sub>2"
  proof -
    have "\<beta> u \<Turnstile> \<Psi> (\<gamma> (2*n+1)) 3"
      using satisfies_Psi H_gr_2 beta_2a by simp
    moreover have "\<beta> u \<Turnstile> \<Psi> (\<gamma> (2*n+2)) 3"
      using satisfies_Psi H_gr_2 beta_2b by simp
    ultimately show ?thesis
      using PHI2_def satisfies_def by auto
  qed
  moreover have "\<beta> u \<Turnstile> \<Phi>\<^sub>3"
  proof -
    have "\<beta> u \<Turnstile> \<Psi> (\<gamma> (2*i+1)) 2" if "i < n" for i
      using satisfies_Psi that H_gr_2 length_gamma less_imp_le_nat beta_3 by simp
    then show ?thesis
      using PHI3_def satisfies_concat_map' by simp
  qed
  moreover have "\<beta> u \<Turnstile> \<Phi>\<^sub>4"
  proof -
    have "\<beta> u \<Turnstile> \<Psi> (\<gamma> (2*n+2+2*i+1)) 2" if "i < p n" for i
      using satisfies_Psi that H_gr_2 length_gamma less_imp_le_nat beta_4 assms(1) by simp
    then show ?thesis
      using PHI4_def satisfies_concat_map' by simp
  qed
  moreover have "\<beta> u \<Turnstile> \<Phi>\<^sub>5"
  proof -
    have "\<beta> u \<Turnstile> \<Psi> (\<gamma> (2*n+2*p n+3+i)) 0" if "i < T'" for i
      using satisfies_Psi that H_gr_2 length_gamma less_imp_le_nat beta_5 assms(1) by simp
    then show ?thesis
      using PHI5_def satisfies_concat_map' by simp
  qed
  moreover have "\<beta> u \<Turnstile> \<Phi>\<^sub>6"
  proof -
    have "\<beta> u \<Turnstile> \<Psi> (\<gamma> (2*i+2)) (if x ! i then 3 else 2)" if "i < n" for i
      using satisfies_Psi that H_gr_2 length_gamma less_imp_le_nat beta_6 by simp
    then show ?thesis
      using PHI6_def satisfies_concat_map' by simp
  qed
  moreover have "\<beta> u \<Turnstile> \<Phi>\<^sub>7"
  proof -
    have "\<beta> u \<Turnstile> \<Upsilon> (\<gamma> (2*n+4+2*i))" if "i < p n" for i
    proof -
      have "blocky (\<beta> u) (\<gamma> (2*n+4+2*i)) 2 \<or> blocky (\<beta> u) (\<gamma> (2*n+4+2*i)) 3"
        using assms that beta_7[of i u] by (metis (full_types))
      then have "\<beta> u \<Turnstile> \<Psi> (\<gamma> (2*n+4+2*i)) 2 \<or> \<beta> u \<Turnstile> \<Psi> (\<gamma> (2*n+4+2*i)) 3"
        using satisfies_Psi H_gr_2 by auto
      then show ?thesis
        using Psi_2_imp_Upsilon Psi_3_imp_Upsilon H_gr_2 length_gamma by auto
    qed
    then show ?thesis
      using PHI7_def satisfies_concat_map' by simp
  qed
  moreover have "\<beta> u \<Turnstile> \<Phi>\<^sub>8"
    using PHI8_def H_gr_2 assms satisfies_Psi z1_def beta_zeta1
    by (metis One_nat_def Suc_1 Suc_leI length_zeta1 nat_le_linear numeral_3_eq_3)
  moreover have "\<beta> u \<Turnstile> \<Phi>\<^sub>9"
  proof -
    have *: "unary (\<beta> u) (\<gamma> i) = ysymbols u ! i" if "i < length (ysymbols u)" for i
    proof -
      have "i < m'"
        using assms length_ysymbols that by simp
      then consider
          "i = 0"
        | "1 \<le> i \<and> i < 2*n + 1"
        | "2*n+1 \<le> i \<and> i < 2*n+3"
        | "2*n+3 \<le> i \<and> i < m+1"
        | "i \<ge> m + 1 \<and> i < m + 1 + T'"
        using m'_def m_def by linarith
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using ysymbols_at_0 blocky_imp_unary H_gr_2 beta_1 by simp
      next
        case 2
        moreover define j where "j = (i - 1) div 2"
        ultimately have j: "j < n" "i = 2 * j + 1 \<or> i = 2 * j + 2"
          by auto
        show ?thesis
        proof (cases "i = 2 * j + 1")
          case True
          then show ?thesis
            using ysymbols_first_at(1) blocky_imp_unary H_gr_2 j(1) beta_3 by simp
        next
          case False
          then have "i = 2 * j + 2"
            using j(2) by simp
          then show ?thesis
            using ysymbols_first_at(2) blocky_imp_unary H_gr_2 j(1) beta_4 beta_6 by simp
        qed
      next
        case 3
        show ?thesis
        proof (cases "i = 2*n+1")
          case True
          then show ?thesis
            using ysymbols_at_2n1 blocky_imp_unary H_gr_2 beta_2a by simp
        next
          case False
          then have "i = 2*n+2"
            using 3 by simp
          then show ?thesis
            using ysymbols_at_2n2 blocky_imp_unary H_gr_2 beta_2b by simp
        qed
      next
        case 4
        moreover define j where "j = (i - 2*n-3) div 2"
        ultimately have j: "j < p n" "i = 2*n+2+2 * j + 1 \<or> i = 2*n+2+2 * j + 2"
          using j_def m_def by auto
        show ?thesis
        proof (cases "i = 2*n+2+2 * j + 1")
          case True
          then show ?thesis
            using ysymbols_second_at(1) assms(1) blocky_imp_unary H_gr_2 j(1) beta_4 by simp
        next
          case False
          then have i: "i = 2*n+4+2 * j"
            using j(2) by simp
          then have "ysymbols u ! (2*n+2+2*j+2) = (if u ! j then 3 else 2)"
            using ysymbols_second_at(2) assms j(1) by simp
          then have "ysymbols u ! (2*n+4+2*j) = (if u ! j then 3 else 2)"
            by (metis False i j(2))
          then have "ysymbols u ! i = (if u ! j then 3 else 2)"
            using i by simp
          then show ?thesis
            using beta_7[OF j(1)] blocky_imp_unary H_gr_2 length_gamma i assms(1) by simp
        qed
      next
        case 5
        then obtain ii where ii: "ii < T'" "i = m + 1 + ii"
          by (metis le_iff_add nat_add_left_cancel_less)
        have "blocky (\<beta> u) (\<gamma> (2*n+2*p n + 3 + ii)) 0"
          using beta_5[OF ii(1)] by simp
        then have "blocky (\<beta> u) (\<gamma> i) 0"
          using ii(2) m_def numeral_3_eq_3 by simp
        then have "unary (\<beta> u) (\<gamma> i) = 0"
          using blocky_imp_unary by simp
        moreover have "ysymbols u ! i = 0"
          using ysymbols_last[OF assms(1)] 5 by simp
        ultimately show ?thesis
          by simp
      qed
    qed
    have "\<beta> u \<Turnstile> \<chi> (Suc t)" (is "\<beta> u \<Turnstile> \<chi> ?t")
      if "t < T'" for t
    proof (cases "prev m ?t < ?t")
      case True
      have t: "?t \<le> T'"
        using that by simp
      then have "unary (\<beta> u) (\<zeta>\<^sub>0 ?t) = z0 u ?t"
        using blocky_imp_unary z0_le beta_zeta0 by simp
      moreover have "ysymbols u ! (inputpos m ?t) = unary (\<beta> u) (\<gamma> (inputpos m ?t))"
        using * assms(1) inputpos_less' length_ysymbols by simp
      ultimately have "unary (\<beta> u) (\<zeta>\<^sub>0 ?t) = unary (\<beta> u) (\<gamma> (inputpos m ?t))"
        using assms(1) z0 by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>1 ?t) = z1 u ?t"
        using beta_zeta1 blocky_imp_unary z1_le t by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>2 ?t) = z2 u ?t"
        using beta_zeta2 blocky_imp_unary z2_le t by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>0 (prev m ?t)) = z0 u (prev m ?t)"
        using beta_zeta0 blocky_imp_unary z0_le t True by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>1 (prev m ?t)) = z1 u (prev m ?t)"
        using beta_zeta1 blocky_imp_unary z1_le t True by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>2 (prev m ?t)) = z2 u (prev m ?t)"
        using beta_zeta2 blocky_imp_unary z2_le t True by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>0 (?t - 1)) = z0 u (?t - 1)"
        using beta_zeta0 blocky_imp_unary z0_le t True by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>1 (?t - 1)) = z1 u (?t - 1)"
        using beta_zeta1 blocky_imp_unary z1_le t True by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>2 (?t - 1)) = z2 u (?t - 1)"
        using beta_zeta2 blocky_imp_unary z2_le t True by simp
      ultimately show ?thesis
        using True assms(1) satisfies_chi_less[OF True] t z1 z2'
        by (metis bot_nat_0.extremum less_nat_zero_code nat_less_le)
    next
      case False
      then have prev: "prev m ?t = ?t"
        using prev_le by (meson le_neq_implies_less)
      have t: "?t \<le> T'"
        using that by simp
      then have "unary (\<beta> u) (\<zeta>\<^sub>0 ?t) = z0 u ?t"
        using beta_zeta0 blocky_imp_unary z0_le by simp
      moreover have "ysymbols u ! (inputpos m ?t) = unary (\<beta> u) (\<gamma> (inputpos m ?t))"
        using * assms(1) inputpos_less' length_ysymbols by simp
      ultimately have "unary (\<beta> u) (\<zeta>\<^sub>0 ?t) = unary (\<beta> u) (\<gamma> (inputpos m ?t))"
        using assms(1) z0 by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>1 ?t) = z1 u ?t"
        using beta_zeta1 blocky_imp_unary z1_le t by simp
      moreover have "z1 u ?t = \<box>"
        using z1' beta_zeta1 assms(1) prev t by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>2 ?t) = z2 u ?t"
        using beta_zeta2 blocky_imp_unary z2_le t by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>0 (?t - 1)) = z0 u (?t - 1)"
        using beta_zeta0 blocky_imp_unary z0_le t by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>1 (?t - 1)) = z1 u (?t - 1)"
        using beta_zeta1 blocky_imp_unary z1_le t by simp
      moreover have "unary (\<beta> u) (\<zeta>\<^sub>2 (?t - 1)) = z2 u (?t - 1)"
        using beta_zeta2 blocky_imp_unary z2_le t by simp
      ultimately show ?thesis
        using satisfies_chi_eq[OF prev] start_config2 start_config_pos t that z1_def z2 assms(1)
        by (metis (no_types, lifting) One_nat_def Suc_1 Suc_less_eq add_diff_inverse_nat
          execute.simps(1) less_one n_not_Suc_n plus_1_eq_Suc)
    qed
    then show ?thesis
      using PHI9_def satisfies_concat_map' by presburger
  qed
  ultimately show ?thesis
    using satisfies_append' PHI_def by simp
qed

corollary ex_u_imp_sat_PHI:
  assumes "length u = p n" and "exc \<langle>x; u\<rangle> T' <.> 1 = \<one>"
  shows "satisfiable \<Phi>"
  using satisfies_beta_PHI assms satisfiable_def by auto

text \<open>
The formula $\Phi$ has the desired property:
\<close>

theorem L_iff_satisfiable: "x \<in> L \<longleftrightarrow> satisfiable \<Phi>"
  using L_iff_ex_u ex_u_imp_sat_PHI sat_PHI_imp_ex_u by auto

end  (* locale reduction_sat_x *)

end
