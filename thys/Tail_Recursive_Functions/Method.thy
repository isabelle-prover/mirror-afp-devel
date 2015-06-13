(*  Title:       A General Method for the Proof of Theorems on Tail-recursive Functions
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "Method rationale"

(*<*)
theory Method
imports Main 
begin
(*>*)

text {*
Tail-recursive function definitions are sometimes more intuitive and
straightforward than alternatives, and this alone would be enough to make them
preferable in such cases for the mere purposes of functional programming. However,
proving theorems about them with a formal proof assistant like Isabelle may be
roundabout because of the peculiar form of the resulting recursion induction
rules.

Let:

\begin{itemize}

\item
@{text f_naive} be a tail-recursive function of type
@{text "'a\<^sub>1 \<Rightarrow> ... \<Rightarrow> 'a\<^sub>n \<Rightarrow> 'b"}.

\item
@{text a} be an @{text n}-tuple of values of types @{text "'a\<^sub>1"}, ...,
@{text "'a\<^sub>n"} such that the computation of @{text "f_naive a"}, say outputting
value @{text b}, involves at least one recursive call -- which is what happens in
general for significant inputs (e.g. those complying with initial conditions for
accumulator arguments), as otherwise a non-recursive function definition would be
sufficient.

\item
@{text "a\<^sub>1"}, ..., @{text "a\<^sub>m"} be the sequence of the intermediate
@{text n}-tuples of values of types @{text "'a\<^sub>1"}, ..., @{text "'a\<^sub>n"} arising from
the computation of @{text "f_naive a"}.

\item
@{text "f_naive X\<^sub>1 = f_naive X'\<^sub>1"}, ..., @{text "f_naive X\<^sub>m = f_naive X'\<^sub>m"},
@{text "f_naive X = Y"} be the sequence (possibly with repetitions) of the
equations involved in the computation of @{text "f_naive a"} -- which implies
that, putting @{text "a\<^sub>0 = a"}, they are satisfied for
@{text "(X\<^sub>1, X'\<^sub>1) = (a\<^sub>0, a\<^sub>1)"}, ..., @{text "(X\<^sub>m, X'\<^sub>m) = (a\<^sub>m\<^sub>-\<^sub>1, a\<^sub>m)"},
@{text "(X, Y) = (a\<^sub>m, b)"}, respectively.

\end{itemize}

That being stated, suppose that theorem @{text "P (f_naive a)"} has to be proven.
If recursion induction is applied to such goal, for each @{text "i \<in> {1..m}"},
the recursive equation @{text "f_naive X\<^sub>i = f_naive X'\<^sub>i"} gives rise to subgoal
@{text "P (f_naive X'\<^sub>i) \<Longrightarrow> P (f_naive X\<^sub>i)"}, trivially discharged by
simplification. On the contrary, the non-recursive equation
@{text "f_naive X = Y"} brings about the generation of subgoal
@{text "P (f_naive X)"}, which is intractable unless it trivially follows from
either the equation or the form of pattern @{text X}.

Indeed, in non-trivial cases such as the case studies examined in this paper, this
formula even fails to be a theorem, thus being hopeless as a goal, since it is
false for some values of its variables. The reason for this is that non-trivial
properties of the output of tail-recursive functions depend on the input as well
as on the whole recursive call pipeline leading from the input to the output, and
all of this information corresponds to missing necessary assumptions in subgoal
@{text "P (f_naive X)"}.

Therefore, for a non-trivial theorem @{text "P (f_naive a)"}, recursion induction
is rather applicable to some true conditional statement
@{text "f_inv x \<longrightarrow> P (f_naive x)"} complying with both of the following
requirements:

\begin{itemize}

\item
subgoal @{text "f_inv X \<longrightarrow> P (f_naive X)"} arising from equation
@{text "f_naive X = Y"} be tractable, and

\item
formula @{text "f_inv a"} can be shown to be true, so that theorem
@{text "P (f_naive a)"} can be inferred from conditional
@{text "f_inv a \<longrightarrow> P (f_naive a)"} by \emph{modus ponens}.

\end{itemize}

Observe that the antecedent of the conditional may not have the form
@{text "f_inv (f_naive x)"}. Otherwise, the latter requirement would ask for
proving formula @{text "f_inv (f_naive a)"}, which would be at least as hard to
prove as formula @{text "P (f_naive a)"} being the former a sufficient condition
for the latter. Hence, the same problem as that originating from the proof of
formula @{text "P (f_naive a)"} would have to be solved again, which would give
rise to a \emph{regressio ad infinitum}.

The latter requirement entails that formula @{text "f_inv a\<^sub>0"} holds. Moreover,
for each @{text "i \<in> {1..m}"}, in the proof of conditional
@{text "f_inv x \<longrightarrow> P (f_naive x)"} by recursion induction, the recursive equation
@{text "f_naive X\<^sub>i = f_naive X'\<^sub>i"} brings about the generation of subgoal
@{text "f_inv X'\<^sub>i \<longrightarrow> P (f_naive X'\<^sub>i) \<Longrightarrow> f_inv X\<^sub>i \<longrightarrow> P (f_naive X\<^sub>i)"}. Assuming
that formula @{text "f_inv a\<^sub>i\<^sub>-\<^sub>1"} holds, it turns out that the conclusion
antecedent @{text "f_inv X\<^sub>i"} may not be shown to be false, as @{text n}-tuple
@{text "a\<^sub>i\<^sub>-\<^sub>1"} matches pattern @{text "X\<^sub>i"}; thus, the conclusion consequent
@{text "P (f_naive X\<^sub>i)"} has to be proven.

In non-trivial cases, this requires that the assumption antecedent
@{text "f_inv X'\<^sub>i"} be derived from the conclusion antecedent @{text "f_inv X\<^sub>i"}
used as a further assumption, so that the assumption consequent
@{text "P (f_naive X'\<^sub>i)"} -- matching @{text "P (f_naive X\<^sub>i)"} by virtue of
equation @{text "f_naive X\<^sub>i = f_naive X'\<^sub>i"} -- can be proven by
\emph{modus ponens}. This in turn requires that @{text "f_inv X\<^sub>i"} imply
@{text "f_inv X'\<^sub>i"}, i.e. that @{text "f_inv x\<^sub>i"} imply @{text "f_inv x'\<^sub>i"} for any
pair of @{text n}-tuples @{text "x\<^sub>i"}, @{text "x'\<^sub>i"} matching patterns @{text "X\<^sub>i"},
@{text "X'\<^sub>i"} with respect to the same value assignment. But such are
@{text n}-tuples @{text "a\<^sub>i\<^sub>-\<^sub>1"}, @{text "a\<^sub>i"} as they solve equation
@{text "f_naive X\<^sub>i = f_naive X'\<^sub>i"}, so that the supposed truth of
@{text "f_inv a\<^sub>i\<^sub>-\<^sub>1"} entails that of @{text "f_inv a\<^sub>i"}.

Hence, by induction, all of formulae @{text "f_inv a"}, @{text "f_inv a\<^sub>1"}, ...,
@{text "f_inv a\<^sub>m"} turn out to be true. On the other hand, the former requirement
is verified if either the antecedent @{text "f_inv X"} can be shown to be false,
which would entail its falsity for any @{text n}-tuple matching pattern @{text X},
or else the consequent @{text "P (f_naive X)"} can be shown to be true using the
antecedent as an assumption. Since formula @{text "f_inv a\<^sub>m"} is true and
@{text n}-tuple @{text "a\<^sub>m"} matches pattern @{text X}, the case that actually
occurs is the second one.

Thus, the former requirement is equivalent to asking for an introduction rule to
be proven -- in fact, a conditional with a contradiction as antecedent may not be
used as an introduction rule -- having the form
@{text "f_inv X \<Longrightarrow> P (f_naive X)"}, or rather
@{text "\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_naive x)"} for a suitable predicate
@{text f_form} satisfied by any @{text n}-tuple matching pattern @{text X}. In
the degenerate case in which the rule can be shown to be true for
@{text "f_form = (\<lambda>x. True)"}, it admits to be put into the simpler equivalent
form @{text "f_inv x \<Longrightarrow> P (f_naive x)"}.

An even more important consequence of the previous argument is that in non-trivial
cases, the task of proving conditional @{text "f_inv x \<longrightarrow> P (f_naive x)"} by
recursion induction requires that @{text "f_inv X'\<^sub>i"} be derived from
@{text "f_inv X\<^sub>i"} for each recursive equation @{text "f_naive X\<^sub>i = f_naive X'\<^sub>i"},
where @{text "i \<in> {1..m}"}.

Let:

\begin{itemize}

\item
@{text 'a} be the Cartesian product of types @{text "'a\<^sub>1"}, ..., @{text "'a\<^sub>n"}.

\item
@{text f_set} be the inductive set of type @{text "'a \<Rightarrow> 'a set"} defined by
introduction rules @{text "x \<in> f_set x"},
@{text "X\<^sub>1 \<in> f_set x \<Longrightarrow> X'\<^sub>1 \<in> f_set x"}, ...,
@{text "X\<^sub>m \<in> f_set x \<Longrightarrow> X'\<^sub>m \<in> f_set x"} -- where patterns @{text "X\<^sub>1"},
@{text "X'\<^sub>1"}, ..., @{text "X\<^sub>m"}, @{text "X'\<^sub>m"} are now viewed as values of type
@{text 'a}.

\end{itemize}

Then, the problem of discharging the above proof obligation on predicate
@{text f_inv} is at least as hard as that of proving by rule induction
introduction rule @{text "\<lbrakk>y \<in> f_set x; f_inv x\<rbrakk> \<Longrightarrow> f_inv y"} -- which states that
for any @{text x} such that @{text "f_inv x"} is true, @{text f_inv} is an
invariant over inductive set @{text "f_set x"}, i.e. @{text "f_inv y"} is true for
each @{text "y \<in> f_set x"}.

In fact, the application of rule induction to this goal generates subgoals
@{text "f_inv x \<Longrightarrow> f_inv x"},
@{text "\<lbrakk>X\<^sub>1 \<in> f_set x; f_inv X\<^sub>1; f_inv x\<rbrakk> \<Longrightarrow> f_inv X'\<^sub>1"}, ...,
@{text "\<lbrakk>X\<^sub>m \<in> f_set x; f_inv X\<^sub>m; f_inv x\<rbrakk> \<Longrightarrow> f_inv X'\<^sub>m"}; the first is trivial,
and such would also be the other ones if rules @{text "f_inv X\<^sub>1 \<Longrightarrow> f_inv X'\<^sub>1"},
..., @{text "f_inv X\<^sub>m \<Longrightarrow> f_inv X'\<^sub>m"} were available.

Furthermore, suppose that the above invariance property of predicate @{text f_inv}
have been proven; then, the proof of conditional
@{text "f_inv x \<longrightarrow> P (f_naive x)"} by recursion induction can be made unnecessary
by slightly refining the definition of function @{text f_naive}, as shown in the
continuation.

Let @{text f_aux} be the tail-recursive function of type @{text "'a \<Rightarrow> 'a"} whose
definition is obtained from that of @{text f_naive} by treating as fixed points
the patterns to which non-recursive equations apply as well as those to which no
equation applies, if any -- i.e. by replacing recursive equation
@{text "f_naive X\<^sub>i = f_naive X'\<^sub>i"} with @{text "f_aux X\<^sub>i = f_aux X'\<^sub>i"} for each
@{text "i \<in> {1..m}"} and non-recursive equation @{text "f_naive X = Y"} with
@{text "f_aux X = X"}.

Then, define function @{text f} by means of a non-recursive equation
@{text "f x = f_out (f_aux (f_in x))"}, where:

\begin{itemize}

\item
@{text f_in} is a function of type @{text "'a' \<Rightarrow> 'a"}, for a suitable type
@{text 'a'}, whose range contains all the significant inputs of function
@{text f_naive}.

\item
@{text f_out} is a function of type @{text "'a \<Rightarrow> 'b"} mapping the outputs of
@{text f_aux} to those of @{text f_naive}, i.e. the values of type @{text 'a}
matching pattern @{text X} to those of type @{text 'b} matching pattern
@{text Y} with respect to the same value assignment.

\end{itemize}

The definitions of functions @{text f_aux} and @{text f_out} entail that equation
@{text "f_naive x = f_out (f_aux x)"} holds for any @{text x}. Particularly,
@{text "f_naive a = f_out (f_aux a)"}; thus, being @{text a'} an inverse image of
@{text a} under @{text f_in}, viz. @{text "a = f_in a'"}, it follows that
@{text "f_naive a = f a'"}. As a result, theorem @{text "P (f_naive a)"} may be
rewritten as @{text "P (f a')"}.

For any @{text x}, @{text "f_set x"} is precisely the set of the values
recursively input to function @{text f_aux} in the computation of
@{text "f_aux x"}, including @{text x} itself, and it can easily be ascertained
that @{text "f_aux x"} is such a value. In fact, the equation invoked last in the
computation of @{text "f_aux x"} must be a non-recursive one, so that it has the
form @{text "f_aux X = X"}, since all non-recursive equations in the definition
of @{text f_aux} apply to fixed points. Thus, being @{text "f_aux x"} the output
of the computation, the right-hand side of the equation, i.e. the pattern
@{text X} also input to function @{text f_aux} in the left-hand side, is
instantiated to value @{text "f_aux x"}.

Therefore, @{text "f_aux x \<in> f_set x"} for any @{text x}. Observe that the
argument rests on the assumption that whatever @{text x} is given, a sequence of
equations leading from @{text x} to @{text "f_aux x"} be actually available -- and
what is more, nothing significant could be proven on @{text "f_aux x"} for any
@{text x} for which its value were undefined, and then arbitrary. The trick of
making the definition of @{text f_aux} total by adding equations for the patterns
not covered in the definition of @{text f_naive}, if any, guarantees that this
assumption be satisfied.

An additional consequence of the previous argument is that
@{text "f_aux (f_aux x) = f_aux x"} for any @{text x}, i.e. function @{text f_aux}
is idempotent. If introduction rule @{text "\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_naive x)"}
is rewritten by applying equation @{text "f_naive x = f_out (f_aux x)"},
instantiating free variable @{text x} to @{text "f_aux x"}, and then applying the
idempotence of function @{text f_aux}, the result is formula
@{text "\<lbrakk>f_inv (f_aux x); f_form (f_aux x)\<rbrakk> \<Longrightarrow> P (f_out (f_aux x))"}, which is
nothing but an instantiation of introduction rule
@{text "\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_out x)"}.

Observe that this rule is just a refinement of a rule whose proof is required for
proving conditional @{text "f_inv x \<longrightarrow> P (f_naive x)"} by recursion induction, so
that it does not give rise to any additional proof obligation. Moreover, it
contains neither function @{text f_naive} nor @{text f_aux}, thus its proof does
not require recursion induction with respect to the corresponding induction rules.

The instantiation of such refined introduction rule with value @{text "f_aux a"}
is @{text "\<lbrakk>f_inv (f_aux a); f_form (f_aux a)\<rbrakk> \<Longrightarrow> P (f_out (f_aux a))"}, which by
virtue of equality @{text "a = f_in a'"} and the definition of function @{text f}
is equivalent to formula
@{text "\<lbrakk>f_inv (f_aux a); f_form (f_aux a)\<rbrakk> \<Longrightarrow> P (f a')"}. Therefore, the rule is
sufficient to prove theorem @{text "P (f a')"} -- hence making unnecessary the
proof of conditional @{text "f_inv x \<longrightarrow> P (f_naive x)"} by recursion induction,
as mentioned previously -- provided the instantiated assumptions
@{text "f_inv (f_aux a)"}, @{text "f_form (f_aux a)"} can be shown to be true.

This actually is the case: the former assumption can be derived from formulae
@{text "f_aux a \<in> f_set a"}, @{text "f_inv a"} and the invariance of predicate
@{text f_inv} over @{text "f_set a"}, while the latter can be proven by recursion
induction, as by construction goal @{text "f_form X"} is trivial for any pattern
@{text X} to which some non-recursive equation in the definition of function
@{text f_naive} applies. If further non-recursive equations whose patterns do not
satisfy predicate @{text f_form} have been added to the definition of
@{text f_aux} to render it total, rule inversion can be applied to exclude that
@{text "f_aux a"} may match any of such patterns, again using formula
@{text "f_aux a \<in> f_set a"}.
*}

section "Method summary"

text {*
The general method developed so far can be schematized as follows.

Let @{text f_naive} be a tail-recursive function of type
@{text "'a\<^sub>1 \<Rightarrow> ... \<Rightarrow> 'a\<^sub>n \<Rightarrow> 'b"}, and @{text "P (f_naive a\<^sub>1 ... a\<^sub>n)"} be a
non-trivial theorem having to be proven on this function.

In order to accomplish such task, the following procedure shall be observed.

\begin{itemize}

\item
\emph{Step 1} --- Refine the definition of @{text f_naive} into that of an
auxiliary tail-recursive function @{text f_aux} of type @{text "'a \<Rightarrow> 'a"}, where
@{text 'a} is a product or record type with types @{text "'a\<^sub>1"}, ..., @{text "'a\<^sub>n"}
as components, by treating as fixed points the patterns to which non-recursive
equations apply as well as those to which no equation applies, if any.

\item
\emph{Step 2} --- Define a function @{text f} of type @{text "'a' \<Rightarrow> 'b"} by means
of a non-recursive equation @{text "f x = f_out (f_aux (f_in x))"}, where
@{text f_in} is a function of type @{text "'a' \<Rightarrow> 'a"} (possibly matching the
identity function) whose range contains all the significant inputs of function
@{text f_naive}, and @{text f_out} is a function of type @{text "'a \<Rightarrow> 'b"}
mapping the outputs of @{text f_aux} to those of @{text f_naive}.
\\Then, denoting with @{text a} the value of type @{text 'a} with components
@{text "a\<^sub>1"}, ..., @{text "a\<^sub>n"}, and with @{text a'} an inverse image of @{text a}
under function @{text f_in}, the theorem to be proven takes the equivalent form
@{text "P (f a')"}.

\item
\emph{Step 3} --- Let @{text "f_aux X\<^sub>1 = f_aux X'\<^sub>1"}, ...,
@{text "f_aux X\<^sub>m = f_aux X'\<^sub>m"} be the recursive equations in the definition of
function @{text f_aux}.
\\Then, define an inductive set @{text f_set} of type @{text "'a \<Rightarrow> 'a set"} with
introduction rules @{text "x \<in> f_set x"},
@{text "X\<^sub>1 \<in> f_set x \<Longrightarrow> X'\<^sub>1 \<in> f_set x"}, ...,
@{text "X\<^sub>m \<in> f_set x \<Longrightarrow> X'\<^sub>m \<in> f_set x"}.
\\If the right-hand side of some recursive equation contains conditionals in the
form of @{text "if"} or @{text case} constructs, the corresponding introduction
rule can be split into as many rules as the possible mutually exclusive cases;
each of such rules shall then provide for the related case as an additional
assumption.

\item
\emph{Step 4} --- Prove lemma @{text "f_aux x \<in> f_set x"}; a general inference
scheme, independent of the specific function @{text f_aux}, applies to this proof.
\\First, prove lemma @{text "y \<in> f_set x \<Longrightarrow> f_set y \<subseteq> f_set x"}, which can easily
be done by rule induction.
\\Next, applying recursion induction to goal @{text "f_aux x \<in> f_set x"} and then
simplifying, a subgoal @{text "X\<^sub>i \<in> f_set X\<^sub>i"} arises for each non-recursive
equation @{text "f_aux X\<^sub>i = X\<^sub>i"}, while a subgoal
@{text "f_aux X'\<^sub>j \<in> f_set X'\<^sub>j \<Longrightarrow> f_aux X'\<^sub>j \<in> f_set X\<^sub>j"} arises for each recursive
equation @{text "f_aux X\<^sub>j = f_aux X'\<^sub>j"}.
\\The former subgoals can be proven by introduction rule @{text "x \<in> f_set x"}, the
latter ones as follows: rule instantiations @{text "X\<^sub>j \<in> f_set X\<^sub>j"} and
@{text "X\<^sub>j \<in> f_set X\<^sub>j \<Longrightarrow> X'\<^sub>j \<in> f_set X\<^sub>j"} imply formula @{text "X'\<^sub>j \<in> f_set X\<^sub>j"};
thus @{text "f_set X'\<^sub>j \<subseteq> f_set X\<^sub>j"} by the aforesaid lemma; from this and subgoal
assumption @{text "f_aux X'\<^sub>j \<in> f_set X'\<^sub>j"}, subgoal conclusion
@{text "f_aux X'\<^sub>j \<in> f_set X\<^sub>j"} ensues.
\\As regards recursive equations containing conditionals, the above steps have to
be preceded by a case distinction, so as to obtain further assumptions sufficient
for splitting such conditionals.

\item
\emph{Step 5} --- Define a predicate @{text f_inv} of type @{text "'a \<Rightarrow> bool"} in
such a way as to meet the proof obligations prescribed by the following steps.

\item
\emph{Step 6} --- Prove lemma @{text "f_inv a"}.
\\In case of failure, return to step 5 so as to suitably change the definition of
predicate @{text f_inv}.

\item
\emph{Step 7} --- Prove introduction rule @{text "f_inv x \<Longrightarrow> P (f_out x)"}, or
rather @{text "\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_out x)"}, where @{text f_form} is a
suitable predicate of type @{text "'a \<Rightarrow> bool"} satisfied by any pattern to which
some non-recursive equation in the definition of function @{text f_naive} applies.
\\In case of failure, return to step 5 so as to suitably change the definition of
predicate @{text f_inv}.

\item
\emph{Step 8} --- In case an introduction rule of the second form has been proven
in step 7, prove lemma @{text "f_form (f_aux a)"} by recursion induction.
\\If the definition of function @{text f_aux} resulting from step 1 contains
additional non-recursive equations whose patterns do not satisfy predicate
@{text f_form}, rule inversion can be applied to exclude that @{text "f_aux a"}
may match any of such patterns, using instantiation @{text "f_aux a \<in> f_set a"} of
the lemma proven in step 4.

\item
\emph{Step 9} --- Prove by rule induction introduction rule
@{text "\<lbrakk>y \<in> f_set x; f_inv x\<rbrakk> \<Longrightarrow> f_inv y"}, which states the invariance of
predicate @{text f_inv} over inductive set @{text "f_set x"} for any @{text x}
satisfying @{text f_inv}.
\\In case of failure, return to step 5 so as to suitably change the definition of
predicate @{text f_inv}.
\\Observe that the order in which the proof obligations related to predicate
@{text f_inv} are distributed among steps 6 to 9 is ascending in the effort
typically required to discharge them. The reason why this strategy is advisable is
that in case one step fails, which forces to revise the definition of predicate
@{text f_inv} and then also the proofs already worked out, such proofs will be the
least demanding ones so as to minimize the effort required for their revision.

\item
\emph{Step 10} --- Prove theorem @{text "P (f a')"} by means of the following
inference scheme.
\\First, derive formula @{text "f_inv (f_aux a)"} from introduction rule
@{text "\<lbrakk>y \<in> f_set x; f_inv x\<rbrakk> \<Longrightarrow> f_inv y"} and formulae
@{text "f_aux a \<in> f_set a"}, @{text "f_inv a"}.
\\Then, derive formula @{text "P (f_out (f_aux a))"} from either introduction rule
@{text "f_inv x \<Longrightarrow> P (f_out x)"} or @{text "\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_out x)"}
and formulae @{text "f_inv (f_aux a)"}, @{text "f_form (f_aux a)"} (in the latter
case).
\\Finally, derive theorem @{text "P (f a')"} from formulae
@{text "P (f_out (f_aux a))"}, @{text "a = f_in a'"} and the definition of
function @{text f}.

\end{itemize}

In the continuation, the application of this method is illustrated by analyzing
two case studies drawn from an exercise comprised in Isabelle online course
material; see \cite{R5}. The salient points of definitions and proofs are
commented; for additional information see Isabelle documentation, particularly
\cite{R1}, \cite{R2}, \cite{R3}, and \cite{R4}.
*}

(*<*)
end
(*>*)
