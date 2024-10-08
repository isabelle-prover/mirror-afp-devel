(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de

Copyright (C) 2006-2008 Norbert Schirmer
*)

section \<open>Examples using the Verification Environment\<close>

theory VcgEx imports "../HeapList" "../Vcg" begin

text \<open>Some examples, especially the single-step Isar proofs are taken from
\texttt{HOL/Isar\_examples/HoareEx.thy}.
\<close>

subsection \<open>State Spaces\<close>

text \<open>
 First of all we provide a store of program variables that
 occur in the programs considered later.  Slightly unexpected
 things may happen when attempting to work with undeclared variables.
\<close>

record 'g vars = "'g state" +
  A_' :: nat
  I_' :: nat
  M_' :: nat
  N_' :: nat
  R_' :: nat
  S_' :: nat
  B_' :: bool
  Arr_' :: "nat list"
  Abr_':: string



text \<open>We decorate the state components in the record with the suffix \<open>_'\<close>,
to avoid cluttering the namespace with the simple names that could no longer
be used for logical variables otherwise.
\<close>

text \<open>We will first consider programs without procedures, later on
we will regard procedures without global variables and finally we
will get the full pictures: mutually recursive procedures with global
variables (including heap).
\<close>

subsection \<open>Basic Examples\<close>

text \<open>
 We look at few trivialities involving assignment and sequential
 composition, in order to get an idea of how to work with our
 formulation of Hoare Logic.
\<close>

text \<open>
 Using the basic rule directly is a bit cumbersome.
\<close>

lemma "\<Gamma>\<turnstile> {|\<acute>N = 5|} \<acute>N :== 2 * \<acute>N {|\<acute>N = 10|}"
  apply (rule HoarePartial.Basic)  apply simp
  done

text \<open>
 If we refer to components (variables) of the state-space of the program
 we always mark these with \<open>\<acute>\<close>. It is the acute-symbol and is present on
 most keyboards. So all program variables are marked with the acute and all
 logical variables are not.
 The assertions of the Hoare tuple are
 ordinary Isabelle sets. As we usually want to refer to the state space
 in the assertions, we provide special brackets for them. They can be written
 as {\verb+{| |}+} in ASCII or \<open>\<lbrace> \<rbrace>\<close> with symbols. Internally
 marking variables has two effects. First of all we refer to the implicit
 state and secondary we get rid of the suffix \<open>_'\<close>.
 So the assertion @{term "{|\<acute>N = 5|}"} internally gets expanded to
 \<open>{s. N_' s = 5}\<close> written in ordinary set comprehension notation of
 Isabelle. It describes the set of states where the \<open>N_'\<close> component
 is equal to \<open>5\<close>.
\<close>


text \<open>
 Certainly we want the state modification already done, e.g.\ by
 simplification.  The \<open>vcg\<close> method performs the basic state
 update for us; we may apply the Simplifier afterwards to achieve
 ``obvious'' consequences as well.
\<close>


lemma "\<Gamma>\<turnstile> \<lbrace>True\<rbrace> \<acute>N :== 10 \<lbrace>\<acute>N = 10\<rbrace>"
  by vcg

lemma "\<Gamma>\<turnstile> \<lbrace>2 * \<acute>N = 10\<rbrace> \<acute>N :== 2 * \<acute>N \<lbrace>\<acute>N = 10\<rbrace>"
  by vcg

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> \<acute>N :== 2 * \<acute>N \<lbrace>\<acute>N = 10\<rbrace>"
  apply vcg
  apply simp
  done

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N + 1 = a + 1\<rbrace> \<acute>N :== \<acute>N + 1 \<lbrace>\<acute>N = a + 1\<rbrace>"
  by vcg

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = a\<rbrace> \<acute>N :== \<acute>N + 1 \<lbrace>\<acute>N = a + 1\<rbrace>"
  by vcg


lemma "\<Gamma>\<turnstile> \<lbrace>a = a \<and> b = b\<rbrace> \<acute>M :== a;; \<acute>N :== b \<lbrace>\<acute>M = a \<and> \<acute>N = b\<rbrace>"
  by vcg


lemma "\<Gamma>\<turnstile> \<lbrace>True\<rbrace> \<acute>M :== a;; \<acute>N :== b \<lbrace>\<acute>M = a \<and> \<acute>N = b\<rbrace>"
  by vcg

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = a \<and> \<acute>N = b\<rbrace>
                \<acute>I :== \<acute>M;; \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I
              \<lbrace>\<acute>M = b \<and> \<acute>N = a\<rbrace>"
  by vcg

text \<open>
We can also perform verification conditions generation step by step by using
the \<open>vcg_step\<close> method.
\<close>

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = a \<and> \<acute>N = b\<rbrace>
               \<acute>I :== \<acute>M;; \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I
              \<lbrace>\<acute>M = b \<and> \<acute>N = a\<rbrace>"
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  done

text \<open>
 It is important to note that statements like the following one can
 only be proven for each individual program variable.  Due to the
 extra-logical nature of record fields, we cannot formulate a theorem
 relating record selectors and updates schematically.
\<close>

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = a\<rbrace> \<acute>N :== \<acute>N \<lbrace>\<acute>N = a\<rbrace>"
  by vcg


(*
lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>x = a\<rbrace> \<acute>x :== \<acute>x \<lbrace>\<acute>x = a\<rbrace>"
  apply (rule HoarePartial.Basic)
  -- {* We can't proof this since we don't know what @{text "x_'_update"} is. *}
  oops
 *)
lemma "\<Gamma>\<turnstile>{s. x_' s = a} (Basic (\<lambda>s. x_'_update (x_' s) s)) {s. x_' s = a}"
  oops


text \<open>
 In the following assignments we make use of the consequence rule in
 order to achieve the intended precondition.  Certainly, the
 \<open>vcg\<close> method is able to handle this case, too.
\<close>

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = \<acute>N\<rbrace> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
proof -
  have "\<lbrace>\<acute>M = \<acute>N\<rbrace> \<subseteq> \<lbrace>\<acute>M + 1 \<noteq> \<acute>N\<rbrace>"
    by auto
  also have "\<Gamma>\<turnstile> \<dots> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
    by vcg
  finally show ?thesis .
qed

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = \<acute>N\<rbrace> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
proof -
  have "\<And>m n::nat. m = n \<longrightarrow> m + 1 \<noteq> n"
      \<comment> \<open>inclusion of assertions expressed in ``pure'' logic,\<close>
      \<comment> \<open>without mentioning the state space\<close>
    by simp
  also have "\<Gamma>\<turnstile> \<lbrace>\<acute>M + 1 \<noteq> \<acute>N\<rbrace> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
    by vcg
  finally show ?thesis .
qed

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = \<acute>N\<rbrace> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
  apply vcg
  apply simp
  done

subsection \<open>Multiplication by Addition\<close>

text \<open>
 We now do some basic examples of actual \texttt{WHILE} programs.
 This one is a loop for calculating the product of two natural
 numbers, by iterated addition.  We first give detailed structured
 proof based on single-step Hoare rules.
\<close>

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
      WHILE \<acute>M \<noteq> a
      DO \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 OD
      \<lbrace>\<acute>S = a * b\<rbrace>"
proof -
  let "\<Gamma>\<turnstile> _ ?while _" = ?thesis
  let "\<lbrace>\<acute>?inv\<rbrace>" = "\<lbrace>\<acute>S = \<acute>M * b\<rbrace>"

  have "\<lbrace>\<acute>M = 0 & \<acute>S = 0\<rbrace> \<subseteq> \<lbrace>\<acute>?inv\<rbrace>" by auto
  also have "\<Gamma>\<turnstile> \<dots> ?while \<lbrace>\<acute>?inv \<and> \<not> (\<acute>M \<noteq> a)\<rbrace>"
  proof
    let ?c = "\<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1"
    have "\<lbrace>\<acute>?inv \<and> \<acute>M \<noteq> a\<rbrace> \<subseteq> \<lbrace>\<acute>S + b = (\<acute>M + 1) * b\<rbrace>"
      by auto
    also have "\<Gamma>\<turnstile> \<dots> ?c \<lbrace>\<acute>?inv\<rbrace>" by vcg
    finally show "\<Gamma>\<turnstile> \<lbrace>\<acute>?inv \<and> \<acute>M \<noteq> a\<rbrace> ?c \<lbrace>\<acute>?inv\<rbrace>" .
  qed
  also have "\<lbrace>\<acute>?inv \<and> \<not> (\<acute>M \<noteq> a)\<rbrace> \<subseteq> \<lbrace>\<acute>S = a * b\<rbrace>" by auto
  finally show ?thesis by blast
qed


text \<open>
 The subsequent version of the proof applies the \<open>vcg\<close> method
 to reduce the Hoare statement to a purely logical problem that can be
 solved fully automatically.  Note that we have to specify the
 \texttt{WHILE} loop invariant in the original statement.
\<close>

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          WHILE \<acute>M \<noteq> a
          INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
          DO \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 OD
          \<lbrace>\<acute>S = a * b\<rbrace>"
  apply vcg
  apply auto
  done

text \<open>Here some examples of ``breaking'' out of a loop\<close>

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          TRY
            WHILE True
            INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
            DO IF \<acute>M = a THEN THROW ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 FI OD
          CATCH
            SKIP
          END
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          TRY
            WHILE True
            INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
            DO IF \<acute>M = a THEN \<acute>Abr :== ''Break'';;THROW
               ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1
               FI
            OD
          CATCH
            IF \<acute>Abr = ''Break'' THEN SKIP ELSE Throw FI
          END
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done


text \<open>Some more syntactic sugar, the label statement \<open>\<dots> \<bullet> \<dots>\<close> as shorthand
for the \<open>TRY-CATCH\<close> above, and the \<open>RAISE\<close> for an state-update followed
by a \<open>THROW\<close>.
\<close>
lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          \<lbrace>\<acute>Abr = ''Break''\<rbrace>\<bullet> WHILE True INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
           DO IF \<acute>M = a THEN RAISE \<acute>Abr :== ''Break''
              ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1
              FI
           OD
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          TRY
            WHILE True
            INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
            DO IF \<acute>M = a THEN RAISE \<acute>Abr :== ''Break''
               ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1
               FI
            OD
          CATCH
            IF \<acute>Abr = ''Break'' THEN SKIP ELSE Throw FI
          END
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          \<lbrace>\<acute>Abr = ''Break''\<rbrace> \<bullet> WHILE True
          INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
          DO IF \<acute>M = a THEN RAISE \<acute>Abr :== ''Break''
               ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1
               FI
          OD
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done

text \<open>Blocks\<close>

lemma  "\<Gamma>\<turnstile>\<lbrace>\<acute>I = i\<rbrace> LOC \<acute>I;; \<acute>I :== 2  COL \<lbrace>\<acute>I \<le> i\<rbrace>"
  apply vcg
  by simp
lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = n\<rbrace> LOC \<acute>N :== 10;; \<acute>N :== \<acute>N + 2 COL \<lbrace>\<acute>N = n\<rbrace>"
  by vcg

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = n\<rbrace> LOC \<acute>N :== 10, \<acute>M;; \<acute>N :== \<acute>N + 2 COL \<lbrace>\<acute>N = n\<rbrace>"
  by vcg


subsection \<open>Summing Natural Numbers\<close>

text \<open>
 We verify an imperative program to sum natural numbers up to a given
 limit.  First some functional definition for proper specification of
 the problem.
\<close>

primrec
  sum :: "(nat => nat) => nat => nat"
where
  "sum f 0 = 0"
| "sum f (Suc n) = f n + sum f n"

syntax
  "_sum" :: "idt => nat => nat => nat"
    (\<open>SUMM _<_. _\<close> [0, 0, 10] 10)
syntax_consts
  "_sum" == sum
translations
  "SUMM j<k. b" == "CONST sum (\<lambda>j. b) k"

text \<open>
 The following proof is quite explicit in the individual steps taken,
 with the \<open>vcg\<close> method only applied locally to take care of
 assignment and sequential composition.  Note that we express
 intermediate proof obligation in pure logic, without referring to the
 state space.
\<close>

theorem "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>
           \<acute>S :== 0;; \<acute>I :== 1;;
           WHILE \<acute>I \<noteq> n
           DO
             \<acute>S :== \<acute>S + \<acute>I;;
             \<acute>I :== \<acute>I + 1
           OD
           \<lbrace>\<acute>S = (SUMM j<n. j)\<rbrace>"
  (is "\<Gamma>\<turnstile> _ (_;; ?while) _")
proof -
  let ?sum = "\<lambda>k. SUMM j<k. j"
  let ?inv = "\<lambda>s i. s = ?sum i"

  have "\<Gamma>\<turnstile> \<lbrace>True\<rbrace> \<acute>S :== 0;; \<acute>I :== 1 \<lbrace>?inv \<acute>S \<acute>I\<rbrace>"
  proof -
    have "True \<longrightarrow> 0 = ?sum 1"
      by simp
    also have "\<Gamma>\<turnstile> \<lbrace>\<dots>\<rbrace> \<acute>S :== 0;; \<acute>I :== 1 \<lbrace>?inv \<acute>S \<acute>I\<rbrace>"
      by vcg
    finally show ?thesis .
  qed
  also have "\<Gamma>\<turnstile> \<lbrace>?inv \<acute>S \<acute>I\<rbrace> ?while \<lbrace>?inv \<acute>S \<acute>I \<and> \<not> \<acute>I \<noteq> n\<rbrace>"
  proof
    let ?body = "\<acute>S :== \<acute>S + \<acute>I;; \<acute>I :== \<acute>I + 1"
    have "\<And>s i. ?inv s i \<and> i \<noteq> n \<longrightarrow>  ?inv (s + i) (i + 1)"
      by simp
    also have "\<Gamma>\<turnstile> \<lbrace>\<acute>S + \<acute>I = ?sum (\<acute>I + 1)\<rbrace> ?body \<lbrace>?inv \<acute>S \<acute>I\<rbrace>"
      by vcg
    finally show "\<Gamma>\<turnstile> \<lbrace>?inv \<acute>S \<acute>I \<and> \<acute>I \<noteq> n\<rbrace> ?body \<lbrace>?inv \<acute>S \<acute>I\<rbrace>" .
  qed
  also have "\<And>s i. s = ?sum i \<and> \<not> i \<noteq> n \<longrightarrow> s = ?sum n"
    by simp
  finally show ?thesis .
qed

text \<open>
 The next version uses the \<open>vcg\<close> method, while still explaining
 the resulting proof obligations in an abstract, structured manner.
\<close>

theorem "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>
           \<acute>S :== 0;; \<acute>I :== 1;;
           WHILE \<acute>I \<noteq> n
           INV \<lbrace>\<acute>S = (SUMM j<\<acute>I. j)\<rbrace>
           DO
             \<acute>S :== \<acute>S + \<acute>I;;
             \<acute>I :== \<acute>I + 1
           OD
          \<lbrace>\<acute>S = (SUMM j<n. j)\<rbrace>"
proof -
  let ?sum = "\<lambda>k. SUMM j<k. j"
  let ?inv = "\<lambda>s i. s = ?sum i"

  show ?thesis
  proof vcg
    show "?inv 0 1" by simp
  next
    fix i s assume "?inv s i" "i \<noteq> n"
    thus "?inv (s + i) (i + 1)" by simp
  next
    fix i s assume x: "?inv s i" "\<not> i \<noteq> n"
    thus "s = ?sum n" by simp
  qed
qed

text \<open>
 Certainly, this proof may be done fully automatically as well, provided
 that the invariant is given beforehand.
\<close>

theorem "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>
           \<acute>S :== 0;; \<acute>I :== 1;;
           WHILE \<acute>I \<noteq> n
           INV \<lbrace>\<acute>S = (SUMM j<\<acute>I. j)\<rbrace>
           DO
             \<acute>S :== \<acute>S + \<acute>I;;
             \<acute>I :== \<acute>I + 1
           OD
           \<lbrace>\<acute>S = (SUMM j<n. j)\<rbrace>"
  apply vcg
  apply auto
  done

subsection \<open>SWITCH\<close>

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> SWITCH \<acute>B
                        {True} \<Rightarrow> \<acute>N :== 6
                      | {False} \<Rightarrow> \<acute>N :== 7
                     END
          \<lbrace>\<acute>N > 5\<rbrace>"
apply vcg
apply simp
done

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> SWITCH \<acute>N
                        {v. v < 5} \<Rightarrow> \<acute>N :== 6
                      | {v. v \<ge> 5} \<Rightarrow> \<acute>N :== 7
                     END
          \<lbrace>\<acute>N > 5\<rbrace>"
apply vcg
apply simp
done

subsection \<open>(Mutually) Recursive Procedures\<close>

subsubsection \<open>Factorial\<close>

text \<open>We want to define a procedure for the factorial. We first
define a HOL functions that calculates it to specify the procedure later on.
\<close>

primrec fac:: "nat \<Rightarrow> nat"
where
"fac 0 = 1" |
"fac (Suc n) = (Suc n) * fac n"

lemma fac_simp [simp]: "0 < i \<Longrightarrow>  fac i = i * fac (i - 1)"
  by (cases i) simp_all

text \<open>Now we define the procedure\<close>

procedures
  Fac (N|R) = "IF \<acute>N = 0 THEN \<acute>R :== 1
                       ELSE \<acute>R :== CALL Fac(\<acute>N - 1);;
                            \<acute>R :== \<acute>N * \<acute>R
                       FI"



text \<open>A procedure is given by the signature of the procedure
followed by the procedure body.
The signature consists of the name of the procedure and a list of
parameters. The parameters in front of the pipe \<open>|\<close> are value parameters
and behind the pipe are the result parameters. Value parameters model call by value
semantics. The value of a result parameter at the end of the procedure is passed back
to the caller.
\<close>



text \<open>
Behind the scenes the \<open>procedures\<close> command provides us convenient syntax
for procedure calls, defines a constant for the procedure body
(named @{term "Fac_body"}) and creates some locales. The purpose of locales
is to set up logical contexts to support modular reasoning.
A locale is named \<open>Fac_impl\<close> and extends the \<open>hoare\<close> locale
with a theorem @{term "\<Gamma> ''Fac'' = Fac_body"} that simply states how the
procedure is defined in the procedure context. Check out the locales.
The purpose of the locales is to give us easy means to setup the context
in which we will prove programs correct.
In these locales the procedure context @{term "\<Gamma>"} is fixed.
So always use this letter in procedure
specifications. This is crucial, if we later on prove some tuples under the
assumption of some procedure specifications.
\<close>

thm Fac_body.Fac_body_def
print_locale Fac_impl

text \<open>
To see how a call is syntactically translated you can switch off the
printing translation via the configuration option \<open>hoare_use_call_tr'\<close>
\<close>

context Fac_impl
begin
text \<open>
@{term "CALL Fac(\<acute>N,\<acute>M)"} is internally:
\<close>
declare [[hoare_use_call_tr' = false]]
text \<open>
@{term "CALL Fac(\<acute>N,\<acute>M)"}
\<close>
term "CALL Fac(\<acute>N,\<acute>M)"
declare [[hoare_use_call_tr' = true]]
end

text \<open>
Now let us prove that @{term "Fac"} meets its specification.
\<close>

text \<open>
Procedure specifications are ordinary Hoare tuples. We use the parameterless
call for the specification; \<open>\<acute>R :== PROC Fac(\<acute>N)\<close> is syntactic sugar
for \<open>Call ''Fac''\<close>. This emphasises that the specification
describes the internal behaviour of the procedure, whereas parameter passing
corresponds to the procedure call.
\<close>


lemma (in Fac_impl)
  shows "\<forall>n. \<Gamma>,\<Theta>\<turnstile>\<lbrace>\<acute>N=n\<rbrace>  PROC Fac(\<acute>N,\<acute>R) \<lbrace>\<acute>R = fac n\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply vcg
  apply simp
  done


text \<open>
Since the factorial was implemented recursively,
the main ingredient of this proof is, to assume that the specification holds for
the recursive call of @{term Fac} and prove the body correct.
The assumption for recursive calls is added to the context by
the rule @{thm [source] HoarePartial.ProcRec1}
(also derived from general rule for mutually recursive procedures):
@{thm [display] HoarePartial.ProcRec1 [no_vars]}
The verification condition generator will infer the specification out of the
context when it encounters a recursive call of the factorial.
\<close>

text \<open>We can also step through verification condition generation. When
the verification condition generator encounters a procedure call it tries to
use the rule \<open>ProcSpec\<close>. To be successful there must be a specification
of the procedure in the context.
\<close>

lemma (in Fac_impl)
  shows "\<forall>n. \<Gamma>\<turnstile>\<lbrace>\<acute>N=n\<rbrace> \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac n\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply vcg_step
  apply   vcg_step
  apply  vcg_step
  apply vcg_step
  apply vcg_step
  apply simp
  done


text \<open>Here some Isar style version of the proof\<close>
lemma (in Fac_impl)
  shows "\<forall>n. \<Gamma>\<turnstile>\<lbrace>\<acute>N=n\<rbrace> \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac n\<rbrace>"
proof (hoare_rule HoarePartial.ProcRec1)
  have Fac_spec: "\<forall>n. \<Gamma>,(\<Union>n. {(\<lbrace>\<acute>N=n\<rbrace>, Fac_'proc, \<lbrace>\<acute>R = fac n\<rbrace>,{})})
                       \<turnstile> \<lbrace>\<acute>N=n\<rbrace> \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac n\<rbrace>"
    apply (rule allI)
    apply (rule hoarep.Asm)
    by auto
  show "\<forall>n. \<Gamma>,(\<Union>n. {(\<lbrace>\<acute>N=n\<rbrace>, Fac_'proc, \<lbrace>\<acute>R = fac n\<rbrace>,{})})
            \<turnstile> \<lbrace>\<acute>N=n\<rbrace> IF \<acute>N = 0 THEN \<acute>R :== 1
            ELSE \<acute>R :== CALL Fac(\<acute>N - 1);; \<acute>R :== \<acute>N * \<acute>R FI \<lbrace>\<acute>R = fac n\<rbrace>"
    apply vcg
    apply simp
    done
qed

text \<open>To avoid retyping of potentially large pre and postconditions in
the previous proof we can use the casual term abbreviations of the Isar
language.
\<close>

lemma (in Fac_impl)
  shows "\<forall>n. \<Gamma>\<turnstile>\<lbrace>\<acute>N=n\<rbrace> \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac n\<rbrace>"
  (is "\<forall>n. \<Gamma>\<turnstile>(?Pre n) ?Fac (?Post n)")
proof (hoare_rule HoarePartial.ProcRec1)
  have Fac_spec: "\<forall>n. \<Gamma>,(\<Union>n. {(?Pre n, Fac_'proc, ?Post n,{})})
                       \<turnstile>(?Pre n) ?Fac (?Post n)"
    apply (rule allI)
    apply (rule hoarep.Asm)
    by auto
  show "\<forall>n. \<Gamma>,(\<Union>n. {(?Pre n, Fac_'proc, ?Post n,{})})
            \<turnstile> (?Pre n) IF \<acute>N = 0 THEN \<acute>R :== 1
            ELSE \<acute>R :== CALL Fac(\<acute>N - 1);; \<acute>R :== \<acute>N * \<acute>R FI (?Post n)"
    apply vcg
    apply simp
    done
qed

text \<open>The previous proof pattern has still some kind of inconvenience.
The augmented context is always printed in the proof state. That can
mess up the state, especially if we have large specifications. This may
be annoying if we want to develop single step or structured proofs. In this
case it can be a good idea to introduce a new variable for the augmented
context.
\<close>

lemma (in Fac_impl) Fac_spec:
  shows "\<forall>n. \<Gamma>\<turnstile>\<lbrace>\<acute>N=n\<rbrace> \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac n\<rbrace>"
  (is "\<forall>n. \<Gamma>\<turnstile>(?Pre n) ?Fac (?Post n)")
proof (hoare_rule HoarePartial.ProcRec1)
  define \<Theta>' where "\<Theta>' = (\<Union>n. {(?Pre n, Fac_'proc, ?Post n,{}::('a, 'b) vars_scheme set)})"
  have Fac_spec: "\<forall>n. \<Gamma>,\<Theta>'\<turnstile>(?Pre n) ?Fac (?Post n)"
    by (unfold \<Theta>'_def, rule allI, rule hoarep.Asm) auto
  txt \<open>We have to name the fact \<open>Fac_spec\<close>, so that the vcg can
   use the specification for the recursive call, since it cannot infer it
   from the opaque @{term "\<Theta>'"}.\<close>
  show "\<forall>\<sigma>. \<Gamma>,\<Theta>'\<turnstile> (?Pre \<sigma>) IF \<acute>N = 0 THEN \<acute>R :== 1
            ELSE \<acute>R :== CALL Fac(\<acute>N - 1);; \<acute>R :== \<acute>N * \<acute>R FI (?Post \<sigma>)"
    apply vcg
    apply simp
    done
qed

text \<open>There are different rules available to prove procedure calls,
depending on the kind of postcondition and whether or not the
procedure is recursive or even mutually recursive.
See for example @{thm [source] HoarePartial.ProcRec1},
@{thm [source] HoarePartial.ProcNoRec1}.
They are all derived from the most general rule
@{thm [source] HoarePartial.ProcRec}.
All of them have some side-condition concerning definedness of the procedure.
They can be
solved in a uniform fashion. Thats why we have created the method
\<open>hoare_rule\<close>, which behaves like the method \<open>rule\<close> but automatically
tries to solve the side-conditions.
\<close>

subsubsection \<open>Odd and Even\<close>

text \<open>Odd and even are defined mutually recursive here. In the
\<open>procedures\<close> command we conjoin both definitions with \<open>and\<close>.
\<close>

procedures
 odd(N | A) = "IF \<acute>N=0 THEN \<acute>A:==0
                     ELSE IF \<acute>N=1 THEN CALL even (\<acute>N - 1,\<acute>A)
                          ELSE CALL odd (\<acute>N - 2,\<acute>A)
                          FI
                     FI"


and
  even(N | A) = "IF \<acute>N=0 THEN \<acute>A:==1
                        ELSE IF \<acute>N=1 THEN CALL odd (\<acute>N - 1,\<acute>A)
                             ELSE CALL even (\<acute>N - 2,\<acute>A)
                             FI
                        FI"

print_theorems
thm odd_body.odd_body_def
thm even_body.even_body_def
print_locale odd_even_clique


text \<open>To prove the procedure calls to @{term "odd"} respectively
@{term "even"} correct we first derive a rule to justify that we
can assume both specifications to verify the bodies. This rule can
be derived from the general @{thm [source] HoarePartial.ProcRec} rule. An ML function does
this work:
\<close>

ML \<open>ML_Thms.bind_thm ("ProcRec2", Hoare.gen_proc_rec @{context} Hoare.Partial 2)\<close>


lemma (in odd_even_clique)
  shows odd_spec: "\<forall>n. \<Gamma>\<turnstile>\<lbrace>\<acute>N=n\<rbrace> \<acute>A :== PROC odd(\<acute>N)
                  \<lbrace>(\<exists>b. n = 2 * b + \<acute>A) \<and> \<acute>A < 2 \<rbrace>" (is ?P1)
   and even_spec: "\<forall>n. \<Gamma>\<turnstile>\<lbrace>\<acute>N=n\<rbrace> \<acute>A :== PROC even(\<acute>N)
                  \<lbrace>(\<exists>b. n + 1 = 2 * b + \<acute>A) \<and> \<acute>A < 2 \<rbrace>" (is ?P2)
proof -
  have "?P1 \<and> ?P2"
    apply (hoare_rule ProcRec2)
    apply  vcg
    apply  clarsimp
    apply  (rule_tac x="b + 1" in exI)
    apply  arith
    apply vcg
    apply clarsimp
    apply arith
    done
  thus "?P1" "?P2"
    by iprover+
qed

subsection \<open>Expressions With Side Effects\<close>


text \<open>\texttt{R := N++ + M++}\<close>
lemma "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>
  \<acute>N \<ggreater> n. \<acute>N :== \<acute>N + 1 \<ggreater>
  \<acute>M \<ggreater> m. \<acute>M :== \<acute>M + 1 \<ggreater>
  \<acute>R :== n + m
  \<lbrace>\<acute>R = \<acute>N + \<acute>M - 2\<rbrace>"
apply vcg
apply simp
done

text \<open>\texttt{R := Fac (N) + Fac (M)}\<close>
lemma (in Fac_impl) shows
  "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>
  CALL Fac(\<acute>N) \<ggreater> n. CALL Fac(\<acute>M) \<ggreater> m.
  \<acute>R :== n + m
  \<lbrace>\<acute>R = fac \<acute>N + fac \<acute>M\<rbrace>"
apply vcg
done


text \<open>\texttt{ R := (Fac(Fac (N)))}\<close>
lemma (in Fac_impl) shows
  "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>
  CALL Fac(\<acute>N) \<ggreater> n. CALL Fac(n) \<ggreater> m.
  \<acute>R :== m
  \<lbrace>\<acute>R = fac (fac \<acute>N)\<rbrace>"
apply vcg
done


subsection \<open>Global Variables and Heap\<close>


text \<open>
Now we define and verify some procedures on heap-lists. We consider
list structures consisting of two fields, a content element @{term "cont"} and
a reference to the next list element @{term "next"}. We model this by the
following state space where every field has its own heap.
\<close>

record globals_list =
  next_' :: "ref \<Rightarrow> ref"
  cont_' :: "ref \<Rightarrow> nat"

record 'g list_vars = "'g state" +
  p_'    :: "ref"
  q_'    :: "ref"
  r_'    :: "ref"
  root_' :: "ref"
  tmp_'  :: "ref"

text \<open>Updates to global components inside a procedure will
always be propagated to the caller. This is implicitly done by the
parameter passing syntax translations. The record containing the global variables must begin with the prefix "globals".
\<close>

text \<open>We first define an append function on lists. It takes two
references as parameters. It appends the list referred to by the first
parameter with the list referred to by the second parameter, and returns
the result right into the first parameter.
\<close>

procedures
  append(p,q|p) =
    "IF \<acute>p=Null THEN \<acute>p :== \<acute>q ELSE \<acute>p \<rightarrow>\<acute>next:== CALL append(\<acute>p\<rightarrow>\<acute>next,\<acute>q) FI"

(*
  append_spec:
   "\<forall>\<sigma> Ps Qs.
     \<Gamma>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {}\<rbrace>
           \<acute>p :== PROC append(\<acute>p,\<acute>q)
         \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"

  append_modifies:
   "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC append(\<acute>p,\<acute>q){t. t may_only_modify_globals \<sigma> in [next]}"
*)

context append_impl
begin
declare [[hoare_use_call_tr' = false]]
term "CALL append(\<acute>p,\<acute>q,\<acute>p\<rightarrow>\<acute>next)"
declare [[hoare_use_call_tr' = true]]
end
text \<open>Below we give two specifications this time.
One captures the functional behaviour and focuses on the
entities that are potentially modified by the procedure, the other one
is a pure frame condition.
The list in the modifies clause has to list all global state components that
may be changed by the procedure. Note that we know from the modifies clause
that the @{term cont} parts of the lists will not be changed. Also a small
side note on the syntax. We use ordinary brackets in the postcondition
of the modifies clause, and also the state components do not carry the
acute, because we explicitly note the state @{term t} here.

The functional specification now introduces two logical variables besides the
state space variable @{term "\<sigma>"}, namely @{term "Ps"} and @{term "Qs"}.
They are universally quantified and range over both the pre and the postcondition, so
that we are able to properly instantiate the specification
during the proofs. The syntax \<open>\<lbrace>\<sigma>. \<dots>\<rbrace>\<close> is a shorthand to fix the current
state: \<open>{s. \<sigma> = s \<dots>}\<close>.
\<close>

lemma (in append_impl) append_spec:
  shows "\<forall>\<sigma> Ps Qs. \<Gamma>\<turnstile>
            \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {}\<rbrace>
                \<acute>p :== PROC append(\<acute>p,\<acute>q)
            \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply vcg
  apply fastforce
  done


text \<open>The modifies clause is equal to a proper record update specification
of the following form.
\<close>


lemma "{t. t may_only_modify_globals Z in [next]}
       =
       {t. \<exists>next. globals t=next_'_update (\<lambda>_. next) (globals Z)}"
  apply (unfold mex_def meq_def)
  apply (simp)
  done

text \<open>If the verification condition generator works on a procedure call
it checks whether it can find a modified clause in the context. If one
is present the procedure call is simplified before the Hoare rule
@{thm [source] HoarePartial.ProcSpec} is applied. Simplification of the procedure call means,
that the ``copy back'' of the global components is simplified. Only those
components that occur in the modifies clause will actually be copied back.
This simplification is justified by the rule @{thm [source] HoarePartial.ProcModifyReturn}.
So after this simplification all global components that do not appear in
the modifies clause will be treated as local variables.
\<close>

text \<open>You can study the effect of the modifies clause on the following two
examples, where we want to prove that @{term "append"} does not change
the @{term "cont"} part of the heap.
\<close>

lemma (in append_impl)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>p=Null \<and> \<acute>cont=c\<rbrace> \<acute>p :== CALL append(\<acute>p,Null) \<lbrace>\<acute>cont=c\<rbrace>"
  apply vcg
  oops

text \<open>To prove the frame condition,
we have to tell the verification condition generator to use only the
modifies clauses and not to search for functional specifications by
the parameter \<open>spec=modifies\<close> It will also try to solve the
verification conditions automatically.
\<close>

lemma (in append_impl) append_modifies:
  shows
   "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC append(\<acute>p,\<acute>q){t. t may_only_modify_globals \<sigma> in [next]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done


lemma (in append_impl)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>p=Null \<and> \<acute>cont=c\<rbrace> \<acute>p\<rightarrow>\<acute>next :== CALL append(\<acute>p,Null) \<lbrace>\<acute>cont=c\<rbrace>"
  apply vcg
  apply simp
  done

text \<open>
Of course we could add the modifies clause to the functional specification as
well. But separating both has the advantage that we split up the verification
work. We can make use of the modifies clause before we apply the
functional specification in a fully automatic fashion.
\<close>


text \<open>To verify the body of @{term "append"} we do not need the modifies
clause, since the specification does not talk about @{term "cont"} at all, and
we don't access @{term "cont"} inside the body. This may be different for
more complex procedures.
\<close>

text \<open>
To prove that a procedure respects the modifies clause, we only need
the modifies clauses of the procedures called in the body. We do not need
the functional specifications. So we can always prove the modifies
clause without functional specifications, but me may need the modifies
clause to prove the functional specifications.
\<close>








subsubsection \<open>Insertion Sort\<close>

primrec sorted:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list  \<Rightarrow> bool"
where
"sorted le [] = True" |
"sorted le (x#xs) = ((\<forall>y\<in>set xs. le x y) \<and> sorted le xs)"



procedures
  insert(r,p | p) =
    "IF \<acute>r=Null THEN SKIP
     ELSE IF \<acute>p=Null THEN \<acute>p :== \<acute>r;; \<acute>p\<rightarrow>\<acute>next :== Null
          ELSE IF \<acute>r\<rightarrow>\<acute>cont \<le> \<acute>p\<rightarrow>\<acute>cont
               THEN \<acute>r\<rightarrow>\<acute>next :== \<acute>p;; \<acute>p:==\<acute>r
               ELSE \<acute>p\<rightarrow>\<acute>next :== CALL insert(\<acute>r,\<acute>p\<rightarrow>\<acute>next)
               FI
          FI
     FI"


text \<open>
In the postcondition of the functional specification there is a small but
important subtlety. Whenever we talk about the @{term "cont"} part we refer to
the one of the pre-state, even in the conclusion of the implication.
The reason is, that we have separated out, that @{term "cont"} is not modified
by the procedure, to the modifies clause. So whenever we talk about unmodified
parts in the postcondition we have to use the pre-state part, or explicitly
state an equality in the postcondition.
The reason is simple. If the postcondition would talk about \<open>\<acute>cont\<close>
instead of \<open>\<^bsup>\<sigma>\<^esup>cont\<close>, we get a new instance of \<open>cont\<close> during
verification and the postcondition would only state something about this
new instance. But as the verification condition generator uses the
modifies clause the caller of \<open>insert\<close> instead still has the
old \<open>cont\<close> after the call. Thats the very reason for the modifies clause.
So the caller and the specification will simply talk about two different things,
without being able to relate them (unless an explicit equality is added to
the specification).
\<close>

lemma (in insert_impl) insert_modifies:
  "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC insert(\<acute>r,\<acute>p){t. t may_only_modify_globals \<sigma> in [next]}"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done


lemma (in insert_impl) insert_spec:
    "\<forall>\<sigma> Ps . \<Gamma>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and> sorted (\<le>) (map \<acute>cont Ps) \<and>
                  \<acute>r \<noteq> Null \<and> \<acute>r \<notin> set Ps\<rbrace>
         \<acute>p :== PROC insert(\<acute>r,\<acute>p)
   \<lbrace>\<exists>Qs. List \<acute>p \<acute>next Qs \<and> sorted (\<le>) (map \<^bsup>\<sigma>\<^esup>cont  Qs) \<and>
           set Qs = insert \<^bsup>\<sigma>\<^esup>r (set Ps) \<and>
           (\<forall>x. x \<notin> set Qs \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"

apply (hoare_rule HoarePartial.ProcRec1)
apply vcg
apply (intro conjI impI)
apply    fastforce
apply   fastforce
apply  fastforce
apply (clarsimp)
apply force
done

procedures
  insertSort(p | p) =
    "\<acute>r:==Null;;
     WHILE (\<acute>p \<noteq> Null) DO
       \<acute>q :== \<acute>p;;
       \<acute>p :== \<acute>p\<rightarrow>\<acute>next;;
       \<acute>r :== CALL insert(\<acute>q,\<acute>r)
     OD;;
     \<acute>p:==\<acute>r"




lemma (in insertSort_impl) insertSort_modifies:
  shows
   "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC insertSort(\<acute>p)
              {t. t may_only_modify_globals \<sigma> in [next]}"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done


text \<open>Insertion sort is not implemented recursively here but with a while
loop. Note that the while loop is not annotated with an invariant in the
procedure definition. The invariant only comes into play during verification.
Therefore we will annotate the body during the proof with the
rule @{thm [source] HoarePartial.annotateI}.
\<close>


lemma (in insertSort_impl) insertSort_body_spec:
  shows "\<forall>\<sigma> Ps. \<Gamma>,\<Theta>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<rbrace>
              \<acute>p :== PROC insertSort(\<acute>p)
          \<lbrace>\<exists>Qs. List \<acute>p \<acute>next Qs \<and> sorted (\<le>) (map \<^bsup>\<sigma>\<^esup>cont Qs) \<and>
           set Qs = set Ps\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (hoare_rule anno=
         "\<acute>r :== Null;;
         WHILE \<acute>p \<noteq> Null
         INV \<lbrace>\<exists>Qs Rs. List \<acute>p \<acute>next Qs \<and> List \<acute>r \<acute>next Rs \<and>
                  set Qs \<inter> set Rs = {} \<and>
                  sorted (\<le>) (map \<acute>cont Rs) \<and> set Qs \<union> set Rs = set Ps \<and>
                  \<acute>cont = \<^bsup>\<sigma>\<^esup>cont \<rbrace>
          DO \<acute>q :== \<acute>p;; \<acute>p :== \<acute>p\<rightarrow>\<acute>next;; \<acute>r :== CALL insert(\<acute>q,\<acute>r) OD;;
          \<acute>p :== \<acute>r" in HoarePartial.annotateI)
  apply vcg
  apply   fastforce
  prefer 2
  apply  fastforce
  apply (clarsimp)
  apply (rule_tac x=ps in exI)
  apply (intro conjI)
  apply    (rule heap_eq_ListI1)
  apply     assumption
  apply    clarsimp
  apply    (subgoal_tac "x\<noteq>p \<and> x \<notin> set Rs")
  apply     auto
  done

subsubsection "Memory Allocation and Deallocation"

text \<open>The basic idea of memory management is to keep a list of allocated
references in the state space. Allocation of a new reference adds a
new reference to the list deallocation removes a reference. Moreover
we keep a counter "free" for the free memory.
\<close>

record globals_list_alloc = globals_list +
  alloc_'::"ref list"
  free_'::nat

record 'g list_vars' = "'g list_vars" +
  i_'::nat
  first_'::ref


definition "sz = (2::nat)"

text \<open>Restrict locale \<open>hoare\<close> to the required type.\<close>

locale hoare_ex =
  hoare \<Gamma> for \<Gamma> :: "'c \<rightharpoonup> (('a globals_list_alloc_scheme, 'b) list_vars'_scheme, 'c, 'd) com"

lemma (in hoare_ex)
  "\<Gamma>\<turnstile> \<lbrace>\<acute>i = 0 \<and> \<acute>first = Null \<and> n*sz \<le> \<acute>free\<rbrace>
       WHILE \<acute>i < n
       INV \<lbrace>\<exists>Ps. List \<acute>first \<acute>next Ps \<and> length Ps = \<acute>i \<and> \<acute>i \<le> n \<and>
             set Ps \<subseteq> set \<acute>alloc \<and> (n - \<acute>i)*sz \<le> \<acute>free\<rbrace>
       DO
         \<acute>p :== NEW sz [\<acute>cont:==0,\<acute>next:== Null];;
         \<acute>p\<rightarrow>\<acute>next :== \<acute>first;;
         \<acute>first :== \<acute>p;;
         \<acute>i :== \<acute>i+ 1
       OD
       \<lbrace>\<exists>Ps. List \<acute>first \<acute>next  Ps \<and> length Ps = n \<and> set Ps \<subseteq> set \<acute>alloc\<rbrace>"

apply (vcg)
apply   simp
apply  clarsimp
apply  (rule conjI)
apply   clarsimp
apply   (rule_tac x="new (set alloc)#Ps" in exI)
apply   clarsimp
apply   (rule conjI)
apply    fastforce
apply   (simp add: sz_def)
apply  (simp add: sz_def)
apply fastforce
done


lemma (in hoare_ex)
  "\<Gamma>\<turnstile> \<lbrace>\<acute>i = 0 \<and> \<acute>first = Null \<and> n*sz \<le> \<acute>free\<rbrace>
       WHILE \<acute>i < n
       INV \<lbrace>\<exists>Ps. List \<acute>first \<acute>next Ps \<and> length Ps = \<acute>i \<and> \<acute>i \<le> n \<and>
             set Ps \<subseteq> set \<acute>alloc \<and> (n - \<acute>i)*sz \<le> \<acute>free\<rbrace>
       DO
         \<acute>p :== NNEW sz [\<acute>cont:==0,\<acute>next:== Null];;
         \<acute>p\<rightarrow>\<acute>next :== \<acute>first;;
         \<acute>first :== \<acute>p;;
         \<acute>i :== \<acute>i+ 1
       OD
       \<lbrace>\<exists>Ps. List \<acute>first \<acute>next  Ps \<and> length Ps = n \<and> set Ps \<subseteq> set \<acute>alloc\<rbrace>"

apply (vcg)
apply   simp
apply  clarsimp
apply  (rule conjI)
apply   clarsimp
apply   (rule_tac x="new (set alloc)#Ps" in exI)
apply   clarsimp
apply   (rule conjI)
apply    fastforce
apply   (simp add: sz_def)
apply  (simp add: sz_def)
apply fastforce
done

subsection \<open>Fault Avoiding Semantics\<close>

text \<open>
If we want to ensure that no runtime errors occur we can insert guards into
the code. We will not be able to prove any nontrivial Hoare triple
about code with guards, if we cannot show that the guards will never fail.
A trivial hoare triple is one with an empty precondition.
\<close>


lemma "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>  \<lbrace>\<acute>p\<noteq>Null\<rbrace>\<longmapsto> \<acute>p\<rightarrow>\<acute>next :== \<acute>p \<lbrace>True\<rbrace>"
apply vcg
oops

lemma "\<Gamma>\<turnstile> {}  \<lbrace>\<acute>p\<noteq>Null\<rbrace>\<longmapsto> \<acute>p\<rightarrow>\<acute>next :== \<acute>p \<lbrace>True\<rbrace>"
apply vcg
done

text \<open>Let us consider this small program that reverts a list. At
first without guards.
\<close>
lemma (in hoare_ex) rev_strip:
  "\<Gamma>\<turnstile> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and>
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;;
     \<acute>p :== \<acute>p\<rightarrow> \<acute>next;;
     \<acute>r\<rightarrow>\<acute>next :== \<acute>q;;
     \<acute>q :== \<acute>r OD
  \<lbrace>List \<acute>q \<acute>next (rev Ps @ Qs) \<and> set Ps\<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>"
apply (vcg)
apply fastforce+
done

text \<open>If we want to ensure that we do not dereference @{term "Null"} or
access unallocated memory, we have to add some guards.
\<close>

locale hoare_ex_guard =
  hoare \<Gamma> for \<Gamma> :: "'c \<rightharpoonup> (('a globals_list_alloc_scheme, 'b) list_vars'_scheme, 'c, bool) com"

lemma
  (in hoare_ex_guard)
  "\<Gamma>\<turnstile> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and>
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;;
     \<lbrace>\<acute>p\<noteq>Null \<and> \<acute>p\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>p :== \<acute>p\<rightarrow> \<acute>next;;
     \<lbrace>\<acute>r\<noteq>Null \<and> \<acute>r\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>q;;
     \<acute>q :== \<acute>r OD
 \<lbrace>List \<acute>q \<acute>next (rev Ps @ Qs) \<and> set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>"
apply (vcg)
apply fastforce+
done


text \<open>We can also just prove that no faults will occur, by giving the
trivial postcondition.
\<close>
lemma (in hoare_ex_guard) rev_noFault:
  "\<Gamma>\<turnstile> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and>
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;;
     \<lbrace>\<acute>p\<noteq>Null \<and> \<acute>p\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>p :== \<acute>p\<rightarrow> \<acute>next;;
     \<lbrace>\<acute>r\<noteq>Null \<and> \<acute>r\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>q;;
     \<acute>q :== \<acute>r OD
  UNIV,UNIV"
apply (vcg)
apply fastforce+
done

lemma (in hoare_ex_guard) rev_moduloGuards:
  "\<Gamma>\<turnstile>\<^bsub>/{True}\<^esub> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and>
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;;
     \<lbrace>\<acute>p\<noteq>Null \<and> \<acute>p\<in>set \<acute>alloc\<rbrace>\<surd> \<longmapsto> \<acute>p :== \<acute>p\<rightarrow> \<acute>next;;
     \<lbrace>\<acute>r\<noteq>Null \<and> \<acute>r\<in>set \<acute>alloc\<rbrace>\<surd> \<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>q;;
     \<acute>q :== \<acute>r OD
 \<lbrace>List \<acute>q \<acute>next (rev Ps @ Qs) \<and> set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>"
apply vcg
apply fastforce+
done




lemma CombineStrip':
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c' Q,A"
  assumes deriv_strip: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c'' UNIV,UNIV"
  assumes c'': "c''= mark_guards False (strip_guards (-F) c')"
  assumes c: "c = mark_guards False c'"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c Q,A"
proof -
  from deriv_strip [simplified c'']
  have "\<Gamma>,\<Theta>\<turnstile> P (strip_guards (- F) c') UNIV,UNIV"
    by (rule HoarePartialProps.MarkGuardsD)
  with deriv
  have "\<Gamma>,\<Theta>\<turnstile> P c' Q,A"
    by (rule HoarePartialProps.CombineStrip)
  hence "\<Gamma>,\<Theta>\<turnstile> P mark_guards False c' Q,A"
    by (rule HoarePartialProps.MarkGuardsI)
  thus ?thesis
    by (simp add: c)
qed


text \<open>We can then combine the prove that no fault will occur with the
functional proof of the programme without guards to get the full prove by
the rule @{thm HoarePartialProps.CombineStrip}
\<close>


lemma
  (in hoare_ex_guard)
  "\<Gamma>\<turnstile> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and>
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;;
     \<lbrace>\<acute>p\<noteq>Null \<and> \<acute>p\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>p :== \<acute>p\<rightarrow> \<acute>next;;
     \<lbrace>\<acute>r\<noteq>Null \<and> \<acute>r\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>q;;
     \<acute>q :== \<acute>r OD
 \<lbrace>List \<acute>q \<acute>next (rev Ps @ Qs) \<and> set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>"

apply (rule CombineStrip' [OF rev_moduloGuards rev_noFault])
apply  simp
apply simp
done


text \<open>In the previous example the effort to split up the prove did not
really pay off. But when we think of programs with a lot of guards and
complicated specifications it may be better to first focus on a prove without
the messy guards. Maybe it is possible to automate the no fault proofs so
that it suffices to focus on the stripped program.
\<close>


text \<open>
The purpose of guards is to watch for faults that can occur during
evaluation of expressions. In the example before we watched for null pointer
dereferencing or memory faults. We can also look for array index bounds or
division by zero. As the condition of a while loop is evaluated in each
iteration we cannot just add a guard before the while loop. Instead we need
a special guard for the condition.
Example: @{term "WHILE  \<lbrace>\<acute>p\<noteq>Null\<rbrace>\<longmapsto> \<acute>p\<rightarrow>\<acute>next\<noteq>Null DO SKIP OD"}
\<close>

subsection \<open>Circular Lists\<close>
definition
  distPath :: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> ref \<Rightarrow> ref list \<Rightarrow> bool" where
  "distPath x next y as = (Path x next y as  \<and>  distinct as)"

lemma neq_dP: "\<lbrakk>p \<noteq> q; Path p h q Ps; distinct Ps\<rbrakk> \<Longrightarrow>
 \<exists>Qs. p\<noteq>Null \<and> Ps = p#Qs \<and> p \<notin> set Qs"
by (cases Ps, auto)

lemma circular_list_rev_I:
  "\<Gamma>\<turnstile> \<lbrace>\<acute>root = r \<and>  distPath \<acute>root \<acute>next \<acute>root (r#Ps)\<rbrace>
   \<acute>p :== \<acute>root;; \<acute>q :== \<acute>root\<rightarrow>\<acute>next;;
  WHILE \<acute>q \<noteq> \<acute>root
  INV \<lbrace>\<exists> ps qs. distPath \<acute>p \<acute>next \<acute>root ps  \<and> distPath \<acute>q \<acute>next \<acute>root qs \<and>
             \<acute>root = r \<and> r\<noteq>Null \<and> r \<notin> set Ps  \<and> set ps \<inter> set qs = {} \<and>
             Ps = (rev ps) @ qs \<rbrace>
  DO \<acute>tmp :== \<acute>q;; \<acute>q :== \<acute>q\<rightarrow>\<acute>next;; \<acute>tmp\<rightarrow>\<acute>next :== \<acute>p;; \<acute>p:==\<acute>tmp OD;;
  \<acute>root\<rightarrow>\<acute>next :== \<acute>p
  \<lbrace>\<acute>root = r \<and> distPath \<acute>root \<acute>next \<acute>root (r#rev Ps)\<rbrace>"
apply (simp only:distPath_def)
apply vcg
apply   (rule_tac x="[]" in exI)
apply   fastforce
apply  clarsimp
apply  (drule (2) neq_dP)
apply  (rule_tac x="q # ps" in exI)
apply  clarsimp
apply fastforce
done



lemma path_is_list:"\<And>a next b. \<lbrakk>Path b next a Ps ; a \<notin> set Ps; a\<noteq>Null\<rbrakk>
\<Longrightarrow> List b (next(a := Null)) (Ps @ [a])"
apply (induct Ps)
apply (auto simp add:fun_upd_apply)
done

text \<open>
The simple algorithm for acyclic list reversal, with modified
annotations, works for cyclic lists as well.:
\<close>

lemma circular_list_rev_II:
 "\<Gamma>\<turnstile>
 \<lbrace>\<acute>p = r \<and> distPath \<acute>p \<acute>next \<acute>p (r#Ps)\<rbrace>
\<acute>q:==Null;;
WHILE \<acute>p \<noteq> Null
INV
 \<lbrace> ((\<acute>q = Null) \<longrightarrow> (\<exists>ps. distPath \<acute>p \<acute>next r ps  \<and>  ps = r#Ps)) \<and>
  ((\<acute>q \<noteq> Null) \<longrightarrow> (\<exists>ps qs. distPath \<acute>q \<acute>next r qs  \<and> List \<acute>p \<acute>next ps  \<and>
                   set ps \<inter> set qs = {} \<and> rev qs @ ps = Ps@[r])) \<and>
  \<not> (\<acute>p = Null \<and> \<acute>q = Null \<and> r = Null )
   \<rbrace>
DO
  \<acute>tmp :== \<acute>p;; \<acute>p :== \<acute>p\<rightarrow>\<acute>next;; \<acute>tmp\<rightarrow>\<acute>next :== \<acute>q;; \<acute>q:==\<acute>tmp
OD
 \<lbrace>\<acute>q = r \<and> distPath \<acute>q \<acute>next \<acute>q (r # rev Ps)\<rbrace>"

apply (simp only:distPath_def)
apply vcg
apply   clarsimp
apply  clarsimp
apply  (case_tac "(q = Null)")
apply   (fastforce intro: path_is_list)
apply  clarify
apply  (rule_tac x="psa" in exI)
apply  (rule_tac x=" p # qs" in exI)
apply  force
apply fastforce
done

text\<open>Although the above algorithm is more succinct, its invariant
looks more involved. The reason for the case distinction on @{term q}
is due to the fact that during execution, the pointer variables can
point to either cyclic or acyclic structures.
\<close>

text \<open>
When working on lists, its sometimes better to remove
@{thm[source] fun_upd_apply} from the simpset, and instead include @{thm[source] fun_upd_same} and @{thm[source] fun_upd_other} to
the simpset
\<close>

(*
declare fun_upd_apply[simp del]fun_upd_same[simp] fun_upd_other[simp]
*)


lemma "\<Gamma>\<turnstile> {\<sigma>}
            \<acute>I :== \<acute>M;;
            ANNO \<tau>. \<lbrace>\<tau>. \<acute>I = \<^bsup>\<sigma>\<^esup>M\<rbrace>
                      \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I
                    \<lbrace>\<acute>M = \<^bsup>\<tau>\<^esup>N \<and> \<acute>N = \<^bsup>\<tau>\<^esup>I\<rbrace>
            \<lbrace>\<acute>M = \<^bsup>\<sigma>\<^esup>N \<and> \<acute>N = \<^bsup>\<sigma>\<^esup>M\<rbrace>"
apply vcg
apply auto
done


lemma "\<Gamma>\<turnstile> ({\<sigma>} \<inter> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>)
      (ANNO \<tau>. ({\<tau>} \<inter> \<lbrace>\<acute>A=\<^bsup>\<sigma>\<^esup>A \<and> \<acute>I=\<^bsup>\<sigma>\<^esup>I \<and> \<acute>M=0 \<and> \<acute>S=0\<rbrace>)
      WHILE \<acute>M \<noteq> \<acute>A
      INV \<lbrace>\<acute>S = \<acute>M * \<acute>I \<and> \<acute>A=\<^bsup>\<tau>\<^esup>A \<and> \<acute>I=\<^bsup>\<tau>\<^esup>I\<rbrace>
      DO \<acute>S :== \<acute>S + \<acute>I;; \<acute>M :== \<acute>M + 1 OD
      \<lbrace>\<acute>S = \<^bsup>\<tau>\<^esup>A * \<^bsup>\<tau>\<^esup>I\<rbrace>)
      \<lbrace>\<acute>S = \<^bsup>\<sigma>\<^esup>A * \<^bsup>\<sigma>\<^esup>I\<rbrace>"
apply vcg_step
apply vcg_step
apply simp
apply vcg_step
apply vcg_step
apply simp
apply vcg
apply simp
apply simp
apply vcg_step
apply auto
done

text \<open>Instead of annotations one can also directly use previously proven lemmas.\<close>
lemma foo_lemma: "\<forall>n m. \<Gamma>\<turnstile> \<lbrace>\<acute>N = n \<and> \<acute>M = m\<rbrace> \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
                     \<lbrace>\<acute>N = n + 1 \<and> \<acute>M = m + 1\<rbrace>"
  by vcg


lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = n \<and> \<acute>M = m\<rbrace> LEMMA foo_lemma
                               \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
                             END;;
                             \<acute>N :== \<acute>N + 1
           \<lbrace>\<acute>N = n + 2 \<and> \<acute>M = m + 1\<rbrace>"
  apply vcg
  apply simp
  done

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = n \<and> \<acute>M = m\<rbrace>
           LEMMA foo_lemma
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
           END;;
           LEMMA foo_lemma
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
           END
           \<lbrace>\<acute>N = n + 2 \<and> \<acute>M = m + 2\<rbrace>"
  apply vcg
  apply simp
  done

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>N = n \<and> \<acute>M = m\<rbrace>
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1;;
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
           \<lbrace>\<acute>N = n + 2 \<and> \<acute>M = m + 2\<rbrace>"
  apply (hoare_rule anno=
          "LEMMA foo_lemma
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
           END;;
           LEMMA foo_lemma
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
           END"
          in HoarePartial.annotate_normI)
  apply vcg
  apply simp
  done

text \<open>Just some test on marked, guards\<close>
lemma "\<Gamma>\<turnstile>\<lbrace>True\<rbrace> WHILE \<lbrace>P \<acute>N \<rbrace>\<surd>, \<lbrace>Q \<acute>M\<rbrace>#, \<lbrace>R \<acute>N\<rbrace>\<longmapsto> \<acute>N < \<acute>M
                    INV \<lbrace>\<acute>N < 2\<rbrace> DO
                    \<acute>N :== \<acute>M
                  OD
           \<lbrace>hard\<rbrace>"
apply vcg
oops

lemma "\<Gamma>\<turnstile>\<^bsub>/{True}\<^esub> \<lbrace>True\<rbrace> WHILE \<lbrace>P \<acute>N \<rbrace>\<surd>, \<lbrace>Q \<acute>M\<rbrace>#, \<lbrace>R \<acute>N\<rbrace>\<longmapsto> \<acute>N < \<acute>M
                    INV \<lbrace>\<acute>N < 2\<rbrace> DO
                    \<acute>N :== \<acute>M
                  OD
           \<lbrace>hard\<rbrace>"
apply vcg
oops



term "\<Gamma>\<turnstile>\<^bsub>/{True}\<^esub> \<lbrace>True\<rbrace> WHILE\<^sub>g  \<acute>N < \<acute>Arr!i
                    FIX Z.
                    INV \<lbrace>\<acute>N < 2\<rbrace>

                  DO
                    \<acute>N :== \<acute>M
                  OD
           \<lbrace>hard\<rbrace>"

lemma "\<Gamma>\<turnstile>\<^bsub>/{True}\<^esub> \<lbrace>True\<rbrace> WHILE\<^sub>g  \<acute>N < \<acute>Arr!i
                    FIX Z.
                    INV \<lbrace>\<acute>N < 2\<rbrace>
                    VAR arbitrary
                  DO
                    \<acute>N :== \<acute>M
                  OD
           \<lbrace>hard\<rbrace>"
apply vcg
oops

lemma "\<Gamma>\<turnstile>\<^bsub>/{True}\<^esub> \<lbrace>True\<rbrace> WHILE \<lbrace>P \<acute>N \<rbrace>\<surd>, \<lbrace>Q \<acute>M\<rbrace>#, \<lbrace>R \<acute>N\<rbrace>\<longmapsto> \<acute>N < \<acute>M
                    FIX Z.
                    INV \<lbrace>\<acute>N < 2\<rbrace>
                    VAR arbitrary
                  DO
                    \<acute>N :== \<acute>M
                  OD
           \<lbrace>hard\<rbrace>"
apply vcg
oops

end
