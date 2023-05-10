(*
  Mike Stannett
  25-27/04/2023
*)

section \<open> MHComputation \<close>

text \<open> In this theory we define five locales
\begin{itemize}
\item Computation
\item ReachabilitySpace
\item Time
\item MHSpacetime
\item MHComputation
\end{itemize}
and use them to verify that the Turing halting problem (HP) can be solved if we are
allowed to exploit the physical properties of so-called Malament-Hogarth spacetimes.

This verification generalises our earlier proof outline \cite{Stannett}, which 
was itself based on the seminal results of Hogarth \cite{Hogarth} and N\'emeti \& Etesi
\cite{Nemeti}.
\<close>

theory MHComputation
  imports Main
begin


subsection \<open>locale: Computation\<close>

text \<open>We think of a computing machine as being placed in an initial configuration,
which includes all of the required details of the program to be run and its inputs.
The machine is equipped with an operating system which ``knows'' how to execute one
instruction at a time, thereby moving the system from one configuration to another 
as time (measured in discrete ``ticks'') passes.

We generally refer to the initial configuration using the variable name \emph{spec}
(for ``specification''). The function \emph{configAtTick} which takes two arguments
, the initial configuration and the tick number $n$, and yields the configuration
of the corresponding system at completion of the $n$'th tick. This is computed by
recursively iterating calls to \emph{getNextConfig}.

We say that the program \emph{halts} if there are two consecutive ticks at which
the configurations are identical.
\<close>

locale Computation = 
  fixes halts :: "'machineConfig \<Rightarrow> bool"
and     getNextConfig :: "'machineConfig \<Rightarrow> 'machineConfig"
and     configAtTick :: "'machineConfig \<Rightarrow> nat \<Rightarrow> 'machineConfig"
assumes 
        halting: "halts spec \<equiv> \<exists> n . (configAtTick spec n = configAtTick spec (n+1))"
and     configs: "configAtTick spec n = 
                   (if n = 0 then spec else getNextConfig (configAtTick spec (n-1)))"
begin

abbreviation haltingTick :: "'machineConfig \<Rightarrow> nat option"
  where "haltingTick spec \<equiv> 
          (if (halts spec) 
           then Some (Min { n . configAtTick spec n = configAtTick spec (n+1) })
           else None)"

end

subsection \<open>locale: ReachabilitySpace \<close>

text \<open>Although we think of computations as taking place in a special type of spacetime,
this interpretation is far more constraining that required for the proof to work.
All we need to know is whether there is a traversible path from one spacetime location 
to another. We do not specify what we mean by a ``location'', but we can think of 
locations as points in a (3+1)-dimensional spacetime, with traversibility indicating 
the existence of a timelike curve from one location to another.
\<close>


locale ReachabilitySpace = 
  fixes   reachable :: "'location \<Rightarrow> 'location \<Rightarrow> bool" ("_ \<leadsto> _")
begin
end


subsection \<open>locale: Time\<close>

text \<open>We'll be modelling time using values in a linearly ordered field. However,
such fields can include infinite values. We want to ensure that the user can solve
the halting problem in a known finite amount of time, so we need some way of
saying that a positive value is finite. The details are unimportant. One way 
would be to note that each natural number can be embedded naturally in the field, and 
say that a positive value is finite iff it is bounded above by some natural number.
\<close>

locale Time = linordered_field +
  fixes isFinite  :: "'a \<Rightarrow> bool"
begin

fun embedTick :: "nat \<Rightarrow> 'a" 
  where "embedTick 0 = zero"
  |     "embedTick (Suc n) = plus one (embedTick n)"

end





subsection \<open>locale: MHSpacetime\<close>

text \<open> A \emph{Malament-Hogarth spacetime} is a spacetime which contains a point 
$mhpoint$ and a timelike curve $mhline$, where $mhline$ has infinite proper length 
and $mhpoint$ is reachable from every point on $mhline$. If we arrange for the computer 
to traverse $mhline$, this ensures that any program that ought to run forever without
halting  will have ``enough time'' to do so.

We represent $mhline$ as a path comprising locations parameterised by proper time, where
proper times are assumed to form a linearly ordered field (in the algebraic sense).
Because linearly ordered fields contain unboundedly large values, this ensures that the
proper length of $mhline$ is infinite.

Since $mhpoint$ is reachable from $mhline(0)$, there exists some fixed path $basePath$ 
between the two points, which takes some finite proper time $baseTime$ to traverse.
\<close>

(*
  'location = locations
  'b = numbers
*)

locale MHSpacetime = ReachabilitySpace + Time +
  fixes mhpoint   :: "'location"
and     mhline    :: "'b \<Rightarrow> 'location"
and     basePath  :: "'b \<Rightarrow> 'location"
and     baseTime  :: "'b"
assumes 
        mhprop:   "(mhline t) \<leadsto> mhpoint"
and     baseprop: "(basePath zero = mhline zero) \<and> (basePath baseTime = mhpoint)
                    \<and> (isFinite baseTime)"
begin
end



subsection \<open>locale: MHComputation\<close>

text \<open>This locale combines \emph{Computation} and \emph{MHSpacetime} by assuming that
the computer and user follow special paths while the program executes. We think of
the user being co-located with the computer at time 0, when some program of interest 
begins execution on some specific set of inputs (both the program and the inputs are 
provided by the user in the initial configuration). Our task is to determine 
(in \emph{finite} -- and program-independent -- time as measured by the user) whether or not the execution will
eventually halt.

To do this, we send the computer along the path $mhline$, while the user travels instead
to $mhpoint$ via $basePath$. The machine's operating system is equipped with a 
signalling device, which is triggered if (and only if) the program is found to have halted.

To determine whether the program eventually halts, all the user has to do is check when
they arrive at $mhpoint$ whether or not a signal is also present. If so, the operating
system must have been been triggered to send it, which means that the program must
have halted at some point. If no signal is present, then no step of the program triggered
the operating system to send one, which means the program never halted while the
computer traversed $mhline$. Since this trajectory provided the computer with enough
time to execute an unlimited number of ticks, this means that the program ran forever.

The runtime, $baseTime$, of this procedure is finite, and is the same for all choices 
of initial configuration, $spec$.
\<close>


(*
  'a = 'machineConfig
  'b = locations
  'c = numbers
*)
locale MHComputation = Computation + MHSpacetime +
  fixes machinePath      :: "'c \<Rightarrow> 'b"
and     userPath         :: "'c \<Rightarrow> 'b"
and     signalSentFrom   :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
and     signalPresentAt  :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
and     runtime          :: "'c"
assumes
    pathOfMachine:   "machinePath = mhline"
and pathOfUser:      "userPath = basePath"
and decisionTime:    "runtime  = baseTime"
and signalling:      "(signalSentFrom spec pt) \<longleftrightarrow> 
                           (\<exists> n . (haltingTick spec = Some n)
                               \<and> (pt = machinePath (embedTick n)) )"
and signalReception: "(signalPresentAt spec pt \<longleftrightarrow>  
                           (\<exists> pt' . signalSentFrom spec pt' \<and> (pt' \<leadsto> pt)))"

begin

subsubsection \<open>lemma: hpMHDecidable ~ \\The halting problem is decidable in MH-Spacetime\<close>

text \<open>We show that the user can determine whether or not any specified program will
eventually halt by checking for the receipt of a signal after a fixed finite
runtime. The same runtime works regardless of which program is being examined.\<close>


abbreviation decisionAtTime :: "'a \<Rightarrow> 'c \<Rightarrow> bool"
  where "decisionAtTime spec t \<equiv> signalPresentAt spec (userPath t)"


lemma hpMHDecidable: "(isFinite runtime) \<and>
                      (\<forall> spec . (decisionAtTime spec runtime = True) \<longleftrightarrow> halts spec)"
proof -
  have part1: "isFinite runtime" using baseprop decisionTime by auto

  moreover have part2: "\<forall> spec . (decisionAtTime spec runtime = True) \<longleftrightarrow> halts spec"
  proof -
    { fix spec
  
      { assume case1: "decisionAtTime spec runtime = True"
        hence "signalPresentAt spec (userPath runtime)" by simp
        then obtain pt'  where pt': "(signalSentFrom spec pt') \<and> (pt' \<leadsto> (userPath runtime))"
          using signalReception by auto
        then obtain n where n: "haltingTick spec = Some n" using signalling by auto
        hence "halts spec" by (meson option.distinct(1))
      }
      hence "decisionAtTime spec runtime = True \<longrightarrow> halts spec" by auto
    
      moreover have "halts spec \<longrightarrow> decisionAtTime spec runtime = True"
      proof -
        { assume case2: "halts spec"
          obtain m where m: "m = Min { n . configAtTick spec n = configAtTick spec (n+1) }"
            by auto
          define pt where pt: "pt = machinePath (embedTick m)"
          hence "(haltingTick spec = Some m) \<and> (pt = machinePath (embedTick m))" using m case2 by simp
          hence "signalSentFrom spec pt" using signalling by auto
          moreover have "pt \<leadsto> mhpoint" by (metis mhprop pathOfMachine pt)
          ultimately have "signalPresentAt spec (userPath runtime)" 
            using baseprop decisionTime pathOfUser signalReception by auto
          hence "decisionAtTime spec runtime = True" by simp
        }
        thus ?thesis by auto
      qed
  
      ultimately have "(decisionAtTime spec runtime = True) \<longleftrightarrow> halts spec"
        by blast
    }
    thus ?thesis by blast
  qed

  ultimately show ?thesis by blast
qed

end
end
                             