section \<open>Register Machines\<close>

subsection \<open>Register Machine Specification\<close>
theory RegisterMachineSpecification
  imports Main
begin

subsubsection \<open>Basic Datatype Definitions\<close>

text \<open>The following specification of register machines is inspired by \<^cite>\<open>"mech_turing"\<close> (see 
      \<^cite>\<open>"mech_turing_afp"\<close> for the corresponding AFP article).\<close>

(* Type synonyms for registers (= register indices) the "tape" (sim. to a
 * Turing machine) that contains a list of register values.
 *)
type_synonym register = nat
type_synonym tape = "register list"

(* The register machine understands "instructions" that operate on state(-id)s
 * and modify register(-id)s. The machine stops at the HALT instruction.
 *)
type_synonym state = nat
datatype instruction =
  isadd: Add (modifies : register) (goes_to : state) |
  issub: Sub (modifies : register) (goes_to : state) (goes_to_alt : state) |
  ishalt: Halt
where
  "modifies Halt = 0" |
  "goes_to_alt (Add _ next) = next"

(* A program, then, just becomes a list of these instructions *)
type_synonym program = "instruction list"

(* A configuration of the (runtime of) a machine encodes information about the
 * instruction and the state of the registers (i.e., the tape). We describe it
 * here as a tuple.
 *)
type_synonym configuration = "(state * tape)"

subsubsection \<open>Essential Functions to operate the Register Machine\<close>

(* Given a tape of register values and some instruction(s) the register
 * machine first reads the value of the register from the tape (by convention
 * assume that the value "read" by the HALT state is zero). The machine then,
 * fetches the next instruction from the program, and finally updates the
 * tape to reflect changes by the last instruction.
 *)

definition read :: "tape \<Rightarrow> program \<Rightarrow> state \<Rightarrow> nat"
  where "read t p s = t ! (modifies (p!s))"

definition fetch :: "state \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> state" where
  "fetch s p v = (if issub (p!s) \<and> v = 0 then goes_to_alt (p!s)
                       else if ishalt (p!s) then s
                       else goes_to (p!s))"

definition update :: "tape \<Rightarrow> instruction \<Rightarrow> tape" where
  "update t i = (if ishalt i then t
                    else if isadd i then list_update t (modifies i) (t!(modifies i) + 1)
                    else list_update t (modifies i) (if t!(modifies i) = 0 then 0 else (t!(modifies i)) - 1) )"

definition step :: "configuration \<Rightarrow> program \<Rightarrow> configuration"
  where
    "(step ic p) = (let nexts = fetch (fst ic) p (read (snd ic) p (fst ic));
                        nextt = update (snd ic) (p!(fst ic))
                        in (nexts, nextt))"

fun steps :: "configuration \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> configuration"
  where
    steps_zero: "(steps c p 0) = c"
  | steps_suc:  "(steps c p (Suc n)) = (step (steps c p n) p)"


subsubsection \<open>Validity Checks and Assumptions\<close>

(* check bound for each type of instruction *)
(* take a m representing the upper bound for state number *)
fun instruction_state_check :: "nat \<Rightarrow> instruction \<Rightarrow> bool"
  where isc_halt: "instruction_state_check _ Halt = True"
  |     isc_add: "instruction_state_check m (Add _ ns) = (ns < m)"
  |     isc_sub: "instruction_state_check m (Sub _ ns1 ns2) = ((ns1 < m) & (ns2 < m))"

fun instruction_register_check :: "nat \<Rightarrow> instruction \<Rightarrow> bool"
  where "instruction_register_check _ Halt = True"
  |     "instruction_register_check n (Add reg _) = (reg < n)"
  |     "instruction_register_check n (Sub reg _ _) = (reg < n)"

(* passes function via currying into list_all *)
fun program_state_check :: "program \<Rightarrow> bool"
  where "program_state_check p = list_all (instruction_state_check (length p)) p"

fun program_register_check :: "program \<Rightarrow> nat \<Rightarrow> bool"
  where "program_register_check p n = list_all (instruction_register_check n) p"

fun tape_check_initial :: "tape \<Rightarrow> nat \<Rightarrow> bool"
  where "tape_check_initial t a = (t \<noteq> [] \<and> t!0 = a \<and> (\<forall>l>0. t ! l = 0))"

fun program_includes_halt :: "program \<Rightarrow> bool"
  where "program_includes_halt p = (length p > 1 \<and> ishalt (p ! (length p -1)) \<and> (\<forall>k<length p-1. \<not> ishalt (p!k)))"

text \<open>Is Valid and Terminates\<close>

definition is_valid
  where "is_valid c p = (program_includes_halt p \<and> program_state_check p
                            \<and> (program_register_check p (length (snd c))))"

definition is_valid_initial
  where "is_valid_initial c p a = ((is_valid c p)
                                \<and> (tape_check_initial (snd c) a)
                                \<and> (fst c = 0))"

definition correct_halt
  where "correct_halt c p q = (ishalt (p ! (fst (steps c p q)))  \<comment> \<open>halting\<close>
                            \<and> (\<forall>l<(length (snd c)). snd (steps c p q) ! l = 0))"

definition terminates :: "configuration \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> bool"
  where "terminates c p q = ((q>0)
                          \<and> (correct_halt c p q)
                          \<and> (\<forall>x<q. \<not> ishalt (p ! (fst (steps c p x)))))"

definition initial_config :: "nat \<Rightarrow> nat \<Rightarrow> configuration" where
  "initial_config n a = (0, (a # replicate n 0))"

end
