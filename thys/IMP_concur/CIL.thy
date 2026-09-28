chapter\<open> Appendix: A Syntactic Frontend for \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>\<close>

theory CIL
  imports   "IMP_concur" (* Core semantics based on HOL-CSPM. *)
  keywords  "SYSTEM" :: thy_decl
      and   "globals" "locks" "LOCK" "UNLOCK" "thread" "WHILE" "IF" "ELSE" "THEN"
            "end;" "any" "actions" "DO" "<-" "->" "SKIP" "DONE"
 
begin

section \<open>Introduction\<close>

text\<open>This theory defines syntactic support for a Concurrent Imperative Language (CIL) on top of
\<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>, a semantic language with threads, thread-local and thread-global states on which 
the threads may synchronize via semaphores (locks and unlocks). \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close> itself is based on 
HOL-CSPM; the semantics is constructed in a way that a conversion to Proc-Omata is possible.\<close>

text\<open>This appendix has been authored by Mathilde Needham and Zineddine Kermadj on their 
internship in summer 2025. \<close>

section \<open>Interface\<close>

definition SEMAPHORES 
  where   \<open>SEMAPHORES idx \<equiv> Renaming (semaphore idx) id id\<close>
         \<comment> \<open>lifting semaphores to the global alphabet\<close>   
 
definition GLOBALVARS ::  "\<sigma> \<Rightarrow> string \<Rightarrow> evs process"
  where   \<open>GLOBALVARS \<sigma>\<^sub>i\<^sub>n\<^sub>i\<^sub>t idx \<equiv> Renaming (global_vars \<sigma>\<^sub>i\<^sub>n\<^sub>i\<^sub>t idx) (\<lambda>x. x) (\<lambda>y. y)\<close>

definition LOCALVARS 
  where   \<open>LOCALVARS  \<sigma>\<^sub>i\<^sub>n\<^sub>i\<^sub>t idx \<equiv> Renaming (local_vars  \<sigma>\<^sub>i\<^sub>n\<^sub>i\<^sub>t idx)(\<lambda>x. x) (\<lambda>y. y)\<close>


section \<open>Parsing and Term-Reading\<close>

ML\<open> 

val quiet_mode = false

fun message quiet_mode s = if quiet_mode then () else writeln s;

datatype ('a, 'b) sum = inl of 'a | inr of 'b;

exception Undeclared_Variable of string

local open HOLogic in

fun map_opt f _ (SOME a) = f a
   |map_opt _ a NONE = a

fun map_option f  = map_opt (SOME o f) NONE

(* remove this *)
fun map_option f (SOME a) = SOME(f a)
   |map_option _ NONE = NONE



val parse_var_decl = (Parse.binding --| Parse.$$$ ":" -- (Parse.position (Parse.term)))
                   -- (Scan.option ( Parse.$$$ "=" |-- Parse.term))
                    : ((binding*(string*Position.T))*string option) parser

(*declarations de locks*)
val parse_locks = Parse.binding --| Parse.$$$ ":" -- (Parse.position (Parse.term)) 
                  : (binding*(string*Position.T)) parser


datatype a = Skip
            | Assign of binding*string 
            | Unlock of binding 
            | Lock of binding
            | Send of binding*string 
            | Receive of binding*binding
            | Ifelse of (string*(a list))*(a list) 
            | While of string*(a list)

val parse_lock = \<^keyword>\<open>LOCK\<close> |-- Parse.binding --| Parse.$$$ ";"
                 >> (fn (x) => Lock(x))
                  : a parser
val parse_unlock =  \<^keyword>\<open>UNLOCK\<close> |-- Parse.binding --| Parse.$$$ ";"
                 >>  (fn (x) => Unlock(x))
                  : a parser
val parse_assign = Parse.binding --| Parse.$$$ "=" -- Parse.term --| Parse.$$$ ";"
                >> (fn (x) => Assign(x))
                  : a parser
val parse_send = Parse.binding --| \<^keyword>\<open>->\<close> -- Parse.term --| Parse.$$$ ";"
                 >> (fn (x) => Send(x))
                  : a parser
val parse_receive = Parse.binding --| \<^keyword>\<open><-\<close> -- Parse.binding --| Parse.$$$ ";"
                >> (fn (x) => Receive(x))
                  : a parser
val parse_skip = \<^keyword>\<open>SKIP\<close> |-- Parse.$$$ ";"
                >> (fn _  => Skip) : a parser

fun parse_actions TL   =( Scan.repeat ( parse_lock 
                                  || parse_unlock 
                                  || parse_assign
                                  || parse_send 
                                  || parse_receive
                                  || parse_skip
                                  || parse_if_else 
                                  || parse_while 
                                  )) TL
and  parse_if_else TL = ((\<^keyword>\<open>IF\<close> |-- Parse.term --| \<^keyword>\<open>THEN\<close>
                    -- parse_actions --| \<^keyword>\<open>ELSE\<close> -- parse_actions--| \<^keyword>\<open>DONE\<close>)
                    >>(fn (x) => Ifelse(x))) TL
and parse_while TL =(( \<^keyword>\<open>WHILE\<close> |-- Parse.term --| \<^keyword>\<open>DO\<close> -- parse_actions --|\<^keyword>\<open>DONE\<close>)
                    >> (fn (x) => While(x))) TL


                                

(*thread T1 : where var_local_decl
             actions  action1;
                       ... ;
                      actionN;
   thread T2: actions  action1;
                       ... ;
                      actionN;
 *)
val parse_threads =( \<^keyword>\<open>thread\<close> |-- (Scan.option (Parse.binding)) --| Parse.$$$ ":"
                                      -- (Scan.option (\<^keyword>\<open>any\<close> |--  Scan.repeat1 (parse_var_decl) ))
                                     -- (\<^keyword>\<open>actions\<close> |-- parse_actions))

type raw_absy =  (((binding (*system name*)
            *
             ((binding * (string * Position.T)) * string option)list) (*globals*)
            *
            (binding * (string * Position.T)) list) (*locks*)
           *
           ((binding option * (*a thread's name*)
             ((binding * (string * Position.T)) *string option)list option) (*a thread's locals*)
            *
              a list (*a thread's actions*)
           ) list) (*threads lists*)

type raw_thread_absy = (binding option * (*a thread's name*)
                       ((binding * (string * Position.T)) *string option)list option)* (*a thread's locals*)
                        a list (*a thread's actions*)
                     

val parse_system_spec = (
          Parse.binding 
       --| \<^keyword>\<open>globals\<close>    -- (Scan.repeat parse_var_decl)
       --| \<^keyword>\<open>locks\<close>      -- (Scan.repeat parse_locks)
       -- (Scan.repeat1 parse_threads)
       --| \<^keyword>\<open>end;\<close>
      ) : raw_absy parser

end
\<close>


typedecl pre_event_type

section\<open>Context Checking\<close>
ML\<open>
val pre_event_type = @{typ \<open>pre_event_type\<close>}

datatype a_term = SkipA
            | AssignA of binding*term 
            | UnlockA of binding 
            | LockA of binding
            | SendA of binding*term 
            | ReceiveA of binding*binding
            | IfelseA of (term*(a_term list))*(a_term list) 
            | WhileA of term*(a_term list)
            | SeqA of a_term * a_term

type thread_absy = {nom_thread  : binding ,
                    locals_decl : ((binding * typ) * term option) list ,
                    actions     : a_term list,
                    locstab     : (term option) Symtab.table
                   }
type absy = {system          : binding,
             globals_decls   : (binding * typ * Position.T * term option) list,
             varstab         : (term option) Symtab.table,
             locks_decls     : (binding * term * Position.T) list,
             threads_decls   : thread_absy list
            }


val SPY = Unsynchronized.ref(NONE:absy option)
val SPYG= Unsynchronized.ref([Bound 0])

fun pre_const ((bdg, typ), _) = (bdg, typ, NoSyn)
fun pre_const' (b, trm) = (b,   fastype_of trm, Mixfix.NoSyn) 
fun pre_const_bar (b, trm, _) = (Binding.suffix_name "'" b,  
                                  fastype_of trm, Mixfix.NoSyn) 
fun pre_const2 (b, typ, _, _) = (b,  typ, Mixfix.NoSyn) 
fun pre_const3 (b, trm, _) = (b, fastype_of trm, Mixfix.NoSyn) 

fun pre_event (b, trm, _) = (b, fastype_of trm --> pre_event_type, 
                                   Mixfix.NoSyn)  


(* Got replaced but would be cool to know why isn't it working

fun check_vars term varstab locstab =
  let
    val vars = Term.add_free_names term []
    fun is_declared v = Symtab.defined varstab v orelse Symtab.defined locstab v
    val undeclared = List.filter (not o is_declared) vars
  in
    if null undeclared then ()
    else error ("Undeclared variable(s) used: " ^ String.concatWith ", " undeclared)
  end*)


fun read_term_err thy msg bind str = 
        let val pos = Position.here(Binding.pos_of bind)
        in  (Syntax.read_term_global thy str
             handle ERROR s => error("error in "^msg^" :"^ pos ^"\n"^ s ) ) 
        end

fun read_term_err_pos thy msg _ str pos = 
        (Syntax.read_term_global thy str
             handle ERROR s => error("error in "^msg^" :"^ (Position.here pos) ^"\n"^ s ) ) 

(* Utilitaire pour lire un terme à partir d’un string *)
fun get_term_and_vars thy str =
  let
    val ctxt = Proof_Context.init_global thy
    val term = Syntax.read_term ctxt str
    val vars = Term.add_free_names term []
  in
    (term, vars)
  end

(* Résout une variable selon priorité locale ou globale *)
fun resolve_var prefer_global var locstab varstab =
  let
    val loc = Symtab.lookup locstab var
    val global = Symtab.lookup varstab var
  in
    if prefer_global then
      (case global of
         SOME (SOME t) => SOME t
       | _ => (case loc of
                 SOME (SOME t) => SOME t
               | _ => NONE))
    else
      (case loc of
         SOME (SOME t) => SOME t
       | _ => (case global of
                 SOME (SOME t) => SOME t
               | _ => NONE))
  end

(* Variante stricte qui renvoie une erreur si non trouvé *)
fun resolve_var_strict prefer_global var locstab varstab =
  case resolve_var prefer_global var locstab varstab of
    SOME t => t
  | NONE => error ("Variable "^var^" non déclarée")

fun check_thread thy thy3 vars_tab (((SOME thread_name, locals_opt), actions_list): raw_thread_absy) =
  let
    fun loc_decls_conv ((bdg, (s, pos)), SOME init_term) =
          let 
            val typ = Syntax.read_typ_global thy s
            val inferred_type = fastype_of init_term
            val ctxt = Proof_Context.init_global thy
            val inferred_str = Syntax.string_of_typ ctxt inferred_type
            val declared_str = Syntax.string_of_typ ctxt typ
          in
            if inferred_type <> typ then
              error ("Type mismatch in variable " ^ Binding.name_of bdg ^
                     ": expected " ^ declared_str ^ ", but got " ^ inferred_str ^ "at " ^ Position.here pos )
            else
              ((bdg, typ), SOME init_term)
          end
        | loc_decls_conv ((bdg, (s, pos)), NONE) =
          ((bdg, Syntax.read_typ_global thy s), NONE)

    fun action_conv _ _ Skip = SkipA
      | action_conv _ _ (Lock b) = LockA b
      | action_conv _ _ (Unlock b) = UnlockA b
      | action_conv varstab locstab (Assign (bdg, str)) =
           let
              val (term, vars) = get_term_and_vars thy str
              val assign_term = term
             val _ =
              if Symtab.defined locstab (Binding.name_of bdg) 
                 orelse Symtab.defined varstab (Binding.name_of bdg)
              then ()
              else error ("Variable " ^ (Binding.name_of bdg) ^ " is not declared (in assign binding)")
            in
              AssignA (bdg, assign_term)
            end


      | action_conv varstab locstab (Send (b, str)) =
          let
            val (term, _) = get_term_and_vars thy str
            val _ =
              if Symtab.defined locstab (Binding.name_of b) 
                 orelse Symtab.defined varstab (Binding.name_of b)
              then ()
              else error ("Variable " ^ (Binding.name_of b) ^ " is not declared (in send)")
          in
            SendA (b, term)
          end

      | action_conv varstab locstab (Receive (blv, bsv)) =
        let
           val _ =
              if Symtab.defined locstab (Binding.name_of blv)
                 then   if (Symtab.defined varstab (Binding.name_of bsv)) then ()
                        else error ("Variable " ^ (Binding.name_of bsv) ^ " is not declared (in receive binding)")
              else error ("Variable " ^ (Binding.name_of blv) ^ " is not declared (in receive binding)")
        in
          ReceiveA (blv, bsv)
        end

      | action_conv varstab locstab (Ifelse ((cond_str, then_branch), else_branch)) =
          let
          val (term, vars) = get_term_and_vars thy cond_str
          val cond_term = term
          val then_branch' = map (action_conv varstab locstab) then_branch
          val else_branch' = map (action_conv varstab locstab) else_branch
        in
          IfelseA ((cond_term, then_branch'), else_branch')
        end

      | action_conv varstab locstab (While (cond_str, body)) =
          let
            val (term, vars) = get_term_and_vars thy cond_str
           (* val cond_term =
              case vars of
                [x] => resolve_var_strict false x locstab varstab
              | _ => term*)
            val cond_term =  term  
            val actions = map (action_conv varstab locstab) body
          in
            WhileA (cond_term, actions)
          end

    val (loc_decls', thy3') = case locals_opt of
        NONE => ([], thy3)
      | SOME locals =>
          let
            val locals_terms = map (fn ((bdg,(s,pos)), init_opt_str) =>
               let
                 val init_opt_term = case init_opt_str of
                     NONE => NONE
                   | SOME str => SOME (read_term_err thy "local init" bdg str)
               in
                 ((bdg, (s,pos)), init_opt_term)
               end) locals
    
            val decls = map loc_decls_conv locals_terms
            val thy4 = Sign.add_consts (map pre_const decls) thy3
          in
            (decls, thy4)
          end

    fun conv_decl_init ((n, _), init_opt) = (Binding.name_of n, init_opt)
    val locstab'     = Symtab.make (map conv_decl_init loc_decls')
    val actions' = map (action_conv vars_tab locstab') actions_list  in
    { nom_thread = thread_name, locals_decl = loc_decls', actions = actions', locstab = locstab' }
  end
  | check_thread _ _ _ ((NONE, _), _) =
      error "Current syntax restriction: threads must have label."




val context_check = fn (((system: binding , 
                          globals :  ((binding * (string * Position.T)) * string option)list),
                          locks :  (binding * (string * Position.T)) list),
                          threads : raw_thread_absy list)
                           =>
                     fn thy : theory => 
                     let val read = read_term_err thy
                         fun global_decls_conv ((bdg, (s, pos)), SOME init_term) =
                            let 
                              val typ = Syntax.read_typ_global thy s
                              val inferred_type = fastype_of init_term
                              val ctxt = Proof_Context.init_global thy
                              val inferred_str = Syntax.string_of_typ ctxt inferred_type
                              val declared_str = Syntax.string_of_typ ctxt typ
                            in
                              if inferred_type <> typ then
                                error ("Type mismatch in variable " ^ Binding.name_of bdg ^
                                       ": expected " ^ declared_str ^ ", but got " ^ inferred_str ^  
                                       "at " ^Position.here pos)
                              else
                                (bdg, typ, pos, SOME init_term)
                            end
                          | global_decls_conv ((bdg, (s, pos)), NONE) =
                            (bdg, Syntax.read_typ_global thy s, pos, NONE)
                     val (global_decls', thy3') = 
                                  let
                                    val global_terms = map (fn ((bdg,(s,pos)), init_opt_str) =>
                                       let
                                         val init_opt_term = case init_opt_str of
                                             NONE => NONE
                                           | SOME str => SOME (read_term_err thy "local init" bdg str)
                                       in
                                         ((bdg, (s,pos)), init_opt_term)
                                       end) globals
                            
                                    val decls = map global_decls_conv global_terms
                                    val thy4 = Sign.add_consts (map pre_const2 decls) thy
                                  in
                                    (decls, thy4)
                                  end

                         fun conv_decl_init (n,_, _  , init_opt) = (Binding.name_of n, init_opt)
                         val varstab     = Symtab.make (map conv_decl_init global_decls')
                         val lock_decls'= map (fn (b, (str,pos)) => (b, read "lock_decl" b str, pos)) locks
                         val thy'        = Sign.add_consts (map pre_const2 global_decls') thy
                         val thy''       = thy' |> Sign.add_consts (map pre_event lock_decls')

                         val threads' = map (check_thread thy thy'' varstab) threads 
                        val res = {system = system,
                                   globals_decls = global_decls',
                                   varstab = varstab,
                                   locks_decls = lock_decls',
                                   threads_decls = threads'}
                     in  SPY:=(SOME (res)); res end


\<close>


section\<open>Semantic Check\<close>
ML\<open>
(* Redéfinir les types de base de la sémantique *)
type SV = string  (* Shared Variables *)
type V = string   (* Thread-Local Variables *)  
type MV = int     (* Mutex IDs *)
type D = int      (* Data type - simplifié à int *)

type state = string -> int

fun safe_lookup var state =
  case state var of
    ~1 => raise Undeclared_Variable var
  | v => v

type arith_expr = state -> int
type bool_expr = state -> bool

datatype com = 
    SKIP
  | Assign of string * arith_expr
  | Seq of com * com  
  | Cond of bool_expr * com * com
  | While of bool_expr * com
  | Lock of string
  | Unlock of string
  | Store of arith_expr * string
  | Load of string * string

(* Table de mapping pour les locks *)
val lock_table = Unsynchronized.ref (Symtab.empty : int Symtab.table)
val lock_counter = Unsynchronized.ref 1
(*                 
type absy = {system          : binding,
             globals_decls   : (binding * typ * Position.T * term option) list,
             varstab         : (term option) Symtab.table,
             locks_decls     : (binding * term * Position.T) list,
             threads_decls   : thread_absy list
            }

fun get_lock_id (lock_name : string) : int =
  case Symtab.lookup (!lock_table) lock_name of
    SOME id => id
  | NONE => 
      let 
        val new_id = !lock_counter
        val _ = lock_counter := new_id + 1
        val _ = lock_table := Symtab.update (lock_name, new_id) (!lock_table)
      in 
        new_id 
      end
*)

fun declared_lock (name: string) (machine: absy) : bool =
  List.exists (fn (b, _, _) => Binding.name_of b = name) (#locks_decls machine)

fun get_lock_id (lock_name: string) (machine: absy) : int =
  if not (declared_lock lock_name machine) then
    error ("Lock " ^ lock_name ^ " not declared")
  else
    case Symtab.lookup (!lock_table) lock_name of
        SOME id => id
      | NONE =>
          let
            val new_id = !lock_counter
            val _ = lock_counter := new_id + 1
            val _ = lock_table := Symtab.update (lock_name, new_id) (!lock_table)
          in
            new_id
          end;
(* Évaluation des termes Isabelle/HOL *)
fun eval_term_to_int (thy : theory) (term : term) (state : state) : int =
  let
    (* Fonction récursive pour évaluer les termes *)
    fun eval t =
      case t of
        Const (@{const_name "Groups.plus_class.plus"}, _) $ t1 $ t2 =>
          (eval t1) + (eval t2)
      | Const (@{const_name "Groups.minus_class.minus"}, _) $ t1 $ t2 =>
          (eval t1) - (eval t2)
      | Const (@{const_name "Groups.times_class.times"}, _) $ t1 $ t2 =>
          (eval t1) * (eval t2)
      | Const (@{const_name "HOL.Trueprop"}, _) $ t1 => eval t1
      | @{term "0::nat"} => 0
      | @{term "1::nat"} => 1
      | Free (name, _) => safe_lookup name state
      | Bound i =>  i (* Placeholder pour les variables liées *)
      | _ => 
          (* Essayer d'extraire les constantes numériques *)
          (case try (HOLogic.dest_number #> snd) t of
            SOME n => n
          | NONE => 0) (* Valeur par défaut *)
  in
    eval term
  end

fun eval_term_to_bool (thy : theory) (term : term) (state : state) : bool =
  let
    fun eval t =
      case t of
        @{term "True"} => true
      | @{term "False"} => false
      | Const (@{const_name "HOL.conj"}, _) $ t1 $ t2 =>
          (eval t1) andalso (eval t2)
      | Const (@{const_name "HOL.disj"}, _) $ t1 $ t2 =>
          (eval t1) orelse (eval t2)
      | Const (@{const_name "HOL.Not"}, _) $ t1 =>
          not (eval t1)
      | Const (@{const_name "HOL.eq"}, _) $ t1 $ t2 =>
          (eval_term_to_int thy t1 state) = (eval_term_to_int thy t2 state)
      | Const (@{const_name "Orderings.ord_class.less"}, _) $ t1 $ t2 =>
          (eval_term_to_int thy t1 state) < (eval_term_to_int thy t2 state)
      | Const (@{const_name "Orderings.ord_class.less_eq"}, _) $ t1 $ t2 =>
          (eval_term_to_int thy t1 state) <= (eval_term_to_int thy t2 state)
      | Free (name, _) => 
          (case try (fn () => safe_lookup name state) () of
            SOME 0 => false
          | SOME _ => true
          | NONE => false)
      | _ => error ("Unsupported boolean expression: " ^ Pretty.string_of (Syntax.pretty_term_global thy t) )
                                                         (*Syntax.string_of_term_global thy t)*)
  in
    eval term
  end
(* Fixed record pattern matching *)
(*fun process_absy absy_data =
  let
    val {system, globals_decls, locks_decls, threads_decls, varstab} = absy_data
  in
    (* Process the fields *)
    (system, globals_decls, locks_decls, threads_decls)
  end
*)
(* Fonction de conversion de l'AST vers com *)
fun convert_to_com (thy : theory) (actions : a_term list) 
                   (varstab : (term option) Symtab.table) 
                   (locstab : (term option) Symtab.table) : com =
  let
    fun term_to_arith_expr (t : term) : arith_expr = 
      fn state => eval_term_to_int thy t state
    
    fun term_to_bool_expr (t : term) : bool_expr =
      fn state => eval_term_to_bool thy t state
    
    fun convert_action (action : a_term) : com =
      case action of
        SkipA => SKIP
      | AssignA (bdg, term) => 
        let
          val name = Binding.name_of bdg
          val is_local = Symtab.defined locstab name
        in
          if is_local
          then Assign (name, term_to_arith_expr term)  (* local *)
          else Store (term_to_arith_expr term, name)   (* global *)
        end
      | LockA bdg => 
          Lock (Binding.name_of bdg)
      | UnlockA bdg => 
          Unlock (Binding.name_of bdg)
      | SendA (bdg, term) => 
          Store (term_to_arith_expr term, Binding.name_of bdg)
      | ReceiveA (local_bdg, shared_bdg) => 
          Load (Binding.name_of local_bdg, Binding.name_of shared_bdg)
      | IfelseA ((cond_term, then_actions), else_actions) =>
          Cond (term_to_bool_expr cond_term,
                convert_actions_to_seq then_actions,
                convert_actions_to_seq else_actions)
      | WhileA (cond_term, body_actions) =>
          While (term_to_bool_expr cond_term, convert_actions_to_seq body_actions)
        
    
    and convert_actions_to_seq (actions : a_term list) : com =
      case actions of
        [] => SKIP
      | [action] => convert_action action
      | action :: rest => Seq (convert_action action, convert_actions_to_seq rest)
  in
    convert_actions_to_seq actions
  end

fun check_lock_ownership (thread_name : string) (actions : a_term list) =
  let
    fun check [] _ = NONE
      | check (LockA b :: rest) held =
          let val l = Binding.name_of b in
            if List.exists (fn x => x = l) held then 
              SOME ("Thread " ^ thread_name ^ ": LOCK " ^ l ^ " already held")
            else
              check rest (l :: held)
          end
      | check (UnlockA b :: rest) held =
          let val l = Binding.name_of b in
            if List.exists (fn x => x = l) held then
              check rest (remove (op =) l held)
            else
              SOME ("Thread " ^ thread_name ^ ": tries to UNLOCK " ^ l ^ " without holding it")
          end
      | check (IfelseA ((_, ifBody), elseBody) :: rest) held =
          (case check ifBody held of
              SOME err => SOME err
            | NONE =>
              (case check elseBody held of
                  SOME err => SOME err
                | NONE => check rest held))
      | check (WhileA (_, body) :: rest) held = 
          (case check body held of
              SOME err => SOME err
            | NONE => check rest held)
      | check (_ :: rest) held = check rest held
  in
    check actions []
  end

(* Alternative CPS-style semantics *)
datatype csp_event = 
    LockEvent of string * int
  | UnlockEvent of string * int  
  | ReadEvent of string * int
  | UpdateEvent of string * int
  | AssignEvent of string * int
  | SkipEvent
(* Mise à jour de l’état fonctionnel *)
fun update_state state x v = fn y => if y = x then v else state y

(* Semantique CPS complète *)
fun sem_cps _ SKIP cont =
      (fn state => SkipEvent :: cont state)

  | sem_cps _ (Assign (x, e)) cont = 
      (fn state =>
        let
          val v = e state
        in
          AssignEvent (x, v) :: cont (update_state state x v)
        end)

  | sem_cps machine (Seq (P, Q)) cont = 
      sem_cps machine P (sem_cps machine Q cont)

  | sem_cps machine (Cond (cond, t1, t2)) cont =
      (fn state =>
        if cond state then sem_cps machine t1 cont state
        else sem_cps machine t2 cont state)

  | sem_cps machine (While (cond, body)) cont =
      (let
        fun loop state =
          if cond state then
            sem_cps  machine body loop state
          else cont state
      in loop end)

  | sem_cps machine (Lock id) cont =
      (fn state => LockEvent (id, get_lock_id id machine) :: cont state)

  | sem_cps machine (Unlock id) cont =
      (fn state => UnlockEvent (id, get_lock_id id machine) :: cont state)

  | sem_cps _ (Store (e, x)) cont =
    (fn state =>
      let
        val v = e state
        val new_state = update_state state x v
      in
        UpdateEvent (x, v) :: cont new_state
      end)
  | sem_cps _ (Load (x, y)) cont =
    (fn state =>
      let         
        val v = safe_lookup y state
        val new_state = update_state state x v
      in
        ReadEvent (y, v) :: cont new_state
      end)
type csp_trace = csp_event list

(* Fonction Sem adaptée avec gestion des événements CSP *)
fun sem_step (thy : theory) (machine: absy) (cmd : com) (cont : state * csp_trace -> state * csp_trace) 
             (s : state, trace : csp_trace) : state * csp_trace =
  case cmd of
    SKIP => cont (s, trace)
  | Assign (x, expr) => 
      let 
        val new_value = expr s
        val new_state = fn v => if v = x then new_value else s v
      in 
        cont (new_state, trace) 
      end
  | Seq (p, q) => 
      sem_step thy machine p (fn (s', trace') => sem_step thy machine  q cont (s', trace')) (s, trace)
  | Cond (guard, c1, c2) =>
      if guard s 
      then sem_step thy  machine  c1 cont (s, trace)
      else sem_step thy  machine c2 cont (s, trace)
  | While (guard, body) =>
      if guard s 
      then sem_step thy  machine body (fn (s', trace') => 
             sem_step thy  machine (While (guard, body)) cont (s', trace')) (s, trace)
      else cont (s, trace)
  | Lock lock_name => 
      let
        val lock_id = get_lock_id lock_name machine
        val new_trace = LockEvent (lock_name, lock_id) :: trace
      in
        cont (s, new_trace)
      end
  | Unlock lock_name =>
      let
        val lock_id = get_lock_id lock_name machine
        val new_trace = UnlockEvent (lock_name, lock_id) :: trace
      in
        cont (s, new_trace)
      end
  | Store (expr, var) =>
    let
      val value = expr s
      val new_state = update_state s var value
      val new_trace = UpdateEvent (var, value) :: trace
    in
      cont (new_state, new_trace)
    end
  | Load (local_var, global_var) =>
      let
        (*TODO*)
        val read_value = s global_var
        val new_state = fn v => if v = local_var then read_value else s v
        val new_trace = ReadEvent (global_var, read_value) :: trace
      in
        cont (new_state, new_trace)
      end

(* Analyses sémantiques avancées *)

(* Détection de deadlocks simples *)
fun detect_potential_deadlock (threads : thread_absy list) : string list =
  let
    fun extract_locks_from_actions (actions : a_term list) : string list =
      let
        fun extract_from_action action =
          case action of
            LockA bdg => [Binding.name_of bdg]
          | UnlockA bdg => []
          | IfelseA ((_, then_actions), else_actions) =>
              (extract_locks_from_actions then_actions) @ 
              (extract_locks_from_actions else_actions)
          | WhileA (_, body_actions) =>
              extract_locks_from_actions body_actions
          | _ => []                                                                                                       
      in
        List.concat (map extract_from_action actions)
      end
    
    fun get_thread_locks (thread : thread_absy) : string * string list =
      let
        val {nom_thread, actions, ...} = thread
        val locks = extract_locks_from_actions actions
      in
        (Binding.name_of nom_thread, locks)
      end
    
    val thread_locks = map get_thread_locks threads
    
    (* Détection simple : si deux threads utilisent les mêmes verrous *)
    fun find_shared_locks [] = []
      | find_shared_locks ((t1, locks1) :: rest) =
          let
            fun check_overlap (t2, locks2) =
              let
                val shared = List.filter (fn l => List.exists (fn l2 => l = l2) locks2) locks1
              in
                if null shared then NONE
                else SOME ("Potential deadlock between " ^ t1 ^ " and " ^ t2 ^ 
                          " on locks: " ^ String.concatWith ", " shared)
              end
            val warnings = List.mapPartial check_overlap rest
          in
            warnings @ find_shared_locks rest
          end
  in
    find_shared_locks thread_locks
  end

(* Détection de race conditions *)
fun detect_race_conditions (threads : thread_absy list) : string list =
  let
    fun extract_global_vars_from_actions (actions : a_term list) : (string * bool) list =
      let
        fun extract_from_action action =
          case action of
            SendA (bdg, _) => [(Binding.name_of bdg, true)]  (* write *)
          | ReceiveA (_, bdg) => [(Binding.name_of bdg, false)] (* read *)
          | IfelseA ((_, then_actions), else_actions) =>
              (extract_global_vars_from_actions then_actions) @ 
              (extract_global_vars_from_actions else_actions)
          | WhileA (_, body_actions) =>
              extract_global_vars_from_actions body_actions
          | _ => []
      in
        List.concat (map extract_from_action actions)
      end
    
    fun get_thread_global_access (thread : thread_absy) : string * (string * bool) list =
      let
        val {nom_thread, actions, ...} = thread
        val accesses = extract_global_vars_from_actions actions
      in
        (Binding.name_of nom_thread, accesses)
      end
    
    val thread_accesses = map get_thread_global_access threads
    
    (* Détection : si deux threads accèdent à la même variable et au moins un écrit *)
    fun find_races [] = []
      | find_races ((t1, accesses1) :: rest) =
          let
            fun check_race (t2, accesses2) =
              let
                fun has_conflict var =
                  let
                    val t1_writes = List.exists (fn (v, is_write) => v = var andalso is_write) accesses1
                    val t1_reads = List.exists (fn (v, is_write) => v = var andalso not is_write) accesses1
                    val t2_writes = List.exists (fn (v, is_write) => v = var andalso is_write) accesses2
                    val t2_reads = List.exists (fn (v, is_write) => v = var andalso not is_write) accesses2
                  in
                    (t1_writes orelse t1_reads) andalso (t2_writes orelse t2_reads) andalso
                    (t1_writes orelse t2_writes)
                  end
                
                val all_vars = map fst (accesses1 @ accesses2)
                val conflicting_vars = List.filter has_conflict all_vars
              in
                if null conflicting_vars then []
                else ["Potential race condition between " ^ t1 ^ " and " ^ t2 ^ 
                     " on variables: " ^ String.concatWith ", " conflicting_vars]
              end
            val warnings = List.concat (map check_race rest)
          in
            warnings @ find_races rest
          end
  in
    find_races thread_accesses
  end
(* Vérification de cohérence des types *)
fun type_check_thread (thy : theory) (thread : thread_absy) (vars_decl) : string list =
  let
    val {nom_thread, locals_decl, actions, locstab} = thread
    fun check_action_types (action, errors) =      case action of
        AssignA (bdg, term) =>
          let
            val var_name = Binding.name_of bdg
            val term_type = fastype_of term
            val expected_type_opt = 
                          case find_first (fn ((bdg', _), _) => Binding.name_of bdg' = var_name) locals_decl of
                            SOME ((_, typ), _) => SOME typ
                          | NONE => NONE
          in
            case expected_type_opt of
              SOME expected_type =>
                if term_type = expected_type then
                  errors
                else
                  ("Type mismatch in assignment to " ^ var_name ^
                   ": expected " ^ Syntax.string_of_typ_global thy expected_type ^
                   ", got " ^ Syntax.string_of_typ_global thy term_type) :: errors
            | NONE =>
                ("Variable " ^ var_name ^ " is not locally declared") :: errors
          end

      | SendA (bdg, term) =>
          let
            val var_name = Binding.name_of bdg
            val term_type = fastype_of term
            val expected_type_opt = 
                          case find_first (fn ( bdg', _, _, _) => Binding.name_of bdg' = var_name) vars_decl of
                            SOME ( _, typ, _, _) => SOME typ
                          | NONE => NONE
          in
            case expected_type_opt of
              SOME expected_type =>
                if term_type = expected_type then
                  errors
                else
                  ("Type mismatch in assignment to " ^ var_name ^
                   ": expected " ^ Syntax.string_of_typ_global thy expected_type ^
                   ", got " ^ Syntax.string_of_typ_global thy term_type) :: errors
            | NONE =>
                ("Variable " ^ var_name ^ " is not globally declared") :: errors
          end

      | ReceiveA (local_bdg, shared_bdg) =>
          let
            val local_var = Binding.name_of local_bdg
            val shared_var = Binding.name_of shared_bdg
            val local_type_opt =
                          case find_first (fn ((bdg', _), _) => Binding.name_of bdg' = local_var) locals_decl of
                            SOME ((_, typ), _) => SOME typ
                          | NONE => NONE

            val shared_type_opt =
              (* DOUBLE CHECK IF THIS CAN SAFELY BE REMOVED

              case Symtab.lookup varstab shared_var of
                SOME (SOME t) => fastype_of t
              | NONE =>
                case Symtab.lookup (!SPY |> Option.valOf |> #varstab) shared_var of
                  SOME (SOME t) => fastype_of t
                | _ => error ("Shared variable " ^ shared_var ^ " not declared")
              | SOME NONE => error ("Variable " ^ shared_var ^ " declared but has no initial value")*)
                case find_first (fn ( bdg', _, _, _) => Binding.name_of bdg' = shared_var) vars_decl of
                                            SOME ( _, typ, _, _) => SOME typ
                                          | NONE => NONE

           in
            case (local_type_opt, shared_type_opt) of
              (SOME local_type, SOME shared_type) =>
                if local_type = shared_type then 
                  errors
                else
                  ("Type mismatch in receive: cannot assign " ^ shared_var ^ " to " ^ local_var ^
                   " (expected " ^ Syntax.string_of_typ_global thy local_type ^
                   ", got " ^ Syntax.string_of_typ_global thy shared_type ^ ")") :: errors
            | (NONE, _) =>
                ("Local variable " ^ local_var ^ " not declared") :: errors
            | (_, NONE) =>
                ("Shared variable " ^ shared_var ^ " not declared") :: errors
          end
      | IfelseA ((cond, then_branch), else_branch) =>
        let
          val cond_type =
            let
              val t = cond
            in
              case cond of
                Free (x, _) =>
                  (case Symtab.lookup locstab x of
                     SOME (SOME t') => fastype_of t'
                   | SOME NONE => error ("Variable " ^ x ^ " declared but has no initial value")
                   | NONE =>
                       (case Symtab.lookup (!SPY |> Option.valOf |> #varstab) x of
                          SOME (SOME t') => fastype_of t'
                        | SOME NONE => error ("Global variable " ^ x ^ " declared but has no initial value")
                        | NONE => fastype_of t))  (* fallback to actual term type *)
              | _ => fastype_of t
            end
    
          val cond_error =
            if cond_type = @{typ bool} then []
            else ["Condition must be boolean, got: " ^ Syntax.string_of_typ_global thy cond_type]
    
          val then_errors = List.foldl check_action_types [] then_branch
          val else_errors = List.foldl check_action_types [] else_branch
        in
          cond_error @ then_errors @ else_errors @ errors
        end

     | WhileA (cond, body) =>
            let
              val cond_type =
                let
                  val t = cond
                in
                  case cond of
                    Free (x, _) =>
                      (case Symtab.lookup locstab x of
                         SOME (SOME t') => fastype_of t'
                       | SOME NONE => error ("Variable " ^ x ^ " declared but has no initial value")
                       | NONE =>
                           (case Symtab.lookup (!SPY |> Option.valOf |> #varstab) x of
                              SOME (SOME t') => fastype_of t'
                            | SOME NONE => error ("Global variable " ^ x ^ " declared but has no initial value")
                            | NONE => fastype_of t))  (* fallback *)
                  | _ => fastype_of t
                end
        
              val cond_error =
                if cond_type = @{typ bool} then []
                else ["While condition must be boolean, got: " ^ Syntax.string_of_typ_global thy cond_type]
        
              val body_errors = List.foldl check_action_types [] body
            in
              cond_error @ body_errors @ errors
            end

      | _ => errors

  in
    List.foldl check_action_types [] actions
  end

fun build_initial_state_for_thread 
      (globals : (binding * typ * Position.T * term option) list) 
      (locals : ((binding * typ) * term option) list) (thy: theory) : state =
  let
    fun term_to_int t_opt =
        case t_opt of
            NONE => 0
          | SOME t => eval_term_to_int thy t (fn _ => 0)

    val global_vals = map (fn (bdg, _, _, t_opt) =>
                            (Binding.name_of bdg, term_to_int t_opt)) globals

    val local_vals  = map (fn ((bdg, _), t_opt) =>
                            (Binding.name_of bdg, term_to_int t_opt)) locals

    val all_vals = local_vals @ global_vals
  in
    fn var => case AList.lookup (op =) all_vals var of
                SOME v => v
              | NONE => 0
  end

(* Fonction de vérification sémantique principale complète *)
fun semantic_check (absy_data : absy) (thy : theory) : theory =
  let
    val {system, globals_decls, varstab, locks_decls, threads_decls} = absy_data
    
    val _ = message false ("=== SEMANTIC ANALYSIS FOR SYSTEM: " ^ 
                          Binding.name_of system ^ " ===")
    
    (* Vérification 1: Analyse des deadlocks *)
    val deadlock_warnings = detect_potential_deadlock threads_decls
    val _ = if null deadlock_warnings then 
              message false "\<checkmark> No potential deadlocks detected"
            else 
              (message false "DEADLOCK WARNINGS:";
               map (message false) deadlock_warnings; ())
    
    (* Vérification 2: Analyse des race conditions *)
    val race_warnings = detect_race_conditions threads_decls  
    val _ = if null race_warnings then
              message false "\<checkmark> No race conditions detected"
            else
              (message false "RACE CONDITION WARNINGS:";
               map (message false) race_warnings; ())
    
    (* Vérification 3: Vérification des types pour chaque thread *)
    fun check_thread (machine :absy) (thread : thread_absy) : unit =
      let
        val{system, globals_decls, varstab, locks_decls, threads_decls} = machine
        val {nom_thread, locals_decl, actions, locstab} = thread
        val thread_name = Binding.name_of nom_thread
        
        val _ = message false ("Analyzing thread: " ^ thread_name)
        
        (* Conversion vers com pour analyse sémantique *)
        val com_program = convert_to_com thy actions varstab locstab

        val initial_state = build_initial_state_for_thread globals_decls locals_decl thy

        val cps_trace = sem_cps machine com_program (fn _ => []) initial_state

        val _ = message false (" \<checkmark> CPS-style trace for " ^ thread_name ^ ":")
        val _ = List.app (fn ev => message false ("    " ^ @{make_string} ev)) cps_trace
        (* Vérification des types *)
        val type_errors = type_check_thread thy thread globals_decls
        val _ = if null type_errors then
                  message false (" \<checkmark> Type checking passed for " ^ thread_name)
                else
                  (message false (" \<crossmark> Type errors in " ^ thread_name ^ ":");
                   map (fn err => message false ("    " ^ err)) type_errors; ())
        (* Vérification que lock et unlock respectent des regles d'appartenance *)
        val _ = case check_lock_ownership thread_name actions of
          NONE => ()
        | SOME msg => error msg

        (* Simulation d'exécution pour détecter d'autres problèmes *)
        val initial_state = build_initial_state_for_thread globals_decls locals_decl thy
        val (final_state, execution_trace) = 
          sem_step thy machine  com_program (fn (s, t) => (s, t)) (initial_state, [])
        
        val _ = message false ("  \<checkmark> Execution simulation completed for " ^ thread_name)
        val _ = message false (" Generated " ^ 
                             Int.toString (length execution_trace) ^ " CSP events")
      in
        ()
      end
    
    val _ = map (check_thread absy_data) (threads_decls)
    
    (* Vérification 4: Cohérence globale du système *)
    val _ = message false "=== GLOBAL SYSTEM CONSISTENCY ==="
    
    (* Vérifier que tous les verrous utilisés sont déclarés *)
    fun check_lock_declarations () =
      let
        val declared_locks = map (fn (bdg, _, _) => Binding.name_of bdg) locks_decls
        
        fun extract_used_locks_from_thread (thread : thread_absy) =
          let
            fun extract_from_actions actions =
              List.concat (map (fn action =>
                case action of
                  LockA bdg => [Binding.name_of bdg]
                | UnlockA bdg => [Binding.name_of bdg]
                | IfelseA ((_, then_acts), else_acts) =>
                    extract_from_actions then_acts @ extract_from_actions else_acts
                | WhileA (_, body_acts) => extract_from_actions body_acts
                | _ => []) actions)
          in
            extract_from_actions (#actions thread)
          end
        
        val used_locks = List.concat (map extract_used_locks_from_thread threads_decls)
        val undeclared_locks = List.filter (fn used => 
          not (List.exists (fn decl => decl = used) declared_locks)) used_locks
      in
        if null undeclared_locks then
          message false "\<checkmark> All used locks are properly declared"
        else
          (message false "\<crossmark> Undeclared locks used:";
           map (fn lock => message false ("  " ^ lock)) undeclared_locks; ())
      end
    
    val _ = check_lock_declarations ()
    
    fun check_var_declarations () =
      let
        (* ------------------ 1. Ensemble des noms globaux ---------------- *)
        val global_names =
          map (fn (bdg, _, _, _) => Binding.name_of bdg) globals_decls
    
        (* ------------------ 2. Noms locaux d’un thread ------------------ *)
        fun local_names_of_thread ({locals_decl, ...} : thread_absy) : string list =
          map (fn ((bdg, _), _) => Binding.name_of bdg) locals_decl
    
        (* ------------------ 3. Variables utilisées dans des actions ----- *)
        fun extract_vars (actions : a_term list) : string list =
          List.concat (map (fn action =>
            case action of
                AssignA  (bdg, _)        => [Binding.name_of bdg]
              | SendA    (bdg, _)        => [Binding.name_of bdg]
              | ReceiveA (lbdg, sbdg)    => [Binding.name_of lbdg,
                                             Binding.name_of sbdg]
              | IfelseA  ((_, t1), t2)   => extract_vars t1 @ extract_vars t2
              | WhileA   (_, body)       => extract_vars body
              | _                        => []) actions)
    
        (* ------------------ 4. Manquantes dans un thread donné ---------- *)
        fun undeclared_in_thread (thr : thread_absy) : string list =
          let
            val declared = global_names @ local_names_of_thread thr
            val used     = extract_vars (#actions thr)
          in
            List.filter (fn v => not (List.exists (fn d => d = v) declared)) used
          end
    
        (* ------------------ 5. Agrégation globale ----------------------- *)
        val missing =
          List.concat (map undeclared_in_thread threads_decls)
          |> sort_distinct string_ord
      in
        if null missing then
          message false "\<checkmark> All used variables are properly declared (globals or locals)"
        else
          (message false "\<crossmark> Undeclared variables (neither global nor local):";
           List.app (fn v => message false ("  " ^ v)) missing)
      end
    
    (* Appel de la vérification dans semantic_check ---------------------- *)
    val _ = check_var_declarations ()
    
    val _ = message false "=== SEMANTIC CHECK COMPLETED ==="
  in
    thy
  end

fun semantics (absy_cl: theory -> absy) (thy : theory) = 
  let
    val absy_data = absy_cl thy
  in
    semantic_check absy_data thy
  end

fun sequence_actions [] = SkipA
  | sequence_actions [a] = a
  | sequence_actions (a::rest) = SeqA (a, sequence_actions rest)
(*
(*Fonction pour générer le code CSP complet *)
fun generate_csp_code (absy_data : absy) (thy : theory) : string =
let
    val {system, globals_decls, locks_decls, threads_decls, varstab} = absy_data
    val system_name = Binding.name_of system

    (*Génération des événements CSP *)
    fun generate_events () =
      let
        val lock_events = map (fn (bdg, _, _) => 
          let val name = Binding.name_of bdg
          in "channel lock_" ^ name ^ ", unlock_" ^ name ^ " : Int"
          end) locks_decls

        val global_events = map (fn (bdg, _, _, _) =>
          let val name = Binding.name_of bdg  
          in "channel read_" ^ name ^ ", update_" ^ name ^ " : Int"
          end) globals_decls
      in
        String.concatWith "\n" (lock_events @ global_events)
      end

    (*Conversion d'une action en CSP *)
fun action_list_to_csp [] state thy = ("SKIP", state)
  | action_list_to_csp [a] state thy = action_to_csp a state thy
  | action_list_to_csp (a::rest) state thy =
      let
        val (s1, state1) = action_to_csp a state thy
        val (s2, state2) = action_list_to_csp rest state1 thy
      in
        if (a =SkipA) then 
          (s2, state2)
        else
          (s1 ^ "\<rightarrow>" ^ s2, state2)
      end

and action_to_csp action state thy =
  case action of
   SkipA => ("SKIP", state)
  | LockA bdg => ("lock_" ^ Binding.name_of bdg ^ "!0", state)
  | UnlockA bdg => ("unlock_" ^ Binding.name_of bdg ^ "!0", state)
  | AssignA (bdg, term) =>
      let
        val name = Binding.name_of bdg
        val typ = fastype_of term
        val v = if typ = @{typ bool}
                then if eval_term_to_bool thy term state then 1 else 0
                else eval_term_to_int thy term state
        val new_state = update_state state name v
      in
        ("update_" ^ name ^ "!" ^ Int.toString v, new_state)
      end
  | SendA (bdg, term) =>
      let
        val name = Binding.name_of bdg
        val typ = fastype_of term
        val v = if typ = @{typ bool}
                then if eval_term_to_bool thy term state then 1 else 0
                else eval_term_to_int thy term state
        val new_state = update_state state name v
      in
        ("update_" ^ name ^ "!" ^ Int.toString v, new_state)
      end
  | ReceiveA (local_bdg, global_bdg) =>
      let
        val global_var_name = Binding.name_of global_bdg
        val v = safe_lookup global_var_name state
        val local_var_name = Binding.name_of local_bdg
        val new_state = update_state state local_var_name v
      in
        ("read_" ^ global_var_name ^ "!" ^ Int.toString v, new_state)
      end
  | IfelseA ((cond, a1), a2) =>
      let
        val b = eval_term_to_bool thy cond state
        val val_str = if b then "true" else "false"
        val (then_code, _) = action_list_to_csp a1 state thy
        val (else_code, _) = action_list_to_csp a2 state thy
      in
        ("{ (" ^ val_str ^ " & " ^ then_code ^ ") [] (\<not>" ^ val_str ^ " & " ^ else_code ^ ") }", state)
      end
  | WhileA (cond, body) =>
      let
        val val_str = if eval_term_to_bool thy cond state then "true" else "false"
        val (body_code, _) = action_list_to_csp body state thy
      in
        ("{ (" ^ val_str ^ " &  µ X." ^ body_code ^ " -> X) [] (\<not>" ^ val_str ^" & (SKIP) ) }", state)
      end


    (* Conversion d’un thread vers CSP *)
        fun thread_to_csp globals_decls (thread : thread_absy) thy : string =
          let
            val {nom_thread, actions, locals_decl, ...} = thread
            val thread_name = Binding.name_of nom_thread
        
            val initial_state = build_initial_state_for_thread globals_decls locals_decl thy
            val (code, _) = action_list_to_csp actions initial_state thy
          in
            thread_name ^ " = " ^ code 
          end
          
    fun generate_threads globals_decls threads_decls thy =
        String.concatWith "\n" (map (fn t => thread_to_csp globals_decls t thy) threads_decls)

    (*Génération du système global *)
    fun generate_system () =
      let
        val thread_names = map (fn t => Binding.name_of (#nom_thread t)) threads_decls
      in
        system_name ^ " = " ^ String.concatWith " ||| " thread_names
      end

  in
    String.concatWith "\n\n" [
      "-- Channels",
      generate_events (),
      "",
      "-- Threads",
      generate_threads globals_decls threads_decls thy,
      "",
      "-- System",
      generate_system ()
    ]
  end
*)

\<close>
section\<open>Semantic Encoding\<close>
(**************************En travaux***********************)
(*datatype status = Success | Timeout*)

definition SKIP_process :: "evs process"(*\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k*)
  where "SKIP_process \<equiv> Skip"

ML\<open>
(* Convertir une liste de a_term en une seule commande de type com *)
fun sequence_actions [] = SkipA
  | sequence_actions [a] = a
  | sequence_actions (a :: rest) = SeqA (a, sequence_actions rest)
(*
fun subst_with_fresh_env (env_type : typ) (t : term) : term * term =
  let
    (* collect free variable names *)
    val frees = Term.add_free_names t []

    (* generate a fresh variable name "\<sigma>", adding primes if necessary *)
    fun fresh_name base [] = base
      | fresh_name base used =
          let
            fun bump n =
              let val candidate = base ^ replicate_string n "'" in
                if member (op =) used candidate then bump (n + 1) else candidate
              end
          in bump 1 end

    val sigma_name = fresh_name "\<sigma>" frees
    val sigma = Free (sigma_name, env_type)

    (* perform substitution: Free(x) becomes sigma $ "x" *)
    fun subst t =
      case t of
        Free (name, _) => sigma $ HOLogic.mk_string name
      | Const _ => t
      | Bound _ => t
      | Var _ => t
      | Abs (n, T, body) => Abs (n, T, subst body)
      | t1 $ t2 => subst t1 $ subst t2

    val t_subst = subst t
  in
    (sigma, t_subst)
  end
*)

val sigma : term = Free ("\<sigma>", @{typ "string \<Rightarrow> int"})   (* changer le type ici si besoin *)


fun subst_with_sigma (t : term) : term =
  let
    fun subst tm =
      case tm of
        Free (name, _)           => sigma $ HOLogic.mk_string name
      | Const _                  => tm
      | Bound _                  => tm
      | Var _                    => tm
      | Abs (n, T, body)        => Abs (n, T, subst body)
      | tm1 $ tm2               => subst tm1 $ subst tm2
  in
    subst t
  end

fun lambda_sigma_apply_var (env_type : typ) (var_name : string) : term =
  let
    val bound_sigma = Bound 0
    val body = bound_sigma $ HOLogic.mk_string var_name
  in
    Abs ("\<sigma>", env_type, body)
  end

(* 
  Crée une abstraction \<lambda>\<sigma>:typ. t
  en remplaçant les Free("\<sigma>", typ) par Bound 0 dans t
*)
fun make_lambda_sigma (env_type : typ) (sigma_name : string) (t : term) : term =
  let
    fun subst tm =
      case tm of
        Free (n, T) => if n = sigma_name andalso T = env_type then Bound 0 else tm
      | Const _ => tm
      | Bound _ => tm
      | Var _ => tm
      | Abs (n, T, body) => Abs (n, T, subst body)
      | t1 $ t2 => subst t1 $ subst t2
  in
    Abs (sigma_name, env_type, subst t)
  end
(* Conversion d'une action abstraite (a_term) vers le terme logique com *)
fun quote_com _ SkipA =
      @{term "com.SKIP :: com"}  
  (*| quote_com (AssignA (b, e)) =
    let
      val var_str = HOLogic.mk_string (Binding.name_of b)

      val (sigma, e') = subst_with_fresh_env @{typ "string \<Rightarrow> int"} e
      val lam = Abs (fst (Term.dest_Free sigma), @{typ "string \<Rightarrow> int"}, e')
      val lam = Abs ("\<sigma>", @{typ "string \<Rightarrow> nat"}, e')

    in
      @{term assign} $ var_str $ lam
    end*)
   (* | quote_com (AssignA (b, e)) =
        let
          val var_str = HOLogic.mk_string (Binding.name_of b)
          val e'      = subst_with_sigma e               (* \<sigma> ''x'' \<dots> *)
          val lam     = Abs ("\<sigma>", @{typ "string \<Rightarrow> int"}, e')*)
| quote_com _ (AssignA (b, e)) =
    let
      val var_str = HOLogic.mk_string (Binding.name_of b)
      val expr = subst_with_sigma e  (* ou autre expression contenant \<sigma> ''x'' *)
      val lam = make_lambda_sigma @{typ "string \<Rightarrow> int"} "\<sigma>" expr
    in
      @{term com.assign} $ var_str $ lam
    end
       
  | quote_com machine (SeqA (c1, c2)) =
      @{term com.seq} $ quote_com machine c1 $ quote_com machine c2
  | quote_com machine (LockA b) =
      let 
        val n_str = Binding.name_of b
        val n = HOLogic.mk_number @{typ int} (get_lock_id n_str machine)
        (*val n = case Int.fromString n_str of
                  SOME i => HOLogic.mk_number @{typ nat} i
                | NONE => error ("Invalid lock number: " ^ n_str)*)
      in 
        @{term "com.lock :: int \<Rightarrow> com"} $ n 
      end
  | quote_com machine (UnlockA b) =
      let 
        val n_str = Binding.name_of b
       val n = HOLogic.mk_number @{typ int} (get_lock_id n_str machine)
      in 
        @{term "com.unlock :: int \<Rightarrow> com"} $ n 
      end
  | quote_com _ (SendA (sv, e)) =
      let
        val sv_str = HOLogic.mk_string (Binding.name_of sv)
        val expr = subst_with_sigma e 
        val lam = make_lambda_sigma @{typ "string \<Rightarrow> int"} "\<sigma>" expr
      in 
        @{term "com.send :: (\<sigma> \<Rightarrow> int) \<Rightarrow> string \<Rightarrow> com"} $ lam $ sv_str
       end

  | quote_com _ (ReceiveA (v, sv)) =
      let
        val v_str = HOLogic.mk_string (Binding.name_of v)
        val sv_str = HOLogic.mk_string (Binding.name_of sv)
      in
        @{term "com.rec :: string \<Rightarrow> string \<Rightarrow> com"} $ v_str $ sv_str
      end
  | quote_com machine (IfelseA ((cond, then_branch), else_branch)) =
    let
     (* val (sigma, e') = subst_with_fresh_env @{typ "string \<Rightarrow> int"} cond
         
      val lam = Abs (fst (Term.dest_Free sigma), @{typ "string \<Rightarrow> int"}, e')*)

      val expr = subst_with_sigma cond
      val lam = make_lambda_sigma @{typ "string \<Rightarrow> int"} "\<sigma>" expr
    in
      @{term com.cond} $ lam 
                   $ quote_com machine (sequence_actions then_branch)
                   $ quote_com machine (sequence_actions else_branch)
    end
      
  | quote_com machine (WhileA (cond, body)) =
         let
      val expr = subst_with_sigma cond 
      val lam = make_lambda_sigma @{typ "string \<Rightarrow> int"} "\<sigma>" expr
           
          in
            @{term com.while} $ lam 
                         $ quote_com machine (sequence_actions body)
          end
\<close>

ML\<open>
(* Fonction pour déclarer les termes des threads *)
fun declare_thread_terms (thy: theory) (machine : absy) (threads: thread_absy list)
                         (varstab: (term option) Symtab.table)
                         : theory =
  fold (fn {nom_thread, actions, ...} => fn thy' =>
    let
      val name = Binding.name_of nom_thread
      val bname = Binding.name (name ^ "_term")

      (* Convert actions into com *)
      val com_ast = sequence_actions actions
      val com_term = quote_com machine com_ast
      val com_term = Type.constraint @{typ com} com_term
  
      (* Create a simple definition: thread_name_term = com_term *)
      val lthy = Named_Target.theory_init thy'
      val ((_, term_def), lthy') =
        Local_Theory.define ((bname, NoSyn), ((Binding.empty, []), com_term)) lthy
      val thy'' = Local_Theory.exit_global lthy'
      
      val _ = writeln ("\<checkmark> Defined command term: " ^ Binding.name_of bname)

      (* Optionally, create the semantic term separately *)
      val sem_bname = Binding.name (name ^ "_sem")
      val cont = Abs ("s", @{typ \<sigma>}, @{term "SKIP_process"})
      val sem_term = @{const Sem\<^sub>0} $ com_term $ cont
      
      val lthy2 = Named_Target.theory_init thy''
      val ((_, sem_def), lthy2') =
        Local_Theory.define ((sem_bname, NoSyn), ((Binding.empty, []), sem_term)) lthy2
      val thy''' = Local_Theory.exit_global lthy2'
      
      val _ = writeln ("\<checkmark> Defined semantic term: " ^ Binding.name_of sem_bname)

    in
      thy'''
    end)
    threads thy
\<close>

ML\<open>
(* Fonction pour générer les termes sémantiques *)
fun generate_terms (absy_data : absy) (thy : theory) : theory =
  let 
    val {system, globals_decls, locks_decls, threads_decls, varstab} = absy_data
    val system_name = Binding.name_of system

    (* Fonction pour vérifier l'égalité des termes dans une table *)
    fun term_equals_in_table (tab : (term option) Symtab.table) (b : binding) (t : term) : bool =
      case Symtab.lookup tab (Binding.name_of b) of
        SOME (SOME t') => Term.aconv (t, t')
      | _ => false

    (* Fonction pour mettre à jour l'état *)
    fun update_state (locstab : (term option) Symtab.table)
                     (globtab : (term option) Symtab.table)
                     (state : term -> int)
                     (x : binding)
                     (v : int) : term -> int =
      let
        val x_name = Binding.name_of x
        fun equals_var y =
          case Symtab.lookup locstab x_name of
            SOME (SOME t') => Term.aconv (y, t')
          | _ =>
              (case Symtab.lookup globtab x_name of
                 SOME (SOME t'') => Term.aconv (y, t'')
               | _ => false)
      in
        fn y => if equals_var y then v else state y
      end

    (* Fonction d'évaluation basique d'un terme *)
    fun eval_term (t : term) (state : term -> int) : int =
      case t of
        Const (@{const_name "Groups.zero_class.zero"}, _) => 0
      | Const (@{const_name "Groups.one_class.one"}, _) => 1
      | x => state x  (* Évaluation simplifiée,TODO *)

    (* Fonction pour convertir une action en terme *)
    fun action_to_term (action : a_term)
                       (state : term -> int)
                       (locstab : term option Symtab.table)
                       (globtab : term option Symtab.table)
        : term * (term -> int) =
      case action of
        SkipA => 
          (@{term "com.SKIP :: com"}, state)
          
      | AssignA (name, assignation) =>
          let
            val v = eval_term assignation state
            val updated_state = update_state locstab globtab state name v
            val name_str = HOLogic.mk_string (Binding.name_of name)
            val assign_term = @{term assign} $ name_str $ assignation
          in
            (assign_term, updated_state)
          end

      | SeqA (SkipA, C) =>
          action_to_term C state locstab globtab

      | SeqA (A, B) =>
          let
            val (term_A, stateA) = action_to_term A state locstab globtab
            val (term_B, stateB) = action_to_term B stateA locstab globtab
            val seq_term = @{term com.seq} $ term_A $ term_B
          in
            (seq_term, stateB)
          end

      | LockA name =>
          let
            val n_str = Binding.name_of name
            val n = HOLogic.mk_number @{typ int} (get_lock_id n_str absy_data)
            val lock_term = @{term com.lock} $ n
          in
            (lock_term, state)
          end

      | UnlockA name =>
          let
            val n_str = Binding.name_of name
            val n = HOLogic.mk_number @{typ int} (get_lock_id n_str absy_data)
            (*val n = case Int.fromString n_str of
                      SOME i => HOLogic.mk_number @{typ nat} i
                    | NONE => error ("Invalid unlock number: " ^ n_str)*)
            val unlock_term = @{term com.unlock} $ n
          in
            (unlock_term, state)
          end

      | _ => 
          error ("Unsupported action type in action_to_term")

    (* État par défaut *)
    fun default_state (_ : term) = 0

    (* Traiter tous les threads *)
    val _ = List.app (fn {nom_thread, actions, locstab, ...} =>
      case actions of
        [] => writeln ("Thread " ^ Binding.name_of nom_thread ^ " has no actions")
      | _ =>
          let
            val _ = writeln ("== Processing thread " ^ Binding.name_of nom_thread ^ " ==")
            val com_ast = sequence_actions actions
            val (res_term, final_state) = action_to_term com_ast default_state locstab varstab
            val _ = writeln ("\<checkmark> Successfully processed thread " ^ Binding.name_of nom_thread)
          in
            ()
          end
    ) threads_decls

    (* Déclarer les termes des threads dans la théorie *)
    val thy' = declare_thread_terms thy absy_data threads_decls varstab
  in
    thy'
  end

fun define_cmd (const_name : string) (rhs : term) (thy : theory) : theory =
  let
    val bname  = Binding.name const_name           (* nom de la constante *)
    val lthy   = Named_Target.theory_init thy      (* entrée en contexte local *)

    (*   definition const_name where "const_name = rhs"   *)
    val ((_, def_thm), lthy') =
      Local_Theory.define ((bname, NoSyn), ((Binding.empty, []), rhs)) lthy

    val thy'   = Local_Theory.exit_global lthy'    (* on ressort en théorie *)

    val _ = writeln ("\<checkmark> defined “" ^ const_name ^ "” : " ^
                     Syntax.string_of_typ_global thy' (fastype_of rhs))
    val _ = writeln ("" ^ Syntax.string_of_term_global thy' rhs)
    val _ = writeln (" theorem: " ^ Thm.string_of_thm_global thy' (snd def_thm))
  in
    thy'
  end
\<close>

(**********************************************************)
(*abbreviation UNIV :: "(sema_evs + vars_ev) set"
  where "UNIV \<equiv> top"*)
(*fun mk_UNIV T = Const ("Orderings.top_class.top", mk_setT T);
*)
section\<open>Impression\<close>
ML\<open>   
fun mk_sumT (T1, T2) = Type ("Sum_Type.sum", [T1, T2])

val UNIV_ = HOLogic.mk_UNIV @{typ evs}
val empty_evs_set = Const (@{const_name bot}, @{typ "evs set"})


fun mk_fun_upd (f, x, y) =
  let
    val T_dom = @{typ string}
    val T_cod = @{typ int}
  in
    Const (@{const_name fun_upd},
           (T_dom --> T_cod) --> T_dom --> T_cod --> (T_dom --> T_cod))
    $ f $ x $ y
  end

fun make_sigma_term (tab : term option Symtab.table) : term =
  let
    val zero = HOLogic.mk_number @{typ int} 0
    val base = Abs ("_", @{typ string}, zero) 

    fun apply_update (name, SOME value) acc =
          mk_fun_upd (acc, HOLogic.mk_string name, value)
      | apply_update (_, NONE) acc = acc

    val updated = Symtab.fold apply_update tab base
  in
    updated  
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>SYSTEM\<close>
      "defines System Specification"
      (parse_system_spec >>
       (fn system_data => Toplevel.theory (fn thy =>
        let
          (* 1. syntactic & semantic checks -------------------------------- *)
          val checked  = context_check system_data thy
          val thy_sem  = semantic_check checked thy

          val lthy0 = Named_Target.theory_init thy_sem

          fun define_cmd ({nom_thread, actions, ...} : thread_absy) lthy =
            let
              val name      = Binding.name_of nom_thread
              val const_bnd = Binding.name (name ^ "_cmd")
              val com_term  = quote_com checked (sequence_actions actions)
              val ((_, _), lthy') =
                    Local_Theory.define ((const_bnd, NoSyn),
                                         ((Binding.empty, []), com_term)) lthy

      (*Affichage*)
              val _ = writeln ("\<checkmark> Defined constant: " ^ Binding.name_of const_bnd)
            
              val _ = writeln ("  " ^ Syntax.string_of_term_global thy_sem com_term)

              in lthy' end

          val lthy_final = fold define_cmd (#threads_decls checked) lthy0
          val thy'       = Local_Theory.exit_global lthy_final

            
          (* ---------------------------------------------------------------- *)
          (* 2.  Construction du réseau GLOBALVARS ------------------------- *)
        (*  val globals_names : term list =
            map (fn (b, _, _, _) => HOLogic.mk_string (Binding.name_of b)) (#globals_decls checked)
          
          val globals_list_term =
            HOLogic.mk_list @{typ string} globals_names
          
          val globals_mset_term =
            Cspm_API.mk_mset globals_list_term
          
          (*val sumT = Type ("Sum_Type.sum", [@{typ sema_evs}, @{typ vars_ev}])*)
          val procT = Cspm_API.mk_processT @{typ evs}
          val sigma0_term = make_sigma_term (#varstab checked)    
      
          (*val GLOBALVARS_const =
            Const (@{const_name GLOBALVARS}, @{typ string} --> procT)
          
          val lam_GLOBALVARS =
            Abs ("idx", @{typ string}, GLOBALVARS_const $ Bound 0)*)

          val GLOBALVARS_partial = Const (@{const_name GLOBALVARS}, @{typ \<sigma>} --> @{typ string} --> procT)
          val lam_GLOBALVARS = Abs ("idx", @{typ string}, GLOBALVARS_partial $ sigma0_term $ Bound 0)

          val temp_test = Cspm_API.mk_MultiInter globals_mset_term lam_GLOBALVARS
           val _ = writeln ("[SYSTEM]  global test :\n  " ^
                                     Syntax.string_of_term_global thy' temp_test) 
val _ = tracing ("\n [DEBUG] Type full_term = " ^
                                 Syntax.string_of_typ_global @{theory} (fastype_of (temp_test) ))       



          val processes : term list =
            map (fn name => lam_GLOBALVARS $ name) globals_names
          (* globals_names : term list de strings *)
          
          val globals_net_term : term option =
            (case processes of
               [] => NONE
             | [t] => SOME t
             | ts => SOME (foldr1 (fn (t1, t2) => Cspm_API.mk_Inter t1 t2) ts))*)

          (* 2. Construction du réseau GLOBALVARS compactifié ------------------------- *)
          val globals_names : term list =
            map (fn (b, _, _, _) => HOLogic.mk_string (Binding.name_of b)) (#globals_decls checked)
          
          val globals_list_term =
            HOLogic.mk_list @{typ string} globals_names
          
          val globals_mset_term =
            Cspm_API.mk_mset globals_list_term
          
          val procT = Cspm_API.mk_processT @{typ evs}
          val sigma0_term = make_sigma_term (#varstab checked)
          
          val GLOBALVARS_partial = Const (@{const_name GLOBALVARS}, @{typ \<sigma>} --> @{typ string} --> procT)
          val lam_GLOBALVARS = Abs ("idx", @{typ string}, GLOBALVARS_partial $ sigma0_term $ Bound 0)
          
          (* Utilisation de MultiSync avec ensemble d'événements vide pour compactifier *)
          val globals_net_term : term option =
            (case globals_names of
               [] => NONE
             | _ => 
               let
                 val multisync_const = Const (@{const_name MultiSync}, 
                                             @{typ "evs set"} --> 
                                             @{typ "string multiset"} --> 
                                             @{typ "string \<Rightarrow> (evs) process"} --> 
                                             @{typ "(evs) process"})
                 val compact_term = multisync_const $ empty_evs_set $ globals_mset_term $ lam_GLOBALVARS
               in
                 SOME compact_term
               end)
          
          val _ = (case globals_net_term of
                    SOME t => writeln ("[SYSTEM] réseau GLOBALVARS compactifié :\n  " ^
                                      Syntax.string_of_term_global thy' t)
                  | NONE => writeln ("[SYSTEM] Aucune variable globale déclarée"))
          
          

          (* 3.  Construction du réseau SEMAPHORES -------------------------------- *)
          
          (* extraire les noms de verrous depuis checked *)
          
          val lock_ids_terms : term list =
            map (fn (b, _, _) =>
                   HOLogic.mk_number @{typ int} (get_lock_id (Binding.name_of b) checked))  
                   (* get_lock_id : binding -> int *)
                       (#locks_decls checked)
          
          val locks_list_term =
            HOLogic.mk_list @{typ int} lock_ids_terms
          
          val locks_mset_term =
            Cspm_API.mk_mset locks_list_term  (* {# \<dots> #} *)
          
          val SEMAPHORES_const =
            Const (@{const_name SEMAPHORES}, @{typ int} --> procT)

         val lam_SEMAPHORES =
                    Abs ("idx", @{typ int}, SEMAPHORES_const $ Bound 0)
        val processes : term list = map (fn name => lam_SEMAPHORES $ name) lock_ids_terms
          (* globals_names : term list de strings *)
          
       (*  val semaphores_net_term : term option =
              case processes of
                [] => NONE
              | [t] => SOME t
              | ts => SOME (foldr1 (fn (t1, t2) => Cspm_API.mk_Inter t1 t2) ts)*)

 
          val semaphores_net_term : term option =
            (case lock_ids_terms of
               [] => NONE
             | _ =>
               let
                 val empty_evs_set = Const (@{const_name bot}, @{typ "evs set"})
                 val multisync_const = Const (@{const_name MultiSync}, 
                                              @{typ "evs set"} --> 
                                              @{typ "int multiset"} --> 
                                              @{typ "int \<Rightarrow> (evs) process"} --> 
                                              @{typ "(evs) process"})
                 val compact_term = multisync_const $ empty_evs_set $ locks_mset_term $ lam_SEMAPHORES
               in
                 SOME compact_term
               end)
            

         
          
          (*val semaphores_net_term = 
             SOME( Cspm_API.mk_MultiInter_ sumT locks_mset_term lam_SEMAPHORES ) *)          

             (*|NONE => writeln ("[SYSTEM]  réseau SEMAPHORES :\n Vous n'avez pas de Locks \n") *)

          (* 4. Construction du réseau des THREADS --------------------------- *)
         (* val thread_names : string list =
            map (fn {nom_thread, ...} => Binding.name_of nom_thread) (#threads_decls checked)

          val thread_consts : term list =
            map (fn name =>
              Const (Sign.full_name thy (Binding.name (name ^ "_cmd")), @{typ com}))
            thread_names


          val thread_processes : term list =
            map (fn t => sem_const $ t) thread_consts

          val thread_net_term =
            (case thread_processes of
                [] => error "No threads declared"
              | [t] => t
              | ts => foldr1 (fn (t1, t2) => Cspm_API.mk_Inter t1 t2) ts)*)
          (*fun define_cmd ({nom_thread, actions, ...} : thread_absy) lthy =
            let
              val name      = Binding.name_of nom_thread
              val const_bnd = Binding.name (name ^ "_cmd")
              val com_term  = quote_com checked (sequence_actions actions)
              val ((lhs, _), lthy') =
                    Local_Theory.define ((const_bnd, NoSyn),
                                         ((Binding.empty, []), com_term)) lthy
              val const_name = Local_Theory.full_name lthy' const_bnd
              val _ = writeln ("\<checkmark> Defined constant: " ^ const_name)
            in
              (const_name, lthy')  (* swapped! *)
            end*)
          fun define_cmd ({nom_thread, actions, ...} : thread_absy) lthy =
            let
              val name      = Binding.name_of nom_thread
              val const_bnd = Binding.name (name ^ "_cmd")
              val com_term  = quote_com checked (sequence_actions actions)
              
              val _ = Thm.cterm_of (Proof_Context.init_global (Local_Theory.exit_global lthy)) com_term
              
              val const_type = fastype_of com_term
              val lhs_const = Free (Binding.name_of const_bnd, const_type)
              val def_eq = Logic.mk_equals (lhs_const, com_term)
              
              val ((lhs_term, (_, def_thm)), lthy') = 
                Specification.definition
                  {verbose = true}
                  (SOME (const_bnd, NONE, NoSyn))  (* binding option *)
                  []                               (* parameters list *)
                  []                               (* premises list *)
                  ((Binding.empty, []), def_eq)    (* attributes and equation *)
                  lthy                             (* local theory *)
              
              val const_name = Local_Theory.full_name lthy' const_bnd
              val _ = writeln ("\<checkmark> Defined constant: " ^ const_name)
            in
              (const_name, lthy')  
            end
          (* 1. Définition des constantes de threads, et sortie du local_theory *)
          val (cmd_const_names, lthy_final) =
            fold_map define_cmd (#threads_decls checked) lthy0
          
          val thy' = Local_Theory.exit_global lthy_final
          
          (* 2. Maintenant on peut construire les termes Const(...) depuis thy' *)
          val thread_consts : term list =
            map (fn full_name => Const (full_name, @{typ com})) cmd_const_names

          (* A.  noms des threads ------------------------------------------------ *)
          val thread_names : string list =
            map (fn {nom_thread, ...} => Binding.name_of nom_thread)
                (#threads_decls checked)
          

          
          (* C.  fabrique le réseau LOCALVARS pour un thread donné --------------- *)
          fun localvars_net ({locals_decl, locstab, ...} : thread_absy) : term option =
              if null locals_decl then NONE
              else    
                let
                    val names =
                      map (fn ((bdg,_),_) => HOLogic.mk_string (Binding.name_of bdg)) locals_decl
                    val mset = Cspm_API.mk_mset (HOLogic.mk_list @{typ string} names)
              
                    (* --- nouveau \<sigma> pour CE thread --- *)
                    val sigma_thread_term = make_sigma_term locstab
              
                    val LOCALVARS_partial =
                          Const (@{const_name LOCALVARS},
                                  @{typ \<sigma>} --> @{typ string} --> procT)
              
                    val lam =
                          Abs ("idx", @{typ string},
                               LOCALVARS_partial $ sigma_thread_term $ Bound 0)
  
                   val processes : term list =
                              map (fn name => lam $ name) names
            
                    val locals_net_term : term option =
                    (case globals_names of
                       [] => NONE
                     | _ => 
                       let
                         val empty_evs_set = Const (@{const_name bot}, @{typ "evs set"})
                         val multisync_const = Const (@{const_name MultiSync}, 
                                                     @{typ "evs set"} --> 
                                                     @{typ "string multiset"} --> 
                                                     @{typ "string \<Rightarrow> (evs) process"} --> 
                                                     @{typ "(evs) process"})
                         val compact_term = multisync_const $ empty_evs_set $ mset $ lam
                       in
                         SOME compact_term
                       end)
                in
                   locals_net_term
                  (*(case processes of
                      [] => NONE
                    | [t] => SOME t
                    | ts => SOME (foldr1 (fn (t1, t2) => Cspm_API.mk_Inter t1 t2) ts))
                  *)

                end
            
          
          (* D.  compose  Sem ti_cmd  ||  LOCALVARSᵢ  ---------------------------- *)
         
          val sem_const = Const (@{const_name Sem}, @{typ com} --> procT)
          val thread_processes : term list =
            ListPair.map (fn (th_absy, cmd_term) =>
                let
                  val sem_proc = sem_const $ cmd_term
                  val lvars_net = localvars_net th_absy 
                in
                  case lvars_net of 
                  NONE =>  sem_proc 
                  |SOME t =>Cspm_API.mk_Sync sem_proc UNIV_ t(* par_const $ sem_proc $ @{term UNIV} $ t*)
                end)
              (#threads_decls checked, thread_consts)
             
          (* E.  réseau des threads (+ locals) combiné avec  ||| ----------------- *)
          val thread_net_term : term =
            (case thread_processes of
                []   => error "No threads declared"
              | [t]  => t
              | ts   => foldr1 (fn (t1, t2) => Cspm_API.mk_Inter t1 t2) ts)
          
                    val _ = writeln ("[SYSTEM]  réseau THREADS :\n  " ^
                                     Syntax.string_of_term_global thy' thread_net_term)
                    (* 5. Composition globale :  (SEMAPHORES ||| GLOBALVARS) [|UNIV|]  THREADS  *)

                    val net1 = (case globals_net_term of 
                                SOME t => SOME( Cspm_API.mk_Sync (the semaphores_net_term) empty_evs_set t)
                                          (* par_const  $ thread_net_term  $ @{term empty}  $t *)
                               |NONE =>  semaphores_net_term)
  
                    val full_system_term = (case net1 of
                                          SOME t => Cspm_API.mk_Sync t UNIV_ thread_net_term
                                          (* par_const  $ net1 $ @{term UNIV} $ (t) *)
                                          |NONE => thread_net_term)
          
                    val _ = writeln ("[SYSTEM]  réseau complet :\n  " ^
                                     Syntax.string_of_term_global thy' full_system_term)
             (*   val _ = tracing ("\n [DEBUG] Type threads = " ^
                                 Syntax.string_of_typ_global @{theory} (fastype_of (thread_net_term) ))
                  val _ = tracing ("\n [DEBUG] Type lam_GLOBALVARS = " ^
                                 Syntax.string_of_typ_global @{theory} (fastype_of (the globals_net_term) )) 
                  val _ = tracing ("\n [DEBUG] Type semaphores_net_term = " ^
                                 Syntax.string_of_typ_global @{theory} (fastype_of (the semaphores_net_term) ))     
                  val _ = tracing ("\n [DEBUG] Type full_term = " ^
                                 Syntax.string_of_typ_global @{theory} (fastype_of (full_system_term) ))*)     
                     
              val _ =Thm.cterm_of (Proof_Context.init_global thy') full_system_term
              val const_bnd = #system checked
              val lthy_sys = Named_Target.theory_init thy'
              

              val const_type = fastype_of full_system_term
              val lhs_const = Free (Binding.name_of const_bnd, const_type)
              val def_eq = Logic.mk_equals (lhs_const, full_system_term)
              
              val ((lhs_term, (_, def_thm)), lthy') = 
                Specification.definition
                  {verbose = true}
                  (SOME (const_bnd, NONE, NoSyn))  (* binding option *)
                  []                               (* parameters list *)
                  []                               (* premises list *)
                  ((Binding.empty, []), def_eq)   (* attributes and equation *)
                  lthy_sys                         (* local theory *)
              
              (* Exit to global theory *)
              val thy'' = Local_Theory.exit_global lthy'
                 
         in
              thy''
            end)))
\<close>


section\<open>Tests\<close>

SYSTEM S
  globals 
  locks 
  thread empty:
         actions 
  thread empty2:
         actions 
end;
                                                     

SYSTEM System_A
  globals x:\<open>int\<close> = \<open>3 :: int\<close> var1:\<open>int\<close> = \<open>4::int\<close>  var4:\<open>int\<close> = \<open>4::int\<close>
  locks   l:\<open>()\<close>    l2:\<open>()\<close>   l3:\<open>()\<close>                                
  thread t1 : 
         any y : \<open>int\<close> = \<open>36 :: int\<close> var2 : \<open>int\<close>
         actions 
         SKIP;
         LOCK l;
          y <- var1;
         UNLOCK l;
         IF \<open>var1\<le>(3:: int)\<close> THEN 
            WHILE \<open>var1\<le>(3:: int)\<close> DO 
              LOCK l2;
              SKIP;
              var2 = \<open>var2 + 1 ::int\<close>;
              var1 -> \<open>var2 :: int\<close>;
              UNLOCK l2;                                                         
            DONE 
         ELSE
            SKIP;
         DONE
        y  = \<open>y+2 :: int\<close>;
        y  = \<open>y+2 :: int\<close>;
        var1 -> \<open>y :: int\<close>;

  thread t2 :
         any var2:\<open>int\<close> = \<open>(4+6) :: int\<close> y : \<open>int\<close> = \<open>28 :: int\<close>
         actions                          
         SKIP;
         LOCK l;

         UNLOCK l;
         IF \<open>3 = (5:: int)\<close> THEN 
            WHILE \<open>x -(8 ::int) < x \<close> DO 
              LOCK l; 
              UNLOCK l;
            DONE 
         ELSE
            SKIP;
         DONE
        y = \<open>var2 + 3 :: int\<close>; 
  thread t3:
       any test :int = \<open>-3 ::int\<close>  var_local :int = \<open>4 :: int\<close>   
       actions 
          var_local = \<open>(4+42) :: int\<close>;
          test = \<open>2* var_local :: int\<close>;
          test = \<open>test+3 :: int\<close>;
       IF \<open>x > (6 :: int)\<close> 
          THEN 
            WHILE \<open>x > (2 :: int)\<close> DO 
               test = \<open>test-3 :: int\<close>;
            DONE 
          ELSE
            test = \<open>test+3 :: int\<close>;
          DONE
end;               

thm t1_cmd_def empty2_cmd_def 
thm System_A_def

ML\<open>
val temp  = \<^term>\<open>Sem(t1_cmd)\<close>
val temp2 = \<^term>\<open>Sem(t1_cmd)\<close>
val temp3 = \<^term>\<open>(t1_cmd)\<close>         
val temp4 = \<^term>\<open>empty2_cmd\<close>

val tem2= Cspm_API.mk_Det temp temp2
\<close>

ML\<open>
val temp = \<^term>\<open>System_A\<close>

val c = Thm.cterm_of @{context} temp

\<close>

find_theorems (500)name : "CIL"
            
lemmas X = System_A_def [simplified t1_cmd_def t2_cmd_def t3_cmd_def Sem_def]


(*<*)
end  
(*>*)
