(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : POTS example
 *
 * Copyright (c) 2023 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)


chapter\<open> Example: Plain Old Telephone System\<close>

text\<open>The "Plain Old Telephone Service is a standard medium-size example for
     architectural modeling of a concurrent system. 

     Plain old telephone service (POTS), or plain ordinary telephone system,[1] 
     is a retronym for voice-grade telephone service employing analog signal  transmission over 
     copper loops. POTS was the standard service offering from telephone companies from 1876 until 
     1988[2] in the United States when the Integrated Services Digital Network (ISDN) Basic Rate 
     Interface (BRI) was introduced, followed by cellular telephone systems, and voice over 
     IP (VoIP). POTS remains the basic form of residential and small business service connection 
     to the telephone network in many parts of the world. The term reflects the technology that has 
     been available since the introduction of the public telephone system in the late 19th century, 
     in a form mostly unchanged despite the introduction of Touch-Tone dialing, electronic telephone 
     exchanges and fiber-optic communication into the public switched telephone network (PSTN).


     C.f. wikipedia \<^url>\<open>https://en.wikipedia.org/wiki/Plain_old_telephone_service\<close>.
\<close> (* rework this small text *)


theory POTS                                               
  imports CSPM 
begin 

text \<open>We need to see \<^typ>\<open>int\<close> as a \<^class>\<open>cpo\<close>.\<close>
\<comment>\<open>We may replace this instantiation by an import of "HOLCF-Library.Int_Discrete"\<close>
instantiation int :: discrete_cpo
begin

definition below_int_def:
  "(x::int) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_int_def)

end



section\<open> The Alphabet and Basic Types of POTS \<close>

text\<open>Underlying terminology apparent in the acronyms: 
\<^enum> T-side (target side, callee side)
\<^enum> O-side (originator (?) side, caller side)\<close>

datatype MtcO = Osetup | Odiscon_o
datatype MctO = Obusy  | Oalert    | Oconnect | Odiscon_t
datatype MtcT = Tbusy  | Talert    | Tconnect | Tdiscon_t
datatype MctT = Tsetup | Tdiscon_o

type_synonym Phones = \<open>int\<close>


datatype channels = tcO \<open>Phones \<times> MtcO\<close>            \<comment>\<open>  \<close>       
                  | ctO \<open>Phones \<times> MctO\<close>            
                  | tcT \<open>Phones \<times> MtcT \<times> Phones\<close> 
                  | ctT \<open>Phones \<times> MctT \<times> Phones\<close> 
                  | tcOdial    \<open>Phones \<times> Phones\<close>   
                  | StartReject Phones            \<comment>\<open> phone x rejects from now on to be called \<close>
                  | EndReject   Phones            \<comment>\<open> phone x accepts from now on to be called \<close>
                  | terminal    Phones 
                  | off_hook    Phones     
                  | on_hook     Phones      
                  | digits     \<open>Phones \<times> Phones\<close> \<comment>\<open> communication relation: x calls y \<close>     
                  | tone_ring   Phones    
                  | tone_quiet  Phones   
                  | tone_busy   Phones
                  | tone_dial   Phones    
                  | connected   Phones


locale POTS = 
  fixes min_phones :: int
    and max_phones :: int
    and VisibleEvents :: \<open>channels set\<close>
  assumes min_phones_g_1[simp]          :          \<open>1 \<le> min_phones\<close>
      and max_phones_g_min_phones[simp] : \<open>min_phones < max_phones\<close>
begin

definition phones :: \<open>Phones set\<close> where \<open>phones \<equiv> {min_phones ..  max_phones}\<close>

lemma nonempty_phones[simp]: \<open>phones \<noteq> {}\<close>
  and finite_phones[simp]: \<open>finite phones\<close>
  and at_least_two_phones[simp]: \<open>2 \<le> card phones\<close>
  and not_singl_phone[simp]: \<open>phones - {p} \<noteq> {}\<close>
  apply (simp_all add: phones_def)
  using max_phones_g_min_phones apply linarith+
  by (metis atLeastAtMost_iff less_le_not_le max_phones_g_min_phones order_refl singletonD subsetD)



definition  EventsIPhone :: \<open>Phones \<Rightarrow> channels set\<close>
  where    \<open>EventsIPhone u \<equiv> {tone_ring u, tone_quiet u, tone_busy u, tone_dial u, connected u}\<close>
definition  EventsUser :: \<open>Phones \<Rightarrow> channels set\<close>
  where    \<open>EventsUser u \<equiv> {off_hook u, on_hook u} \<union> {x . \<exists> n. x = digits (u, n)}\<close>



section\<open>Auxilliaries to Substructure the Specification\<close>

abbreviation Sliding :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process \<Rightarrow> '\<alpha> process\<close> (infixl \<open>\<rhd>\<close> 78)
  where \<open>P \<rhd> Q \<equiv> (P \<box> Q) \<sqinter> Q\<close>
\<comment> \<open>This operator is also called Timeout, more studied in future theories.\<close>

abbreviation
  Tside_connected     :: \<open>Phones \<Rightarrow> Phones \<Rightarrow> channels process\<close>
where \<open>Tside_connected ts os \<equiv> 
           (ctT\<^bold>!(ts,Tdiscon_o,os) \<rightarrow> tcT\<^bold>!(ts,Tdiscon_t,os) \<rightarrow> EndReject\<^bold>!ts\<rightarrow>SKIP)
       \<rhd> (tcT\<^bold>!(ts,Tdiscon_t,os) \<rightarrow> ctT\<^bold>!(ts,Tdiscon_o,os) \<rightarrow> EndReject\<^bold>!ts\<rightarrow>SKIP)\<close>



abbreviation
  Oside_connected     :: \<open>Phones \<Rightarrow> channels process\<close>
where   \<open>Oside_connected ts \<equiv>
            (ctO\<^bold>!(ts,Odiscon_t) \<rightarrow> tcO\<^bold>!(ts,Odiscon_o) \<rightarrow> EndReject\<^bold>!ts\<rightarrow>SKIP)
        \<rhd> (tcO\<^bold>!(ts,Odiscon_o) \<rightarrow> ctO\<^bold>!(ts,Odiscon_t) \<rightarrow> EndReject\<^bold>!ts\<rightarrow>SKIP)\<close>



abbreviation
   Oside1 :: \<open>[Phones, Phones] \<Rightarrow> channels process\<close>
where 
  \<open>Oside1 ts p \<equiv>  tcOdial\<^bold>!(ts,p)
	                 \<rightarrow>   (ctO\<^bold>!(ts,Oalert)
                         \<rightarrow> ctO\<^bold>!(ts,Oconnect)
                         \<rightarrow> (Oside_connected ts))
                      \<box>(ctO\<^bold>!(ts,Oconnect) \<rightarrow>(Oside_connected ts))
                      \<box>(ctO\<^bold>!(ts,Obusy) \<rightarrow> tcO\<^bold>!(ts,Odiscon_o) \<rightarrow> EndReject\<^bold>!ts \<rightarrow> SKIP)\<close>


definition
  ITside_connected    :: \<open>[Phones,Phones,channels process] \<Rightarrow> channels process\<close>
where
 \<open>ITside_connected ts os IT \<equiv> (ctT(ts,Tdiscon_o,os)
                                \<rightarrow>(  (tone_busy\<^bold>!ts
                                       \<rightarrow> on_hook\<^bold>!ts
                                       \<rightarrow> tcT\<^bold>!(ts,Tdiscon_t,os)
                                       \<rightarrow> EndReject\<^bold>!ts 
                                       \<rightarrow> IT)
                                   \<box> (on_hook\<^bold>!ts
                                       \<rightarrow> tcT\<^bold>!(ts,Tdiscon_t,os)
                                       \<rightarrow> EndReject\<^bold>!ts
                                       \<rightarrow> IT)
                                   ))
                                \<box> (on_hook\<^bold>!ts
                                     \<rightarrow> tcT\<^bold>!(ts,Tdiscon_t,os)
                                     \<rightarrow> ctT\<^bold>!(ts,Tdiscon_o,os)
                                     \<rightarrow> EndReject\<^bold>!ts
                                     \<rightarrow>IT)\<close>


section\<open>A Telephone \<close>

fixrec     T        :: \<open>Phones \<rightarrow> channels process\<close>
       and Oside    :: \<open>Phones \<rightarrow> channels process\<close>
       and Tside    :: \<open>Phones \<rightarrow> channels process\<close>
       and NoReject :: \<open>Phones \<rightarrow> channels process\<close>
       and Reject   :: \<open>Phones \<rightarrow> channels process\<close>
where
   T_rec        [simp del]: \<open>T\<cdot>ts        = (Tside\<cdot>ts \<^bold>; T\<cdot>ts) \<rhd> (Oside\<cdot>ts \<^bold>; T\<cdot>ts)\<close>
 | Oside_rec    [simp del]: \<open>Oside\<cdot>ts    = StartReject\<^bold>!ts 
                                              \<rightarrow> tcO\<^bold>!(ts,Osetup) 
                                              \<rightarrow> (\<Sqinter> p \<in> phones. Oside1 ts p)\<close>
 | Tside_rec    [simp del]: \<open>Tside\<cdot>ts    = ctT\<^bold>?(y,z,os)\<^bold>|((y,z)=(ts,Tsetup)) 
                                              \<rightarrow> StartReject\<^bold>!ts 
                                              \<rightarrow> (   tcT\<^bold>!(ts,Talert,os)
                                                     \<rightarrow> tcT\<^bold>!(ts,Tconnect,os)
                                                     \<rightarrow>(Tside_connected ts os)
                                                  \<sqinter> (tcT\<^bold>!(ts,Tconnect,os)
                                                     \<rightarrow> (Tside_connected ts os)))\<close>  
 | NoReject_rec [simp del]: \<open>NoReject\<cdot>ts = StartReject\<^bold>!ts \<rightarrow> Reject\<cdot>ts\<close>
 | Reject_rec   [simp del]: \<open>Reject\<cdot>ts   = ctT\<^bold>?(y,z,os)\<^bold>|(y=ts \<and> z=Tsetup \<and> os\<in>phones \<and> os\<noteq>ts)
                                              \<rightarrow>     (tcT\<^bold>!(ts,Tbusy,os) \<rightarrow> Reject\<cdot>ts)
                                                 \<box>  (EndReject\<^bold>!ts \<rightarrow> NoReject\<cdot>ts)\<close>





definition Tel:: \<open>Phones \<Rightarrow> channels process\<close>
  where   \<open>Tel p \<equiv> (T\<cdot>p \<lbrakk>{StartReject p, EndReject p}\<rbrakk> NoReject\<cdot>p) \ {StartReject p, EndReject p}\<close>




section\<open> A Connector with the Network \<close>

fixrec     Call      :: \<open>Phones \<rightarrow> channels process\<close>
       and BUSY      :: \<open>Phones \<rightarrow> Phones \<rightarrow> channels process\<close>
       and Connected :: \<open>Phones \<rightarrow> Phones \<rightarrow> channels process\<close>
where
   Call_rec  [simp del]: \<open>Call\<cdot>os     = (tcO\<^bold>!  (os,Osetup) \<rightarrow> tcOdial\<^bold>?(x,ts)\<^bold>|(x=os) \<rightarrow> (BUSY\<cdot>os\<cdot>ts)) \<^bold>; Call\<cdot>os\<close>
 | BUSY_rec  [simp del]: \<open>BUSY\<cdot>os\<cdot>ts  = (if ts = os 
                              then ctO\<^bold>!(os,Obusy) \<rightarrow> tcO\<^bold>!(os,Odiscon_o) \<rightarrow> SKIP
                              else ctT\<^bold>!(ts,Tsetup,os)
                                   \<rightarrow>( (tcT\<^bold>!(ts,Tbusy,os)
                                          \<rightarrow> ctO\<^bold>!(os,Obusy)
                                          \<rightarrow> tcO\<^bold>!(os,Odiscon_o) \<rightarrow> SKIP)
                                       \<box>
                                         (tcT \<^bold>! (ts,Talert,os)
                                          \<rightarrow> ctO\<^bold>!(os,Oalert)
                                          \<rightarrow> tcT\<^bold>!(ts,Tconnect,os)
                                          \<rightarrow> ctO\<^bold>!(os,Oconnect)
                                          \<rightarrow> Connected\<cdot>os\<cdot>ts)
                                       \<box>
                                         (tcT\<^bold>!(ts,Tconnect,os)
                                          \<rightarrow> ctO\<^bold>!(os,Oconnect)
                                          \<rightarrow> Connected\<cdot>os\<cdot>ts)))\<close>
 | Connected_rec [simp del]: \<open>Connected\<cdot>os\<cdot>ts =  (tcO\<^bold>!(os,Odiscon_o) \<rightarrow>
                             (( (ctT\<^bold>!(ts,Tdiscon_o,os) \<rightarrow> tcT\<^bold>!(ts,Tdiscon_t,os) \<rightarrow> SKIP)
                                \<box> 
                                (tcT\<^bold>!(ts,Tdiscon_t,os)\<rightarrow> ctT\<^bold>!(ts,Tdiscon_o,os) \<rightarrow> SKIP)
                              )
                              \<^bold>; (ctO\<^bold>!(os,Odiscon_t) \<rightarrow> SKIP)))
                              \<box>
                             (tcT\<^bold>!(ts,Tdiscon_t,os) \<rightarrow>
                                     (  (ctO\<^bold>!(os,Odiscon_t) 
                                         \<rightarrow> ctT\<^bold>!(ts,Tdiscon_o,os) 
                                         \<rightarrow> tcO\<^bold>!(os,Odiscon_o) 
                                         \<rightarrow> SKIP )
                                        \<box>
                                        (tcO\<^bold>!(os,Odiscon_o) 
                                         \<rightarrow> ctT\<^bold>!(ts,Tdiscon_o,os) 
                                         \<rightarrow> ctO\<^bold>!(os,Odiscon_t)
                                         \<rightarrow> SKIP) 
                                     )
                             )\<close>



section\<open> Combining NETWORK and TELEPHONES to a SYSTEM \<close>

definition  NETWORK     :: \<open>channels process\<close>
  where      \<open>NETWORK     \<equiv>  (\<^bold>|\<^bold>|\<^bold>| os \<in># (mset_set phones). Call\<cdot>os)\<close>

definition  TELEPHONES  :: \<open>channels process\<close>               
  where      \<open>TELEPHONES  \<equiv>  (\<^bold>|\<^bold>|\<^bold>| ts \<in># (mset_set phones). Tel ts)\<close>

definition  SYSTEM      :: \<open>channels process\<close>
  where      \<open>SYSTEM      \<equiv>  NETWORK \<lbrakk>VisibleEvents\<rbrakk> TELEPHONES\<close>

text \<open>We underline here the usefulness of the architectural operators, especially \<^const>\<open>MultiSync\<close>
      but also \<^const>\<open>MultiNdet\<close> which appears in \<^const>\<open>Oside\<close> recursive definition.\<close>




section\<open>Simple Model of a User \<close>

fixrec     User      :: \<open>Phones \<rightarrow> channels process\<close>
       and UserSCon  :: \<open>Phones \<rightarrow> channels process\<close>
where
  User_rec[simp del]  : \<open>User\<cdot>u = (off_hook\<^bold>!u \<rightarrow>
                         (tone_dial\<^bold>!u \<rightarrow>
                          (\<Sqinter> p \<in> phones. digits\<^bold>!(u,p)\<rightarrow>tone_quiet\<^bold>!u\<rightarrow>
                                          (  (tone_ring\<^bold>!u\<rightarrow>connected\<^bold>!u\<rightarrow>UserSCon\<cdot>u)
                                           \<box> (connected\<^bold>!u\<rightarrow>UserSCon\<cdot>u)
                                           \<box> (tone_busy\<^bold>!u\<rightarrow>on_hook\<^bold>!u\<rightarrow>User\<cdot>u)
                                          )
                          )
                         )
                       \<box> (connected\<^bold>!u \<rightarrow> UserSCon\<cdot>u)
                       )
                        \<box> (tone_ring\<^bold>!u\<rightarrow>off_hook\<^bold>!u\<rightarrow>connected\<^bold>!u \<rightarrow>UserSCon\<cdot>u)\<close>
  | UserSCon_rec[simp del]: \<open>UserSCon\<cdot>u = (tone_busy\<^bold>!u \<rightarrow> on_hook\<^bold>!u \<rightarrow> User\<cdot>u) \<rhd> (on_hook\<^bold>!u \<rightarrow> User\<cdot>u)\<close>



fixrec     User_Ndet      :: \<open>Phones \<rightarrow> channels process\<close>
       and UserSCon_Ndet  :: \<open>Phones \<rightarrow> channels process\<close>
where
  User_Ndet_rec[simp del]  : \<open>User_Ndet\<cdot>u = (off_hook\<^bold>!u \<rightarrow>
                         (tone_dial\<^bold>!u \<rightarrow>
                          (\<Sqinter> p \<in> phones. digits\<^bold>!(u,p)\<rightarrow>tone_quiet\<^bold>!u\<rightarrow>
                                          (  (tone_ring\<^bold>!u\<rightarrow>connected\<^bold>!u\<rightarrow>UserSCon_Ndet\<cdot>u)
                                           \<sqinter> (connected\<^bold>!u\<rightarrow>UserSCon_Ndet\<cdot>u)
                                           \<sqinter> (tone_busy\<^bold>!u\<rightarrow>on_hook\<^bold>!u\<rightarrow>User_Ndet\<cdot>u)
                                          )
                          )
                         )
                       \<sqinter> (connected\<^bold>!u \<rightarrow> UserSCon_Ndet\<cdot>u)
                       )
                        \<sqinter> (tone_ring\<^bold>!u\<rightarrow>off_hook\<^bold>!u\<rightarrow>connected\<^bold>!u \<rightarrow>UserSCon_Ndet\<cdot>u)\<close>
  | UserSCon_Ndet_rec[simp del]: \<open>UserSCon_Ndet\<cdot>u = (tone_busy\<^bold>!u \<rightarrow> on_hook\<^bold>!u \<rightarrow> User_Ndet\<cdot>u) \<sqinter> (on_hook\<^bold>!u \<rightarrow> User_Ndet\<cdot>u)\<close>



definition  ImplementT          :: \<open>Phones \<Rightarrow> channels process\<close>
  where    \<open>ImplementT ts \<equiv> ((Tel ts) \<lbrakk>EventsIPhone ts \<union> EventsUser ts\<rbrakk> (User\<cdot>ts))
                            \ (EventsIPhone ts \<union> EventsUser ts)\<close>




section \<open> Toplevel Proof-Goals\<close>

text\<open> This has been proven in an ancient FDR model for @{term \<open>max_phones = 5\<close>}...  \<close>


lemma \<open>\<forall>p \<in> phones. deadlock_free (Tel p)\<close> oops
lemma \<open>\<forall>p \<in> phones. deadlock_free_v2 (Call\<cdot>p)\<close> oops
lemma \<open>deadlock_free_v2 NETWORK\<close> oops
lemma \<open>deadlock_free_v2 SYSTEM\<close> oops
lemma \<open>lifelock_free SYSTEM\<close> oops 
lemma \<open>\<forall>p \<in> phones. lifelock_free (ImplementT p)\<close> oops
lemma \<open>\<forall>p \<in> phones. Tel p \<sqsubseteq>\<^sub>F\<^sub>D ImplementT p\<close> oops
                                
lemma \<open>\<forall>p \<in> phones. Tel'\<cdot>p  \<sqsubseteq>\<^sub>F RUN UNIV\<close> oops
text\<open>this should represent "deterministic" in process-algebraic terms. . .\<close>


end

end