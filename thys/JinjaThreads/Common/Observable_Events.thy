(*  Title:      JinjaThreads/Common/Observable_Events.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Observable events in JinjaThreads} *}

theory Observable_Events imports 
  Objects
begin

datatype obs_event =
    ExternalCall addr mname "val list" val
  | Synchronization addr
  | ThreadStart thread_id
  | ThreadJoin thread_id

end