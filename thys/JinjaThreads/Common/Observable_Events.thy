(*  Title:      JinjaThreads/Common/Observable_Events.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Observable events in JinjaThreads} *}

theory Observable_Events imports 
  Heap
  "../Framework/FWState"
begin

datatype obs_event =
    ExternalCall addr mname "val list" val
  | ReadMem addr addr_loc val
  | WriteMem addr addr_loc val
  | NewObj addr cname
  | NewArr addr ty nat
  | ThreadStart thread_id
  | ThreadJoin thread_id
  | SyncLock addr
  | SyncUnlock addr

types
  ('x, 'heap) Jinja_thread_action = "(addr,thread_id,'x,'heap,addr,obs_event list) thread_action"
  ('x, 'heap) JT_thread_action    = "(addr,thread_id,'x,'heap,addr,(addr, obs_event) observable list) thread_action"

translations
  (type) "('x, 'heap) Jinja_thread_action" <= (type) "(nat,nat,'x,'heap,nat,obs_event list) thread_action"
  (type) "('x, 'heap) JT_thread_action"    <= (type) "(nat,nat,'x,'heap,nat,(nat, obs_event) observable list) thread_action"

end