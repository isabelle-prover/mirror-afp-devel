(*<*)
(*
   Title:  Gateway_types.thy  (Input/Output Definitions)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*) 
(*>*)
 header {* Gateway: Types*} 

theory Gateway_types 
imports stream
begin

type_synonym
   Coordinates = "nat \<times> nat"
type_synonym 
   CollisionSpeed = "nat"

record ECall_Info = 
   coord :: Coordinates
   speed :: CollisionSpeed

datatype_new GatewayStatus = 
    init_state
  | call
  | connection_ok
  | sending_data
  | voice_com

datatype_new reqType = init | send

datatype_new stopType = stop_vc

datatype_new vcType = vc_com

datatype_new aType = sc_ack

end