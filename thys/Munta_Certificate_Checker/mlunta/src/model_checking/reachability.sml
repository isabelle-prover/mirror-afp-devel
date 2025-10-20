functor ReachabilityChecker(Setup : CHECKING_SETUP) = struct

structure Reachability = ReachabilityChecker(Setup)
local open Property in
fun check system =
        case (Reachability.check system) of
            ((trace, _), true) => Satisfied trace
         |  ((trace, _), _) => Unsatisfied trace
end
end
