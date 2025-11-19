functor AlwaysEventually(Setup : CHECKING_SETUP) = struct
structure Cyclicity = CyclicityChecker(Setup)

fun check system =
    case Cyclicity.check system of
        ((trace, _), true) => Property.Satisfied trace |
        ((trace, _), _) => Property.Unsatisfied trace
end
