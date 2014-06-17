import Test.Tasty

import qualified NanoFeldsparTests
import qualified WellScopedTests

tests = testGroup "AllTests"
    [ NanoFeldsparTests.tests
    , WellScopedTests.tests
    ]

main = defaultMain tests

