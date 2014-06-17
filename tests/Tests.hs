import Test.Tasty

import qualified NanoFeldsparTests
import qualified WellScopedTests
import qualified MonadTests

tests = testGroup "AllTests"
    [ NanoFeldsparTests.tests
    , WellScopedTests.tests
    , MonadTests.tests
    ]

main = defaultMain tests

